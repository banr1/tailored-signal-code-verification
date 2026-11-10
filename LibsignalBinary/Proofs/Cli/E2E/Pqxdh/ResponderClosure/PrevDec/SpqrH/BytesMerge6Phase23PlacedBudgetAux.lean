/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10Budget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6Phase23Placed
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.Basic
import ProofLib.SepLogic.WP
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Handshake `bytes::merge [local#5]` Epilogues and Phase 3

Defines the unified `bytesMergeRawSpecXBoth` inner budget contract and monotonic postcondition
bridges, and proves the `[LibsignalPlacement]` Block-`514` error/drop epilogues (`+0x074`,
`+0x07c`, `+0x254`) and Phase 3 (`+0x210`, `+0x230`) under `RustCliAllocBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6Phase23PlacedBudgetAux

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpecWithStack)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
  (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv doReserveEvents fitsEnv_doReserve_iff
   framelessMemcpyBudgetSpec noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
  (bytesDropEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bmPostVec bytesMergeEventsCore bytesMergeRawSpecGen doReserveClearEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
  (MergePanicGen MergePostGen bmMemcpySpecGen bmMemcpy_placed_of_region bmShimSpecGen
   bmShim_placed_of_base bytesVtableDropSpecBMGen)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux
  (bmMemcpy_placed_of_framelessBudget bmShim_placed_of_noAllocShim doReserveClearEvents_of_le
   doReserveEvents_eq_clear mergeBytes_length_sum)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10Budget
  (doReserve1VecSpecX)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded lsρ lsmpl withLsCl)
open CryptoVerification.CliHandshake.Placed
  (blkLib_eq_514 blkPC_514 blkPl_514 lsProg_514)
open CryptoVerification.RustHeap
  (vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall KindNoHeap bytesBoxU8Buf bytesData bytesPlacedDropFnAddr bytesPlacedVtable
   bytesPtr decodeErrorAtStackLen doReserveStackX extHookStack reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost SepWP.drop_left SepWP.with_vtableSlot_placed
   SepWPp.bm_call_frame_lscl SepWPp.bm_of_sepWP_lscl bitvec_ult_zero bmCapCond
   bmCapCond_after_reserve bmCapCond_mono bmExtraStack bmLenBound bmLenBound_lt63
   bmSliceStack bmTotalStack bm_HighCalleeSaved bm_reserveCap_bound
   bm_vecU8At_eq_header_sep_buf bytesBoxU8Buf_nonempty bytesMergeStackX bytesMutDataWord_bit0
   bytesMutDataWord_getElem_zero bytesMutDataWord_getLsbD_zero bytesMutDataWord_lsr5
   bytesMutDataWord_zero decodeErrorHookStackX decodeVarintSliceStackX
   fold_bytesBoxU8Buf_nonempty fold_stackAt_bytesMergeGen fold_vecU8At_clear
   fold_vecU8At_copied savedRegsStack sliceCursorAfter sliceCursorAt spAligned_sub_224
   stackAt_sliceGen_split vecU8At_entails_bmPostVec vecU8At_nil_eq)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
  (vecU8At_entails_existsBoth)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero

/-! ## 1. Stack Constants, Unified `bytesMergeRawSpecXBoth`, & Postcondition Bridges -/

theorem hbnd_x : bmTotalStack decodeErrorHookStackX ≤ 2 ^ 64 := by decide

theorem hdrop_le_x : extHookStack + 48 ≤ bmSliceStack decodeErrorHookStackX := by decide

theorem hres_le_x : (extHookStack + 48) + 64 ≤ bmSliceStack decodeErrorHookStackX := by decide

theorem hslice_eq_x : decodeVarintSliceStackX = bmSliceStack decodeErrorHookStackX := by decide

/-- Unified inner (`bytesMergeStackX`) budget-threaded specification supporting both
`BytesMergeCapOk` (`< 2 ^ 63`) and unconstrained-capacity `< 2 ^ 62` (`W`). -/
def bytesMergeRawSpecXBoth {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      (BytesMergeCapOk x.valCap x.bs.length ∨ x.bs.length < 2 ^ 62) ∧
      FitsEnv M lim st (BytesMergeEnv x)⌝ ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp bytesMergeStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜BytesMergeEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp bytesMergeStackX ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk x.valCap x.bs.length → BytesMergeCapOk cap' rest.length⌝ ∗
              vecU8At A.repAlloc x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

abbrev MergePostXBoth {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMergeRawSpecXBoth A lim).post (x, st) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergePanicXBoth {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMergeRawSpecXBoth A lim).onPanic (x, st) s0 sf ∗ R)

private theorem bmPostVec_entails_xBoth {reqCap : Bool} {A : CryptoVerification.RustHeap.RustAlloc}
    {P : Prop} {valPtr : BitVec 64} {v rest : List (BitVec 8)}
    (himp : ∀ cap' : BitVec 64, bmCapCond reqCap cap' rest.length →
      (P → BytesMergeCapOk cap' rest.length)) :
    bmPostVec reqCap A valPtr v rest ⊢
      ∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜P → BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A valPtr cap' ptr' v := by
  cases reqCap
  · dsimp only [bmPostVec]
    refine Entails.sepExists_elim fun cap' => Entails.sepExists_elim fun ptr' => ?_
    exact vecU8At_entails_existsBoth A (fun c => P → BytesMergeCapOk c rest.length)
      valPtr cap' ptr' v (himp cap' trivial)
  · dsimp only [bmPostVec]
    refine Entails.sepExists_elim fun cap' => Entails.sepExists_elim fun ptr' =>
      Entails.pure_left fun hm => ?_
    exact vecU8At_entails_existsBoth A (fun c => P → BytesMergeCapOk c rest.length)
      valPtr cap' ptr' v (himp cap' hm)

theorem sepWPp_xBoth_of_reqCap {M : AllocCostModel} {prog : Program}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {reqCap : Bool}
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {P R : SepProp}
    (himp : ∀ cap' restLen, bmCapCond reqCap cap' restLen →
      (BytesMergeCapOk x.valCap x.bs.length → BytesMergeCapOk cap' restLen))
    (h : SepWPp prog (s0.readReg64 .lr) s P
      (MergePostGen decodeErrorHookStackX reqCap A lim x st s0 R)
      (MergePanicGen decodeErrorHookStackX reqCap A lim x st s0 R)) :
    SepWPp prog (s0.readReg64 .lr) s P
      (MergePostXBoth A lim x st s0 R)
      (MergePanicXBoth A lim x st s0 R) := by
  intro F hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h F hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, ?_, hsp, hcs⟩⟩
    intro hmr
    have hp := hpost hmr
    dsimp only [bytesMergeRawSpecGen, bytesMergeRawSpecXBoth] at hp ⊢
    change sf.mem ⊨
      (⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
        (∃∗ evs : List AllocEvent, ⌜BytesMergeEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        stackAt s0.sp bytesMergeStackX ∗ _) ∗ R at hp
    cases hm_eq : mergeBytes x.wt x.bs with
    | none =>
      simpa only [hm_eq] using hp
    | some vr =>
      rcases vr with ⟨v, rest⟩
      simp only [hm_eq] at hp ⊢
      refine Satisfies.mono ?_ hp
      refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))))))
      exact bmPostVec_entails_xBoth (fun cap' hc => himp cap' rest.length hc)
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, hpanic⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem sepWPp_xBoth_of_capInv {M : AllocCostModel} {prog : Program}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {P R : SepProp}
    (hbs_len : x.bs.length < 2 ^ 63)
    (hcapInv : BytesMergeCapOk x.valCap x.bs.length ∨ x.bs.length < 2 ^ 62)
    (hgen : ∀ reqCap : Bool,
      bmLenBound reqCap x.bs.length →
      bmCapCond reqCap x.valCap x.bs.length →
      SepWPp prog (s0.readReg64 .lr) s P
        (MergePostGen decodeErrorHookStackX reqCap A lim x st s0 R)
        (MergePanicGen decodeErrorHookStackX reqCap A lim x st s0 R)) :
    SepWPp prog (s0.readReg64 .lr) s P
      (MergePostXBoth A lim x st s0 R)
      (MergePanicXBoth A lim x st s0 R) := by
  by_cases hcap : BytesMergeCapOk x.valCap x.bs.length
  · exact sepWPp_xBoth_of_reqCap (reqCap := true) (fun _ _ hc _ => hc) (hgen true hbs_len hcap)
  · have hbs62 : x.bs.length < 2 ^ 62 := hcapInv.resolve_left hcap
    exact sepWPp_xBoth_of_reqCap (reqCap := false) (fun _ _ _ hc => absurd hc hcap)
      (hgen false hbs62 trivial)

theorem sepWPp_xBoth_of_capImp {M : AllocCostModel} {prog : Program}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {P R : SepProp}
    {cap' : BitVec 64} {restLen : Nat}
    (hcapImp : BytesMergeCapOk x.valCap x.bs.length → BytesMergeCapOk cap' restLen)
    (hgen : ∀ reqCap : Bool,
      bmCapCond reqCap cap' restLen →
      SepWPp prog (s0.readReg64 .lr) s P
        (MergePostGen decodeErrorHookStackX reqCap A lim x st s0 R)
        (MergePanicGen decodeErrorHookStackX reqCap A lim x st s0 R)) :
    SepWPp prog (s0.readReg64 .lr) s P
      (MergePostXBoth A lim x st s0 R)
      (MergePanicXBoth A lim x st s0 R) := by
  by_cases hcap : BytesMergeCapOk x.valCap x.bs.length
  · exact sepWPp_xBoth_of_reqCap (reqCap := true) (fun _ _ hc _ => hc) (hgen true (hcapImp hcap))
  · exact sepWPp_xBoth_of_reqCap (reqCap := false) (fun _ _ _ hc => absurd hc hcap)
      (hgen false trivial)

theorem sepWPp_xBoth_of_none {M : AllocCostModel} {prog : Program}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {P R : SepProp}
    (hmerge : mergeBytes x.wt x.bs = none)
    (h : SepWPp prog (s0.readReg64 .lr) s P
      (MergePostGen decodeErrorHookStackX false A lim x st s0 R)
      (MergePanicGen decodeErrorHookStackX false A lim x st s0 R)) :
    SepWPp prog (s0.readReg64 .lr) s P
      (MergePostXBoth A lim x st s0 R)
      (MergePanicXBoth A lim x st s0 R) := by
  intro F hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h F hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, ?_, hsp, hcs⟩⟩
    intro hmr
    have hp := hpost hmr
    dsimp only [bytesMergeRawSpecGen, bytesMergeRawSpecXBoth] at hp ⊢
    change sf.mem ⊨
      (⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
        (∃∗ evs : List AllocEvent, ⌜BytesMergeEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        stackAt s0.sp bytesMergeStackX ∗ _) ∗ R at hp
    simpa only [hmerge] using hp
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, hpanic⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-! ## 2. Error & Drop Epilogue Lemmas on Block `514` (`+0x074`, `+0x07c`, `+0x254`) -/

theorem epilogue6_err_0x07c_gen_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {reqCap : Bool}
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    (hmerge : mergeBytes x.wt x.bs = none)
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ st_cur = M.stepEvents evs st)
    (hpc : s.pc = (blkPl_514).base + 124#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 ≠ 0#64)
    (hhigh : bm_HighCalleeSaved s0 s) :
    SepWPp (lsProg_514 H) (s0.readReg64 .lr) s
      (decodeErrorAtStackLen A.repAlloc (s.readReg64 .x0) 0 ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen decodeErrorHookStackX reqCap A lim x st s0 R)
      (MergePanicGen decodeErrorHookStackX reqCap A lim x st s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh
  rcases hevs with ⟨evs, hevs_env, rfl⟩
  dsimp only [savedRegsStack] at hpc ⊢
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeGen s0.sp decodeErrorHookStackX hbnd_x
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by rw [hslice_eq_x]; sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
      h25, h26, h27, h28, hvregs, and_self]⟩
  intro hmf
  dsimp only [Reg.x0, bmTotalStack, bmSliceStack] at hx0 hmf ⊢
  simp (config := { decide := true }) only [bytesMergeRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64,
    RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    Reg.x0, hx0, htrace, ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  simp only [hevs_env, pure_true, emp_sepConj]
  convert hmf using 2
  sep_ac_rfl

theorem epilogue6_err_0x07c_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    (hmerge : mergeBytes x.wt x.bs = none)
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ st_cur = M.stepEvents evs st)
    (hpc : s.pc = (blkPl_514).base + 124#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 ≠ 0#64)
    (hhigh : bm_HighCalleeSaved s0 s) :
    SepWPp (lsProg_514 H) (s0.readReg64 .lr) s
      (decodeErrorAtStackLen A.repAlloc (s.readReg64 .x0) 0 ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostXBoth A lim x st s0 R)
      (MergePanicXBoth A lim x st s0 R) :=
  sepWPp_xBoth_of_none hmerge
    (epilogue6_err_0x07c_gen_placed hmerge hevs hpc hrun hsp hsp_align htrace hx0 hhigh)

theorem epilogue6_decodeErrorFrom_0x074_gen_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {reqCap : Bool}
    (hdef : subroutine_ok (lsProg_514 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {R : SepProp} {w : BitVec 64}
    (hw : KindNoHeap w)
    (hmerge : mergeBytes x.wt x.bs = none)
    (hfits : FitsEnv M lim st (BytesMergeEnv x))
    (hpc : s.pc = (blkPl_514).base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    SepWPp (lsProg_514 H) (s0.readReg64 .lr) s
      (((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool lim st s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen decodeErrorHookStackX reqCap A lim x st s0 R)
      (MergePanicGen decodeErrorHookStackX reqCap A lim x st s0 R) := by
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
      A.pool lim st _ ∗ stackAt (s0.sp - 224#64) decodeErrorHookStackX)
    hdef hcl_call hro_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeErrorFromBudgetSpecWithStack, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [KindNoHeap, wp_norm, arm64_norm, hsp, hw, hfits_de, and_self])
    (by
      rw [hslice_eq_x]
      rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackX decodeErrorHookStackX
        (Nat.le_add_left decodeErrorHookStackX 0x50) hbnd_x]
      sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (by intro _ _ hm; dsimp only [decodeErrorFromBudgetSpecWithStack] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
  intro sf_de hpcf hrunf hspf hcsf _ _
  have hhigh' : bm_HighCalleeSaved s0 sf_de := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [decodeErrorFromBudgetSpecWithStack, arm64_norm, hsp, htrace]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.pure_elim fun ⟨⟨hx0, htr⟩, hevs_de⟩ => ?_
  have hevs_bm : BytesMergeEnv x evs := by
    simpa only [BytesMergeEnv, bytesMergeEventsCore, hmerge, DecodeErrorFromEnv] using hevs_de
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackX))
    (by
      rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackX decodeErrorHookStackX
        (Nat.le_add_left decodeErrorHookStackX 0x50) hbnd_x]
      exact Entails.refl _) (by sep_focus)
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeGen s0.sp decodeErrorHookStackX hbnd_x
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
      h25, h26, h27, h28, hvregs, and_self]⟩
  intro hmf
  dsimp only [bmTotalStack, bmSliceStack] at hmf
  simp (config := { decide := true }) only [bytesMergeRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64,
    RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    Reg.x0, hx0, htr, ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  simp only [hevs_bm, pure_true, emp_sepConj]
  convert hmf using 2
  sep_ac_rfl

theorem epilogue6_decodeErrorFrom_0x074_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_514 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {R : SepProp} {w : BitVec 64}
    (hw : KindNoHeap w)
    (hmerge : mergeBytes x.wt x.bs = none)
    (hfits : FitsEnv M lim st (BytesMergeEnv x))
    (hpc : s.pc = (blkPl_514).base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    SepWPp (lsProg_514 H) (s0.readReg64 .lr) s
      (((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool lim st s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostXBoth A lim x st s0 R)
      (MergePanicXBoth A lim x st s0 R) :=
  sepWPp_xBoth_of_none hmerge
    (epilogue6_decodeErrorFrom_0x074_gen_placed hdef hw hmerge hfits hpc hrun hsp hsp_align
      htrace hhigh hcl hro)

theorem epilogue6_vtableDrop_0x254_gen_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {reqCap : Bool}
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_514 H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim extHookStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st)
    (hcapOk : bmCapCond reqCap cap' rest.length)
    (hpc : s.pc = (blkPl_514).base + 596#64)
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
    SepWPp (lsProg_514 H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr cap' ptr' v ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen decodeErrorHookStackX reqCap A lim x st s0 R)
      (MergePanicGen decodeErrorHookStackX reqCap A lim x st s0 R) := by
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
    (T := bytesBoxU8Buf A.repAlloc tmpPtr v ∗ A.pool lim st_cur _ ∗
      stackAt (s0.sp - 224#64) (extHookStack + 48))
    hVtableDrop hcl_call hro_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bytesVtableDropSpecBMGen, arm64_norm, hsp]; rfl)
    (by
      simp only [Nat.le_refl, Nat.sub_self, BitVec.ofNat_eq_ofNat, true_and]
      simp only [wp_norm, arm64_norm, blkPl_514]
      apply lsRetAddr624_blockPlacement_base_add <;> decide)
    (by
      rw [hslice_eq_x]
      rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackX (extHookStack + 48) hdrop_le_x hbnd_x]
      sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (by intro _ _ hm; dsimp only [bytesVtableDropSpecBMGen] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
  intro sf_dr hpcf hrunf hspf hcsf _ _
  have hhigh' : bm_HighCalleeSaved s0 sf_dr := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [bytesVtableDropSpecBMGen, hevs_eq, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun htr => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackX))
    (by
      rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackX (extHookStack + 48) hdrop_le_x hbnd_x]
      exact Entails.refl _) (by sep_focus)
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeGen s0.sp decodeErrorHookStackX hbnd_x
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.fold (vecU8At_entails_bmPostVec reqCap A.repAlloc x.valPtr cap' ptr' v rest hcapOk)
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
      h25, h26, h27, h28, hvregs, and_self]⟩
  intro hmf
  dsimp only [bmTotalStack, bmSliceStack,
    CryptoVerification.LibsignalTripleRatchet.Prost.bmPostVec] at hmf
  simp (config := { decide := true }) only [bytesMergeRawSpecGen,
    LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPostVec, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64,
    RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    Reg.x0, htr, ↓reduceIte, pure_true, emp_sepConj, sepExists_sepConj_left,
    sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  simp only [hevs_env, pure_true, emp_sepConj]
  convert hmf using 2
  cases reqCap <;> dsimp only <;> sep_ac_rfl

theorem epilogue6_vtableDrop_0x254_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_514 H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim extHookStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st)
    (hcapImp : BytesMergeCapOk x.valCap x.bs.length → BytesMergeCapOk cap' rest.length)
    (hpc : s.pc = (blkPl_514).base + 596#64)
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
    SepWPp (lsProg_514 H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr cap' ptr' v ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostXBoth A lim x st s0 R)
      (MergePanicXBoth A lim x st s0 R) :=
  sepWPp_xBoth_of_capImp hcapImp fun _reqCap hcapOk =>
    epilogue6_vtableDrop_0x254_gen_placed hVtableDrop hmerge hevs hcapOk hpc hrun hsp hsp_align
      htrace hhigh hcl hro hx21 hx22 hx24

/-! ## 3. Phase 3 (`+0x210..+0x250`, `+0x29c..+0x2bc`) on Block `514` -/

theorem phase3_6_from_0x230_gen_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {reqCap : Bool}
    (hmc : subroutine_ok (lsProg_514 H) (lsρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen decodeErrorHookStackX)))
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_514 H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim extHookStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st)
    (hcapOk : bmCapCond reqCap cap' rest.length)
    (hcap' : v.length ≤ cap'.toNat)
    (hv_len : v.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_514).base + 560#64)
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
    SepWPp (lsProg_514 H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr cap' ptr' [] ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen decodeErrorHookStackX reqCap A lim x st s0 R)
      (MergePanicGen decodeErrorHookStackX reqCap A lim x st s0 R) := by
  rcases v with _ | ⟨b0, v'⟩
  · have hep := fun {s : State} =>
      @epilogue6_vtableDrop_0x254_gen_placed _ M A lim H reqCap x st st_cur s0 s R [] rest tmpPtr cap' ptr'
        hVtableDrop hmerge hevs hcapOk
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_514).base + 596#64)
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
    exact Entails.of_eq (by
      simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
        RustCliAllocBudget.pool_writeReg64])
  · set v := b0 :: v'
    have hep := fun {s : State} =>
      @epilogue6_vtableDrop_0x254_gen_placed _ M A lim H reqCap x st st_cur s0 s R v rest tmpPtr cap' ptr'
        hVtableDrop hmerge hevs hcapOk
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
        stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackX) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0))
      (Entails.of_eq (by
        rw [hslice_eq_x]
        sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨htmp_ne, hv_lt63⟩ => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsρ "memcpy")
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.bm_call_frame_lscl (x := (ptr', tmpPtr, v))
      (T := memRegion ptr' v.length ∗ (tmpPtr ↦ₛ v) ∗
        stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackX))
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
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, _, _, _, _, h29f, _⟩ := hcsf
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
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_514).base + 596#64)
    apply sepWP_seg_ls_vm (Q := lsProg_514 (hooksException H)) blkLib_eq_514
      (mid := (blkPl_514).base + 596#64)
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
      (hnext := ?_)
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
      (by
        obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh'
        simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
          h25, h26, h27, h28, hvregs, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21, h20f, hx20, hbytesPtr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24]))
    exact Entails.of_eq (by
      rw [hslice_eq_x]
      sep_ac_rfl)

theorem phase3_6_from_0x230_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hmc : subroutine_ok (lsProg_514 H) (lsρ "memcpy") framelessMemcpyBudgetSpec)
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_514 H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim extHookStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st)
    (hcapImp : BytesMergeCapOk x.valCap x.bs.length → BytesMergeCapOk cap' rest.length)
    (hcap' : v.length ≤ cap'.toNat)
    (hv_len : v.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_514).base + 560#64)
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
    SepWPp (lsProg_514 H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr cap' ptr' [] ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostXBoth A lim x st s0 R)
      (MergePanicXBoth A lim x st s0 R) :=
  sepWPp_xBoth_of_capImp hcapImp fun _reqCap hcapOk =>
    phase3_6_from_0x230_gen_placed (bmMemcpy_placed_of_framelessBudget hmc) hVtableDrop hmerge
      hevs hcapOk hcap' hv_len hpc hrun hsp hsp_align htrace hhigh hcl hro
      hx19 hx20 hx21 hx22 hx23 hx24

theorem phase3_6_from_0x210_gen_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {reqCap : Bool}
    (hmc : subroutine_ok (lsProg_514 H) (lsρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen decodeErrorHookStackX)))
    (hReserve : subroutine_ok (lsProg_514 H) (lsmpl.base 517)
      (withLsCl lsmpl (doReserve1VecSpecX M A lim)))
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_514 H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim extHookStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hfits_res : FitsEvents M lim st_cur (doReserveClearEvents x.valCap.toNat v.length))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧
      M.stepEvents (doReserveClearEvents x.valCap.toNat v.length ++ bytesDropEvents v) st_cur =
        M.stepEvents evs st)
    (hv_len : v.length < 2 ^ 63)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_514).base + 528#64)
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
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    SepWPp (lsProg_514 H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen decodeErrorHookStackX reqCap A lim x st s0 R)
      (MergePanicGen decodeErrorHookStackX reqCap A lim x st s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hsum : 1 + v.length + rest.length ≤ x.bs.length := mergeBytes_length_sum hmerge
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp3 := fun (st_next : M.σ) (cap' ptr' : BitVec 64) {s : State}
      (hevs' : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (bytesDropEvents v) st_next = M.stepEvents evs st)
      (hcapOk' : bmCapCond reqCap cap' rest.length) (hcap' : v.length ≤ cap'.toNat) =>
    @phase3_6_from_0x230_gen_placed _ M A lim H reqCap hmc x st st_next s0 s R v rest tmpPtr cap' ptr'
      hVtableDrop hmerge hevs' hcapOk' hcap' hv_len
  rw [bm_vecU8At_eq_header_sep_buf A.repAlloc x.valPtr x.valCap x.valBuf x.valBs]
  dsimp only [vecHeader] at hpc hReserve hp3 ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro
    (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true
      then (blkPl_514).base + 668#64 else (blkPl_514).base + 544#64)
  apply sepWP_seg_ls_vm (Q := lsProg_514 (hooksException H)) blkLib_eq_514
    (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true
      then (blkPl_514).base + 668#64 else (blkPl_514).base + 544#64)
  intro _m_strip
  wp_steps
  refine SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
    (hnext := ?_)
  apply SepWP.fold (fold_vecU8At_clear A.repAlloc x.valPtr x.valCap x.valBuf x.valBs) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  by_cases hult : x.valCap.ult (BitVec.ofNat 64 v.length) = true
  · simp only [hult, ↓reduceIte] at hcl1 hro1 ⊢
    have hcap_lt : x.valCap.toNat < v.length := by
      simpa [BitVec.ult, hlen_toNat] using hult
    have hnewCap_bound :
        reserveCap x.valCap.toNat ([] : List (BitVec 8)).length v.length ≤ 9223372036854775807 :=
      bm_reserveCap_bound reqCap hcapOk hcap_lt hsum hbs_len
    have hcapOk' :
        bmCapCond reqCap (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) rest.length :=
      bmCapCond_after_reserve hcapOk hcap_lt hsum hbs63
    have hnewCap_ge :
        v.length ≤ (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)).toNat := by
      dsimp [reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap] at hnewCap_bound ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hnewCap_ule :
        (BitVec.ofNat 64 v.length).ule
          (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) = true := by
      simp only [BitVec.ule, hlen_toNat, decide_eq_true_eq]
      exact hnewCap_ge
    let rc : DoReserveCall :=
      { v := x.valPtr, cap := x.valCap, ptr := x.valBuf, bs := [], additional := v.length }
    have hrc_evs : doReserveEvents rc = doReserveClearEvents x.valCap.toNat v.length :=
      doReserveEvents_eq_clear x.valPtr x.valCap x.valBuf v.length hcap_lt
    have hfits_rc : FitsEnv M lim st_cur (DoReserveEnv rc) := by
      rw [fitsEnv_doReserve_iff, hrc_evs]
      exact hfits_res
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := lsmpl.base 517)
    wp_steps
    refine ProofLib.SepWP.transport_budgetPool (A := A) (lim := lim) (st := st_cur) ?_ (hnext := ?_)
    · exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    refine SepWPp.weaken_pre (P' :=
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf [] ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur _ ∗
        (memRegion (s0.sp - 224#64 - BitVec.ofNat 64 (bmSliceStack decodeErrorHookStackX))
          (bmSliceStack decodeErrorHookStackX - doReserveStackX) ∗
          stackAt (s0.sp - 224#64) doReserveStackX) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (Entails.of_eq (by
        rw [hslice_eq_x, stackAt_sliceGen_split s0.sp decodeErrorHookStackX doReserveStackX hres_le_x hbnd_x]
        dsimp only [bmExtraStack]
        sep_ac_rfl)) ?_
    refine SepWPp.bm_call_frame_lscl
      (x := (rc, st_cur))
      (T := vecU8At A.repAlloc x.valPtr x.valCap x.valBuf [] ∗
        A.pool lim st_cur _ ∗ stackAt (s0.sp - 224#64) doReserveStackX)
      hReserve hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [doReserve1VecSpecX, arm64_norm, hsp]; rfl)
      (by
        refine ⟨rfl, rfl, hlen_toNat, ?_, hfits_rc⟩
        dsimp [rc, reserveCap] at hnewCap_bound ⊢; omega)
      (by sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [doReserve1VecSpecX] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
    intro sf_res hpcf hrunf hspf hcsf hclf hrof
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
    obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
    dsimp only [doReserve1VecSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      rc, List.length_nil]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun htr => ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptr' => ?_
    rw [bm_vecU8At_eq_header_sep_buf A.repAlloc x.valPtr
      (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' []]
    dsimp only [vecHeader, List.length_nil]
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_514).base + 560#64)
    wp_steps
    apply SepWP.fold
      (fold_vecU8At_clear A.repAlloc x.valPtr
        (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' [])
      (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl3 hro3
    have hevs' : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (bytesDropEvents v) (M.stepEvents (doReserveEvents rc) st_cur) =
          M.stepEvents evs st := by
      obtain ⟨evs, he1, he2⟩ := hevs
      refine ⟨evs, he1, ?_⟩
      rw [← M.stepEvents_append, hrc_evs]
      exact he2
    refine SepWPp.weaken_pre ?_
      (hp3 (M.stepEvents (doReserveEvents rc) st_cur)
        (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' hevs' hcapOk' hnewCap_ge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
          h25f, h26f, h27f, h28f, h29f, hvregsf, h25_0, h26_0, h27_0, h28_0, hvregs_0, and_self])
        hcl3 hro3
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f, hx20])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h23f])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24]))
    exact Entails.of_eq (by
      simp (config := { decide := true }) only [arm64_norm, hsp,
        RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
        RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
        RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
      rw [hslice_eq_x]
      rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackX doReserveStackX hres_le_x hbnd_x]
      dsimp only [bmExtraStack]
      sep_ac_rfl)
  · have hult_eq : x.valCap.ult (BitVec.ofNat 64 v.length) = false :=
      Bool.eq_false_iff.mpr hult
    simp only [hult_eq, Bool.false_eq_true, ↓reduceIte] at hcl1 hro1 ⊢
    have hcap_ge : v.length ≤ x.valCap.toNat := by
      simp [BitVec.ult, hlen_toNat] at hult_eq
      exact hult_eq
    have hcapOk' : bmCapCond reqCap x.valCap rest.length :=
      bmCapCond_mono hcapOk (by omega)
    have hevs' : ∃ evs, BytesMergeEnv x evs ∧
        M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st := by
      rwa [doReserveClearEvents_of_le hcap_ge, List.nil_append] at hevs
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_514).base + 560#64)
    wp_steps
    refine ProofLib.SepWP.transport_budgetPool (A := A) (lim := lim) (st := st_cur) ?_ (hnext := ?_)
    · exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hp3 st_cur x.valCap x.valBuf hevs' hcapOk' hcap_ge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
        (by
          obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh
          simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
            h25, h26, h27, h28, hvregs, and_self])
        hcl2 hro2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24]))

theorem phase3_6_from_0x210_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hmc : subroutine_ok (lsProg_514 H) (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hReserve : subroutine_ok (lsProg_514 H) (lsmpl.base 517)
      (withLsCl lsmpl (doReserve1VecSpecX M A lim)))
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_514 H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim extHookStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hfits_res : FitsEvents M lim st_cur (doReserveClearEvents x.valCap.toNat v.length))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧
      M.stepEvents (doReserveClearEvents x.valCap.toNat v.length ++ bytesDropEvents v) st_cur =
        M.stepEvents evs st)
    (hv_len : v.length < 2 ^ 63)
    (hbs_len : x.bs.length < 2 ^ 63)
    (hcapInv : BytesMergeCapOk x.valCap x.bs.length ∨ x.bs.length < 2 ^ 62)
    (hpc : s.pc = (blkPl_514).base + 528#64)
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
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    SepWPp (lsProg_514 H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostXBoth A lim x st s0 R)
      (MergePanicXBoth A lim x st s0 R) :=
  sepWPp_xBoth_of_capInv hbs_len hcapInv fun _reqCap hbs_req hcapOk =>
    phase3_6_from_0x210_gen_placed (bmMemcpy_placed_of_framelessBudget hmc) hReserve hVtableDrop
      hmerge hfits_res hevs hv_len hbs_req hcapOk hpc hrun hsp hsp_align htrace hhigh hcl hro
      hx19 hx20 hx21 hx22 hx24

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6Phase23PlacedBudgetAux
