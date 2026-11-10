/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Envelopes, Helpers, and Miss Path for `Dir::put::<String>` (Block 542)

Defines the `DirPutEnv` and `DirPutTailEnv` allocator event envelopes, budget-threaded call and
epilogue helpers, and the cache-miss path (`+196 .. +288`) for `Dir::put::<String>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks
  ls_hook_ok_ultra_of_mem lsmpl lsρ
)
open CryptoVerification.RustHeap (
  arrayAt arrayAt_concat arrayAt_cons arrayAt_nil vecAt vecBuf vecBuf_expose_arrayAt
  vecBuf_of_ne_zero vecHeader vecHeader_entails_memRegion vecU8 vecU8At
)
open CryptoVerification.LibsignalTripleRatchetRepr (strRefAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  SepWPp.of_sepWP_cs_placed StepInvPlaced
)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (
  CliBcmpCall DirGhost DirPutGhost GrowOneDirGhost cliBcmpName cliBcmpSpec
  dirAt dirEntryAt
)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_542 lsProg_542)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Put.Helpers (
  PutCalleeOkPlaced PutCalleeSavedPlaced dirAt_of_vecAt memRegion_48_split_entry
  putCalleeOkPlaced_get putCalleeOkPlaced_mk putSavedCells putSavedCells_pack
  setOrPush_hit setOrPush_miss sp_sub_96_aligned stackAt_put_frame stackAt_sub_split
  stk_lt_two_pow_64 subroutine_ok_withPutCSPlaced subroutine_ok_withPutCSPlaced_lscro
  vecU8At_eq_header_rest' vecU8Rest vecU8Rest_dealloc vecU8Rest_expose_bytes
  vecU8_intro_header_rest withPutCSPlaced
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget RustLayoutOk
  rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rawVecGrowEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget (
  sepWPp_call_cs_placed_noPanic
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget (GrowOneDirEnv growOneDirRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsXCliPlaced dirPutSpecPlaced growOneDirSpecPlaced
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Canonical Event Envelope & Call / Epilogue Helpers -/

/-- Tail `AllocEvent` envelope shared by `Dir::put::<String>` and the post-`to_owned` body of
`Dir::put::<&str>`:
- on a miss (`∀ e ∈ dir.changed, e.1 ≠ name`), either `[]` (spare capacity) or
  `rawVecGrowEvents 48 4 8 (BitVec.ofNat 64 dir.changed.length)` (`grow_one`);
- on a hit (`¬ ∀ e ∈ dir.changed, e.1 ≠ name`), only deallocation events (`FreeOnlyEvs`). -/
def DirPutTailEnv (dir : DirGhost) (name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  if ∀ e ∈ dir.changed, e.1 ≠ name then
    evs = [] ∨ evs = rawVecGrowEvents 48 4 8 (BitVec.ofNat 64 dir.changed.length)
  else
    FreeOnlyEvs evs

/-- Canonical `AllocEvent` envelope for `Dir::put::<String>`. -/
def DirPutEnv (dir : DirGhost) (name _bytes : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  DirPutTailEnv dir name evs

theorem dirPutTailEnv_miss_nil {dir : DirGhost} {name : List (BitVec 8)}
    (hmiss : ∀ e ∈ dir.changed, e.1 ≠ name) :
    DirPutTailEnv dir name [] := by
  unfold DirPutTailEnv
  split
  · exact Or.inl rfl
  · rename_i hc; exact (hc hmiss).elim

theorem dirPutTailEnv_miss_grow {dir : DirGhost} {name : List (BitVec 8)}
    (hmiss : ∀ e ∈ dir.changed, e.1 ≠ name) :
    DirPutTailEnv dir name (rawVecGrowEvents 48 4 8 (BitVec.ofNat 64 dir.changed.length)) := by
  unfold DirPutTailEnv
  split
  · exact Or.inr rfl
  · rename_i hc; exact (hc hmiss).elim

theorem dirPutTailEnv_hit_freeOnly {dir : DirGhost} {name : List (BitVec 8)}
    {evs : List AllocEvent}
    (hhit : ¬ ∀ e ∈ dir.changed, e.1 ≠ name) (hf : FreeOnlyEvs evs) :
    DirPutTailEnv dir name evs := by
  unfold DirPutTailEnv
  split
  · rename_i hc; exact (hhit hc).elim
  · exact hf

/-- Execute `bl bcmp` (`aRo = false, bRo = false`) inside `Dir::put::<String>`'s stack frame,
transporting `A.pool lim curSt` across `withVmPreserved cliBcmpSpec`. -/
theorem step_bcmp_call_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {stk : Nat}
    {call_pc : BitVec 64} {s0 s : State} {curSt : M.σ}
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hbcmp : subroutine_ok (lsProg_542 H) call_pc
      (withPutCSPlaced s0 (withVmPreserved cliBcmpSpec)))
    (hsub : extHookStack ≤ stk - 96)
    (hle : stk ≤ 2 ^ 64)
    (a b ret_pc : BitVec 64) (bsA bsB : List (BitVec 8))
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = a)
    (hx1 : s.readReg64 .x1 = b)
    (hx2 : (s.readReg64 .x2).toNat = bsA.length)
    (hlen : bsB.length = bsA.length)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = ((a ↦ₛ bsA) ∗ (b ↦ₛ bsB) ∗ A.pool lim curSt s ∗
        stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace →
      ((sm.readReg64 .x0).setWidth 32 = 0#32 ↔ bsA = bsB) →
      CalleeSavedPreserved s sm →
      PutCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_542 H) ret sm
        (((a ↦ₛ bsA) ∗ (b ↦ₛ bsB) ∗ A.pool lim curSt sm ∗
            stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
        Q Qp) :
    SepWPp (lsProg_542 H) ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := CliBcmpCall.mk a false bsA b false bsB)
    (F := A.pool lim curSt s ∗
      memRegion (s0.sp - 96#64 - BitVec.ofNat 64 (stk - 96)) (stk - 96 - extHookStack) ∗ F)
    hbcmp hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_split hsub (by omega) (s0.sp - 96#64)] at hm
    simp only [withPutCSPlaced, withVmPreserved, cliBcmpSpec,
      CryptoVerification.SpqrV1.ChainProofs.bytesAt, Bool.false_eq_true,
      ↓reduceIte, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hlen⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf R' _ hm
    simp only [withPutCSPlaced, withVmPreserved, cliBcmpSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1
  · intro sf R' _ hm
    exact allowPanic_not_exited hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withPutCSPlaced, withVmPreserved, cliBcmpSpec,
      CryptoVerification.SpqrV1.ChainProofs.bytesAt, Bool.false_eq_true,
      ↓reduceIte, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => ?_
    refine SepWPp.pure_elim fun ⟨heq_iff, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm' heq_iff hcsm
        (hcs.trans (PutCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [← A.pool_of_vmPreserved hvm, stackAt_sub_split hsub (by omega) (s0.sp - 96#64)]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Execute `bl __rust_dealloc(ptr, cap.toNat, 1)` on `vecU8Rest A.repAlloc cap ptr bs` (`cap ≠ 0`)
inside `Dir::put::<String>`'s stack frame, advancing `A.pool lim curSt` by
`rustDeallocEvents cap.toNat 1`. -/
theorem step_dealloc_call_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {stk : Nat}
    {call_pc : BitVec 64} {s0 s : State} {curSt : M.σ}
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hdealloc : subroutine_ok (lsProg_542 H) call_pc
      (withPutCSPlaced s0 (rustDeallocExternSpecWithStack M A lim extHookStack)))
    (hsub : extHookStack ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hcap0 : cap ≠ 0)
    (hbs_le : bs.length ≤ cap.toNat)
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : s.readReg64 .x1 = cap)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = (vecU8Rest A.repAlloc cap ptr bs ∗ A.pool lim curSt s ∗
        stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      PutCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_542 H) ret sm
        ((A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) curSt) sm ∗
            stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
        Q Qp)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp (lsProg_542 H) ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hlayout, hrest⟩ := vecU8Rest_dealloc (A := A.repAlloc) (ptr := ptr) hcap0 hbs_le hcap_lt
  have hrlo : RustLayoutOk cap.toNat 1 := ⟨hlayout, by decide⟩
  refine sepWPp_call_cs_placed_noPanic (x := (ptr, cap.toNat, 1, curSt))
    (F := memRegion (s0.sp - 96#64 - BitVec.ofNat 64 (stk - 96)) (stk - 96 - extHookStack) ∗ F)
    hdealloc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_split hsub (by omega) (s0.sp - 96#64)] at hm
    have hm' := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_left (sepConj_mono_left hrest))) hm
    simp only [withPutCSPlaced, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, by simp [hx1], by simp [hx2], hrlo, by rw [hlr]; exact hlr_ls⟩, ?_⟩
    convert hm' using 1; sep_ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf R' _ hm
    exact allowPanic_not_exited hm
  · intro sf R' _ hm
    simp only [withPutCSPlaced, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      satisfies_pure_sepConj] at hm
    exact hm.1
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withPutCSPlaced, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm' hcsm
        (hcs.trans (PutCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_sub_split hsub (by omega) (s0.sp - 96#64)]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Execute `bl grow_one` inside `Dir::put::<String>`'s stack frame, advancing `A.pool lim curSt`
by `rawVecGrowEvents 48 4 8 cap` with `onPanic = ⌜False⌝` under `FitsEnv`. -/
theorem step_grow_call_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {growStk stk : Nat}
    {call_pc : BitVec 64} {s0 s : State} {curSt : M.σ}
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hgrow : subroutine_ok (lsProg_542 H) call_pc
      (withPutCSPlaced s0 (growOneDirRawSpec A lim growStk)))
    (hsub : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (v cap ptr ret_pc : BitVec 64) (xs : List (List (BitVec 8) × List (BitVec 8)))
    (hcap_lt : cap.toNat < 2 ^ 32)
    (hfits : FitsEnv M lim curSt (GrowOneDirEnv (GrowOneDirGhost.mk v cap ptr xs)))
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = (vecAt A.repAlloc 48 8 (dirEntryAt A.repAlloc) v cap ptr xs ∗ A.pool lim curSt s ∗
        stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      PutCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_542 H) ret sm
        ((vecAt A.repAlloc 48 8 (dirEntryAt A.repAlloc) v
            (BitVec.ofNat 64 (max (2 * cap.toNat) 4)) newPtr xs ∗
          A.pool lim (M.stepEvents (rawVecGrowEvents 48 4 8 cap) curSt) sm ∗
          stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
        Q Qp) :
    SepWPp (lsProg_542 H) ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (GrowOneDirGhost.mk v cap ptr xs, curSt))
    (F := memRegion (s0.sp - 96#64 - BitVec.ofNat 64 (stk - 96)) (stk - 96 - growStk) ∗ F)
    hgrow hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_split hsub (by omega) (s0.sp - 96#64)] at hm
    simp only [withPutCSPlaced, growOneDirRawSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hcap_lt, hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf R' _ hm
    exact allowPanic_not_exited hm
  · intro sf R' _ hm
    exact allowPanic_not_exited hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withPutCSPlaced, growOneDirRawSpec, GrowOneDirEnv]
    simp only [sepExists_sepConj_left, hsp, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => ?_
    refine SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    subst hevs
    refine SepWPp.exists_elim fun newPtr => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (PutCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_sub_split hsub (by omega) (s0.sp - 96#64)]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Normal-return `SepWPp` postcondition expected by `subroutine_ok_of_sepWPp` for
`dirPutSpecPlaced A lim PutEnv stk`. -/
abbrev putRetQPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) (x : DirPutGhost) (st0 : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A lim PutEnv stk).post (x, st0) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

/-- Panic `SepWPp` postcondition expected by `subroutine_ok_of_sepWPp` for
`dirPutSpecPlaced A lim PutEnv stk`. -/
abbrev putPanicQPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) (x : DirPutGhost) (st0 : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A lim PutEnv stk).onPanic (x, st0) s0 sf ∗ R)

private abbrev stepDstP {a b : State} (_ : StepInvPlaced a b) : State := b

/-- Execute shared epilogue `+248 .. +272` (`LDP .. RET`) and discharge `dirPutSpecPlaced`'s
postcondition at accumulated event list `evsAcc`. -/
theorem step_epilogue_ret_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {stk : Nat}
    {s0 s : State} {x : DirPutGhost} {st0 : M.σ} {evsAcc : List AllocEvent}
    {v3 : BitVec 64} {P R : SepProp}
    (h96 : 0x60 ≤ stk)
    (hle_stk : stk ≤ 2 ^ 64)
    (hEnv : PutEnv x.dir x.name x.bytes evsAcc)
    (hpc : s.pc = (blkPl_542).base + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) ∗
        memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗
        A.pool lim (M.stepEvents evsAcc st0) s) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A lim PutEnv stk x st0 s0 R)
      (putPanicQPlaced A lim PutEnv stk x st0 s0 R) := by
  subst hP
  unfold putSavedCells
  have hsp_align : (s0.sp - 96#64) &&& 15#64 = 0#64 := sp_sub_96_aligned halign
  apply SepWPp.of_sepWP_cs_placed (mid := s0.readReg64 .lr)
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_ep
  let sf := stepDstP hinv_ep
  have htr_sf : sf.trace = s0.trace := by simp only [sf, stepDstP, arm64_norm, htr]
  dsimp only [sf, stepDstP] at htr_sf
  refine SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm,
      by simp only [arm64_norm, *],
      by simp only [CalleeSavedPreserved, arm64_norm, hcs.1, hcs.2.1]⟩
  dsimp only [dirPutSpecPlaced, withLsCodeRoLoaded]
  refine Entails.sepExists_right evsAcc ?_
  refine Entails.pure_right ⟨htr_sf, hEnv⟩ ?_
  refine Entails.trans (Entails.of_eq (show _ =
    dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) ∗
      memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗
      (stackAt (s0.sp - 96#64) (stk - 96) ∗ putSavedCells s0 v3) ∗
      A.pool lim (M.stepEvents evsAcc st0) (stepDstP hinv_ep) by
    unfold putSavedCells; sep_ac_rfl))
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (putSavedCells_pack h96 hle_stk s0 v3)))))

/-- Execute hit-branch tail-dealloc epilogue `+156 .. +192` (`MOV X0..X2`, pop frame,
`B __rust_dealloc`) when `nameCap ≠ 0` and discharge `dirPutSpecPlaced`'s postcondition at
`evsAcc ++ rustDeallocEvents nameCap.toNat 1`. -/
theorem step_epilogue_tail_dealloc_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {stk : Nat}
    {s0 s : State} {x : DirPutGhost} {st0 : M.σ} {evsAcc : List AllocEvent}
    {v3 nameCap namePtr : BitVec 64} {P R : SepProp}
    (hdealloc : subroutine_ok (lsProg_542 H) (lsρ lsRustDeallocSymCli)
      (withPutCSPlaced s0 (rustDeallocExternSpecWithStack M A lim extHookStack)))
    (h96 : 0x60 ≤ stk)
    (hhook : extHookStack ≤ stk)
    (hle_stk : stk ≤ 2 ^ 64)
    (hcap0 : nameCap ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hEnv : PutEnv x.dir x.name x.bytes (evsAcc ++ rustDeallocEvents nameCap.toNat 1))
    (hpc : s.pc = (blkPl_542).base + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) ∗
        memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗
        A.pool lim (M.stepEvents evsAcc st0) s)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A lim PutEnv stk x st0 s0 R)
      (putPanicQPlaced A lim PutEnv stk x st0 s0 R) := by
  subst hP
  unfold putSavedCells
  have hsp_align : (s0.sp - 96#64) &&& 15#64 = 0#64 := sp_sub_96_aligned halign
  apply SepWPp.of_sepWP_cs_placed (mid := lsρ lsRustDeallocSymCli)
  wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_ep
  let s1 := stepDstP hinv_ep
  obtain ⟨hlayout, hrest⟩ := vecU8Rest_dealloc (A := A.repAlloc) (ptr := namePtr) hcap0 hna_le hna_lt
  have hrlo : RustLayoutOk nameCap.toNat 1 := ⟨hlayout, by decide⟩
  have hcs1 : CalleeSavedPreserved s0 s1 := by
    simp only [s1, stepDstP, CalleeSavedPreserved, arm64_norm, hcs.1, hcs.2.1]
  have hput_cs1 : PutCalleeSavedPlaced s0 s1 :=
    ⟨by simp only [s1, stepDstP, arm64_norm, hcs.1],
     by simp only [s1, stepDstP, arm64_norm, hcs.2.1],
     hcs.2.2.trans hinv_ep⟩
  have hsp1 : s1.sp = s0.sp := by simp only [s1, stepDstP, arm64_norm, *]
  have hsp_aligned1 : s1.spAligned = true := by
    simp only [State.spAligned, hsp1, beq_iff_eq]
    exact halign
  dsimp only [s1, stepDstP] at hcs1 hput_cs1 hsp1 hsp_aligned1
  refine sepWPp_call_cs_placed_noPanic (ret_pc := s0.readReg64 .lr)
    (x := (namePtr, nameCap.toNat, 1, M.stepEvents evsAcc st0))
    (F := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
      dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) ∗
      memRegion x.nameV 24 ∗ memRegion x.bytesV 24)
    hdealloc
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hsp_aligned1
    (by simp only [arm64_norm, *])
    ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    have hpack :
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
         ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
         ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
         ((s0.sp - 72#64) ↦₆₄ v3) ∗
         ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
         ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
         ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) ∗
        stackAt (s0.sp - 96#64) (stk - 96) ⊢ stackAt s0.sp stk := by
      rw [sepConj_comm]
      exact putSavedCells_pack h96 hle_stk s0 v3
    have hm1 := Satisfies.mono
      (sepConj_mono_left (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono hpack
          (sepConj_mono_left (Q := dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) ∗
            memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗
            A.pool lim (M.stepEvents evsAcc st0) (stepDstP hinv_ep)) hrest)))) hm
    rw [stackAt_sub_split hhook hle_stk s0.sp] at hm1
    simp only [withPutCSPlaced, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      hsp1, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hput_cs1, ⟨by simp only [arm64_norm, *], by simp [arm64_norm],
      by simp [arm64_norm], hrlo, by simpa only [Reg.x30, Reg.lr, arm64_norm] using hlr_ls⟩, ?_⟩
    convert hm1 using 1; sep_ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf R' _ hm
    exact allowPanic_not_exited hm
  · intro sf R' _ hm
    simp only [withPutCSPlaced, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      satisfies_pure_sepConj] at hm
    exact hm.1
  · intro sf hpcsf hrunsf hspsf hcsm _
    rw [hsp1] at hspsf
    simp only [withPutCSPlaced, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      hsp1, sepConj_assoc]
    refine SepWPp.pure_elim fun htrsf => ?_
    have htr_final : sf.trace = s0.trace := htrsf.trans (by simp only [arm64_norm, htr])
    refine SepWPp.done hpcsf hrunsf ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm,
      hspsf, hcs1.trans hcsm⟩
    dsimp only [dirPutSpecPlaced, withLsCodeRoLoaded]
    refine Entails.sepExists_right (evsAcc ++ rustDeallocEvents nameCap.toNat 1) ?_
    refine Entails.pure_right ⟨htr_final, hEnv⟩ ?_
    rw [M.stepEvents_append, stackAt_sub_split hhook hle_stk s0.sp]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. Miss Path (`+196 .. +288`) -/

/-- Push `{name, bytes}` into an already non-full `Dir.changed` buffer (`+208 .. +244`)
and finish via `step_epilogue_ret_p` (`+248 .. +272`). -/
theorem step_write_miss_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {stk : Nat}
    {s0 s : State} {x : DirPutGhost} {st0 : M.σ} {evsAcc : List AllocEvent}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (h96 : 0x60 ≤ stk)
    (hle_stk : stk ≤ 2 ^ 64)
    (hmiss : ∀ e ∈ x.dir.changed, e.1 ≠ x.name)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hfit : x.dir.changed.length < cap.toNat)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (hEnv : PutEnv x.dir x.name x.bytes evsAcc)
    (hpc : s.pc = (blkPl_542).base + 208#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx22 : s.readReg64 .x22 = x.self)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.name.length)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length)
    (hx25 : s.readReg64 .x25 = ptr)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecAt A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.self cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A.repAlloc x.bytesV x.bytes ∗
        A.pool lim (M.stepEvents evsAcc st0) s) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A lim PutEnv stk x st0 s0 R)
      (putPanicQPlaced A lim PutEnv stk x st0 s0 R) := by
  subst hP
  have hcap0 : cap ≠ 0 := by
    intro h0
    rw [h0] at hfit
    change x.dir.changed.length < 0 at hfit
    omega
  unfold vecAt vecHeader vecU8
  rw [vecBuf_of_ne_zero A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed hcap0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun bytesCap => ?_
  refine SepWPp.exists_elim fun bytesPtr => ?_
  rw [vecU8At_eq_header_rest' A.repAlloc x.bytesV bytesCap bytesPtr x.bytes,
      show vecHeader x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) =
        (x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) from rfl]
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜x.dir.changed.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ⌜x.bytes.length ≤ bytesCap.toNat ∧ bytesCap.toNat < 2 ^ 63 ∧ bytesPtr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr x.dir.changed ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        (x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Rest A.repAlloc bytesCap bytesPtr x.bytes ∗
        A.pool lim (M.stepEvents evsAcc st0) s) by sep_ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap48_lt, hptr_ne⟩ => ?_
  refine SepWPp.pure_elim fun ⟨hbs_le, hbs_lt, hbs_ptr⟩ => ?_
  have hspare_eq :
      (cap.toNat - x.dir.changed.length) * 48 =
        48 + (cap.toNat - (x.dir.changed.length + 1)) * 48 := by
    have : cap.toNat - x.dir.changed.length = 1 + (cap.toNat - (x.dir.changed.length + 1)) := by
      omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hspare_split := ProofLib.memRegion_split
    (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
    48 ((cap.toNat - (x.dir.changed.length + 1)) * 48) (by omega)
  have hslot_next :
      ptr + BitVec.ofNat 64 (x.dir.changed.length * 48) + 48#64 =
        ptr + BitVec.ofNat 64 ((x.dir.changed.length + 1) * 48) := by
    rw [BitVec.add_assoc, show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl,
      ← BitVec.ofNat_add, Nat.succ_mul]
  have hmul_bv :
      BitVec.ofNat 64 (x.dir.changed.length * 48) =
        BitVec.ofNat 64 x.dir.changed.length * 48#64 := by
    rw [show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl, ← BitVec.ofNat_mul]
  rw [hspare_eq, hspare_split, hslot_next, hmul_bv,
      memRegion_48_split_entry (ptr + BitVec.ofNat 64 x.dir.changed.length * 48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun l1 => ?_
  refine SepWPp.exists_elim fun q1 => ?_
  refine SepWPp.exists_elim fun l0 => ?_
  refine SepWPp.exists_elim fun p0 => ?_
  refine SepWPp.exists_elim fun c0 => ?_
  unfold pointsTo128
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 248#64)
  wp_steps_sync_pool ((blkPl_542).base + 248#64)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_w
  set slot := ptr + BitVec.ofNat 64 (x.dir.changed.length * 48)
  have hslot_eq : ptr + BitVec.ofNat 64 x.dir.changed.length * 48#64 = slot :=
    congrArg (ptr + ·) hmul_bv.symm
  have hlen1_eq :
      BitVec.ofNat 64 x.dir.changed.length + 1#64 =
        BitVec.ofNat 64 (x.dir.changed.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hentry_pack :
      ((slot ↦₆₄ nameCap) ∗ ((slot + 8#64) ↦₆₄ namePtr) ∗
        ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name) ∗
      (((slot + 24#64) ↦₆₄ bytesCap) ∗ ((slot + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
        ((slot + 40#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Rest A.repAlloc bytesCap bytesPtr x.bytes) ⊢
      dirEntryAt A.repAlloc (x.name, x.bytes) slot := by
    have hname_v :
        (slot ↦₆₄ nameCap) ∗ ((slot + 8#64) ↦₆₄ namePtr) ∗
          ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
          vecU8Rest A.repAlloc nameCap namePtr x.name ⊢ vecU8 A.repAlloc slot x.name := by
      have hhdr :
          (slot ↦₆₄ nameCap) ∗ ((slot + 8#64) ↦₆₄ namePtr) ∗
            ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
            vecU8Rest A.repAlloc nameCap namePtr x.name =
          vecHeader slot nameCap namePtr (BitVec.ofNat 64 x.name.length) ∗
            vecU8Rest A.repAlloc nameCap namePtr x.name := by
        unfold vecHeader; sep_ac_rfl
      rw [hhdr]
      exact vecU8_intro_header_rest hna_le hna_lt hna_ptr
    have hbytes_v :
        ((slot + 24#64) ↦₆₄ bytesCap) ∗ ((slot + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
          ((slot + 40#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Rest A.repAlloc bytesCap bytesPtr x.bytes ⊢
        vecU8 A.repAlloc (slot + 0x18#64) x.bytes := by
      have h40 : slot + 40#64 = (slot + 0x18#64) + 16#64 := by bv_arith
      have h24 : slot + 24#64 = slot + 0x18#64 := rfl
      rw [h40, h24]
      have hhdr2 :
          ((slot + 0x18#64) ↦₆₄ bytesCap) ∗ (((slot + 0x18#64) + 8#64) ↦₆₄ bytesPtr) ∗
            (((slot + 0x18#64) + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A.repAlloc bytesCap bytesPtr x.bytes =
          vecHeader (slot + 0x18#64) bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A.repAlloc bytesCap bytesPtr x.bytes := by
        unfold vecHeader; sep_ac_rfl
      rw [hhdr2]
      exact vecU8_intro_header_rest hbs_le hbs_lt hbs_ptr
    exact sepConj_mono hname_v hbytes_v
  have hput_eq : (x.dir.put x.name x.bytes) =
      { changed := x.dir.changed ++ [(x.name, x.bytes)], path := x.dir.path } := by
    simp only [DirGhost.put, setOrPush_miss hmiss]
  have hvec_pack :
      (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (x.dir.changed.length + 1)) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        (arrayAt (dirEntryAt A.repAlloc) 48 ptr x.dir.changed ∗
          dirEntryAt A.repAlloc (x.name, x.bytes) slot) ∗
        memRegion (ptr + BitVec.ofNat 64 ((x.dir.changed.length + 1) * 48))
          ((cap.toNat - (x.dir.changed.length + 1)) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ⊢
      dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) := by
    have hnew_len : (x.dir.changed ++ [(x.name, x.bytes)]).length = x.dir.changed.length + 1 := by
      simp
    rw [hput_eq, ← arrayAt_concat (dirEntryAt A.repAlloc) 48 ptr x.dir.changed (x.name, x.bytes),
        ← hnew_len]
    refine Entails.trans ?_
      (dirAt_of_vecAt A.repAlloc x.self cap ptr (x.dir.changed ++ [(x.name, x.bytes)]) x.dir.path)
    unfold vecAt vecHeader
    rw [vecBuf_of_ne_zero A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr _ hcap0,
        pure_sepConj_of_true ⟨by rw [hnew_len]; omega, hcap48_lt, hptr_ne⟩]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre ?_
    (step_epilogue_ret_p (A := A) (lim := lim) (PutEnv := PutEnv) (H := H) (stk := stk)
      (st0 := st0) (evsAcc := evsAcc) (v3 := v3) (R := R)
      h96 hle_stk hEnv
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      halign
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) hinv_w)
      rfl)
  rw [hslot_eq, hlen1_eq]
  have hbytesV_mem :
      ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) ⊢ memRegion x.bytesV 24 := by
    have hhdrV :
        ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) =
        vecHeader x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) := by
      unfold vecHeader; sep_ac_rfl
    rw [hhdrV]
    exact vecHeader_entails_memRegion x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hvec_pack
        (sepConj_mono_right (sepConj_mono_left hbytesV_mem)))))
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left
            (sepConj_mono_right hentry_pack)))))))))

/-- Full miss handler (`+196 .. +288`): checks capacity at `+196 .. +204`, calls `grow_one`
at `+276 .. +288` if `len = cap`, and delegates to `step_write_miss_p` at `+208`. -/
theorem step_miss_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {growStk stk : Nat}
    {s0 s : State} {x : DirPutGhost} {st0 : M.σ}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hgrow : subroutine_ok (lsProg_542 H) (lsmpl.base 586)
      (withPutCSPlaced s0 (growOneDirRawSpec A lim growStk)))
    (h96 : 0x60 ≤ stk)
    (hgrow_stk : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hmiss : ∀ e ∈ x.dir.changed, e.1 ≠ x.name)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (hFit0 : FitsEnv M lim st0 (PutEnv x.dir x.name x.bytes))
    (hPutEnv : ∀ evs, DirPutTailEnv x.dir x.name evs → PutEnv x.dir x.name x.bytes evs)
    (hpc : s.pc = (blkPl_542).base + 196#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx22 : s.readReg64 .x22 = x.self)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.name.length)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length)
    (hx25 : s.readReg64 .x25 = ptr)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecAt A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.self cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A.repAlloc x.bytesV x.bytes ∗ A.pool lim st0 s) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A lim PutEnv stk x st0 s0 R)
      (putPanicQPlaced A lim PutEnv stk x st0 s0 R) := by
  subst hP
  unfold vecAt vecHeader
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_right
        (vecBuf_expose_arrayAt A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed))))) ?_
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜x.dir.changed.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧
        x.dir.changed.length * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr x.dir.changed ∗
        (if cap = 0 then emp
         else A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((cap.toNat - x.dir.changed.length) * 48)) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A.repAlloc x.bytesV x.bytes ∗ A.pool lim st0 s) by sep_ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hlen_le, hcap48_lt, _, hptr_ne⟩ => ?_
  have hvec_back :
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr x.dir.changed ∗
        (if cap = 0 then emp
         else A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((cap.toNat - x.dir.changed.length) * 48))) =
      vecAt A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.self cap ptr x.dir.changed := by
    unfold vecAt vecHeader vecBuf
    rw [pure_sepConj_of_true ⟨hlen_le, hcap48_lt, hptr_ne⟩]
    by_cases h0 : cap = 0
    · subst h0
      have hnil : x.dir.changed = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen_le)
      simp only [hnil, ↓reduceIte, arrayAt_nil]
      sep_ac_rfl
    · simp only [h0, ↓reduceIte]
      sep_ac_rfl
  by_cases hcap_eq : BitVec.ofNat 64 x.dir.changed.length = cap
  · have hcap_nat : cap.toNat = x.dir.changed.length := by
      rw [← hcap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hEnvGrow : PutEnv x.dir x.name x.bytes (rawVecGrowEvents 48 4 8 cap) := by
      rw [← hcap_eq]
      exact hPutEnv _ (dirPutTailEnv_miss_grow hmiss)
    have hfits_grow :
        FitsEnv M lim st0 (GrowOneDirEnv (GrowOneDirGhost.mk x.self cap ptr x.dir.changed)) :=
      FitsEnv.mono (fun evs hevs => by rw [GrowOneDirEnv] at hevs; rwa [hevs]) hFit0
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 586)
    wp_steps_sync_pool (lsmpl.base 586)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    let retGrow := (blkPl_542).base + 284#64
    refine step_grow_call_p (A := A) (lim := lim) (H := H) (growStk := growStk) (stk := stk)
      (curSt := st0)
      (F := putSavedCells s0 v3 ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A.repAlloc x.bytesV x.bytes)
      hgrow hgrow_stk hle_stk x.self cap ptr retGrow x.dir.changed
      (by omega) hfits_grow
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      halign
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; rfl)
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) hinv1)
      (by rw [← hvec_back]; sep_ac_rfl)
      fun sm newPtr hpcm hrunm hspm htrm hcsm hput_csm => ?_
    dsimp only [retGrow] at hpcm
    clear retGrow
    rcases hcsm with ⟨hc19, hc20, hc21, hc22, hc23, hc24, _, _, _, _, _, _⟩
    have sm_x19 : sm.readReg64 .x19 = namePtr := hc19.trans (by simp only [arm64_norm, *])
    have sm_x20 : sm.readReg64 .x20 = nameCap := hc20.trans (by simp only [arm64_norm, *])
    have sm_x21 : sm.readReg64 .x21 = x.bytesV := hc21.trans (by simp only [arm64_norm, *])
    have sm_x22 : sm.readReg64 .x22 = x.self := hc22.trans (by simp only [arm64_norm, *])
    have sm_x23 : sm.readReg64 .x23 = BitVec.ofNat 64 x.name.length :=
      hc23.trans (by simp only [arm64_norm, *])
    have sm_x24 : sm.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length :=
      hc24.trans (by simp only [arm64_norm, *])
    set newCap := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
    unfold vecAt vecHeader
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 208#64)
    wp_steps_sync_pool ((blkPl_542).base + 208#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    have hnew_fit : x.dir.changed.length < newCap.toNat := by
      simp only [newCap, BitVec.toNat_ofNat, hcap_nat]
      omega
    refine SepWPp.weaken_pre ?_
      (step_write_miss_p (A := A) (lim := lim) (PutEnv := PutEnv) (H := H) (stk := stk)
        (st0 := st0) (evsAcc := rawVecGrowEvents 48 4 8 cap)
        (v3 := v3) (cap := newCap) (ptr := newPtr) (nameCap := nameCap) (namePtr := namePtr)
        (R := R)
        h96 hle_stk hmiss hlen_lt32 hnew_fit hna_le hna_lt hna_ptr hEnvGrow
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        halign
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hput_csm.step (by simp only [arm64_norm]) hinv2)
        rfl)
    unfold vecAt vecHeader
    exact Entails.of_eq (by sep_ac_rfl)
  · have hfit : x.dir.changed.length < cap.toNat := by
      have hne_nat : x.dir.changed.length ≠ cap.toNat := by
        intro heq
        apply hcap_eq
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact heq
      omega
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 208#64)
    wp_steps_sync_pool ((blkPl_542).base + 208#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    refine SepWPp.weaken_pre ?_
      (step_write_miss_p (A := A) (lim := lim) (PutEnv := PutEnv) (H := H) (stk := stk)
        (st0 := st0) (evsAcc := [])
        (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr)
        (R := R)
        h96 hle_stk hmiss hlen_lt32 hfit hna_le hna_lt hna_ptr
        (hPutEnv [] (dirPutTailEnv_miss_nil hmiss))
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        halign
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) hinv1)
        rfl)
    rw [M.stepEvents_nil, ← hvec_back]
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
