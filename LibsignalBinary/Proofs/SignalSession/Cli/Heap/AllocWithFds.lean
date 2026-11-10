/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Pool-Carried `FdsGe3Closed` Allocator Wrapper (`withFds`)

Wraps any `A : RustCliAllocBudget M` into `withFds A`, conjoining `⌜FdsGe3Closed s.fs⌝` into
`pool lim st s` when `lim.enforced = true` while keeping `zeroBudgetLimits`, `live`, `block_valid`,
`repAlloc`, and `toRustCliAlloc` definitionally equal to `A`'s. Lifts allocator hook/entry bundles
via `AllocCallPreserved`, lifts `SpqrHooksBudget` via `withFdsGe3Closed` HMAC contracts, and
derives `withFdsGe3Closed` corollaries for `grow_one` (block 621) and `PolynomialEncoder::merge`
(block 297).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic SepProp
open CryptoGames.CBC (AesKey Block)
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement LsBlockBound lsmpl)
open CryptoVerification.E2E (aesDecHookMallocng aesEncHookMallocng libcruxHmacHookMallocng)
open CryptoVerification.LibsignalSpqrV1
  (LibcruxHmacCall MlKem libcruxHmacName)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack withLsCodeRoLoaded)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsAesDecSym lsAesEncSym lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns cliGhostExterns_shim withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_panic_handle_error lsLibcruxHmacSymCli)
open CryptoVerification.SpqrV1.Prost.MessageMerge (blkPC_297 blkPl_297)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FdsHiFrame FitsEnv FitsEvents
   MallocngCostModelIface MallocngCostModelSound NullAllowed OomPreserved PoolPreserved
   RustAllocAddrs RustCliAllocBudget RustCliAllocBudgetEntries RustCliAllocBudgetEntriesBase
   RustCliAllocBudgetHooks RustCliAllocBudgetHooksBase RustLayoutOk VmPreserved rustAllocEvents
   rustCliAllocBudgetSpec rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpec
   rustCliDeallocBudgetSpecBase rustCliReallocBudgetSpec rustCliReallocBudgetSpecBase
   rustDeallocEvents rustReallocEvents zeroBudgetLimits)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (growOneVecU8BudgetSpec rawVecGrowBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (AllocHooksBudget AllocHooksBudgetBase LibcruxHmacEnv SpqrHooksBudget aesCallPreBudget
   aesDecBudgetSpec aesEncBudgetSpec decodeErrorFromBudgetSpec libcruxHmacBudgetSpec
   rustAllocZeroedBudgetSpec rustAllocZeroedBudgetSpecBase)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (aesDecHookMallocng_budget_ok aesEncHookMallocng_budget_ok fineAesDec_budget_hookOk
   fineAesEnc_budget_hookOk fineHookRustCliAllocBudget fineLibcruxHmac_budget_hookOk
   libcruxHmacHookMallocng_budget_ok mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds
  (aesDecHookMallocng_budget_withFdsGe3Closed_ok aesEncHookMallocng_budget_withFdsGe3Closed_ok
   cliGhostExterns_aesDec_withFdsGe3Closed_hookSat cliGhostExterns_aesEnc_withFdsGe3Closed_hookSat
   cliGhostExterns_libcruxHmac_withFdsGe3Closed_hookSat fineAesDec_budget_withFdsGe3Closed_hookOk
   fineAesEnc_budget_withFdsGe3Closed_hookOk fineLibcruxHmac_budget_withFdsGe3Closed_hookOk
   libcruxHmacHookMallocng_budget_withFdsGe3Closed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliAllocHooks CliGhostAllocHooks CliGhostSpqrAllocHooks cliExternsPlaced_alloc_budget_sat
   cliExternsPlaced_realloc_budget_sat)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget (growOneVecU8_caller_cro_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (bytesMerge3RawBudgetSpec polyEncoderMergeSpec polyEncoderMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlacedBudget
  (polyEncoderMerge_cro_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-! ## `FdsGe3Closed` Transport Across `FdsHiFrame` and `VmPreserved` -/

theorem fdsGe3Closed_of_fdsHiFrame {s s' : State}
    (hfr : FdsHiFrame s s') (h : FdsGe3Closed s.fs) : FdsGe3Closed s'.fs := by
  intro fd hlo hhi
  rw [hfr fd hlo hhi]
  exact h fd hlo hhi

theorem fdsGe3Closed_iff_of_fdsHiFrame {s s' : State} (hfr : FdsHiFrame s s') :
    FdsGe3Closed s'.fs ↔ FdsGe3Closed s.fs :=
  ⟨fdsGe3Closed_of_fdsHiFrame hfr.symm, fdsGe3Closed_of_fdsHiFrame hfr⟩

theorem fdsGe3Closed_iff_of_vmPreserved {s s' : State} (h : VmPreserved s s') :
    FdsGe3Closed s'.fs ↔ FdsGe3Closed s.fs :=
  fdsGe3Closed_iff_of_fdsHiFrame h.fdsHiFrame

/-! ## `withFds` Allocator Wrapper and Definitional Projections -/

/-- Wrap `A : RustCliAllocBudget M` so `pool lim st s` carries `⌜FdsGe3Closed s.fs⌝` whenever
    `lim.enforced = true`. Parameterized variant taking an explicit `VmPreserved → FdsHiFrame`
    bridge (instantiated unconditionally in `withFds` via `VmPreserved.fdsHiFrame`). -/
@[expose]
def withFdsOf {M : AllocCostModel}
    (hfr : ∀ s s' : State, VmPreserved s s' → FdsHiFrame s s')
    (A : RustCliAllocBudget M) : RustCliAllocBudget M where
  pool lim st s :=
    if lim.enforced then (⌜FdsGe3Closed s.fs⌝ ∗ A.pool lim st s) else A.pool lim st s
  live := A.live
  block_valid := A.block_valid
  pool_transport := by
    intro lim st s s' hvm
    by_cases henf : lim.enforced
    · simp only [henf, ↓reduceIte, propext (fdsGe3Closed_iff_of_fdsHiFrame (hfr s s' hvm)),
        A.pool_transport lim st s s' hvm]
    · simp only [henf, Bool.false_eq_true, ↓reduceIte, A.pool_transport lim st s s' hvm]
  pool_zero_transport := by
    intro st s s' hp
    change A.pool zeroBudgetLimits st s' = A.pool zeroBudgetLimits st s
    exact A.pool_zero_transport st s s' hp

/-- Wrap `A : RustCliAllocBudget M` so `pool lim st s` carries `⌜FdsGe3Closed s.fs⌝` whenever
    `lim.enforced = true`. -/
@[expose]
def withFds {M : AllocCostModel} (A : RustCliAllocBudget M) : RustCliAllocBudget M :=
  withFdsOf (fun _ _ h => h.fdsHiFrame) A

@[simp]
theorem withFds_live {M : AllocCostModel} (A : RustCliAllocBudget M) :
    (withFds A).live = A.live := rfl

@[simp]
theorem withFds_block_valid {M : AllocCostModel} (A : RustCliAllocBudget M) :
    (withFds A).block_valid = A.block_valid := rfl

@[simp]
theorem withFds_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M) :
    (withFds A).repAlloc = A.repAlloc := rfl

@[simp]
theorem withFds_toRustCliAlloc {M : AllocCostModel} (A : RustCliAllocBudget M) :
    (withFds A).toRustCliAlloc = A.toRustCliAlloc := rfl

theorem withFds_pool_enforced {M : AllocCostModel} (A : RustCliAllocBudget M)
    {lim : BudgetLimits} (henf : lim.enforced = true) (st : M.σ) (s : State) :
    (withFds A).pool lim st s = (⌜FdsGe3Closed s.fs⌝ ∗ A.pool lim st s) := by
  simp [withFds, withFdsOf, henf]

theorem withFds_pool_unenforced {M : AllocCostModel} (A : RustCliAllocBudget M)
    {lim : BudgetLimits} (henf : lim.enforced = false) (st : M.σ) (s : State) :
    (withFds A).pool lim st s = A.pool lim st s := by
  simp [withFds, withFdsOf, henf]

@[simp]
theorem withFds_pool_zeroBudgetLimits {M : AllocCostModel} (A : RustCliAllocBudget M)
    (st : M.σ) (s : State) :
    (withFds A).pool zeroBudgetLimits st s = A.pool zeroBudgetLimits st s :=
  rfl

/-! ## Core Allocator Hook and Subroutine Bundle Lifts -/

private theorem hookOk_of_pre_post {α : Type} {f : State → State} {spec1 spec2 : Spec α}
    {Q : α → State → Prop}
    (hok : HookOk f spec1)
    (hpan : spec2.onPanic = spec1.onPanic)
    (hexc : spec2.onExit = spec1.onExit)
    (hoom : spec2.onOom = spec1.onOom)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec2.pre x s0 ∗ R) → Q x s0 ∧ (s0.mem ⊨ spec1.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, Q x s0 → (sf.mem ⊨ spec1.post x s0 sf ∗ R) →
      (sf.mem ⊨ spec2.post x s0 sf ∗ R)) :
    HookOk f spec2 := by
  intro x R s0 hrun hpre2 hsp
  obtain ⟨hq, hpre1⟩ := hpre x R s0 hpre2
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre1 hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hp1⟩ | ⟨hp, hpan1⟩ | ⟨c, hc, hexc1⟩ | ⟨ho, hoom1⟩
  · exact Or.inl ⟨hret, hcc, hpost x R s0 (f s0) hq hp1⟩
  · exact Or.inr (Or.inl ⟨hp, hpan ▸ hpan1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc ▸ hexc1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hoom1⟩))

private theorem hookSat_of_hookOk_lift {α : Type} {hooks : String → Option (State → State)}
    {sym : String} {spec1 spec2 : Spec α}
    (hlift : ∀ f, HookOk f spec1 → HookOk f spec2)
    (hsat : HookSat hooks sym spec1) :
    HookSat hooks sym spec2 := by
  rcases hsat with ⟨f, hf, hok⟩
  exact ⟨f, hf, hlift f hok⟩

private theorem subroutine_ok_of_pre_post {α : Type} {P : Program} {entry : BitVec 64}
    {spec1 spec2 : Spec α} {Q : α → State → Prop}
    (hok : subroutine_ok P entry spec1)
    (hpan : spec2.onPanic = spec1.onPanic)
    (hexc : spec2.onExit = spec1.onExit)
    (hoom : spec2.onOom = spec1.onOom)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec2.pre x s0 ∗ R) → Q x s0 ∧ (s0.mem ⊨ spec1.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, Q x s0 → (sf.mem ⊨ spec1.post x s0 sf ∗ R) →
      (sf.mem ⊨ spec2.post x s0 sf ∗ R)) :
    subroutine_ok P entry spec2 := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre2 hsp _
  obtain ⟨hq, hpre1⟩ := hpre x R s0 hpre2
  refine subroutine_ok.mono_outcome hok x R s0 hpc hrun hpre1 hsp ?_
  rintro sf (⟨hret, hcc, hp1⟩ | ⟨hp, hpan1⟩ | ⟨c, hc, hexc1⟩ | ⟨ho, hoom1⟩)
  · exact Or.inl ⟨hret, hcc, hpost x R s0 sf hq hp1⟩
  · exact Or.inr (Or.inl ⟨hp, hpan ▸ hpan1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc ▸ hexc1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hoom1⟩))

private theorem alloc_pre_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true) {P0 : Prop}
    {st : M.σ} {s0 : State} {R : SepProp}
    (h : s0.mem ⊨ (⌜P0⌝ ∗ (withFds A).pool lim st s0 ∗ stackAt s0.sp allocHookStack) ∗ R) :
    FdsGe3Closed s0.fs ∧
      (s0.mem ⊨ (⌜P0⌝ ∗ A.pool lim st s0 ∗ stackAt s0.sp allocHookStack) ∗ R) := by
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (⌜P0⌝ ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗ stackAt s0.sp allocHookStack) ∗ R =
      ⌜FdsGe3Closed s0.fs⌝ ∗ ((⌜P0⌝ ∗ A.pool lim st s0 ∗ stackAt s0.sp allocHookStack) ∗ R) := by
    sep_ac_rfl
  rwa [hEq, satisfies_pure_sepConj] at h

private theorem alloc_post_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {st' : M.σ} {s0 sf : State} {Tail R : SepProp}
    (hClosed0 : FdsGe3Closed s0.fs)
    (h : sf.mem ⊨ (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st' sf ∗ Tail) ∗ R) :
    sf.mem ⊨ (⌜AllocCallPreserved s0 sf⌝ ∗ (withFds A).pool lim st' sf ∗ Tail) ∗ R := by
  have hEq1 :
      (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st' sf ∗ Tail) ∗ R =
      ⌜AllocCallPreserved s0 sf⌝ ∗ (A.pool lim st' sf ∗ Tail ∗ R) := by
    sep_ac_rfl
  rw [hEq1, satisfies_pure_sepConj] at h
  rcases h with ⟨hacp, hrest⟩
  have hClosedF : FdsGe3Closed sf.fs := hacp.1 ▸ hClosed0
  rw [withFds_pool_enforced A henf]
  have hEq2 :
      (⌜AllocCallPreserved s0 sf⌝ ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim st' sf) ∗ Tail) ∗ R =
      ⌜AllocCallPreserved s0 sf⌝ ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ (A.pool lim st' sf ∗ Tail ∗ R)) := by
    sep_ac_rfl
  rw [hEq2, satisfies_pure_sepConj]
  exact ⟨hacp, (satisfies_pure_sepConj _ _ _).mpr ⟨hClosedF, hrest⟩⟩

private theorem dealloc_pre_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true) {P0 : Prop}
    {st : M.σ} {s0 : State} {Tail R : SepProp}
    (h : s0.mem ⊨ (⌜P0⌝ ∗ (withFds A).pool lim st s0 ∗ Tail) ∗ R) :
    FdsGe3Closed s0.fs ∧ (s0.mem ⊨ (⌜P0⌝ ∗ A.pool lim st s0 ∗ Tail) ∗ R) := by
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (⌜P0⌝ ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗ Tail) ∗ R =
      ⌜FdsGe3Closed s0.fs⌝ ∗ ((⌜P0⌝ ∗ A.pool lim st s0 ∗ Tail) ∗ R) := by
    sep_ac_rfl
  rwa [hEq, satisfies_pure_sepConj] at h

private theorem dealloc_post_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true) {Q0 : Prop}
    {st' : M.σ} {s0 sf : State} {Tail R : SepProp}
    (hClosed0 : FdsGe3Closed s0.fs)
    (h : sf.mem ⊨ (⌜AllocCallPreserved s0 sf ∧ Q0⌝ ∗ A.pool lim st' sf ∗ Tail) ∗ R) :
    sf.mem ⊨ (⌜AllocCallPreserved s0 sf ∧ Q0⌝ ∗ (withFds A).pool lim st' sf ∗ Tail) ∗ R := by
  have hEq1 :
      (⌜AllocCallPreserved s0 sf ∧ Q0⌝ ∗ A.pool lim st' sf ∗ Tail) ∗ R =
      ⌜AllocCallPreserved s0 sf ∧ Q0⌝ ∗ (A.pool lim st' sf ∗ Tail ∗ R) := by
    sep_ac_rfl
  rw [hEq1, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hacp, hq0⟩, hrest⟩
  have hClosedF : FdsGe3Closed sf.fs := hacp.1 ▸ hClosed0
  rw [withFds_pool_enforced A henf]
  have hEq2 :
      (⌜AllocCallPreserved s0 sf ∧ Q0⌝ ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim st' sf) ∗ Tail) ∗ R =
      ⌜AllocCallPreserved s0 sf ∧ Q0⌝ ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ (A.pool lim st' sf ∗ Tail ∗ R)) := by
    sep_ac_rfl
  rw [hEq2, satisfies_pure_sepConj]
  exact ⟨⟨hacp, hq0⟩, (satisfies_pure_sepConj _ _ _).mpr ⟨hClosedF, hrest⟩⟩

private theorem allocSpec_eq_unenforced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = false) (zeroed : Bool) :
    rustCliAllocBudgetSpec M (withFds A) lim zeroed = rustCliAllocBudgetSpec M A lim zeroed := by
  simp only [rustCliAllocBudgetSpec, withFds_pool_unenforced A henf, withFds_live]

private theorem deallocSpec_eq_unenforced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = false) :
    rustCliDeallocBudgetSpec M (withFds A) lim = rustCliDeallocBudgetSpec M A lim := by
  simp only [rustCliDeallocBudgetSpec, withFds_pool_unenforced A henf, withFds_live]

private theorem reallocSpec_eq_unenforced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = false) :
    rustCliReallocBudgetSpec M (withFds A) lim = rustCliReallocBudgetSpec M A lim := by
  simp only [rustCliReallocBudgetSpec, withFds_pool_unenforced A henf, withFds_live]

private theorem allocSpecBase_eq_unenforced {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = false) (zeroed : Bool) :
    rustCliAllocBudgetSpecBase M (withFds A) lim zeroed =
      rustCliAllocBudgetSpecBase M A lim zeroed := by
  simp only [rustCliAllocBudgetSpecBase, withFds_pool_unenforced A henf, withFds_live]

private theorem deallocSpecBase_eq_unenforced {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = false) :
    rustCliDeallocBudgetSpecBase M (withFds A) lim = rustCliDeallocBudgetSpecBase M A lim := by
  simp only [rustCliDeallocBudgetSpecBase, withFds_pool_unenforced A henf, withFds_live]

private theorem reallocSpecBase_eq_unenforced {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = false) :
    rustCliReallocBudgetSpecBase M (withFds A) lim = rustCliReallocBudgetSpecBase M A lim := by
  simp only [rustCliReallocBudgetSpecBase, withFds_pool_unenforced A henf, withFds_live]

theorem hookOk_allocBudget_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool} {f : State → State}
    (hok : HookOk f (rustCliAllocBudgetSpec M A lim zeroed)) :
    HookOk f (rustCliAllocBudgetSpec M (withFds A) lim zeroed) := by
  cases henf : lim.enforced
  · rwa [allocSpec_eq_unenforced A henf zeroed]
  · refine hookOk_of_pre_post (Q := fun _ s0 => FdsGe3Closed s0.fs) hok rfl rfl rfl ?_ ?_
    · rintro ⟨size, align, st⟩ R s0 hpre
      exact alloc_pre_enforced henf hpre
    · rintro ⟨size, align, st⟩ R s0 sf hClosed0 hpost
      dsimp only [rustCliAllocBudgetSpec, withFds_live] at hpost ⊢
      exact alloc_post_enforced henf hClosed0 hpost

theorem hookOk_deallocBudget_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {f : State → State}
    (hok : HookOk f (rustCliDeallocBudgetSpec M A lim)) :
    HookOk f (rustCliDeallocBudgetSpec M (withFds A) lim) := by
  cases henf : lim.enforced
  · rwa [deallocSpec_eq_unenforced A henf]
  · refine hookOk_of_pre_post (Q := fun _ s0 => FdsGe3Closed s0.fs) hok rfl rfl rfl ?_ ?_
    · rintro ⟨p, size, align, st⟩ R s0 hpre
      dsimp only [rustCliDeallocBudgetSpec, withFds_live] at hpre ⊢
      exact dealloc_pre_enforced henf hpre
    · rintro ⟨p, size, align, st⟩ R s0 sf hClosed0 hpost
      dsimp only [rustCliDeallocBudgetSpec] at hpost ⊢
      exact dealloc_post_enforced henf hClosed0 hpost

theorem hookOk_reallocBudget_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {f : State → State}
    (hok : HookOk f (rustCliReallocBudgetSpec M A lim)) :
    HookOk f (rustCliReallocBudgetSpec M (withFds A) lim) := by
  cases henf : lim.enforced
  · rwa [reallocSpec_eq_unenforced A henf]
  · refine hookOk_of_pre_post (Q := fun _ s0 => FdsGe3Closed s0.fs) hok rfl rfl rfl ?_ ?_
    · rintro ⟨p, old, align, new, bs, st⟩ R s0 hpre
      dsimp only [rustCliReallocBudgetSpec, withFds_live] at hpre ⊢
      exact dealloc_pre_enforced henf hpre
    · rintro ⟨p, old, align, new, bs, st⟩ R s0 sf hClosed0 hpost
      dsimp only [rustCliReallocBudgetSpec, withFds_live] at hpost ⊢
      exact alloc_post_enforced henf hClosed0 hpost

theorem subroutine_ok_allocBudget_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool} {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (rustCliAllocBudgetSpec M A lim zeroed)) :
    subroutine_ok P entry (rustCliAllocBudgetSpec M (withFds A) lim zeroed) := by
  cases henf : lim.enforced
  · rwa [allocSpec_eq_unenforced A henf zeroed]
  · refine subroutine_ok_of_pre_post (Q := fun _ s0 => FdsGe3Closed s0.fs) hok rfl rfl rfl ?_ ?_
    · rintro ⟨size, align, st⟩ R s0 hpre
      exact alloc_pre_enforced henf hpre
    · rintro ⟨size, align, st⟩ R s0 sf hClosed0 hpost
      dsimp only [rustCliAllocBudgetSpec, withFds_live] at hpost ⊢
      exact alloc_post_enforced henf hClosed0 hpost

theorem subroutine_ok_deallocBudget_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok P entry (rustCliDeallocBudgetSpec M (withFds A) lim) := by
  cases henf : lim.enforced
  · rwa [deallocSpec_eq_unenforced A henf]
  · refine subroutine_ok_of_pre_post (Q := fun _ s0 => FdsGe3Closed s0.fs) hok rfl rfl rfl ?_ ?_
    · rintro ⟨p, size, align, st⟩ R s0 hpre
      dsimp only [rustCliDeallocBudgetSpec, withFds_live] at hpre ⊢
      exact dealloc_pre_enforced henf hpre
    · rintro ⟨p, size, align, st⟩ R s0 sf hClosed0 hpost
      dsimp only [rustCliDeallocBudgetSpec] at hpost ⊢
      exact dealloc_post_enforced henf hClosed0 hpost

theorem subroutine_ok_reallocBudget_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok P entry (rustCliReallocBudgetSpec M (withFds A) lim) := by
  cases henf : lim.enforced
  · rwa [reallocSpec_eq_unenforced A henf]
  · refine subroutine_ok_of_pre_post (Q := fun _ s0 => FdsGe3Closed s0.fs) hok rfl rfl rfl ?_ ?_
    · rintro ⟨p, old, align, new, bs, st⟩ R s0 hpre
      dsimp only [rustCliReallocBudgetSpec, withFds_live] at hpre ⊢
      exact dealloc_pre_enforced henf hpre
    · rintro ⟨p, old, align, new, bs, st⟩ R s0 sf hClosed0 hpost
      dsimp only [rustCliReallocBudgetSpec, withFds_live] at hpost ⊢
      exact alloc_post_enforced henf hClosed0 hpost

theorem hookOk_allocBudgetBase_withFds {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool} {f : State → State}
    (hok : HookOk f (rustCliAllocBudgetSpecBase M A lim zeroed)) :
    HookOk f (rustCliAllocBudgetSpecBase M (withFds A) lim zeroed) := by
  cases henf : lim.enforced
  · rwa [allocSpecBase_eq_unenforced A henf zeroed]
  · refine hookOk_of_pre_post (Q := fun _ s0 => FdsGe3Closed s0.fs) hok rfl rfl rfl ?_ ?_
    · rintro ⟨size, align, st⟩ R s0 hpre
      exact alloc_pre_enforced henf hpre
    · rintro ⟨size, align, st⟩ R s0 sf hClosed0 hpost
      dsimp only [rustCliAllocBudgetSpecBase, withFds_live] at hpost ⊢
      exact alloc_post_enforced henf hClosed0 hpost

theorem hookOk_deallocBudgetBase_withFds {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {f : State → State}
    (hok : HookOk f (rustCliDeallocBudgetSpecBase M A lim)) :
    HookOk f (rustCliDeallocBudgetSpecBase M (withFds A) lim) := by
  cases henf : lim.enforced
  · rwa [deallocSpecBase_eq_unenforced A henf]
  · refine hookOk_of_pre_post (Q := fun _ s0 => FdsGe3Closed s0.fs) hok rfl rfl rfl ?_ ?_
    · rintro ⟨p, size, align, st⟩ R s0 hpre
      dsimp only [rustCliDeallocBudgetSpecBase, withFds_live] at hpre ⊢
      exact dealloc_pre_enforced henf hpre
    · rintro ⟨p, size, align, st⟩ R s0 sf hClosed0 hpost
      dsimp only [rustCliDeallocBudgetSpecBase] at hpost ⊢
      exact dealloc_post_enforced henf hClosed0 hpost

theorem hookOk_reallocBudgetBase_withFds {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {f : State → State}
    (hok : HookOk f (rustCliReallocBudgetSpecBase M A lim)) :
    HookOk f (rustCliReallocBudgetSpecBase M (withFds A) lim) := by
  cases henf : lim.enforced
  · rwa [reallocSpecBase_eq_unenforced A henf]
  · refine hookOk_of_pre_post (Q := fun _ s0 => FdsGe3Closed s0.fs) hok rfl rfl rfl ?_ ?_
    · rintro ⟨p, old, align, new, bs, st⟩ R s0 hpre
      dsimp only [rustCliReallocBudgetSpecBase, withFds_live] at hpre ⊢
      exact dealloc_pre_enforced henf hpre
    · rintro ⟨p, old, align, new, bs, st⟩ R s0 sf hClosed0 hpost
      dsimp only [rustCliReallocBudgetSpecBase, withFds_live] at hpost ⊢
      exact alloc_post_enforced henf hClosed0 hpost

theorem subroutine_ok_allocBudgetBase_withFds {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool} {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (rustCliAllocBudgetSpecBase M A lim zeroed)) :
    subroutine_ok P entry (rustCliAllocBudgetSpecBase M (withFds A) lim zeroed) := by
  cases henf : lim.enforced
  · rwa [allocSpecBase_eq_unenforced A henf zeroed]
  · refine subroutine_ok_of_pre_post (Q := fun _ s0 => FdsGe3Closed s0.fs) hok rfl rfl rfl ?_ ?_
    · rintro ⟨size, align, st⟩ R s0 hpre
      exact alloc_pre_enforced henf hpre
    · rintro ⟨size, align, st⟩ R s0 sf hClosed0 hpost
      dsimp only [rustCliAllocBudgetSpecBase, withFds_live] at hpost ⊢
      exact alloc_post_enforced henf hClosed0 hpost

theorem subroutine_ok_deallocBudgetBase_withFds {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok P entry (rustCliDeallocBudgetSpecBase M (withFds A) lim) := by
  cases henf : lim.enforced
  · rwa [deallocSpecBase_eq_unenforced A henf]
  · refine subroutine_ok_of_pre_post (Q := fun _ s0 => FdsGe3Closed s0.fs) hok rfl rfl rfl ?_ ?_
    · rintro ⟨p, size, align, st⟩ R s0 hpre
      dsimp only [rustCliDeallocBudgetSpecBase, withFds_live] at hpre ⊢
      exact dealloc_pre_enforced henf hpre
    · rintro ⟨p, size, align, st⟩ R s0 sf hClosed0 hpost
      dsimp only [rustCliDeallocBudgetSpecBase] at hpost ⊢
      exact dealloc_post_enforced henf hClosed0 hpost

theorem subroutine_ok_reallocBudgetBase_withFds {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (rustCliReallocBudgetSpecBase M A lim)) :
    subroutine_ok P entry (rustCliReallocBudgetSpecBase M (withFds A) lim) := by
  cases henf : lim.enforced
  · rwa [reallocSpecBase_eq_unenforced A henf]
  · refine subroutine_ok_of_pre_post (Q := fun _ s0 => FdsGe3Closed s0.fs) hok rfl rfl rfl ?_ ?_
    · rintro ⟨p, old, align, new, bs, st⟩ R s0 hpre
      dsimp only [rustCliReallocBudgetSpecBase, withFds_live] at hpre ⊢
      exact dealloc_pre_enforced henf hpre
    · rintro ⟨p, old, align, new, bs, st⟩ R s0 sf hClosed0 hpost
      dsimp only [rustCliReallocBudgetSpecBase, withFds_live] at hpost ⊢
      exact alloc_post_enforced henf hClosed0 hpost

theorem rustCliAllocBudgetHooks_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (h : RustCliAllocBudgetHooks M A hooks) :
    RustCliAllocBudgetHooks M (withFds A) hooks where
  alloc lim := hookSat_of_hookOk_lift (fun _ => hookOk_allocBudget_withFds) (h.alloc lim)
  dealloc lim := hookSat_of_hookOk_lift (fun _ => hookOk_deallocBudget_withFds) (h.dealloc lim)
  realloc lim := hookSat_of_hookOk_lift (fun _ => hookOk_reallocBudget_withFds) (h.realloc lim)

theorem rustCliAllocBudgetEntries_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (h : RustCliAllocBudgetEntries M A P addrs) :
    RustCliAllocBudgetEntries M (withFds A) P addrs where
  alloc lim := subroutine_ok_allocBudget_withFds (h.alloc lim)
  dealloc lim := subroutine_ok_deallocBudget_withFds (h.dealloc lim)
  realloc lim := subroutine_ok_reallocBudget_withFds (h.realloc lim)

theorem allocHooksBudget_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hooks : String → Option (State → State)}
    (h : AllocHooksBudget M A lim hooks) :
    AllocHooksBudget M (withFds A) lim hooks where
  alloc := hookSat_of_hookOk_lift (fun _ => hookOk_allocBudget_withFds) h.alloc
  dealloc := hookSat_of_hookOk_lift (fun _ => hookOk_deallocBudget_withFds) h.dealloc
  realloc := hookSat_of_hookOk_lift (fun _ => hookOk_reallocBudget_withFds) h.realloc

theorem rustCliAllocBudgetHooksBase_withFds {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (h : RustCliAllocBudgetHooksBase M A hooks) :
    RustCliAllocBudgetHooksBase M (withFds A) hooks where
  alloc lim := hookSat_of_hookOk_lift (fun _ => hookOk_allocBudgetBase_withFds) (h.alloc lim)
  dealloc lim := hookSat_of_hookOk_lift (fun _ => hookOk_deallocBudgetBase_withFds) (h.dealloc lim)
  realloc lim := hookSat_of_hookOk_lift (fun _ => hookOk_reallocBudgetBase_withFds) (h.realloc lim)

theorem rustCliAllocBudgetEntriesBase_withFds {M : AllocCostModel}
    {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (h : RustCliAllocBudgetEntriesBase M A P addrs) :
    RustCliAllocBudgetEntriesBase M (withFds A) P addrs where
  alloc lim := subroutine_ok_allocBudgetBase_withFds (h.alloc lim)
  dealloc lim := subroutine_ok_deallocBudgetBase_withFds (h.dealloc lim)
  realloc lim := subroutine_ok_reallocBudgetBase_withFds (h.realloc lim)

theorem allocHooksBudgetBase_withFds {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hooks : String → Option (State → State)}
    (h : AllocHooksBudgetBase M A lim hooks) :
    AllocHooksBudgetBase M (withFds A) lim hooks where
  alloc := hookSat_of_hookOk_lift (fun _ => hookOk_allocBudgetBase_withFds) h.alloc
  dealloc := hookSat_of_hookOk_lift (fun _ => hookOk_deallocBudgetBase_withFds) h.dealloc
  realloc := hookSat_of_hookOk_lift (fun _ => hookOk_reallocBudgetBase_withFds) h.realloc

theorem cliAllocHooks_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : CliAllocHooks M A lim) :
    CliAllocHooks M (withFds A) lim where
  alloc := hookOk_allocBudget_withFds h.alloc
  dealloc := hookOk_deallocBudget_withFds h.dealloc
  realloc := hookOk_reallocBudget_withFds h.realloc

theorem cliGhostAllocHooks_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {g : CliGhostHooks}
    (h : CliGhostAllocHooks M A lim g) :
    CliGhostAllocHooks M (withFds A) lim g where
  alloc := hookOk_allocBudget_withFds h.alloc
  dealloc := hookOk_deallocBudget_withFds h.dealloc
  realloc := hookOk_reallocBudget_withFds h.realloc
  alloc_fs := h.alloc_fs
  dealloc_fs := h.dealloc_fs
  realloc_fs := h.realloc_fs
  alloc_fsT := h.alloc_fsT
  dealloc_fsT := h.dealloc_fsT
  realloc_fsT := h.realloc_fsT
  shim_eq := h.shim_eq
  memset := h.memset
  memcpy := h.memcpy
  memcpy_exact := h.memcpy_exact
  memset_acp := h.memset_acp

theorem cliGhostSpqrAllocHooks_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {g : CliGhostHooks}
    (h : CliGhostSpqrAllocHooks M A lim g) :
    CliGhostSpqrAllocHooks M (withFds A) lim g :=
  { cliGhostAllocHooks_withFds h.toCliGhostAllocHooks with
    allocZeroed := hookOk_allocBudget_withFds h.allocZeroed
    allocZeroed_fs := h.allocZeroed_fs
    allocZeroed_fsT := h.allocZeroed_fsT }

/-! ## Crypto Hook and `SpqrHooksBudget` Lifts -/

theorem hookOk_libcruxHmacBudget_withFds_of_enforced {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {f : State → State}
    (hok : HookOk f (withFdsGe3Closed (libcruxHmacBudgetSpec F M A lim))) :
    HookOk f (libcruxHmacBudgetSpec F M (withFds A) lim) := by
  refine hookOk_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    refine ⟨trivial, ?_⟩
    dsimp only [withFdsGe3Closed, libcruxHmacBudgetSpec] at hpre ⊢
    rw [withFds_pool_enforced A henf] at hpre
    have hEq :
        (⌜s0.readReg64 .x8 = x.ret ∧ (s0.readReg64 .x0).setWidth 32 = 0#32 ∧
            s0.readReg64 .x1 = x.keyA ∧ (s0.readReg64 .x2).toNat = x.key.length ∧
            s0.readReg64 .x3 = x.dataA ∧ (s0.readReg64 .x4).toNat = x.data.length ∧
            (s0.readReg64 .x5).setWidth 32 = 1#32 ∧ s0.readReg64 .x6 = 32#64 ∧
            FitsEnv M lim st (LibcruxHmacEnv x)⌝ ∗
          (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
          memRegion x.ret 24 ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗
          stackAt s0.sp extHookStack) ∗ R =
        (⌜FdsGe3Closed s0.fs⌝ ∗
          ⌜s0.readReg64 .x8 = x.ret ∧ (s0.readReg64 .x0).setWidth 32 = 0#32 ∧
            s0.readReg64 .x1 = x.keyA ∧ (s0.readReg64 .x2).toNat = x.key.length ∧
            s0.readReg64 .x3 = x.dataA ∧ (s0.readReg64 .x4).toNat = x.data.length ∧
            (s0.readReg64 .x5).setWidth 32 = 1#32 ∧ s0.readReg64 .x6 = 32#64 ∧
            FitsEnv M lim st (LibcruxHmacEnv x)⌝ ∗
          (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
          memRegion x.ret 24 ∗ A.pool lim st s0 ∗
          stackAt s0.sp extHookStack) ∗ R := by
      sep_ac_rfl
    rwa [hEq] at hpre
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hClosedF, hpost⟩
    dsimp only [libcruxHmacBudgetSpec, withFds_repAlloc] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [withFds_pool_enforced A henf]
    have hEq :
        (⌜x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧
            sf.trace = s0.trace ∧ LibcruxHmacEnv x evs⌝ ∗
          (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
          CryptoVerification.RustHeap.vecU8 A.repAlloc x.ret (hmacWith F x.key x.data) ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp extHookStack) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧
              sf.trace = s0.trace ∧ LibcruxHmacEnv x evs⌝ ∗
            (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
            CryptoVerification.RustHeap.vecU8 A.repAlloc x.ret (hmacWith F x.key x.data) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp extHookStack) ∗ R) := by
      sep_ac_rfl
    rw [hEq, satisfies_pure_sepConj]
    exact ⟨hClosedF, hpost⟩

theorem hookSat_libcruxHmacBudget_withFds_of_enforced {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {abs : String → Option (State → State)} {sym : String}
    (hsat : HookSat abs sym (withFdsGe3Closed (libcruxHmacBudgetSpec F M A lim))) :
    HookSat abs sym (libcruxHmacBudgetSpec F M (withFds A) lim) :=
  hookSat_of_hookOk_lift (fun _ => hookOk_libcruxHmacBudget_withFds_of_enforced henf) hsat

private theorem aes_pre_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 P2 P3 P4 P5 Tail R : SepProp} {st : M.σ} {s0 : State}
    (h : s0.mem ⊨ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (withFds A).pool lim st s0 ∗ Tail) ∗ R) :
    s0.mem ⊨ (⌜FdsGe3Closed s0.fs⌝ ∗ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim st s0 ∗ Tail)) ∗ R := by
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗ Tail) ∗ R =
      (⌜FdsGe3Closed s0.fs⌝ ∗ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim st s0 ∗ Tail)) ∗ R := by
    sep_ac_rfl
  rwa [hEq] at h

private theorem aes_post_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 : List AllocEvent → SepProp} {P2 P3 Tail R : SepProp}
    {st : M.σ} {sf : State}
    (h : sf.mem ⊨ (⌜FdsGe3Closed sf.fs⌝ ∗
        (∃∗ evs : List AllocEvent,
          P1 evs ∗ P2 ∗ P3 ∗ A.pool lim (M.stepEvents evs st) sf ∗ Tail)) ∗ R) :
    sf.mem ⊨ (∃∗ evs : List AllocEvent,
        P1 evs ∗ P2 ∗ P3 ∗ (withFds A).pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨hClosedF, h⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at h ⊢
  rcases h with ⟨evs, h⟩
  refine ⟨evs, ?_⟩
  rw [withFds_pool_enforced A henf]
  have hEq :
      (P1 evs ∗ P2 ∗ P3 ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ Tail) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗ ((P1 evs ∗ P2 ∗ P3 ∗ A.pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj]
  exact ⟨hClosedF, h⟩

theorem hookOk_aesEncBudget_withFds_of_enforced {E : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {f : State → State}
    (hokFd : HookOk f (withFdsGe3Closed (aesEncBudgetSpec E M A lim))) :
    HookOk f (aesEncBudgetSpec E M (withFds A) lim) := by
  refine hookOk_of_pre_post (Q := fun _ _ => True) hokFd rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    dsimp only [withFdsGe3Closed, aesEncBudgetSpec, aesCallPreBudget] at hpre ⊢
    exact ⟨trivial, aes_pre_enforced henf hpre⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, aesEncBudgetSpec, withFds_repAlloc] at hpost ⊢
    exact aes_post_enforced henf hpost

theorem hookOk_aesDecBudget_withFds_of_enforced {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {f : State → State}
    (hokFd : HookOk f (withFdsGe3Closed (aesDecBudgetSpec D M A lim))) :
    HookOk f (aesDecBudgetSpec D M (withFds A) lim) := by
  refine hookOk_of_pre_post (Q := fun _ _ => True) hokFd rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    dsimp only [withFdsGe3Closed, aesDecBudgetSpec, aesCallPreBudget] at hpre ⊢
    exact ⟨trivial, aes_pre_enforced henf hpre⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, aesDecBudgetSpec, withFds_repAlloc] at hpost ⊢
    exact aes_post_enforced henf hpost

theorem hookOk_aesEncBudget_withFds {E : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {f : State → State}
    (hok : HookOk f (aesEncBudgetSpec E M A lim))
    (hokFd : lim.enforced = true → HookOk f (withFdsGe3Closed (aesEncBudgetSpec E M A lim))) :
    HookOk f (aesEncBudgetSpec E M (withFds A) lim) := by
  cases henf : lim.enforced
  · have hEq : aesEncBudgetSpec E M (withFds A) lim = aesEncBudgetSpec E M A lim := by
      simp only [aesEncBudgetSpec, aesCallPreBudget, withFds_pool_unenforced A henf, withFds_repAlloc]
    exact hEq ▸ hok
  · exact hookOk_aesEncBudget_withFds_of_enforced henf (hokFd henf)

theorem hookOk_aesDecBudget_withFds {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {f : State → State}
    (hok : HookOk f (aesDecBudgetSpec D M A lim))
    (hokFd : lim.enforced = true → HookOk f (withFdsGe3Closed (aesDecBudgetSpec D M A lim))) :
    HookOk f (aesDecBudgetSpec D M (withFds A) lim) := by
  cases henf : lim.enforced
  · have hEq : aesDecBudgetSpec D M (withFds A) lim = aesDecBudgetSpec D M A lim := by
      simp only [aesDecBudgetSpec, aesCallPreBudget, withFds_pool_unenforced A henf, withFds_repAlloc]
    exact hEq ▸ hok
  · exact hookOk_aesDecBudget_withFds_of_enforced henf (hokFd henf)

theorem aesDecHookMallocng_budget_withFds_ok
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (D : AesKey → Block → Block) :
    HookOk (aesDecHookMallocng mpl D)
      (aesDecBudgetSpec D M
        (withFds (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart)) lim) :=
  hookOk_aesDecBudget_withFds
    (aesDecHookMallocng_budget_ok hS γ tp brkStart lim hPl D)
    (fun _ => aesDecHookMallocng_budget_withFdsGe3Closed_ok hS γ tp brkStart lim hPl D)

theorem fineAesDec_budget_withFds_hookOk (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (D : AesKey → Block → Block) :
    HookOk (aesDecHookMallocng mpl D)
      (aesDecBudgetSpec D fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mpl tp brkStart)) lim) :=
  hookOk_aesDecBudget_withFds
    (fineAesDec_budget_hookOk γ tp brkStart lim hPl D)
    (fun _ => fineAesDec_budget_withFdsGe3Closed_hookOk γ tp brkStart lim hPl D)

theorem fineAesEnc_budget_withFds_hookOk (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (E : AesKey → Block → Block) :
    HookOk (aesEncHookMallocng mpl E)
      (aesEncBudgetSpec E fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mpl tp brkStart)) lim) :=
  hookOk_aesEncBudget_withFds
    (fineAesEnc_budget_hookOk γ tp brkStart lim hPl E)
    (fun _ => fineAesEnc_budget_withFdsGe3Closed_hookOk γ tp brkStart lim hPl E)

theorem libcruxHmacHookMallocng_budget_withFds_ok
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (F : ShaState → List (BitVec 8) → ShaState) :
    HookOk (libcruxHmacHookMallocng mpl F)
      (libcruxHmacBudgetSpec F M
        (withFds (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart)) lim) := by
  cases henf : lim.enforced
  · have hEq : libcruxHmacBudgetSpec F M
        (withFds (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart)) lim =
        libcruxHmacBudgetSpec F M
          (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim := by
      simp only [libcruxHmacBudgetSpec,
        withFds_pool_unenforced (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) henf,
        withFds_repAlloc]
    exact hEq ▸ libcruxHmacHookMallocng_budget_ok hS γ tp brkStart lim hPl F
  · exact hookOk_libcruxHmacBudget_withFds_of_enforced henf
      (libcruxHmacHookMallocng_budget_withFdsGe3Closed_ok hS γ tp brkStart lim hPl F)

theorem cliGhostExterns_aesEnc_withFds_hookSat
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    {lim : BudgetLimits} (henf : lim.enforced = true) (gh : CliGhostHooks) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
      (aesEncBudgetSpec W.C.E fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim) :=
  hookSat_of_hookOk_lift (fun _ => hookOk_aesEncBudget_withFds_of_enforced henf)
    (cliGhostExterns_aesEnc_withFdsGe3Closed_hookSat γ mmpl tp brkStart lim gh W hPl)

theorem cliGhostExterns_aesDec_withFds_hookSat
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    {lim : BudgetLimits} (henf : lim.enforced = true) (gh : CliGhostHooks) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecBudgetSpec W.C.D fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim) :=
  hookSat_of_hookOk_lift (fun _ => hookOk_aesDecBudget_withFds_of_enforced henf)
    (cliGhostExterns_aesDec_withFdsGe3Closed_hookSat γ mmpl tp brkStart lim gh W hPl)

theorem cliGhostExterns_libcruxHmac_withFds_hookSat
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    {lim : BudgetLimits} (henf : lim.enforced = true) (gh : CliGhostHooks) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (libcruxHmacBudgetSpec W.C.F fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim) :=
  hookSat_libcruxHmacBudget_withFds_of_enforced henf
    (cliGhostExterns_libcruxHmac_withFdsGe3Closed_hookSat γ mmpl tp brkStart lim gh W hPl)

/-- Lift `SpqrHooksBudget C M A lim K abs` to `withFds A` using a `withFdsGe3Closed` HMAC hook
    contract when `lim.enforced = true`. -/
theorem spqrHooksBudget_withFds {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {K : MlKem}
    {abs : String → Option (State → State)}
    (h : SpqrHooksBudget C M A lim K abs)
    (hHmacFd : lim.enforced = true →
      HookSat abs libcruxHmacName (withFdsGe3Closed (libcruxHmacBudgetSpec C.F M A lim))) :
    SpqrHooksBudget C M (withFds A) lim K abs := by
  refine
    { fromSeed := h.fromSeed
      pk1 := h.pk1
      pk2 := h.pk2
      encaps1 := h.encaps1
      encaps2 := h.encaps2
      decaps := h.decaps
      validatePk := h.validatePk
      hmac := ?_ }
  cases henf : lim.enforced
  · have hEq : libcruxHmacBudgetSpec C.F M (withFds A) lim = libcruxHmacBudgetSpec C.F M A lim := by
      simp only [libcruxHmacBudgetSpec, withFds_pool_unenforced A henf, withFds_repAlloc]
    rw [hEq]
    exact h.hmac
  · exact hookSat_libcruxHmacBudget_withFds_of_enforced henf (hHmacFd henf)

/-! ## `grow_one` and `PolynomialEncoder::merge` `withFdsGe3Closed` Corollaries -/

private theorem hExt_withPanics (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {sym : String} (hne : sym ≠ "libsignal_session_rng_fill" := by decide) :
    Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := by
  have h1 : Rust.withPanics ext sym =
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym := by
    simp only [Rust.withPanics, hExt sym hne]
  exact h1.trans (congrFun (withPanics_cliGhostExterns mmpl gh W) sym)

private theorem hookSat_withPanics_hExt {α : Type}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {sym : String} {spec : Spec α}
    (h : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym spec)
    (hne : sym ≠ "libsignal_session_rng_fill" := by decide) :
    HookSat (Rust.withPanics ext) sym spec := by
  rcases h with ⟨f, hf, hok⟩
  exact ⟨f, (hExt_withPanics mmpl gh W hExt hne).trans hf, hok⟩

private theorem cliGhost_noAllocShimBudget_sat
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hShim : gh.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsRustNoAllocShimSymCli
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimSpec :=
  ⟨hookNoop, (cliGhostExterns_shim gh _).trans (congrArg some hShim),
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShim_hookOk⟩

private theorem cro6_pre_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 P2 P3 P4 Tail Cro R : SepProp} {st : M.σ} {s0 : State}
    (hClosed0 : FdsGe3Closed s0.fs)
    (h : s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ A.pool lim st s0 ∗ Tail) ∗ Cro) ∗ R) :
    s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ (withFds A).pool lim st s0 ∗ Tail) ∗ Cro) ∗ R := by
  rw [withFds_pool_enforced A henf]
  have hEq :
      ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗ Tail) ∗ Cro) ∗ R =
      ⌜FdsGe3Closed s0.fs⌝ ∗ (((P1 ∗ P2 ∗ P3 ∗ P4 ∗ A.pool lim st s0 ∗ Tail) ∗ Cro) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj]
  exact ⟨hClosed0, h⟩

private theorem grow_post_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 : List AllocEvent → SepProp} {P2 Tail R : SepProp}
    {st : M.σ} {sf : State}
    (h : sf.mem ⊨ (∃∗ evs : List AllocEvent,
        P1 evs ∗ P2 ∗ (withFds A).pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R) :
    sf.mem ⊨ (⌜FdsGe3Closed sf.fs⌝ ∗
        (∃∗ evs : List AllocEvent,
          P1 evs ∗ P2 ∗ A.pool lim (M.stepEvents evs st) sf ∗ Tail)) ∗ R := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (P1 evs ∗ P2 ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ Tail) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗ ((P1 evs ∗ P2 ∗ A.pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h
  rcases h with ⟨hClosedF, h⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hClosedF, ?_⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨evs, h⟩

private theorem poly_post_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 P2 Tail R : SepProp} {Q : List AllocEvent → SepProp}
    {st : M.σ} {sf : State}
    (h : sf.mem ⊨ (P1 ∗ P2 ∗
        (∃∗ evs : List AllocEvent, Q evs ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗
        Tail) ∗ R) :
    sf.mem ⊨ (⌜FdsGe3Closed sf.fs⌝ ∗
        (P1 ∗ P2 ∗
          (∃∗ evs : List AllocEvent, Q evs ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          Tail)) ∗ R := by
  have hEq1 :
      (P1 ∗ P2 ∗
        (∃∗ evs : List AllocEvent, Q evs ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗
        Tail) ∗ R =
      (∃∗ evs : List AllocEvent, Q evs ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗
        (P1 ∗ P2 ∗ Tail ∗ R) := by
    sep_ac_rfl
  rw [hEq1, sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq2 :
      (Q evs ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)) ∗
        (P1 ∗ P2 ∗ Tail ∗ R) =
      ⌜FdsGe3Closed sf.fs⌝ ∗
        ((Q evs ∗ A.pool lim (M.stepEvents evs st) sf) ∗ (P1 ∗ P2 ∗ Tail ∗ R)) := by
    sep_ac_rfl
  rw [hEq2, satisfies_pure_sepConj] at h
  rcases h with ⟨hClosedF, h⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hClosedF, ?_⟩
  have hEq3 :
      (P1 ∗ P2 ∗
        (∃∗ evs : List AllocEvent, Q evs ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        Tail) ∗ R =
      (∃∗ evs : List AllocEvent, Q evs ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        (P1 ∗ P2 ∗ Tail ∗ R) := by
    sep_ac_rfl
  rw [hEq3, sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨evs, h⟩

/-- Extract `withFdsGe3Closed (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))` from
`growOneVecU8BudgetSpec M (withFds A) lim` when `lim.enforced = true`. -/
theorem subroutine_ok_growOneVecU8_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M (withFds A) lim))) :
    subroutine_ok P entry
      (withFdsGe3Closed (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [withLsCodeRoLoaded, growOneVecU8BudgetSpec, rawVecGrowBudgetSpec,
      withFds_live] at hpreA ⊢
    exact ⟨trivial, cro6_pre_enforced henf hClosed0 hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, withLsCodeRoLoaded, growOneVecU8BudgetSpec,
      rawVecGrowBudgetSpec, withFds_live] at hpost ⊢
    exact grow_post_enforced henf hpost

/-- Closed `cliGhostExterns` instantiation of `grow_one` (block 621) at `withFdsGe3Closed`
when `lim.enforced = true`. -/
theorem cliGrowOneVecU8_at_block_withFdsGe3Closed [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    {bi : Nat} [LsBlockBound bi] (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 621)
      (withFdsGe3Closed (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :=
  subroutine_ok_growOneVecU8_withFdsGe3Closed_of_withFds henf
    (growOneVecU8_caller_cro_ok (A := withFds A)
      ((hExt_withPanics mmpl gh W hExt).trans (cliGhostExterns_panic_handle_error mmpl gh W))
      (hookSat_withPanics_hExt mmpl gh W hExt (cliGhost_noAllocShimBudget_sat mmpl gh W hA.shim_eq))
      (hookSat_withPanics_hExt mmpl gh W hExt
        (cliExternsPlaced_alloc_budget_sat mmpl gh W (cliGhostAllocHooks_withFds hA)))
      (hookSat_withPanics_hExt mmpl gh W hExt
        (cliExternsPlaced_realloc_budget_sat mmpl gh W (cliGhostAllocHooks_withFds hA)))
      hi)

theorem subroutine_ok_polyEncoderMerge_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec (withFds A) lim))) :
    subroutine_ok P entry
      (withFdsGe3Closed (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim))) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [withLsCodeRoLoaded, polyEncoderMergeSpec, polyEncoderMergeSpecOfEnv,
      withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, cro6_pre_enforced henf hClosed0 hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, withLsCodeRoLoaded, polyEncoderMergeSpec,
      polyEncoderMergeSpecOfEnv, withFds_repAlloc] at hpost ⊢
    exact poly_post_enforced henf hpost

/-- Derive `withFdsGe3Closed (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim))` on block 297
(`PolynomialEncoder::merge`) by instantiating `polyEncoderMerge_cro_placed_ok_of_contracts` at
`withFds A`. -/
theorem polyEncoderMerge_cro_placed_ok_withFdsGe3Closed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henf : lim.enforced = true)
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M (withFds A) lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M (withFds A) lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec (withFds A) lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec (withFds A) lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec (withFds A) lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M (withFds A) lim))) :
    subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (blkPl_297).base
      (withFdsGe3Closed (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim))) :=
  subroutine_ok_polyEncoderMerge_withFdsGe3Closed_of_withFds henf
    (polyEncoderMerge_cro_placed_ok_of_contracts
      hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall)

end LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
