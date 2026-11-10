/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.Hoare.MultiCodeROHook
public import VerifiedLibraries.Mallocng.Spec
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalE2E.HooksMallocng
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.Fine.RustEntriesFine
public import LibsignalBinary.Heap.Fine.AllocZeroedFine
public import LibsignalBinary.Proofs.Placed.StringCloneMallocngPlaced
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetHelpers
public import LibsignalBinary.Heap.IfaceBudgetBase
import LibsignalBinary.Heap.IfaceBudgetBaseBridges
import ProofLib.Hoare.OutcomeSteps
import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.HooksE.Common

/-!
# Budget-threaded shared-pool (`mallocng`) crypto and `String::clone` hook discharge

Lifts the shared-pool cryptographic hooks (`aesEncHookMallocng`, `aesDecHookMallocng`,
`libcruxHmacHookMallocng`) and `<String as Clone>::clone` (`stringCloneHookMallocng` and
program-mode specializations) to their `*BudgetSpec` contracts in `SpecBudget.lean` over any
`(M, I)` satisfying `MallocngCostModelSound M I`, with specializations to `fineCostModel`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget

open Arm64 Arm64.CType ProofLib.SepLogic
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open ProofLib.ProgramReflection (WordTree)
open ProofLib.StdStartup (hasInstrs)
open CryptoGames.CBC (AesKey Block blockToBytesLE bytesToBlock cbcDecRaw cbcDecryptBlocks chunks16
  pkcs7Unpad)
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcDecrypt aesCbcEncrypt)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open CryptoVerification.LibsignalTripleRatchet (AesCall extHookStack)
open CryptoVerification.LibsignalSpqrV1 (LibcruxHmacCall length_hmacWith)
open CryptoVerification.E2E (
  aesDecFrameBytes aesDecHookMallocng aesDecOut
  aesEncFrameBytes aesEncHookMallocng aesEncOut
  cloneSrc
  libcruxHmacFrameBytes libcruxHmacHookMallocng
  stepRustAlloc1 writeVecHeader
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits
  FitsEvents
  MallocngCostModelIface MallocngCostModelSound
  NullAllowed OomPreserved RustAllocAddrs RustCliAllocBudget
  RustCliAllocBudgetEntriesBase RustLayoutOk
  mallocngBudgetPool mallocngRustCliAllocBudget
  rustAllocEvents rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase rustCliReallocBudgetSpecBase
  rustDeallocEvents rustReallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  RustStdAllocAuxEntries StringCloneEnv allocMemcpyVmSpec checkBranchStub2
  stringCloneBudgetSpec stringCloneEnv_events stringCloneEvents
)
open LibsignalBinary.Heap.SpecBudget (
  AesDecEnv AesEncEnv LibcruxHmacEnv
  aesCallPreBudget aesDecBudgetSpec aesDecFnBudgetSpec aesDecWeakBudgetSpec
  aesEncBudgetSpec aesEncFnBudgetSpec
  libcruxHmacBudgetSpec libcruxHmacSha256Events
  rustAllocZeroedBudgetSpecBase
)
open LibsignalBinary.Heap.Fine (
  allocMemsetVmSpec
  fineCostModel fineCostModelIface fineCostModelSound
  fineRdlAllocZeroed_budget_placed_ok
  fineRustCliAllocBudget fineRustCliAllocBudgetEntries fineRustCliAllocBudgetEntries_thunks
  fineRustCliAllocZeroedBudget_thunk_ok rdlAllocZeroedInstrs
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  CodeBlocksPermRX CodeBlocksPermRXMem
  allocCallPreserved_refl cc_retHook_setMem_sameRegs codeBlocksPermRX_of_keepsFrozen
  fineHookBudgetPool_of_init fineHookRustCliAllocBudget
  mallocngHookBudgetPool mallocngHookBudgetPool_of_codeLoaded mallocngHookBudgetPool_of_init
  mallocngHookBudgetPool_transport mallocngHookRustCliAllocBudget
  vmPreserved_retHook_setMem
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetHelpers (
  aes_post_calloc_inputs fitsEvent_of_fitsAlloc1 pointsTo_replicate_to_memRegion
  rustAllocEvents_one stepRustAlloc1_budget_cps stepRustDealloc1_budget_cps
  write_aesErr_at_ret write_empty_vecU8 write_vecU8_from_alloc
)
open LibsignalBinary.Proofs.Placed.StringCloneMallocngPlaced (
  lsStringCloneBudget_alias2_ok lsStringCloneBudget_alias2_wordTree_ok
  lsStringCloneBudget_alias_ok lsStringCloneBudget_alias_wordTree_ok
  rustStringCloneBudget_of_hasInstrs_ok rustStringCloneBudget_of_wordTree_ok
  rustStringCloneInstrs
)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMallocng)
open VerifiedLibraries.RustStd (
  RustStdRdlShimCode RustStdThunkCode checkShimInstrsAt mallocngPlacedCAddrs
)

export LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  mallocngHookBudgetPool mallocngHookRustCliAllocBudget fineHookRustCliAllocBudget
  mallocngHookBudgetPool_of_init fineHookBudgetPool_of_init
)

/-! ## Pool-lift bridges (`mallocngRustCliAllocBudget` → `mallocngHookRustCliAllocBudget`) -/

/-- Lift any compiled `rustCliAllocBudgetSpec` witness (for `__rust_alloc` when `zeroed = false` or
    `__rust_alloc_zeroed` when `zeroed = true`) from `mallocngRustCliAllocBudget` to the shared
    hook+program pool `mallocngHookRustCliAllocBudget`. -/
theorem mallocngHookAllocBudget_of_raw {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName}
    {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64} {lim : BudgetLimits} {zeroed : Bool}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry
      (rustCliAllocBudgetSpecBase M (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart) lim zeroed)) :
    subroutine_ok P entry
      (rustCliAllocBudgetSpecBase M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim zeroed) := by
  let A₀ := mallocngRustCliAllocBudget M I hS γ mpl tp brkStart
  let A := mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart
  apply subroutine_ok.of_codeLoaded
  rintro ⟨size, align, st⟩ R s0 hpc hrun hpre hsp _
  have hpre1 : s0.mem ⊨
      ⌜lim.enforced = true → CodeBlocksPermRX mpl s0⌝ ∗
        ((⌜(s0.readReg64 .x0).toNat = size ∧ (s0.readReg64 .x1).toNat = align ∧
            RustLayoutOk size align⌝ ∗
          A₀.pool lim st s0 ∗ stackAt s0.sp allocHookStack) ∗
          (VerifiedLibraries.mallocngLib.codeRO mpl ∗ R)) := by
    dsimp only [rustCliAllocBudgetSpecBase, A, A₀, mallocngHookRustCliAllocBudget,
      mallocngRustCliAllocBudget, mallocngHookBudgetPool] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  obtain ⟨hrx0, hpre₀⟩ := hpre1
  refine (h.to_outcome (size, align, st) (VerifiedLibraries.mallocngLib.codeRO mpl ∗ R)
    s0 hpc hrun hpre₀ hsp).mono_outcome_steps fun sf hsteps hout => ?_
  have hrxf : lim.enforced = true → CodeBlocksPermRX mpl sf :=
    fun henf => codeBlocksPermRX_of_keepsFrozen (hrx0 henf) hsteps.keepsFrozen
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hpool_eq (st' : M.σ) (u : State) :
        A.pool lim st' u = VerifiedLibraries.mallocngLib.codeRO mpl ∗ A₀.pool lim st' u ∗
          ⌜lim.enforced = true → CodeBlocksPermRX mpl u⌝ := rfl
    have hlive_eq : A.live = A₀.live := rfl
    dsimp only [rustCliAllocBudgetSpecBase] at hpost ⊢
    rw [hpool_eq, hlive_eq]
    exact Satisfies.mono
      (Entails.trans (Entails.pure_right hrxf (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl)))
      hpost
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
    dsimp only [rustCliAllocBudgetSpecBase] at hoom ⊢
    exact Satisfies.of_sep_right (P := VerifiedLibraries.mallocngLib.codeRO mpl)
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hoom)

/-- Lift any compiled `rustCliDeallocBudgetSpec` witness from `mallocngRustCliAllocBudget` to
    `mallocngHookRustCliAllocBudget`. -/
theorem mallocngHookDeallocBudget_of_raw {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName}
    {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry
      (rustCliDeallocBudgetSpecBase M (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart) lim)) :
    subroutine_ok P entry
      (rustCliDeallocBudgetSpecBase M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim) := by
  let A₀ := mallocngRustCliAllocBudget M I hS γ mpl tp brkStart
  let A := mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart
  apply subroutine_ok.of_codeLoaded
  rintro ⟨p, size, align, st⟩ R s0 hpc hrun hpre hsp _
  have hpre1 : s0.mem ⊨
      ⌜lim.enforced = true → CodeBlocksPermRX mpl s0⌝ ∗
        ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = size ∧
            (s0.readReg64 .x2).toNat = align⌝ ∗
          A₀.pool lim st s0 ∗ A₀.live p size align ∗ memRegion p size ∗
          stackAt s0.sp allocHookStack) ∗
          (VerifiedLibraries.mallocngLib.codeRO mpl ∗ R)) := by
    dsimp only [rustCliDeallocBudgetSpecBase, A, A₀, mallocngHookRustCliAllocBudget,
      mallocngRustCliAllocBudget, mallocngHookBudgetPool] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  obtain ⟨hrx0, hpre₀⟩ := hpre1
  refine (h.to_outcome (p, size, align, st) (VerifiedLibraries.mallocngLib.codeRO mpl ∗ R)
    s0 hpc hrun hpre₀ hsp).mono_outcome_steps fun sf hsteps hout => ?_
  have hrxf : lim.enforced = true → CodeBlocksPermRX mpl sf :=
    fun henf => codeBlocksPermRX_of_keepsFrozen (hrx0 henf) hsteps.keepsFrozen
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustCliDeallocBudgetSpecBase, A, A₀, mallocngHookRustCliAllocBudget,
      mallocngRustCliAllocBudget, mallocngHookBudgetPool] at hpost ⊢
    exact Satisfies.mono
      (Entails.trans (Entails.pure_right hrxf (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl)))
      hpost
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- Lift any compiled `rustCliReallocBudgetSpec` witness from `mallocngRustCliAllocBudget` to
    `mallocngHookRustCliAllocBudget`. -/
theorem mallocngHookReallocBudget_of_raw {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName}
    {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry
      (rustCliReallocBudgetSpecBase M (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart) lim)) :
    subroutine_ok P entry
      (rustCliReallocBudgetSpecBase M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim) := by
  let A₀ := mallocngRustCliAllocBudget M I hS γ mpl tp brkStart
  let A := mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart
  apply subroutine_ok.of_codeLoaded
  rintro ⟨p, old, align, new, bs, st⟩ R s0 hpc hrun hpre hsp _
  have hpre1 : s0.mem ⊨
      ⌜lim.enforced = true → CodeBlocksPermRX mpl s0⌝ ∗
        ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
            (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
            RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new⌝ ∗
          A₀.pool lim st s0 ∗ A₀.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
          stackAt s0.sp allocHookStack) ∗
          (VerifiedLibraries.mallocngLib.codeRO mpl ∗ R)) := by
    dsimp only [rustCliReallocBudgetSpecBase, A, A₀, mallocngHookRustCliAllocBudget,
      mallocngRustCliAllocBudget, mallocngHookBudgetPool] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  obtain ⟨hrx0, hpre₀⟩ := hpre1
  refine (h.to_outcome (p, old, align, new, bs, st) (VerifiedLibraries.mallocngLib.codeRO mpl ∗ R)
    s0 hpc hrun hpre₀ hsp).mono_outcome_steps fun sf hsteps hout => ?_
  have hrxf : lim.enforced = true → CodeBlocksPermRX mpl sf :=
    fun henf => codeBlocksPermRX_of_keepsFrozen (hrx0 henf) hsteps.keepsFrozen
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hpool_eq (st' : M.σ) (u : State) :
        A.pool lim st' u = VerifiedLibraries.mallocngLib.codeRO mpl ∗ A₀.pool lim st' u ∗
          ⌜lim.enforced = true → CodeBlocksPermRX mpl u⌝ := rfl
    have hlive_eq : A.live = A₀.live := rfl
    dsimp only [rustCliReallocBudgetSpecBase] at hpost ⊢
    rw [hpool_eq, hlive_eq]
    exact Satisfies.mono
      (Entails.trans (Entails.pure_right hrxf (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl)))
      hpost
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
    dsimp only [rustCliReallocBudgetSpecBase] at hoom ⊢
    exact Satisfies.of_sep_right (P := VerifiedLibraries.mallocngLib.codeRO mpl)
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hoom)

/-- Lift a `RustCliAllocBudgetEntries` bundle from `mallocngRustCliAllocBudget` to
    `mallocngHookRustCliAllocBudget`. -/
theorem mallocngHookRustCliAllocBudgetEntries_of_raw
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName}
    {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {P : Program} {addrs : RustAllocAddrs}
    (h : RustCliAllocBudgetEntriesBase M
      (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart) P addrs) :
    RustCliAllocBudgetEntriesBase M
      (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) P addrs where
  alloc lim := mallocngHookAllocBudget_of_raw hS (h.alloc lim)
  dealloc lim := mallocngHookDeallocBudget_of_raw hS (h.dealloc lim)
  realloc lim := mallocngHookReallocBudget_of_raw hS (h.realloc lim)

/-- `fineCostModel` `RustCliAllocBudgetEntries` at direct `__rdl_*` shims over `fineHookRustCliAllocBudget`. -/
theorem fineHookRustCliAllocBudgetEntries
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) P rdlAddrs :=
  mallocngHookRustCliAllocBudgetEntries_of_raw fineCostModelSound
    (fineRustCliAllocBudgetEntries hP γ tp brkStart hShims hMemcpy)

/-- `fineCostModel` `RustCliAllocBudgetEntries` at 1-instruction `B`-thunks `__rustc::__rust_{alloc,dealloc,realloc}`. -/
theorem fineHookRustCliAllocBudgetEntries_thunks
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) P thunkAddrs :=
  mallocngHookRustCliAllocBudgetEntries_of_raw fineCostModelSound
    (fineRustCliAllocBudgetEntries_thunks hP γ tp brkStart hThunks hShims hMemcpy)

/-- `fineCostModel` `rustAllocZeroedBudgetSpec` at `__rdl_alloc_zeroed` over `fineHookRustCliAllocBudget`. -/
theorem fineHookRdlAllocZeroed_budget_placed_ok
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart allocZeroedAddr memsetAddr : BitVec 64)
    (lim : BudgetLimits)
    (hCode : hasInstrs P allocZeroedAddr
      (rdlAllocZeroedInstrs allocZeroedAddr (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc")
        (mallocngPlacedCAddrs mpl).posixMemalign memsetAddr))
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec) :
    subroutine_ok P allocZeroedAddr
      (rustAllocZeroedBudgetSpecBase fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  mallocngHookAllocBudget_of_raw fineCostModelSound
    (fineRdlAllocZeroed_budget_placed_ok hP γ tp brkStart allocZeroedAddr memsetAddr lim
      hCode hMemset)

/-- `fineCostModel` `rustAllocZeroedBudgetSpec` at `__rustc::__rust_alloc_zeroed` over `fineHookRustCliAllocBudget`. -/
theorem fineHookRustCliAllocZeroedBudget_thunk_ok
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart thunkAddr rdlAddr memsetAddr : BitVec 64)
    (lim : BudgetLimits)
    (hThunk : hasInstrs P thunkAddr [ .b (rdlAddr - thunkAddr) ])
    (hCode : hasInstrs P rdlAddr
      (rdlAllocZeroedInstrs rdlAddr (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc")
        (mallocngPlacedCAddrs mpl).posixMemalign memsetAddr))
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec) :
    subroutine_ok P thunkAddr
      (rustAllocZeroedBudgetSpecBase fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  mallocngHookAllocBudget_of_raw fineCostModelSound
    (fineRustCliAllocZeroedBudget_thunk_ok hP γ tp brkStart thunkAddr rdlAddr memsetAddr lim
      hThunk hCode hMemset)

/-! ## AES-256-CBC encrypt and decrypt (`aesEncHookMallocng`, `aesDecHookMallocng`) -/

private theorem cbcDecryptBlocks_length (g : Block → Block) :
    ∀ (prev : Block) (cs : List Block), (cbcDecryptBlocks g prev cs).length = cs.length
  | _, [] => rfl
  | prev, c :: cs => by simp [cbcDecryptBlocks, cbcDecryptBlocks_length g c cs]

private theorem flatMap_blockToBytesLE_length :
    ∀ (bs : List Block), (bs.flatMap blockToBytesLE).length = 16 * bs.length
  | [] => rfl
  | b :: bs => by
    have hb : (blockToBytesLE b).length = 16 := by simp [blockToBytesLE]
    simp only [List.flatMap_cons, List.length_append, hb, flatMap_blockToBytesLE_length bs,
      List.length_cons]
    omega

private theorem pkcs7Unpad_length_le {bs pt : List (BitVec 8)}
    (h : pkcs7Unpad bs = some pt) : pt.length ≤ bs.length := by
  unfold pkcs7Unpad at h
  cases hlast : bs.getLast? with
  | none => simp [hlast] at h
  | some last =>
    simp only [hlast] at h
    split at h
    · cases h
    · split at h
      · injection h with hpt; subst hpt; simp
      · cases h

/-- `aesEncHookMallocng mpl E` satisfies `aesEncBudgetSpec` over any `(M, I)` with `MallocngCostModelSound M I`. -/
theorem aesEncHookMallocng_budget_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (E : AesKey → Block → Block) :
    HookOk (aesEncHookMallocng mpl E)
      (aesEncBudgetSpec E M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim) := by
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  have hpre' := hpre
  dsimp only [aesEncBudgetSpec, aesCallPreBudget, mallocngHookRustCliAllocBudget] at hpre'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hkey_len, hiv_len, hin_lt, hFitEnv⟩, hmem⟩
  unfold aesEncHookMallocng
  have hguard : (s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64) = false := by
    rw [hx3, hx5]; rfl
  simp only [hguard, Bool.false_eq_true, ↓reduceIte, hx1]
  let ctLen := (x.input.length / 16 + 1) * 16
  simp only [show ¬(2 ^ 63 ≤ (x.input.length / 16 + 1) * 16) by omega, ↓reduceIte]
  have hpos : 1 ≤ ctLen := by dsimp [ctLen]; omega
  have hFit : LibsignalBinary.Heap.FitsEvent M lim st (.alloc ctLen) :=
    fitsEvent_of_fitsAlloc1 hpos (hFitEnv (rustAllocEvents ctLen 1) rfl)
  have hmem0 : s0.mem ⊨
      (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗ stackAt s0.sp extHookStack ∗
        (x.frame ∗ memRegion x.ret 24)) ∗ R := by
    unfold AesCall.frame; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine stepRustAlloc1_budget_cps hS hPl true aesEncFrameBytes ctLen
    (by decide) (by decide) hFit hrun rfl rfl rfl hsp
    (Memory.KeepsFrozen.refl _) rfl (allocCallPreserved_refl s0) hmem0 _ ?_
  intro s1 p hp_ne hp_al16 hp_fit64 hs1_run hs1_sp hs1_regs hs1_vregs hkf1 hsym1 hpres1 hmem1
  simp only [↓reduceIte] at hmem1
  obtain ⟨hs1_x8, h_in, h_k, h_iv⟩ := aes_post_calloc_inputs hx0 hx1 hx2 hx4 hx8 hkey_len hiv_len
    hs1_regs (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1)
  let ct := aesCbcEncrypt E (bytesToKey32 x.key) (bytesToBlock x.iv) x.input
  have hout_eq : aesEncOut E s1 = ct := by unfold aesEncOut; rw [h_in, h_k, h_iv]
  have hct_len : ct.length = ctLen := by
    dsimp [ct, ctLen]; unfold aesCbcEncrypt
    rw [flatMap_blockToBytesLE_length, List.Vector.toList_length]
    change 16 * (x.input.length / 16 + 1) = (x.input.length / 16 + 1) * 16; omega
  rw [hout_eq]
  have hm_prep : s1.mem ⊨
      I.BlockM γ p ctLen 16 ∗ memRegion p ctLen ∗ memRegion x.ret 24 ∗
        (x.frame ∗ mallocngHookBudgetPool M I γ mpl tp brkStart lim
          (M.step (.alloc ctLen) st) s1 ∗ stackAt s0.sp extHookStack ∗ R) :=
    Satisfies.mono (Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (pointsTo_replicate_to_memRegion p ctLen))))))
      (Entails.of_eq (by sep_ac_rfl))) hmem1
  obtain ⟨hkf_w, hperm_w, hvec⟩ := write_vecU8_from_alloc hS (mpl := mpl) (tp := tp) (brkStart := brkStart)
    (bs := ct) hp_ne hp_al16 hp_fit64 (by dsimp [ctLen]; omega) (by dsimp [ctLen]; omega) (by omega) hm_prep
  let mf := writeVecHeader (s1.mem.writeBytes p ct) x.ret
    (BitVec.ofNat 64 ctLen) p (BitVec.ofNat 64 ct.length)
  rw [show retHook (fun s => s.setMem (writeVecHeader (s.mem.writeBytes p ct) (s.readReg64 .x8)
      (BitVec.ofNat 64 ct.length) p (BitVec.ofNat 64 ct.length))) s1 =
      retHook (fun s => s.setMem mf) s1 by simp [retHook, hs1_x8, mf, hct_len]]
  obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf hs1_regs hs1_vregs hs1_sp hs1_run
  refine ⟨hkf1.trans hkf_w, hsym1, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
  dsimp only [aesEncBudgetSpec]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨rustAllocEvents ctLen 1, ?_⟩
  have hev_step : M.stepEvents (rustAllocEvents ctLen 1) st = M.step (.alloc ctLen) st := by
    rw [rustAllocEvents_one hpos]; rfl
  have htr_f : (retHook (fun s => s.setMem mf) s1).trace = s0.trace := hpres1.2.1
  have hpool_f :
      (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim
        (M.stepEvents (rustAllocEvents ctLen 1) st) (retHook (fun s => s.setMem mf) s1) =
        mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc ctLen) st) s1 := by
    rw [hev_step]
    exact mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim _
      (vmPreserved_retHook_setMem hperm_w)
  rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
  dsimp only [ct] at hvec
  exact ⟨⟨htr_f, rfl⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hvec⟩

theorem aesEncFnHookMallocng_budget_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (E : AesKey → Block → Block) :
    HookOk (aesEncHookMallocng mpl E)
      (aesEncFnBudgetSpec (fun pt k iv => aesCbcEncrypt E (bytesToKey32 k) (bytesToBlock iv) pt)
        M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim) :=
  aesEncHookMallocng_budget_ok hS γ tp brkStart lim hPl E

theorem fineAesEnc_budget_hookOk (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (E : AesKey → Block → Block) :
    HookOk (aesEncHookMallocng mpl E)
      (aesEncBudgetSpec E fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  aesEncHookMallocng_budget_ok fineCostModelSound γ tp brkStart lim hPl E

theorem fineAesEnc_budget_hookSat {abs : String → Option (State → State)} {name : String}
    (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (E : AesKey → Block → Block)
    (hH : abs name = some (aesEncHookMallocng mpl E)) :
    HookSat abs name
      (aesEncBudgetSpec E fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  ⟨aesEncHookMallocng mpl E, hH, fineAesEnc_budget_hookOk γ tp brkStart lim hPl E⟩

/-- `aesDecHookMallocng mpl D` satisfies `aesDecBudgetSpec` over any `(M, I)` with `MallocngCostModelSound M I`. -/
theorem aesDecHookMallocng_budget_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block) :
    HookOk (aesDecHookMallocng mpl D)
      (aesDecBudgetSpec D M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim) := by
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  have hpre' := hpre
  dsimp only [aesDecBudgetSpec, aesCallPreBudget, mallocngHookRustCliAllocBudget] at hpre'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hkey_len, hiv_len, hin_lt, hFitEnv⟩, hmem⟩
  unfold aesDecHookMallocng
  have hguard : (s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64) = false := by
    rw [hx3, hx5]; rfl
  simp only [hguard, Bool.false_eq_true, ↓reduceIte, hx1]
  by_cases hbad : (x.input.length == 0 || x.input.length % 16 != 0) = true
  · simp only [hbad, ↓reduceIte]
    have hbad_prop : x.input.length = 0 ∨ x.input.length % 16 ≠ 0 := by
      rcases Bool.or_eq_true_iff.mp hbad with h0 | hm
      · exact Or.inl (beq_iff_eq.mp h0)
      · exact Or.inr (bne_iff_ne.mp hm)
    have hdec_none : aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input = none := by
      unfold aesCbcDecrypt cbcDecRaw
      have hcond : x.input = [] ∨ x.input.length % 16 ≠ 0 :=
        hbad_prop.elim (fun h0 => Or.inl (List.eq_nil_of_length_eq_zero h0)) Or.inr
      simp [hcond]
    have hmem_ret : s0.mem ⊨ memRegion x.ret 24 ∗
        (x.frame ∗ mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
          stackAt s0.sp extHookStack ∗ R) := by
      unfold AesCall.frame; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    obtain ⟨hkf_e, hperm_e, herr⟩ := write_aesErr_at_ret hmem_ret
    let mf := (s0.mem.write64 x.ret errTag).write64 (x.ret + 8#64) 1#64
    rw [show retHook (fun s => let r := s.readReg64 .x8; s.setMem ((s.mem.write64 r errTag).write64 (r + 8#64) 1#64)) s0 =
        retHook (fun s => s.setMem mf) s0 by simp [retHook, hx8, mf]]
    obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf rfl rfl rfl hrun
    refine ⟨hkf_e, rfl, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
    dsimp only [aesDecBudgetSpec]
    rw [hdec_none]; dsimp only
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨[], ?_⟩
    have hEnvNil : AesDecEnv x [] := by
      unfold AesDecEnv; split
      · rfl
      · next h => exact False.elim (h hbad_prop)
    have hpool_f :
        (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim
          (M.stepEvents [] st) (retHook (fun s => s.setMem mf) s0) =
          mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 :=
      mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st
        (vmPreserved_retHook_setMem hperm_e)
    rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, hEnvNil⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) herr⟩
  · simp only [Bool.eq_false_iff.mpr hbad, Bool.false_eq_true, ↓reduceIte]
    have hnot_bad : ¬(x.input.length = 0 ∨ x.input.length % 16 ≠ 0) := by
      rintro (h0 | hm)
      · exact hbad (Bool.or_eq_true_iff.mpr (Or.inl (beq_iff_eq.mpr h0)))
      · exact hbad (Bool.or_eq_true_iff.mpr (Or.inr (bne_iff_ne.mpr hm)))
    have hpos : 1 ≤ x.input.length := by omega
    have hEnvOk : AesDecEnv x (rustAllocEvents x.input.length 1) := by
      unfold AesDecEnv; split
      · next h => exact False.elim (hnot_bad h)
      · exact Or.inl rfl
    have hFit : LibsignalBinary.Heap.FitsEvent M lim st (.alloc x.input.length) :=
      fitsEvent_of_fitsAlloc1 hpos (hFitEnv _ hEnvOk)
    have hmem0 : s0.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗ stackAt s0.sp extHookStack ∗
          (x.frame ∗ memRegion x.ret 24)) ∗ R := by
      unfold AesCall.frame; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    refine stepRustAlloc1_budget_cps hS hPl true aesDecFrameBytes x.input.length
      (by decide) (by decide) hFit hrun rfl rfl rfl hsp
      (Memory.KeepsFrozen.refl _) rfl (allocCallPreserved_refl s0) hmem0 _ ?_
    intro s1 p hp_ne hp_al16 hp_fit64 hs1_run hs1_sp hs1_regs hs1_vregs hkf1 hsym1 hpres1 hmem1
    simp only [↓reduceIte] at hmem1
    obtain ⟨hs1_x8, h_in, h_k, h_iv⟩ := aes_post_calloc_inputs hx0 hx1 hx2 hx4 hx8 hkey_len hiv_len
      hs1_regs (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1)
    have hout_eq : aesDecOut D s1 = aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input := by
      unfold aesDecOut; rw [h_in, h_k, h_iv]
    rw [hout_eq]
    rcases hdec : aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with _ | pt
    · dsimp only
      have hm_free : s1.mem ⊨
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim
              (M.step (.alloc x.input.length) st) s1 ∗
            stackAt s0.sp extHookStack ∗
            I.BlockM γ p x.input.length 16 ∗ memRegion p x.input.length ∗
            (x.frame ∗ memRegion x.ret 24)) ∗ R :=
        Satisfies.mono (Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (pointsTo_replicate_to_memRegion p x.input.length))))))
          (Entails.of_eq (by sep_ac_rfl))) hmem1
      refine stepRustDealloc1_budget_cps hS hPl aesDecFrameBytes x.input.length p
        hp_ne hp_al16 hp_fit64 (by decide) (by decide)
        hs1_run hs1_sp hs1_regs hs1_vregs hsp hkf1 hsym1 hpres1 hm_free _ ?_
      intro s2 hs2_run hs2_sp hs2_regs hs2_vregs hkf2 hsym2 hpres2 hmem2
      have hs2_x8 : s2.readReg64 .x8 = x.ret := by simp [State.readReg64, hs2_regs] at hx8 ⊢; exact hx8
      obtain ⟨hkf_e, hperm_e, herr⟩ := write_aesErr_at_ret
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem2 : s2.mem ⊨ memRegion x.ret 24 ∗
          (x.frame ∗ mallocngHookBudgetPool M I γ mpl tp brkStart lim
            (M.step (.free 1 x.input.length) (M.step (.alloc x.input.length) st)) s2 ∗
            stackAt s0.sp extHookStack ∗ R))
      let mf := (s2.mem.write64 x.ret errTag).write64 (x.ret + 8#64) 1#64
      rw [show retHook (fun s => let r := s.readReg64 .x8; s.setMem ((s.mem.write64 r errTag).write64 (r + 8#64) 1#64)) s2 =
          retHook (fun s => s.setMem mf) s2 by simp [retHook, hs2_x8, mf]]
      obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf hs2_regs hs2_vregs hs2_sp hs2_run
      refine ⟨hkf2.trans hkf_e, hsym2, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
      dsimp only [aesDecBudgetSpec]
      rw [hdec]; dsimp only
      rw [sepExists_sepConj_left, satisfies_sepExists]
      let evsErr := rustAllocEvents x.input.length 1 ++ rustDeallocEvents x.input.length 1
      refine ⟨evsErr, ?_⟩
      have hEnvErr : AesDecEnv x evsErr := by
        unfold AesDecEnv; split
        · next h => exact False.elim (hnot_bad h)
        · exact Or.inr rfl
      have hev_step : M.stepEvents evsErr st =
          M.step (.free 1 x.input.length) (M.step (.alloc x.input.length) st) := by
        dsimp [evsErr]; rw [rustAllocEvents_one hpos]; rfl
      have hpool_f :
          (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim
            (M.stepEvents evsErr st) (retHook (fun s => s.setMem mf) s2) =
            mallocngHookBudgetPool M I γ mpl tp brkStart lim
              (M.step (.free 1 x.input.length) (M.step (.alloc x.input.length) st)) s2 := by
        rw [hev_step]
        exact mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim _
          (vmPreserved_retHook_setMem hperm_e)
      rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpres2.2.1, hEnvErr⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) herr⟩
    · dsimp only
      have hpt_le : pt.length ≤ x.input.length := by
        have hdec' := hdec; unfold aesCbcDecrypt cbcDecRaw at hdec'
        split at hdec'
        · simp at hdec'
        · have hle := pkcs7Unpad_length_le hdec'
          rw [flatMap_blockToBytesLE_length, cbcDecryptBlocks_length, chunks16, List.length_ofFn] at hle
          omega
      have hm_prep : s1.mem ⊨
          I.BlockM γ p x.input.length 16 ∗ memRegion p x.input.length ∗ memRegion x.ret 24 ∗
            (x.frame ∗ mallocngHookBudgetPool M I γ mpl tp brkStart lim
              (M.step (.alloc x.input.length) st) s1 ∗ stackAt s0.sp extHookStack ∗ R) :=
        Satisfies.mono (Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (pointsTo_replicate_to_memRegion p x.input.length))))))
          (Entails.of_eq (by sep_ac_rfl))) hmem1
      obtain ⟨hkf_w, hperm_w, hvec⟩ := write_vecU8_from_alloc hS (mpl := mpl) (tp := tp) (brkStart := brkStart)
        (bs := pt) hp_ne hp_al16 hp_fit64 hpos (by omega) hpt_le hm_prep
      let mf := writeVecHeader (s1.mem.writeBytes p pt) x.ret
        (BitVec.ofNat 64 x.input.length) p (BitVec.ofNat 64 pt.length)
      rw [show retHook (fun s => let r := s.readReg64 .x8; s.setMem (writeVecHeader (s.mem.writeBytes p pt) r
          (BitVec.ofNat 64 x.input.length) p (BitVec.ofNat 64 pt.length))) s1 =
          retHook (fun s => s.setMem mf) s1 by simp [retHook, hs1_x8, mf]]
      obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf hs1_regs hs1_vregs hs1_sp hs1_run
      refine ⟨hkf1.trans hkf_w, hsym1, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
      dsimp only [aesDecBudgetSpec]
      rw [hdec]; dsimp only
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨rustAllocEvents x.input.length 1, ?_⟩
      have hev_step : M.stepEvents (rustAllocEvents x.input.length 1) st =
          M.step (.alloc x.input.length) st := by
        rw [rustAllocEvents_one hpos]; rfl
      have hpool_f :
          (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim
            (M.stepEvents (rustAllocEvents x.input.length 1) st)
            (retHook (fun s => s.setMem mf) s1) =
            mallocngHookBudgetPool M I γ mpl tp brkStart lim
              (M.step (.alloc x.input.length) st) s1 := by
        rw [hev_step]
        exact mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim _
          (vmPreserved_retHook_setMem hperm_w)
      rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpres1.2.1, hEnvOk⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hvec⟩

private theorem aesErr_entails_weak (ret : BitVec 64) :
    (ret ↦₆₄ errTag) ∗
      (∃∗ p : BitVec 64, ⌜p ≠ 0⌝ ∗ ((ret + 8#64) ↦₆₄ p)) ∗ memRegion (ret + 16#64) 8 ⊢
      (ret ↦₆₄ errTag) ∗ memRegion (ret + 8#64) 16 := by
  have hp8 : (∃∗ p : BitVec 64, ⌜p ≠ 0⌝ ∗ ((ret + 8#64) ↦₆₄ p)) ⊢ memRegion (ret + 8#64) 8 := by
    rw [memRegion_eight (ret + 8#64)]
    refine Entails.sepExists_elim fun p => Entails.pure_left fun _ => ?_
    exact @Entails.sepExists_intro (BitVec 64) (fun q => (ret + 8#64) ↦₆₄ q) p
  have h16 : memRegion (ret + 8#64) 8 ∗ memRegion (ret + 16#64) 8 = memRegion (ret + 8#64) 16 :=
    (memRegion_split' (b := ret + 8#64) (n := 8) (k := 8) (b' := ret + 16#64)
      rfl (by bv_omega) (by decide)).symm
  rw [← h16]
  exact sepConj_mono_right (sepConj_mono_left hp8)

/-- `aesDecWeakBudgetSpec` corollary of `aesDecHookMallocng_budget_ok`. -/
theorem aesDecWeakHookMallocng_budget_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block) :
    HookOk (aesDecHookMallocng mpl D)
      (aesDecWeakBudgetSpec D M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim) := by
  refine HookOk.mono (aesDecHookMallocng_budget_ok hS γ tp brkStart lim hPl D)
    (fun _ _ _ h => h) ?_ (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
  rintro ⟨x, st⟩ R s0 sf _ hpost
  dsimp only [aesDecBudgetSpec, aesDecWeakBudgetSpec, aesDecFnBudgetSpec] at hpost ⊢
  refine Satisfies.mono (sepConj_mono_left (Entails.sepExists_elim fun evs => ?_)) hpost
  refine Entails.trans ?_
    (@Entails.sepExists_intro (List AllocEvent) _ evs)
  cases aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with
  | none =>
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (aesErr_entails_weak x.ret)))
  | some pt =>
    exact Entails.refl _

theorem fineAesDec_budget_hookOk (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block) :
    HookOk (aesDecHookMallocng mpl D)
      (aesDecBudgetSpec D fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  aesDecHookMallocng_budget_ok fineCostModelSound γ tp brkStart lim hPl D

theorem fineAesDecWeak_budget_hookOk (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block) :
    HookOk (aesDecHookMallocng mpl D)
      (aesDecWeakBudgetSpec D fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  aesDecWeakHookMallocng_budget_ok fineCostModelSound γ tp brkStart lim hPl D

theorem fineAesDec_budget_hookSat {abs : String → Option (State → State)} {name : String}
    (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block)
    (hH : abs name = some (aesDecHookMallocng mpl D)) :
    HookSat abs name
      (aesDecBudgetSpec D fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  ⟨aesDecHookMallocng mpl D, hH, fineAesDec_budget_hookOk γ tp brkStart lim hPl D⟩

theorem fineAesDecWeak_budget_hookSat {abs : String → Option (State → State)} {name : String}
    (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block)
    (hH : abs name = some (aesDecHookMallocng mpl D)) :
    HookSat abs name
      (aesDecWeakBudgetSpec D fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  ⟨aesDecHookMallocng mpl D, hH, fineAesDecWeak_budget_hookOk γ tp brkStart lim hPl D⟩

/-! ## `libcrux_hmac::hmac` (`libcruxHmacHookMallocng` → `libcruxHmacBudgetSpec`) -/

private theorem libcruxHmacSha256Events_eq :
    libcruxHmacSha256Events =
      [.alloc 64, .alloc 64, .alloc 64, .free 1 64, .free 1 64, .free 1 64, .alloc 32] := by
  unfold libcruxHmacSha256Events
  rw [rustAllocEvents_one (by decide : 1 ≤ 64), rustAllocEvents_one (by decide : 1 ≤ 32)]
  rfl

/-- `libcruxHmacHookMallocng mpl F` satisfies `libcruxHmacBudgetSpec` over any `(M, I)` with `MallocngCostModelSound M I`. -/
theorem libcruxHmacHookMallocng_budget_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (F : ShaState → List (BitVec 8) → ShaState) :
    HookOk (libcruxHmacHookMallocng mpl F)
      (libcruxHmacBudgetSpec F M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim) := by
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  have hpre' := hpre
  dsimp only [libcruxHmacBudgetSpec, mallocngHookRustCliAllocBudget] at hpre'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hFitEnv⟩, hmem⟩
  unfold libcruxHmacHookMallocng
  simp only [show ((s0.readReg64 .x0).setWidth 32 != 0#32) = false by rw [hx0]; rfl,
    Bool.false_eq_true, ↓reduceIte, hx2, hx4]
  by_cases hbig : (decide (2 ^ 32 ≤ x.key.length) || decide (2 ^ 32 ≤ x.data.length)) = true
  · simp only [hbig, ↓reduceIte]
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
    dsimp only [libcruxHmacBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    have hge : 2 ^ 32 ≤ x.key.length ∨ 2 ^ 32 ≤ x.data.length := by
      rcases Bool.or_eq_true_iff.mp hbig with hk | hd
      · exact Or.inl (of_decide_eq_true hk)
      · exact Or.inr (of_decide_eq_true hd)
    exact ⟨⟨hge, List.prefix_refl s0.trace⟩,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpre⟩
  · simp only [Bool.eq_false_iff.mpr hbig, Bool.false_eq_true, ↓reduceIte]
    have hkey_lt : x.key.length < 2 ^ 32 := by
      have : ¬(2 ^ 32 ≤ x.key.length) := fun h =>
        hbig (Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true h)))
      omega
    have hdata_lt : x.data.length < 2 ^ 32 := by
      have : ¬(2 ^ 32 ≤ x.data.length) := fun h =>
        hbig (Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true h)))
      omega
    have hEnv : LibcruxHmacEnv x libcruxHmacSha256Events := by
      unfold LibcruxHmacEnv; split
      · rfl
      · next h => exact False.elim (h ⟨hkey_lt, hdata_lt⟩)
    have hFitsAll : FitsEvents M lim st libcruxHmacSha256Events := hFitEnv _ hEnv
    rw [libcruxHmacSha256Events_eq] at hFitsAll
    rcases hFitsAll with ⟨hFit0, hFit1, hFit2, _hFit3, _hFit4, _hFit5, hFit6, -⟩
    have hmem0 : s0.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗ stackAt s0.sp extHookStack ∗
          ((x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24)) ∗ R :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    refine stepRustAlloc1_budget_cps hS hPl true libcruxHmacFrameBytes 64
      (by decide) (by decide) hFit0 hrun rfl rfl rfl hsp
      (Memory.KeepsFrozen.refl _) rfl (allocCallPreserved_refl s0) hmem0 _ ?_
    intro s1 pKey hpKey_ne hpKey_al16 hpKey_fit64 hs1_run hs1_sp hs1_regs hs1_vregs hkf1 hsym1 hpres1 hmem1
    simp only [↓reduceIte] at hmem1
    have hs1_x1 : s1.readReg64 .x1 = x.keyA := by simp [State.readReg64, hs1_regs] at hx1 ⊢; exact hx1
    let st1 := M.step (.alloc 64) st
    have hread_key : s1.mem.readBytes x.keyA x.key.length = x.key :=
      ((IsBlock.pointsToBytes x.keyA x.key).read (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1 :
        s1.mem ⊨ (x.keyA ↦ₛ x.key) ∗ ((x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24 ∗
          mallocngHookBudgetPool M I γ mpl tp brkStart lim st1 s1 ∗ stackAt s0.sp extHookStack ∗
          I.BlockM γ pKey 64 16 ∗ (pKey ↦ₛ List.replicate 64 0#8) ∗ R))).2
    rw [hs1_x1, hread_key]
    have hmem1' : s1.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim st1 s1 ∗ stackAt s0.sp extHookStack ∗
          (I.BlockM γ pKey 64 16 ∗ memRegion pKey 64 ∗
            (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24)) ∗ R :=
      Satisfies.mono (Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (pointsTo_replicate_to_memRegion pKey 64))))))
        (Entails.of_eq (by sep_ac_rfl))) hmem1
    refine stepRustAlloc1_budget_cps hS hPl false libcruxHmacFrameBytes 64
      (by decide) (by decide) hFit1 hs1_run hs1_sp hs1_regs hs1_vregs hsp
      hkf1 hsym1 hpres1 hmem1' _ ?_
    intro s2 pIpad hpIpad_ne hpIpad_al16 hpIpad_fit64 hs2_run hs2_sp hs2_regs hs2_vregs hkf2 hsym2 hpres2 hmem2
    simp only [Bool.false_eq_true, ↓reduceIte] at hmem2
    let st2 := M.step (.alloc 64) st1
    refine stepRustAlloc1_budget_cps hS hPl false libcruxHmacFrameBytes 64
      (by decide) (by decide) hFit2 hs2_run hs2_sp hs2_regs hs2_vregs hsp hkf2 hsym2 hpres2
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem2 : s2.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim st2 s2 ∗ stackAt s0.sp extHookStack ∗
          (I.BlockM γ pIpad 64 16 ∗ memRegion pIpad 64 ∗
            I.BlockM γ pKey 64 16 ∗ memRegion pKey 64 ∗
            (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24)) ∗ R) _ ?_
    intro s3 pOpad hpOpad_ne hpOpad_al16 hpOpad_fit64 hs3_run hs3_sp hs3_regs hs3_vregs hkf3 hsym3 hpres3 hmem3
    simp only [Bool.false_eq_true, ↓reduceIte] at hmem3
    let st3 := M.step (.alloc 64) st2
    have hs3_x3 : s3.readReg64 .x3 = x.dataA := by simp [State.readReg64, hs3_regs] at hx3 ⊢; exact hx3
    have hread_data : s3.mem.readBytes x.dataA x.data.length = x.data :=
      ((IsBlock.pointsToBytes x.dataA x.data).read (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem3 :
        s3.mem ⊨ (x.dataA ↦ₛ x.data) ∗ ((x.keyA ↦ₛ x.key) ∗ memRegion x.ret 24 ∗
          mallocngHookBudgetPool M I γ mpl tp brkStart lim st3 s3 ∗ stackAt s0.sp extHookStack ∗
          I.BlockM γ pOpad 64 16 ∗ memRegion pOpad 64 ∗
          I.BlockM γ pIpad 64 16 ∗ memRegion pIpad 64 ∗
          I.BlockM γ pKey 64 16 ∗ memRegion pKey 64 ∗ R))).2
    rw [hs3_x3, hread_data]
    refine stepRustDealloc1_budget_cps hS hPl libcruxHmacFrameBytes 64 pOpad
      hpOpad_ne hpOpad_al16 hpOpad_fit64 (by decide) (by decide)
      hs3_run hs3_sp hs3_regs hs3_vregs hsp hkf3 hsym3 hpres3 hmem3 _ ?_
    intro s4 hs4_run hs4_sp hs4_regs hs4_vregs hkf4 hsym4 hpres4 hmem4
    let st4 := M.step (.free 1 64) st3
    refine stepRustDealloc1_budget_cps hS hPl libcruxHmacFrameBytes 64 pIpad
      hpIpad_ne hpIpad_al16 hpIpad_fit64 (by decide) (by decide)
      hs4_run hs4_sp hs4_regs hs4_vregs hsp hkf4 hsym4 hpres4
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem4 : s4.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim st4 s4 ∗ stackAt s0.sp extHookStack ∗
          I.BlockM γ pIpad 64 16 ∗ memRegion pIpad 64 ∗
          (I.BlockM γ pKey 64 16 ∗ memRegion pKey 64 ∗
            (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24)) ∗ R) _ ?_
    intro s5 hs5_run hs5_sp hs5_regs hs5_vregs hkf5 hsym5 hpres5 hmem5
    let st5 := M.step (.free 1 64) st4
    refine stepRustDealloc1_budget_cps hS hPl libcruxHmacFrameBytes 64 pKey
      hpKey_ne hpKey_al16 hpKey_fit64 (by decide) (by decide)
      hs5_run hs5_sp hs5_regs hs5_vregs hsp hkf5 hsym5 hpres5
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem5 : s5.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim st5 s5 ∗ stackAt s0.sp extHookStack ∗
          I.BlockM γ pKey 64 16 ∗ memRegion pKey 64 ∗
          ((x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗ memRegion x.ret 24)) ∗ R) _ ?_
    intro s6 hs6_run hs6_sp hs6_regs hs6_vregs hkf6 hsym6 hpres6 hmem6
    let st6 := M.step (.free 1 64) st5
    refine stepRustAlloc1_budget_cps hS hPl false libcruxHmacFrameBytes 32
      (by decide) (by decide) hFit6 hs6_run hs6_sp hs6_regs hs6_vregs hsp
      hkf6 hsym6 hpres6 hmem6 _ ?_
    intro s7 pOut hpOut_ne hpOut_al16 hpOut_fit64 hs7_run hs7_sp hs7_regs hs7_vregs hkf7 hsym7 hpres7 hmem7
    simp only [Bool.false_eq_true, ↓reduceIte] at hmem7
    let st7 := M.step (.alloc 32) st6
    have hs7_x5 : (s7.readReg64 .x5).setWidth 32 = 1#32 := by
      simp [State.readReg64, hs7_regs] at hx5 ⊢; exact hx5
    have hs7_x6 : s7.readReg64 .x6 = 32#64 := by simp [State.readReg64, hs7_regs] at hx6 ⊢; exact hx6
    have hs7_x8 : s7.readReg64 .x8 = x.ret := by simp [State.readReg64, hs7_regs] at hx8 ⊢; exact hx8
    let tag := hmacWith F x.key x.data
    have htag_len : tag.length = 32 := length_hmacWith F x.key x.data
    obtain ⟨hkf_w, hperm_w, hvec⟩ := write_vecU8_from_alloc hS (mpl := mpl) (tp := tp) (brkStart := brkStart)
      (bs := tag) hpOut_ne hpOut_al16 hpOut_fit64 (by decide) (by decide) (by omega)
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem7 : s7.mem ⊨
        I.BlockM γ pOut 32 16 ∗ memRegion pOut 32 ∗ memRegion x.ret 24 ∗
          ((x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
            mallocngHookBudgetPool M I γ mpl tp brkStart lim st7 s7 ∗ stackAt s0.sp extHookStack ∗ R))
    rw [show BitVec.ofNat 64 tag.length = 32#64 by rw [htag_len]] at hkf_w hperm_w hvec
    rw [show (if (s7.readReg64 .x5).setWidth 32 &&& 1#32 != 0#32 then min (s7.readReg64 .x6).toNat 32 else 32) = 32
      by rw [hs7_x5, hs7_x6]; decide]
    let mf := writeVecHeader (s7.mem.writeBytes pOut tag) x.ret 32#64 pOut 32#64
    rw [show retHook (fun s => s.setMem (writeVecHeader (s.mem.writeBytes pOut tag)
        (s.readReg64 .x8) 32#64 pOut 32#64)) s7 =
        retHook (fun s => s.setMem mf) s7 by simp [retHook, hs7_x8, mf]]
    obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf hs7_regs hs7_vregs hs7_sp hs7_run
    refine ⟨hkf7.trans hkf_w, hsym7, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
    dsimp only [libcruxHmacBudgetSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨libcruxHmacSha256Events, ?_⟩
    have hstep_eq : M.stepEvents libcruxHmacSha256Events st = st7 := by
      rw [libcruxHmacSha256Events_eq]; rfl
    have hpool_f :
        (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim
          (M.stepEvents libcruxHmacSha256Events st) (retHook (fun s => s.setMem mf) s7) =
          mallocngHookBudgetPool M I γ mpl tp brkStart lim st7 s7 := by
      rw [hstep_eq]
      exact mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st7
        (vmPreserved_retHook_setMem hperm_w)
    rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
    dsimp only [tag] at hvec
    exact ⟨⟨hkey_lt, hdata_lt, hpres7.2.1, hEnv⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hvec⟩

theorem fineLibcruxHmac_budget_hookOk (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (F : ShaState → List (BitVec 8) → ShaState) :
    HookOk (libcruxHmacHookMallocng mpl F)
      (libcruxHmacBudgetSpec F fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  libcruxHmacHookMallocng_budget_ok fineCostModelSound γ tp brkStart lim hPl F

theorem fineLibcruxHmac_budget_hookSat {abs : String → Option (State → State)} {name : String}
    (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (F : ShaState → List (BitVec 8) → ShaState)
    (hH : abs name = some (libcruxHmacHookMallocng mpl F)) :
    HookSat abs name
      (libcruxHmacBudgetSpec F fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  ⟨libcruxHmacHookMallocng mpl F, hH, fineLibcruxHmac_budget_hookOk γ tp brkStart lim hPl F⟩

/-! ## `<String as Clone>::clone` (`stringCloneHookMallocng` and program-mode lifts) -/

/-- Measured stack frame of `<String as Clone>::clone` (`stp x29, x30, [sp, #-0x30]!`): `48` bytes. -/
abbrev stringCloneFrameBytes : Nat := 0x30

/-- Shared-pool (`mallocng`) hook model for `<String as Clone>::clone`:
    reads the source `String` bytes `cloneSrc s0` at `x0`; if empty, writes the canonical empty
    `Vec` header `{0, 1, 0}` at `x8` (`0` allocations); if non-empty (`n > 0`), allocates `n` bytes
    via `stepRustAlloc1 mpl false stringCloneFrameBytes n`, re-reads `cloneSrc s1`, copies the bytes
    into `p`, and writes header `{n, p, n}` at `x8`. -/
noncomputable def stringCloneHookMallocng (mpl : Obj.MultiPlacement) (s0 : State) : State :=
  let n := (cloneSrc s0).length
  if n == 0 then
    retHook (fun s => s.setMem (writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64)) s0
  else
    stepRustAlloc1 mpl false stringCloneFrameBytes n (fun s1 p =>
      let bs := cloneSrc s1
      retHook (fun s => s.setMem (writeVecHeader (s.mem.writeBytes p bs) (s.readReg64 .x8)
        (BitVec.ofNat 64 n) p (BitVec.ofNat 64 bs.length))) s1) s0

private theorem cloneSrc_of_vecGhostAt {A0 : RustAlloc} {s : State} {g : VecGhost}
    {p : BitVec 64} {Extra : SepProp}
    (hx0 : s.readReg64 .x0 = p)
    (hmem : s.mem ⊨ vecGhostAt A0 g p ∗ Extra) :
    cloneSrc s = g.bytes ∧ g.bytes.length < 2 ^ 63 := by
  have hm' : s.mem ⊨ ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (vecHeader p g.cap g.ptr (BitVec.ofNat 64 g.bytes.length) ∗
        (if g.cap = 0 then emp
         else A0.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
           memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗
        Extra) :=
    Satisfies.mono (Entails.of_eq (by unfold vecGhostAt vecU8At; sep_ac_rfl)) hmem
  rw [satisfies_pure_sepConj] at hm'
  rcases hm' with ⟨⟨hlen_le, hcap_lt, _⟩, hm⟩
  unfold vecHeader at hm
  have hlen_lt : g.bytes.length < 2 ^ 63 := by omega
  have hlen_nat : (BitVec.ofNat 64 g.bytes.length).toNat = g.bytes.length :=
    Nat.mod_eq_of_lt (by omega)
  have hm_ptr : s.mem ⊨ ((p + 8#64) ↦₆₄ g.ptr) ∗
      ((p ↦₆₄ g.cap) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
        (if g.cap = 0 then emp
         else A0.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
           memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗
        Extra) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  have hread_ptr : s.mem.read64 (p + 8#64) = g.ptr :=
    (IsBlock.pointsTo64 (p + 8#64) g.ptr).read hm_ptr
  have hm_len : s.mem ⊨ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      ((p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗
        (if g.cap = 0 then emp
         else A0.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
           memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗
        Extra) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  have hread_len : s.mem.read64 (p + 16#64) = BitVec.ofNat 64 g.bytes.length :=
    (IsBlock.pointsTo64 (p + 16#64) (BitVec.ofNat 64 g.bytes.length)).read hm_len
  refine ⟨?_, hlen_lt⟩
  unfold cloneSrc
  dsimp only
  rw [hx0, hread_ptr, hread_len, hlen_nat]
  by_cases hcap0 : g.cap = 0
  · have hcap0_nat : g.cap.toNat = 0 := by rw [hcap0]; rfl
    have hlen0 : g.bytes.length = 0 := by omega
    rw [List.eq_nil_of_length_eq_zero hlen0]
    rfl
  · simp only [hcap0, ↓reduceIte] at hm
    have hm_bs : s.mem ⊨ (g.ptr ↦ₛ g.bytes) ∗
        ((p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗
          ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
          A0.live g.ptr g.cap.toNat 1 ∗
          memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) ∗
          Extra) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    exact ((IsBlock.pointsToBytes g.ptr g.bytes).read hm_bs).2

/-- `stringCloneHookMallocng mpl` satisfies `stringCloneBudgetSpec` over any `(M, I)` with `MallocngCostModelSound M I`. -/
theorem stringCloneHookMallocng_budget_ok [LibsignalPlacement] {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) :
    HookOk (stringCloneHookMallocng mpl)
      (stringCloneBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim) := by
  let A := mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart
  rintro ⟨p, ret, g, st⟩ R s0 hrun hpre hsp
  have hpre' := hpre
  dsimp only [stringCloneBudgetSpec, A, mallocngHookRustCliAllocBudget] at hpre'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx8, hFitEnv, _hlr⟩, hmem⟩
  obtain ⟨hsrc0, hlen_lt⟩ := cloneSrc_of_vecGhostAt (A0 := A.repAlloc) hx0
    (Satisfies.mono (Entails.of_eq (by dsimp [A, mallocngHookRustCliAllocBudget]; sep_ac_rfl)) hmem)
  unfold stringCloneHookMallocng
  dsimp only
  rw [hsrc0]
  by_cases hz : (g.bytes.length == 0) = true
  · simp only [hz, ↓reduceIte]
    have hlen0 : g.bytes.length = 0 := beq_iff_eq.mp hz
    have hbs0 : g.bytes = [] := List.eq_nil_of_length_eq_zero hlen0
    have hmem_ret : s0.mem ⊨ memRegion ret 24 ∗
        (vecGhostAt A.repAlloc g p ∗
          mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
          stackAt s0.sp extHookStack ∗ R) :=
      Satisfies.mono (Entails.of_eq (by dsimp [A, mallocngHookRustCliAllocBudget]; sep_ac_rfl)) hmem
    obtain ⟨hkf_w, hperm_w, hvec⟩ := write_empty_vecU8 (A := A.repAlloc) hmem_ret
    let mf := writeVecHeader s0.mem ret 0#64 1#64 0#64
    rw [show retHook (fun s => s.setMem (writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64)) s0 =
        retHook (fun s => s.setMem mf) s0 by simp [retHook, hx8, mf]]
    obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf rfl rfl rfl hrun
    refine ⟨hkf_w, rfl, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
    dsimp only [stringCloneBudgetSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨[], ?_⟩
    have hEnvNil : StringCloneEnv g [] := Or.inl ⟨hlen0, rfl⟩
    have hpool_f :
        A.pool lim (M.stepEvents [] st) (retHook (fun s => s.setMem mf) s0) =
          mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 :=
      mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st
        (vmPreserved_retHook_setMem hperm_w)
    rw [hpool_f, hbs0, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, hEnvNil⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hvec⟩
  · simp only [Bool.eq_false_iff.mpr hz, Bool.false_eq_true, ↓reduceIte]
    have hne0 : g.bytes.length ≠ 0 := fun h => hz (beq_iff_eq.mpr h)
    have hpos : 1 ≤ g.bytes.length := Nat.pos_of_ne_zero hne0
    have hEnv : StringCloneEnv g (rustAllocEvents g.bytes.length 1) := Or.inr ⟨hpos, rfl⟩
    have hFit : LibsignalBinary.Heap.FitsEvent M lim st (.alloc g.bytes.length) :=
      fitsEvent_of_fitsAlloc1 hpos (hFitEnv _ hEnv)
    have hmem0 : s0.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗ stackAt s0.sp extHookStack ∗
          (vecGhostAt A.repAlloc g p ∗ memRegion ret 24)) ∗ R :=
      Satisfies.mono (Entails.of_eq (by dsimp [A, mallocngHookRustCliAllocBudget]; sep_ac_rfl)) hmem
    refine stepRustAlloc1_budget_cps hS hPl false stringCloneFrameBytes g.bytes.length
      (by decide) (by decide) hFit hrun rfl rfl rfl hsp
      (Memory.KeepsFrozen.refl _) rfl (allocCallPreserved_refl s0) hmem0 _ ?_
    intro s1 q hq_ne hq_al16 hq_fit64 hs1_run hs1_sp hs1_regs hs1_vregs hkf1 hsym1 hpres1 hmem1
    simp only [Bool.false_eq_true, ↓reduceIte] at hmem1
    have hs1_x0 : s1.readReg64 .x0 = p := by simp [State.readReg64, hs1_regs] at hx0 ⊢; exact hx0
    have hs1_x8 : s1.readReg64 .x8 = ret := by simp [State.readReg64, hs1_regs] at hx8 ⊢; exact hx8
    obtain ⟨hsrc1, _⟩ := cloneSrc_of_vecGhostAt (A0 := A.repAlloc) hs1_x0
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1)
    rw [hsrc1]
    obtain ⟨hkf_w, hperm_w, hvec⟩ := write_vecU8_from_alloc hS (mpl := mpl) (tp := tp) (brkStart := brkStart)
      (bs := g.bytes) hq_ne hq_al16 hq_fit64 hpos hlen_lt (Nat.le_refl _)
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1 : s1.mem ⊨
        I.BlockM γ q g.bytes.length 16 ∗ memRegion q g.bytes.length ∗ memRegion ret 24 ∗
          (vecGhostAt A.repAlloc g p ∗
            mallocngHookBudgetPool M I γ mpl tp brkStart lim
              (M.step (.alloc g.bytes.length) st) s1 ∗
            stackAt s0.sp extHookStack ∗ R))
    let mf := writeVecHeader (s1.mem.writeBytes q g.bytes) ret
      (BitVec.ofNat 64 g.bytes.length) q (BitVec.ofNat 64 g.bytes.length)
    rw [show retHook (fun s => s.setMem (writeVecHeader (s.mem.writeBytes q g.bytes)
        (s.readReg64 .x8) (BitVec.ofNat 64 g.bytes.length) q (BitVec.ofNat 64 g.bytes.length))) s1 =
        retHook (fun s => s.setMem mf) s1 by simp [retHook, hs1_x8, mf]]
    obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf hs1_regs hs1_vregs hs1_sp hs1_run
    refine ⟨hkf1.trans hkf_w, hsym1, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
    dsimp only [stringCloneBudgetSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨rustAllocEvents g.bytes.length 1, ?_⟩
    have hev_step : M.stepEvents (rustAllocEvents g.bytes.length 1) st =
        M.step (.alloc g.bytes.length) st := by
      rw [rustAllocEvents_one hpos]; rfl
    have hpool_f :
        A.pool lim (M.stepEvents (rustAllocEvents g.bytes.length 1) st)
          (retHook (fun s => s.setMem mf) s1) =
          mallocngHookBudgetPool M I γ mpl tp brkStart lim
            (M.step (.alloc g.bytes.length) st) s1 := by
      dsimp only [A, mallocngHookRustCliAllocBudget]
      rw [hev_step]
      exact mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim _
        (vmPreserved_retHook_setMem hperm_w)
    rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpres1.2.1, hEnv⟩, Satisfies.mono (Entails.of_eq (by dsimp [A]; sep_ac_rfl)) hvec⟩

theorem fineStringClone_budget_hookOk [LibsignalPlacement] (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) :
    HookOk (stringCloneHookMallocng mpl)
      (stringCloneBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  stringCloneHookMallocng_budget_ok fineCostModelSound γ tp brkStart lim hPl

theorem fineStringClone_budget_hookSat [LibsignalPlacement] {abs : String → Option (State → State)} {name : String}
    (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hH : abs name = some (stringCloneHookMallocng mpl)) :
    HookSat abs name
      (stringCloneBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  ⟨stringCloneHookMallocng mpl, hH, fineStringClone_budget_hookOk γ tp brkStart lim hPl⟩

/-- Program-mode `fineCostModel` `<String as Clone>::clone` over `fineRustCliAllocBudget`. -/
theorem fineStringCloneBudget_of_hasInstrs_ok [LibsignalPlacement] (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits) {P : Program}
    {allocAddrs : RustAllocAddrs}
    {fnAddr shimAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddrs.alloc memcpyAddr handleErrorAddr))
    (hAlloc : RustCliAllocBudgetEntriesBase fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart) P allocAddrs)
    (hAux : RustStdAllocAuxEntries P shimAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (stringCloneBudgetSpec fineCostModel (fineRustCliAllocBudget γ mpl tp brkStart) lim) :=
  rustStringCloneBudget_of_hasInstrs_ok (fineRustCliAllocBudget γ mpl tp brkStart) lim
    hCode hAlloc hAux

/-- Program-mode `fineCostModel` `<String as Clone>::clone` over the unified hook+program pool
    `fineHookRustCliAllocBudget`. -/
theorem fineHookStringCloneBudget_of_hasInstrs_ok [LibsignalPlacement] (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits) {P : Program}
    {allocAddrs : RustAllocAddrs}
    {fnAddr shimAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddrs.alloc memcpyAddr handleErrorAddr))
    (hAlloc : RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) P allocAddrs)
    (hAux : RustStdAllocAuxEntries P shimAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (stringCloneBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  rustStringCloneBudget_of_hasInstrs_ok (fineHookRustCliAllocBudget γ mpl tp brkStart) lim
    hCode hAlloc hAux

/-- Program-mode `WordTree` `<String as Clone>::clone` over `fineHookRustCliAllocBudget`. -/
theorem fineHookStringCloneBudget_of_wordTree_ok [LibsignalPlacement] (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {P : Program} {t : WordTree} (n : Nat) {allocAddrs : RustAllocAddrs}
    {fnAddr shimAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 33 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none)
    (hok : checkShimInstrsAt P.base t fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddrs.alloc memcpyAddr handleErrorAddr) = true)
    (hAlloc : RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) P allocAddrs)
    (hAux : RustStdAllocAuxEntries P shimAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (stringCloneBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  rustStringCloneBudget_of_wordTree_ok (fineHookRustCliAllocBudget γ mpl tp brkStart) lim
    n hcode hwf hhook hok hAlloc hAux

/-- 1-hop `B`-stub alias lift for `stringCloneBudgetSpec` over `fineHookRustCliAllocBudget`. -/
theorem fineHookStringCloneBudget_alias_ok [LibsignalPlacement] (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits) {P : Program}
    (aliasAddr fnAddr : BitVec 64) (hStub : hasInstrs P aliasAddr [ .b (fnAddr - aliasAddr) ])
    (hTarget : subroutine_ok P fnAddr
      (stringCloneBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)) :
    subroutine_ok P aliasAddr
      (stringCloneBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  lsStringCloneBudget_alias_ok (fineHookRustCliAllocBudget γ mpl tp brkStart) lim
    aliasAddr fnAddr hStub hTarget

/-- 2-hop `B`-stub alias lift for `stringCloneBudgetSpec` over `fineHookRustCliAllocBudget`. -/
theorem fineHookStringCloneBudget_alias2_ok [LibsignalPlacement] (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits) {P : Program}
    (snapstubAddr aliasAddr fnAddr : BitVec 64)
    (hSnap : hasInstrs P snapstubAddr [ .b (aliasAddr - snapstubAddr) ])
    (hAlias : hasInstrs P aliasAddr [ .b (fnAddr - aliasAddr) ])
    (hTarget : subroutine_ok P fnAddr
      (stringCloneBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)) :
    subroutine_ok P snapstubAddr
      (stringCloneBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  lsStringCloneBudget_alias2_ok (fineHookRustCliAllocBudget γ mpl tp brkStart) lim
    snapstubAddr aliasAddr fnAddr hSnap hAlias hTarget

/-- 2-hop `WordTree` `B`-stub alias lift for `stringCloneBudgetSpec` over `fineHookRustCliAllocBudget`. -/
theorem fineHookStringCloneBudget_alias2_wordTree_ok [LibsignalPlacement] (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {P : Program} {t : WordTree} (n : Nat) (snapstubAddr aliasAddr fnAddr : BitVec 64)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhookSnap : ∀ i, i < 1 → P.hookAtOff? ((snapstubAddr - P.base).toNat + 4 * i) = none)
    (hhookAlias : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none)
    (hok : checkBranchStub2 P.base t snapstubAddr aliasAddr fnAddr = true)
    (hTarget : subroutine_ok P fnAddr
      (stringCloneBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)) :
    subroutine_ok P snapstubAddr
      (stringCloneBudgetSpec fineCostModel (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  lsStringCloneBudget_alias2_wordTree_ok (fineHookRustCliAllocBudget γ mpl tp brkStart) lim
    n snapstubAddr aliasAddr fnAddr hcode hwf hhookSnap hhookAlias hok hTarget

end LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
