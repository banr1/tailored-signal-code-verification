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
public import LibsignalBinary.Specifications.LibsignalE2E.HooksMallocng
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Heap.Fine.RustEntriesFine
import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Shared-pool (`mallocng`) budget hook base pool and `runPlacedAllocHook`

Defines `CodeBlocksPermRX`, the `MultiCodeROHook`-compatible budget pool `mallocngHookBudgetPool`,
the `RustCliAllocBudget` instances `mallocngHookRustCliAllocBudget` and `fineHookRustCliAllocBudget`,
startup pool constructors, and the placed-library-to-hook bridge `runPlacedAllocHook`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase

open Arm64 Arm64.CType ProofLib.SepLogic
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.E2E (restoreCallerRegs writeVecHeader)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits
  FdsHiFrame FitsEvent FitsStep
  MallocngCostModelIface MallocngCostModelSound
  MallocngModelEnv MallocngModelPostEnv MallocngStepOomCond
  OomPreserved PoolPreserved RustCliAllocBudget VmMemPreserved VmPreserved
  mallocngBudgetPool mallocngBudgetPoolAt_transport mallocngBudgetPoolAt_transport_mem
  mallocngBudgetPoolAt_zero_transport mallocngBudgetPoolInv mallocngBudgetPool_mapped_lt_userVa
  mallocngBudgetPool_of_init
  mallocngLiveM mallocngRustCliAllocBudget mallocng_oom_false
  steps_of_withSvc_alloc_running_or_oom zeroBudgetLimits
)
open LibsignalBinary.Heap.Fine (
  fineCostModel fineCostModelIface fineCostModelSound fineRustCliAllocBudget
)
open VerifiedLibraries.Mallocng (
  MallocngAddrs MallocngAuxvAt MallocngBrkStartWf MallocngMaxAllocSize
  MallocngProcPreserved MallocngRuntime
  mallocngAddrsOfPlacement mallocngBlockProg mallocngMultiEntryOk mallocngStackBytes
)

/-! ## `CodeBlocksPermRX` and `mallocngHookRustCliAllocBudget` -/

/-- All relocated code-block addresses of `VerifiedLibraries.mallocngLib` at `mpl` carry `Perm.rx`
    in `m` (automatic on any linked ELF via `codeBlocksPermRX_of_codeLoaded`, preserved by
    `VmPreserved` and `Memory.KeepsFrozen`, and ensuring `loadMultiCodeMem` / `restoreMultiCodeMem`
    leave `m.perm` — hence `rwBytes` and `physPlusRw` — invariant). -/
def CodeBlocksPermRXMem (mpl : Obj.MultiPlacement) (m : Memory) : Prop :=
  ∀ a : BitVec 64,
    (VerifiedLibraries.mallocngLib.findCodeBlock mpl a).isSome = true →
    m.perm a = some Perm.rx

abbrev CodeBlocksPermRX (mpl : Obj.MultiPlacement) (s : State) : Prop :=
  CodeBlocksPermRXMem mpl s.mem

theorem codeBlocksPermRX_of_perm_eq {mpl : Obj.MultiPlacement} {m m' : Memory}
    (hperm : ∀ a, m'.perm a = m.perm a) :
    CodeBlocksPermRXMem mpl m' = CodeBlocksPermRXMem mpl m := by
  apply propext
  unfold CodeBlocksPermRXMem
  simp only [hperm]

theorem codeBlocksPermRX_of_keepsFrozen {mpl : Obj.MultiPlacement} {m m' : Memory}
    (h0 : CodeBlocksPermRXMem mpl m) (hkf : m.KeepsFrozen m') :
    CodeBlocksPermRXMem mpl m' := by
  intro a ha
  have hp0 : m.perm a = some Perm.rx := h0 a ha
  have hfr : m.Frozen a := by
    unfold Memory.Frozen
    rw [hp0]
    rfl
  exact (hkf a hfr).2.1.trans hp0

theorem codeBlocksPermRX_of_codeLoaded {mpl : Obj.MultiPlacement} {m : Memory}
    (hCL : VerifiedLibraries.mallocngLib.CodeLoaded mpl m) :
    CodeBlocksPermRXMem mpl m := by
  intro a ha
  cases hf : VerifiedLibraries.mallocngLib.findCodeBlock mpl a with
  | none => simp [hf] at ha
  | some k =>
    have hf' :
        (List.range VerifiedLibraries.mallocngLib.blocks.length).find?
          (fun j => decide (InRegion (mpl.base j)
            (VerifiedLibraries.mallocngLib.blockPatched mpl j).length a)) = some k := hf
    have hk : k < VerifiedLibraries.mallocngLib.blocks.length :=
      List.mem_range.mp (List.mem_of_find?_eq_some hf')
    have hin : InRegion (mpl.base k)
        (VerifiedLibraries.mallocngLib.blockPatched mpl k).length a :=
      of_decide_eq_true (@List.find?_some _ (fun j => decide (InRegion (mpl.base j)
        (VerifiedLibraries.mallocngLib.blockPatched mpl j).length a)) _ _ hf')
    have hprogCL := Program.codeLoaded_iff.mp (hCL k hk)
    have hbase : (VerifiedLibraries.mallocngLib.blockProgram mpl k).base = mpl.base k := rfl
    have hcode : (VerifiedLibraries.mallocngLib.blockProgram mpl k).code =
        VerifiedLibraries.mallocngLib.blockPatched mpl k := rfl
    rw [hbase, hcode] at hprogCL
    have hidx : (a - mpl.base k).toNat <
        (VerifiedLibraries.mallocngLib.blockPatched mpl k).length := hin
    have hperm_idx := (hprogCL.2.2 (a - mpl.base k).toNat hidx).2.1
    have hadj : mpl.base k + BitVec.ofNat 64 (a - mpl.base k).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      bv_omega
    rwa [hadj] at hperm_idx

private theorem perm_eq_of_cells_eq {m1 m2 : Memory} {a : BitVec 64}
    (hc : m1.cells a = m2.cells a) :
    m1.perm a = m2.perm a := by
  unfold Memory.perm
  rw [hc]

theorem perm_loadMultiCodeMem_eq {mpl : Obj.MultiPlacement} {m : Memory}
    (hrx : CodeBlocksPermRXMem mpl m) (a : BitVec 64) :
    (loadMultiCodeMem VerifiedLibraries.mallocngLib mpl m).perm a = m.perm a := by
  cases hf : VerifiedLibraries.mallocngLib.findCodeBlock mpl a with
  | some k =>
    have hc := loadMultiCodeMem_cells_some (m := m) hf
    have hp1 : (loadMultiCodeMem VerifiedLibraries.mallocngLib mpl m).perm a = some Perm.rx := by
      simp [Memory.perm, Perm.rwx, Perm.rx, hc]
    exact hp1.trans (hrx a (by simp [hf])).symm
  | none =>
    exact perm_eq_of_cells_eq (loadMultiCodeMem_cells_none (m := m) hf)

theorem perm_restoreMultiCodeMem_eq {mpl : Obj.MultiPlacement} {m0 mf' : Memory}
    (hrx0 : CodeBlocksPermRXMem mpl m0) (hrxf : CodeBlocksPermRXMem mpl mf') (a : BitVec 64) :
    (restoreMultiCodeMem VerifiedLibraries.mallocngLib mpl m0 mf').perm a = mf'.perm a := by
  cases hf : VerifiedLibraries.mallocngLib.findCodeBlock mpl a with
  | some k =>
    have hc := restoreMultiCodeMem_cells_some (m0 := m0) (mf := mf') hf
    have hp0 : m0.perm a = some Perm.rx := hrx0 a (by simp [hf])
    have hpf : mf'.perm a = some Perm.rx := hrxf a (by simp [hf])
    exact (perm_eq_of_cells_eq hc).trans (hp0.trans hpf.symm)
  | none =>
    exact perm_eq_of_cells_eq (restoreMultiCodeMem_cells_none (m0 := m0) (mf := mf') hf)

theorem vmPreserved_hookEntry {mpl : Obj.MultiPlacement} {i : Nat} {pc : BitVec 64}
    {s0 : State} (hrx0 : CodeBlocksPermRX mpl s0) :
    VmPreserved s0 (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i pc s0) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, fun a => ?_, FdsHiFrame.of_fs_eq ?_⟩
  · exact multiCodeROHookEntry_brkStart VerifiedLibraries.mallocngLib mpl i pc s0
  · exact multiCodeROHookEntry_brk VerifiedLibraries.mallocngLib mpl i pc s0
  · exact multiCodeROHookEntry_tpidrEl0 VerifiedLibraries.mallocngLib mpl i pc s0
  · exact multiCodeROHookEntry_physMemAvail VerifiedLibraries.mallocngLib mpl i pc s0
  · rw [multiCodeROHookEntry_mem]
    exact perm_loadMultiCodeMem_eq hrx0 a
  · exact multiCodeROHookEntry_fs VerifiedLibraries.mallocngLib mpl i pc s0

theorem vmPreserved_hookExit {mpl : Obj.MultiPlacement} {i : Nat}
    {s0 sf' : State} (hrx0 : CodeBlocksPermRX mpl s0) (hrxf : CodeBlocksPermRX mpl sf') :
    VmPreserved sf' (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf') := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, fun a => ?_, FdsHiFrame.of_fs_eq ?_⟩
  · exact multiCodeROHookExit_brkStart VerifiedLibraries.mallocngLib mpl i s0 sf'
  · exact multiCodeROHookExit_brk VerifiedLibraries.mallocngLib mpl i s0 sf'
  · exact multiCodeROHookExit_tpidrEl0 VerifiedLibraries.mallocngLib mpl i s0 sf'
  · exact multiCodeROHookExit_physMemAvail VerifiedLibraries.mallocngLib mpl i s0 sf'
  · rw [multiCodeROHookExit_mem]
    exact perm_restoreMultiCodeMem_eq hrx0 hrxf a
  · exact multiCodeROHookExit_fs VerifiedLibraries.mallocngLib mpl i s0 sf'

/-- Budget-threaded `mallocng` pool for `MultiCodeROHook`-backed hooks: pairs
    `VerifiedLibraries.mallocngLib.codeRO mpl` with `mallocngBudgetPool` and (when
    `lim.enforced = true`) `CodeBlocksPermRX mpl s`. -/
def mallocngHookBudgetPool (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) : SepProp :=
  VerifiedLibraries.mallocngLib.codeRO mpl ∗
    mallocngBudgetPool M I γ mpl tp brkStart lim st s ∗
    ⌜lim.enforced = true → CodeBlocksPermRX mpl s⌝

theorem mallocngHookBudgetPool_transport_mem (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) {s s' : State} (hvm : VmMemPreserved s s') :
    mallocngHookBudgetPool M I γ mpl tp brkStart lim st s' =
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st s := by
  have hpool :
      mallocngBudgetPool M I γ mpl tp brkStart lim st s' =
        mallocngBudgetPool M I γ mpl tp brkStart lim st s :=
    mallocngBudgetPoolAt_transport_mem M I γ (mallocngAddrsOfPlacement mpl) tp brkStart lim st hvm
  have hrx : CodeBlocksPermRX mpl s' = CodeBlocksPermRX mpl s :=
    codeBlocksPermRX_of_perm_eq hvm.2.2
  simp only [mallocngHookBudgetPool, hpool, hrx]

theorem mallocngHookBudgetPool_transport (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) {s s' : State} (hvm : VmPreserved s s') :
    mallocngHookBudgetPool M I γ mpl tp brkStart lim st s' =
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st s :=
  mallocngHookBudgetPool_transport_mem M I γ mpl tp brkStart lim st hvm.toVmMemPreserved

theorem mallocngHookBudgetPool_zero_transport (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (st : M.σ) {s s' : State} (hp : PoolPreserved s s') :
    mallocngHookBudgetPool M I γ mpl tp brkStart zeroBudgetLimits st s' =
      mallocngHookBudgetPool M I γ mpl tp brkStart zeroBudgetLimits st s := by
  have hpool :
      mallocngBudgetPool M I γ mpl tp brkStart zeroBudgetLimits st s' =
        mallocngBudgetPool M I γ mpl tp brkStart zeroBudgetLimits st s :=
    mallocngBudgetPoolAt_zero_transport M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st hp
  have hrx : ∀ u : State, (zeroBudgetLimits.enforced = true → CodeBlocksPermRX mpl u) = True := by
    intro u
    apply propext
    exact ⟨fun _ => trivial, fun _ h => Bool.noConfusion h⟩
  simp only [mallocngHookBudgetPool, hpool, hrx]

/-- Cost-model-parametric `RustCliAllocBudget M` instance for `MultiCodeROHook`-backed hooks over `mallocngLib`. -/
def mallocngHookRustCliAllocBudget (M : AllocCostModel) (I : MallocngCostModelIface M)
    (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    RustCliAllocBudget M where
  pool := mallocngHookBudgetPool M I γ mpl tp brkStart
  live := mallocngLiveM M I γ
  block_valid := (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart).block_valid
  pool_transport lim st _ _ hvm :=
    mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hvm
  pool_zero_transport st _ _ hp :=
    mallocngHookBudgetPool_zero_transport M I γ mpl tp brkStart st hp

/-- `fineCostModel` specialization of `mallocngHookRustCliAllocBudget`. -/
noncomputable def fineHookRustCliAllocBudget (γ : GhostName) (mpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64) : RustCliAllocBudget fineCostModel :=
  mallocngHookRustCliAllocBudget fineCostModel fineCostModelIface fineCostModelSound γ mpl tp brkStart

@[simp] theorem mallocngHookRustCliAllocBudget_repAlloc
    (M : AllocCostModel) (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).repAlloc =
      (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart).repAlloc := rfl

@[simp] theorem fineHookRustCliAllocBudget_repAlloc
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    (fineHookRustCliAllocBudget γ mpl tp brkStart).repAlloc =
      (fineRustCliAllocBudget γ mpl tp brkStart).repAlloc := rfl

/-- Upgrade `mallocngBudgetPool` to `mallocngHookBudgetPool` whenever
    `VerifiedLibraries.mallocngLib.CodeLoaded mpl s.mem` holds (using read-only code ownership
    introduction `satisfies_codeRO_of_codeLoaded`, consuming zero RW cells). -/
theorem mallocngHookBudgetPool_of_codeLoaded {M : AllocCostModel} {I : MallocngCostModelIface M}
    {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {s : State} {R : SepProp}
    (hCL : VerifiedLibraries.mallocngLib.CodeLoaded mpl s.mem)
    (hsat : s.mem ⊨ mallocngBudgetPool M I γ mpl tp brkStart lim st s ∗ R) :
    s.mem ⊨ mallocngHookBudgetPool M I γ mpl tp brkStart lim st s ∗ R := by
  have hcode : s.mem ⊨
      VerifiedLibraries.mallocngLib.codeRO mpl ∗
        (mallocngBudgetPool M I γ mpl tp brkStart lim st s ∗ R) :=
    VerifiedLibraries.mallocngLib.satisfies_codeRO_of_codeLoaded hCL hsat
  have hrx : lim.enforced = true → CodeBlocksPermRX mpl s :=
    fun _ => codeBlocksPermRX_of_codeLoaded hCL
  unfold mallocngHookBudgetPool
  exact Satisfies.mono
    (Entails.trans (Entails.pure_right hrx (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl)))
    hcode

/-- Startup initialization of `mallocngHookBudgetPool` from `VerifiedLibraries.mallocngLib.dataInit mpl`
    and `VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem`. -/
theorem mallocngHookBudgetPool_of_init {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {mpl : Obj.MultiPlacement} {auxvPtr : BitVec 64}
    {lim : BudgetLimits} {staticIvs : List (BitVec 64 × Nat)} {R : SepProp} {s0 : State}
    (hCL : VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat) (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hbrk : s0.brk = s0.brkStart) (hbrkWf : MallocngBrkStartWf s0.brkStart)
    (hInv : mallocngBudgetPoolInv lim staticIvs [] s0)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      s0.mem ⊨
        (mallocngHookRustCliAllocBudget M I hS γ mpl s0.tpidrEl0 s0.brkStart).pool lim M.init s0 ∗ R := by
  obtain ⟨γ, hPool⟩ :=
    mallocngBudgetPool_of_init hS htpLo htpHi hbrk hbrkWf hInv hmem
  exact ⟨γ, mallocngHookBudgetPool_of_codeLoaded hCL hPool⟩

theorem fineHookBudgetPool_of_init {mpl : Obj.MultiPlacement} {auxvPtr : BitVec 64}
    {lim : BudgetLimits} {staticIvs : List (BitVec 64 × Nat)} {R : SepProp} {s0 : State}
    (hCL : VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat) (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hbrk : s0.brk = s0.brkStart) (hbrkWf : MallocngBrkStartWf s0.brkStart)
    (hInv : mallocngBudgetPoolInv lim staticIvs [] s0)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      s0.mem ⊨
        (fineHookRustCliAllocBudget γ mpl s0.tpidrEl0 s0.brkStart).pool lim fineCostModel.init s0 ∗ R :=
  mallocngHookBudgetPool_of_init fineCostModelSound hCL htpLo htpHi hbrk hbrkWf hInv hmem

/-! ## State, stack, and separation-logic helpers -/

theorem allocCallPreserved_refl (s : State) : AllocCallPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem allocCallPreserved_trans {s0 s1 s2 : State}
    (h01 : AllocCallPreserved s0 s1) (h12 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

theorem allocCallPreserved_of_mallocngProcPreserved {s0 sf : State}
    (h : MallocngProcPreserved s0 sf) : AllocCallPreserved s0 sf := by
  rcases h with ⟨hfs, htr, htp, hbrkS, horc, hsym, hsig⟩
  exact ⟨hfs, htr, hsig, htp, hbrkS, horc, hsym⟩

theorem procPreserved_hookExit {mpl : Obj.MultiPlacement} {i : Nat} {pc : BitVec 64}
    {s0 sf' : State}
    (h : MallocngProcPreserved (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i pc s0) sf') :
    MallocngProcPreserved s0 (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf') := by
  rcases h with ⟨hfs, htr, htp, hbrkS, horc, hsym, hsig⟩
  simp only [MallocngProcPreserved, multiCodeROHookEntry_fs, multiCodeROHookEntry_trace,
    multiCodeROHookEntry_tpidrEl0, multiCodeROHookEntry_brkStart, multiCodeROHookEntry_oracle,
    multiCodeROHookEntry_symtab, multiCodeROHookEntry_sigActions, multiCodeROHookExit_fs,
    multiCodeROHookExit_trace, multiCodeROHookExit_tpidrEl0, multiCodeROHookExit_brkStart,
    multiCodeROHookExit_oracle, multiCodeROHookExit_symtab, multiCodeROHookExit_sigActions]
    at hfs htr htp hbrkS horc hsym hsig ⊢
  exact ⟨hfs, htr, htp, hbrkS, horc, hsym, hsig⟩

theorem spAligned_sub_16 {sp : BitVec 64} {fb : Nat}
    (hsp : (sp &&& 0b1111#64) == 0#64) (h16 : fb % 16 = 0) :
    ((sp - BitVec.ofNat 64 fb) &&& 0b1111#64) == 0#64 := by
  have h1 : (sp &&& 0b1111#64).toNat = 0 := by rw [eq_of_beq hsp]; rfl
  rw [BitVec.toNat_and] at h1
  change sp.toNat &&& 15 = 0 at h1
  rw [Nat.and_two_pow_sub_one_eq_mod _ 4] at h1
  apply beq_iff_eq.mpr; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change (sp - BitVec.ofNat 64 fb).toNat &&& 15 = 0
  rw [Nat.and_two_pow_sub_one_eq_mod _ 4, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem stackAt_split_frame (sp : BitVec 64) (fb : Nat)
    (hfb : fb + mallocngStackBytes ≤ extHookStack) :
    stackAt sp extHookStack =
      stackFrameAt (sp - BitVec.ofNat 64 fb) mallocngStackBytes ∗
        (memRegion (sp - BitVec.ofNat 64 extHookStack) (extHookStack - fb - mallocngStackBytes) ∗
          memRegion (sp - BitVec.ofNat 64 fb) fb) := by
  have hm0 : mallocngStackBytes = 1024 := rfl
  have he0 : extHookStack = 16384 := rfl
  have hsub1 : BitVec.ofNat 64 (extHookStack - fb - mallocngStackBytes) =
      BitVec.ofNat 64 extHookStack - BitVec.ofNat 64 fb - BitVec.ofNat 64 mallocngStackBytes := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsub2 : BitVec.ofNat 64 (extHookStack - fb) =
      BitVec.ofNat 64 extHookStack - BitVec.ofNat 64 fb := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [stackAt, stackFrameAt_eq_memRegion (sp - BitVec.ofNat 64 fb) mallocngStackBytes (by omega)]
  have h1 := (SepFrameInfer.memRegion_merge (sp - BitVec.ofNat 64 extHookStack)
    (sp - BitVec.ofNat 64 fb - BitVec.ofNat 64 mallocngStackBytes)
    (extHookStack - fb - mallocngStackBytes) mallocngStackBytes (extHookStack - fb)
    (by rw [hsub1]; bv_omega) (by omega) (by omega)).symm
  have h2 := (SepFrameInfer.memRegion_merge (sp - BitVec.ofNat 64 extHookStack)
    (sp - BitVec.ofNat 64 fb) (extHookStack - fb) fb extHookStack
    (by rw [hsub2]; bv_omega) (by omega) (by omega)).symm
  rw [h2, h1]; sep_ac_rfl

theorem cc_retHook_setMem_sameRegs {s0 s : State} (m : Memory)
    (hregs : s.regs = s0.regs) (hvregs : s.vregs = s0.vregs) (hsp : s.sp = s0.sp)
    (hrun : s.status = .Running) :
    Returned s0 (retHook (fun st => st.setMem m) s) ∧
      CallingConventionPreserved s0 (retHook (fun st => st.setMem m) s) := by
  have hlr : s.readReg64 .lr = s0.readReg64 .lr := by simp [State.readReg64, hregs]
  refine ⟨⟨by simp [retHook, State.setPC, State.setMem, hlr],
    by simp [retHook, State.setPC, State.setMem, hsp],
    by simp [retHook, State.setPC, State.setMem, hrun]⟩, ?_⟩
  simp [CallingConventionPreserved, CalleeSavedPreserved,
    retHook, State.setPC, State.setMem, State.readReg64, hregs, hvregs, hsp]

theorem perm_writeVecHeader (m : Memory) (v cap ptr len : BitVec 64) :
    (writeVecHeader m v cap ptr len).perm = m.perm := by
  simp [writeVecHeader, Memory.perm_write64]

theorem vmPreserved_retHook_setMem {s : State} {m : Memory}
    (hperm : m.perm = s.mem.perm) :
    VmPreserved s (retHook (fun st => st.setMem m) s) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, fun a => ?_, fun _ _ _ => ?_⟩
  · simp [retHook, State.setPC, State.setMem]
  · simp [retHook, State.setPC, State.setMem]
  · simp [retHook, State.setPC, State.setMem]
  · simp [retHook, State.setPC, State.setMem]
  · simp [retHook, State.setPC, State.setMem, congrFun hperm a]
  · simp [retHook, State.setPC, State.setMem]

theorem vmPreserved_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    VmPreserved s (s.writeReg64 r v) :=
  ⟨⟨by cases s; cases r <;> rfl, by cases s; cases r <;> rfl, by cases s; cases r <;> rfl⟩,
   by cases s; cases r <;> rfl,
   fun _ => by cases s; cases r <;> rfl,
   fun _ _ _ => by cases s; cases r <;> rfl⟩

theorem vmPreserved_restoreCallerRegs (sCaller sCallee : State) :
    VmPreserved sCallee (restoreCallerRegs sCaller sCallee) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-! ## `MultiCodeROHook` budget bridge combinators -/

noncomputable def mallocngHook (mpl : Obj.MultiPlacement) (fnName : String) : State → State :=
  VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl fnName
    (fun _ => none) (fun _ => none) Syscall.standard

/-- Lift a `mallocngMultiEntryOk mpl allocMallocng fnName innerSpec` witness directly to
    `HookOk (mallocngHook mpl fnName) callerSpec`, bridging `allocMallocng` to `Syscall.standard`
    via `steps_of_withSvc_alloc_running_or_oom` and exposing `physPlusRw sf' = physPlusRw s0'` and
    `s0'.mem.KeepsFrozen sf'.mem` to both the `.Running` and `.OutOfMemory` callbacks. -/
theorem runPlacedAllocHook {S β α : Type} [ToBaseSpec S β]
    {mpl : Obj.MultiPlacement}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    {fnName : String} {innerSpec : S} {callerSpec : Spec α}
    (hentry : mallocngMultiEntryOk mpl allocMallocng fnName innerSpec)
    (href : ∀ (x : α) (R : SepProp) (s0 : State) (i : Nat),
      (s0.mem ⊨ callerSpec.pre x s0 ∗ R) →
      ∃ (y : β) (R_rest : SepProp),
        (s0.mem ⊨ VerifiedLibraries.mallocngLib.codeRO mpl ∗
          ((ToBaseSpec.toSpec innerSpec (mpl.base i)).pre y
            (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i
              (VerifiedLibraries.mallocngLib.fnAddr mpl fnName) s0) ∗ R_rest)) ∧
        (∀ sf' : State,
          VerifiedLibraries.mallocngLib.CodeLoaded mpl sf'.mem →
          physPlusRw sf' =
            physPlusRw (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i
              (VerifiedLibraries.mallocngLib.fnAddr mpl fnName) s0) →
          (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i
            (VerifiedLibraries.mallocngLib.fnAddr mpl fnName) s0).mem.KeepsFrozen sf'.mem →
          sf'.status = .OutOfMemory →
          (sf'.mem ⊨ (ToBaseSpec.toSpec innerSpec (mpl.base i)).onOom y
            (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i
              (VerifiedLibraries.mallocngLib.fnAddr mpl fnName) s0) sf' ∗
            (VerifiedLibraries.mallocngLib.codeRO mpl ∗ R_rest)) →
          ((multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').mem ⊨
            callerSpec.onOom x s0
              (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf') ∗ R)) ∧
        (∀ sf' : State,
          VerifiedLibraries.mallocngLib.CodeLoaded mpl sf'.mem →
          physPlusRw sf' =
            physPlusRw (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i
              (VerifiedLibraries.mallocngLib.fnAddr mpl fnName) s0) →
          (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i
            (VerifiedLibraries.mallocngLib.fnAddr mpl fnName) s0).mem.KeepsFrozen sf'.mem →
          Returned
            (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i
              (VerifiedLibraries.mallocngLib.fnAddr mpl fnName) s0) sf' →
          CallingConventionPreserved
            (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i
              (VerifiedLibraries.mallocngLib.fnAddr mpl fnName) s0) sf' →
          ((multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').mem ⊨
            VerifiedLibraries.mallocngLib.codeRO mpl ∗
              ((ToBaseSpec.toSpec innerSpec (mpl.base i)).post y
                (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i
                  (VerifiedLibraries.mallocngLib.fnAddr mpl fnName) s0) sf' ∗ R_rest)) →
          ((multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').mem ⊨
            callerSpec.post x s0
              (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf') ∗ R)))
    (hNoPanic : ∀ (y : β) (b : BitVec 64) (R' : SepProp) (s0' sf' : State),
      sf'.status = .Panicked →
        ¬(sf'.mem ⊨ (ToBaseSpec.toSpec innerSpec b).onPanic y s0' sf' ∗ R') := by
      intro _ _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (hNoExit : ∀ (y : β) (b : BitVec 64) (code : BitVec 64) (R' : SepProp) (s0' sf' : State),
      sf'.status = .Exited code →
        ¬(sf'.mem ⊨ (ToBaseSpec.toSpec innerSpec b).onExit y code s0' sf' ∗ R') := by
      intro _ _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    HookOk (mallocngHook mpl fnName) callerSpec := by
  obtain ⟨_hexp, i, off, hlook, hsub_blk⟩ := hentry
  obtain ⟨hi, _⟩ := Obj.lookupBlockSym_some hlook
  let entry := VerifiedLibraries.mallocngLib.fnAddr mpl fnName
  let stdProg := VerifiedLibraries.mallocngLib.blockProgram mpl i
    (fun _ => none) (fun _ => none) Syscall.standard
  have hblk_eq : mallocngBlockProg mpl i allocMallocng = stdProg.withSvc allocMallocng := rfl
  have hstd_no : ∀ pc, stdProg.externAt? pc = none := by
    intro pc
    simp [stdProg, Obj.MultiPlacedLib.blockProgram, Obj.PlacedLib.program,
      Program.externAt?, Program.hookAtOff?]
  have hblk_no : ∀ pc, (mallocngBlockProg mpl i allocMallocng).externAt? pc = none := by
    intro pc
    simp [mallocngBlockProg, Obj.MultiPlacedLib.blockProgram, Obj.PlacedLib.program,
      Program.externAt?, Program.hookAtOff?]
  have hpure_no : ∀ pc, Program.pureMem.externAt? pc = none := fun _ => rfl
  intro x R s0 hrun hpre hsp
  let s0' := multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0
  obtain ⟨y, R_rest, hs0_sat, hOomMap, hPostMap⟩ := href x R s0 i hpre
  have hs0'_sat : s0'.mem ⊨ VerifiedLibraries.mallocngLib.codeRO mpl ∗
      ((ToBaseSpec.toSpec innerSpec (mpl.base i)).pre y s0' ∗ R_rest) :=
    satisfies_loadMultiCodeMem hPl hs0_sat
  have hL0' : VerifiedLibraries.mallocngLib.CodeLoaded mpl s0'.mem :=
    codeLoaded_loadMultiCodeMem hPl s0.mem
  have hp0'_std : stdProg.CodeLoaded s0'.mem := (hL0' i hi).of_base_code rfl rfl
  have hp0'_blk : (mallocngBlockProg mpl i allocMallocng).CodeLoaded s0'.mem :=
    (hL0' i hi).of_base_code rfl rfl
  have hs0'_run : s0'.status = .Running := by
    simpa [s0', multiCodeROHookEntry_status] using hrun
  have hs0'_sp : s0'.spAligned = true := by
    simpa [State.spAligned, s0', multiCodeROHookEntry_sp] using hsp
  let R' := VerifiedLibraries.mallocngLib.codeRO mpl ∗ R_rest
  have hs0'_pre : s0'.mem ⊨
      (VerifiedLibraries.mallocngLib.withCodeLoaded mpl
        (ToBaseSpec.toSpec innerSpec (mpl.base i))).pre y s0' ∗ R' := by
    show s0'.mem ⊨
      ((ToBaseSpec.toSpec innerSpec (mpl.base i)).pre y s0' ∗
        ⌜VerifiedLibraries.mallocngLib.CodeLoaded mpl s0'.mem⌝) ∗ R'
    rw [sepConj_comm _ ⌜_⌝, pure_sepConj_of_true hL0']
    exact Satisfies.mono (Entails.of_eq (by dsimp [R']; sep_ac_rfl)) hs0'_sat
  obtain ⟨sf', hsteps_blk, hout⟩ :=
    subroutine_ok_elim_steps_outcome hsub_blk y R' s0'
      (multiCodeROHookEntry_pc VerifiedLibraries.mallocngLib mpl i entry s0)
      hs0'_run hs0'_pre hs0'_sp hp0'_blk
  have hsteps_alloc : Steps (Program.pureMem.withSvc allocMallocng) s0' sf' :=
    steps_withSvc_alloc_of_noHooks hblk_no rfl hpure_no hsteps_blk
  have hpprw' : physPlusRw sf' = physPlusRw s0' :=
    physPlusRw_steps_withSvc_alloc hpure_no hsteps_alloc
  have hkf' : s0'.mem.KeepsFrozen sf'.mem := hsteps_alloc.keepsFrozen
  have hLf : VerifiedLibraries.mallocngLib.CodeLoaded mpl sf'.mem := hL0'.of_keepsFrozen hkf'
  have hkf_exit : s0.mem.KeepsFrozen
      (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').mem :=
    keepsFrozen_restoreMultiCodeMem hkf'
  have hsym_exit :
      (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').symtab = s0.symtab := by
    rw [multiCodeROHookExit_symtab, hsteps_alloc.symtab_eq, multiCodeROHookEntry_symtab]
  rcases hout with ⟨hret, hcc, hpost_wcl⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · have hsteps_std : Steps stdProg s0' sf' :=
      steps_of_withSvc_alloc_running_or_oom hstd_no rfl (hblk_eq ▸ hsteps_blk) (Or.inl hret.2.2)
    have hhook_eq : mallocngHook mpl fnName s0 =
        multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf' :=
      codeROSubroutineHook_eq_of_steps_outcome hlook hp0'_std.aligned (hstd_no _)
        hsteps_std (Or.inl ⟨hret, hcc, hpost_wcl⟩)
    rw [hhook_eq]
    have hsf'_reord : sf'.mem ⊨ VerifiedLibraries.mallocngLib.codeRO mpl ∗
        ((ToBaseSpec.toSpec innerSpec (mpl.base i)).post y s0' sf' ∗ R_rest) :=
      Satisfies.mono (Entails.of_eq (by dsimp [Obj.MultiPlacedLib.withCodeLoaded, R']; sep_ac_rfl))
        hpost_wcl
    have hsf_restored :
        (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').mem ⊨
          VerifiedLibraries.mallocngLib.codeRO mpl ∗
            ((ToBaseSpec.toSpec innerSpec (mpl.base i)).post y s0' sf' ∗ R_rest) := by
      simpa only [multiCodeROHookExit_mem] using
        satisfies_restoreMultiCodeMem hPl hkf' hs0_sat hsf'_reord
    exact ⟨hkf_exit, hsym_exit,
      Or.inl ⟨multiCodeROHookExit_returned hret, multiCodeROHookExit_cc hcc,
        hPostMap sf' hLf hpprw' hkf' hret hcc hsf_restored⟩⟩
  · exact False.elim (hNoPanic y (mpl.base i) R' s0' sf' hpan hq)
  · exact False.elim (hNoExit y (mpl.base i) code R' s0' sf' hex hq)
  · have hsteps_std : Steps stdProg s0' sf' :=
      steps_of_withSvc_alloc_running_or_oom hstd_no rfl (hblk_eq ▸ hsteps_blk) (Or.inr hoom)
    have hhook_eq : mallocngHook mpl fnName s0 =
        multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf' :=
      codeROSubroutineHook_eq_of_steps_outcome hlook hp0'_std.aligned (hstd_no _)
        hsteps_std (Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩)))
    rw [hhook_eq]
    refine ⟨hkf_exit, hsym_exit, Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))⟩
    · simp [multiCodeROHookExit, hoom]
    · exact hOomMap sf' hLf hpprw' hkf' hoom hq

private theorem extractModelEnvBounds {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {γ : GhostName} {A : MallocngAddrs} {tp brkStart : BitVec 64}
    {st : M.σ} {ivs0 : List (BitVec 64 × Nat)} {s0 : State} {R : SepProp}
    (hsat : s0.mem ⊨ MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ R) :
    ivs0.length ≤ M.maxDynIvs st ∧ (ivs0.map Prod.snd).sum ≤ M.footprint st := by
  let φ := ivs0.length ≤ M.maxDynIvs st ∧ (ivs0.map Prod.snd).sum ≤ M.footprint st
  have hent : MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ R ⊢
      ⌜φ⌝ ∗ (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ R) := by
    unfold MallocngModelEnv
    have hh : I.HeapM γ A tp brkStart s0.brk st ivs0 ⊢
        ⌜φ⌝ ∗ I.HeapM γ A tp brkStart s0.brk st ivs0 :=
      Entails.extract_heap_fact fun hp hhp =>
        let ⟨hlen, hsum, _⟩ := hS.heap_footprint_bound γ A tp brkStart s0.brk st ivs0 hp hhp
        ⟨hlen, hsum⟩
    exact Entails.trans (sepConj_mono_left (sepConj_mono_right hh))
      (Entails.of_eq (by sep_ac_rfl))
  have hsat' := Satisfies.mono hent hsat
  rw [satisfies_pure_sepConj] at hsat'
  exact hsat'.1

theorem unpackHookBudgetPool {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {s0 : State} {Rest : SepProp}
    (hsat : s0.mem ⊨ mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗ Rest) :
    ∃ staticIvs ivs0,
      (lim.enforced = true → CodeBlocksPermRX mpl s0) ∧
      mallocngBudgetPoolInv lim staticIvs ivs0 s0 ∧
      ivs0.length ≤ M.maxDynIvs st ∧
      (ivs0.map Prod.snd).sum ≤ M.footprint st ∧
      (s0.mem ⊨ VerifiedLibraries.mallocngLib.codeRO mpl ∗
        (MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0 ∗ Rest)) := by
  unfold mallocngHookBudgetPool mallocngBudgetPool LibsignalBinary.Heap.mallocngBudgetPoolAt at hsat
  have hsat1 : s0.mem ⊨
      ⌜lim.enforced = true → CodeBlocksPermRX mpl s0⌝ ∗
        ((∃∗ staticIvs : List (BitVec 64 × Nat), ∃∗ ivs : List (BitVec 64 × Nat),
          ⌜mallocngBudgetPoolInv lim staticIvs ivs s0⌝ ∗
          MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs s0) ∗
          (VerifiedLibraries.mallocngLib.codeRO mpl ∗ Rest)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsat
  rw [satisfies_pure_sepConj] at hsat1
  obtain ⟨hrx0, hsat2⟩ := hsat1
  simp only [sepExists_sepConj_left] at hsat2
  obtain ⟨staticIvs, hsat2⟩ := (satisfies_sepExists _ _).mp hsat2
  obtain ⟨ivs0, hsat2⟩ := (satisfies_sepExists _ _).mp hsat2
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsat2
  obtain ⟨hInv0, hsat2⟩ := hsat2
  obtain ⟨hlen, hsum⟩ := extractModelEnvBounds hS hsat2
  exact ⟨staticIvs, ivs0, hrx0, hInv0, hlen, hsum,
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsat2⟩

theorem packHookPostEnv {M : AllocCostModel} (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    {lim : BudgetLimits} {st' : M.σ} {staticIvs ivs0 : List (BitVec 64 × Nat)}
    {i : Nat} {entry : BitVec 64} {s0 sf' : State}
    (hrx0 : lim.enforced = true → CodeBlocksPermRX mpl s0)
    (hInv0 : mallocngBudgetPoolInv lim staticIvs ivs0 s0)
    (hLf : VerifiedLibraries.mallocngLib.CodeLoaded mpl sf'.mem)
    (hpprw' : physPlusRw sf' =
      physPlusRw (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0)) :
    let s0' := multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0
    let sf := multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf'
    VerifiedLibraries.mallocngLib.codeRO mpl ∗
      MallocngModelPostEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st' ivs0 s0' sf' ⊢
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st' sf := by
  intro s0' sf
  unfold MallocngModelPostEnv mallocngHookBudgetPool mallocngBudgetPool
    LibsignalBinary.Heap.mallocngBudgetPoolAt
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun ivsf => ?_
  have hpull :
      VerifiedLibraries.mallocngLib.codeRO mpl ∗
        (⌜VerifiedLibraries.Mallocng.MallocngNoOrphanMappings ivs0 ivsf s0'.mem sf'.mem⌝ ∗
          MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st' ivsf sf') =
      ⌜VerifiedLibraries.Mallocng.MallocngNoOrphanMappings ivs0 ivsf s0'.mem sf'.mem⌝ ∗
        (VerifiedLibraries.mallocngLib.codeRO mpl ∗
          MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st' ivsf sf') := by
    sep_ac_rfl
  rw [hpull]
  refine Entails.pure_left fun hNoOrphan => ?_
  have hrxf' : CodeBlocksPermRX mpl sf' := codeBlocksPermRX_of_codeLoaded hLf
  have hrxExit : lim.enforced = true → CodeBlocksPermRX mpl sf := by
    intro henf
    have hvmExit : VmPreserved sf' sf := vmPreserved_hookExit (hrx0 henf) hrxf'
    have heq := codeBlocksPermRX_of_perm_eq (mpl := mpl) hvmExit.2.2.1
    show CodeBlocksPermRXMem mpl sf.mem
    rw [heq]
    exact hrxf'
  have hInvF : mallocngBudgetPoolInv lim staticIvs ivsf sf := by
    intro henf
    have hvm0 : VmPreserved s0 s0' := vmPreserved_hookEntry (hrx0 henf)
    have hvmExit : VmPreserved sf' sf := vmPreserved_hookExit (hrx0 henf) hrxf'
    have hpprw0 : physPlusRw s0' = physPlusRw s0 := by
      unfold physPlusRw; rw [hvm0.2.1, rwBytes_congr hvm0.2.2.1]
    have hpprwExit : physPlusRw sf = physPlusRw sf' := by
      unfold physPlusRw; rw [hvmExit.2.1, rwBytes_congr hvmExit.2.2.1]
    change physPlusRw sf' = physPlusRw s0' at hpprw'
    obtain ⟨⟨hStLen, hStSum, hStVa, hMap0⟩, hPhys0⟩ := hInv0 henf
    refine ⟨⟨hStLen, hStSum, hStVa, fun a haMapF => ?_⟩, ?_⟩
    · have haMapF' : (sf'.mem.perm a).mapped = true := by rwa [← hvmExit.2.2.1 a]
      cases hm0' : (s0'.mem.perm a).mapped with
      | false => exact Or.inr (hNoOrphan a haMapF' (Or.inl hm0'))
      | true =>
        have hm0 : (s0.mem.perm a).mapped = true := by rwa [← hvm0.2.2.1 a]
        exact (hMap0 a hm0).elim Or.inl fun hDyn0 => Or.inr (hNoOrphan a haMapF' (Or.inr hDyn0))
    · rw [hpprwExit, hpprw', hpprw0]; exact hPhys0
  have henvExit :
      MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st' ivsf sf' =
        MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st' ivsf sf := by
    simp only [MallocngModelEnv, sf,
      multiCodeROHookExit_tpidrEl0, multiCodeROHookExit_brkStart, multiCodeROHookExit_brk]
  rw [henvExit]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left
      (@Entails.sepExists_intro (List (BitVec 64 × Nat))
        (fun stIvs => ∃∗ ivs : List (BitVec 64 × Nat),
          ⌜mallocngBudgetPoolInv lim stIvs ivs sf⌝ ∗
          MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st' ivs sf) staticIvs)))
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left
      (@Entails.sepExists_intro (List (BitVec 64 × Nat))
        (fun ivs =>
          ⌜mallocngBudgetPoolInv lim staticIvs ivs sf⌝ ∗
          MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st' ivs sf) ivsf)))
  exact Entails.trans
    (Entails.pure_right hInvF (Entails.pure_right hrxExit (Entails.refl _)))
    (Entails.of_eq (by sep_ac_rfl))

def mallocHookBridgeSpec (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × M.σ) where
  pre := fun (req, sp, st) s0 =>
    ⌜s0.readReg64 .x0 = req ∧ s0.sp = sp⌝ ∗
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
      stackFrameAt sp mallocngStackBytes
  post := fun (req, sp, st) s0 sf =>
    let ok := decide (req.toNat ≤ MallocngMaxAllocSize)
    let st' := if ok then M.step (.alloc req.toNat) st else st
    ⌜AllocCallPreserved s0 sf⌝ ∗
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st' sf ∗
      stackFrameAt sp mallocngStackBytes ∗
      (if ok then
        ⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
          (sf.readReg64 .x0).toNat + req.toNat < 2 ^ 64⌝ ∗
        I.BlockM γ (sf.readReg64 .x0) req.toNat 16 ∗
        memRegion (sf.readReg64 .x0) req.toNat
       else
        ⌜sf.readReg64 .x0 = 0#64⌝)
  onOom := fun (req, _, st) s0 sf =>
    ⌜¬ FitsEvent M lim st (.alloc req.toNat) ∧ OomPreserved s0 sf⌝

def callocHookBridgeSpec (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × BitVec 64 × M.σ) where
  pre := fun (nmemb, size, sp, st) s0 =>
    ⌜s0.readReg64 .x0 = nmemb ∧ s0.readReg64 .x1 = size ∧ s0.sp = sp⌝ ∗
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
      stackFrameAt sp mallocngStackBytes
  post := fun (nmemb, size, sp, st) s0 sf =>
    let total := nmemb.toNat * size.toNat
    let ok := decide (total ≤ MallocngMaxAllocSize)
    let st' := if ok then M.step (.alloc total) st else st
    ⌜AllocCallPreserved s0 sf⌝ ∗
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st' sf ∗
      stackFrameAt sp mallocngStackBytes ∗
      (if ok then
        ⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
          (sf.readReg64 .x0).toNat + total < 2 ^ 64⌝ ∗
        I.BlockM γ (sf.readReg64 .x0) total 16 ∗
        (sf.readReg64 .x0 ↦ₛ List.replicate total 0#8)
       else
        ⌜sf.readReg64 .x0 = 0#64⌝)
  onOom := fun (nmemb, size, _, st) s0 sf =>
    ⌜¬ FitsEvent M lim st (.alloc (nmemb.toNat * size.toNat)) ∧ OomPreserved s0 sf⌝

def freeHookBridgeSpec (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × BitVec 64 × M.σ) where
  pre := fun (p, n, align, sp, st) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ s0.sp = sp ∧
      (if p = 0#64 then n = 0 else 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64)⌝ ∗
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
      (if p = 0#64 then emp else I.BlockM γ p n (max align 16) ∗ memRegion p n) ∗
      stackFrameAt sp mallocngStackBytes
  post := fun (p, n, align, sp, st) s0 sf =>
    let st' := if p == 0#64 then st else M.step (.free align n) st
    ⌜AllocCallPreserved s0 sf⌝ ∗
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st' sf ∗
      stackFrameAt sp mallocngStackBytes

theorem oomCond_to_oomPreserved_hookExit
    {svc : State → State} {stepB : Nat}
    {mpl : Obj.MultiPlacement} {i : Nat} {entry : BitVec 64} {s0 sf' : State}
    (hOom : MallocngStepOomCond svc stepB
      (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0) sf') :
    OomPreserved s0 (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf') := by
  have hfs := hOom.1
  have htr := hOom.2.1
  have hsig := hOom.2.2.1
  simp only [multiCodeROHookEntry_fs, multiCodeROHookEntry_trace, multiCodeROHookEntry_sigActions]
    at hfs htr hsig
  exact ⟨by simpa [multiCodeROHookExit_fs] using hfs,
    by simpa [multiCodeROHookExit_trace] using htr,
    by simpa [multiCodeROHookExit_sigActions] using hsig⟩

theorem hook_oom_false {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {stepB : Nat}
    {staticIvs ivs0 : List (BitVec 64 × Nat)}
    {mpl : Obj.MultiPlacement} {i : Nat} {entry : BitVec 64} {s0 sf' : State}
    (hFit : FitsStep lim stepB (M.maxDynIvs st) (M.footprint st))
    (hrx0 : lim.enforced = true → CodeBlocksPermRX mpl s0)
    (hInv0 : mallocngBudgetPoolInv lim staticIvs ivs0 s0)
    (hIvsLen : ivs0.length ≤ M.maxDynIvs st)
    (hIvsSum : (ivs0.map Prod.snd).sum ≤ M.footprint st)
    (hpprw' : physPlusRw sf' =
      physPlusRw (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0))
    (hOom : MallocngStepOomCond allocMallocng stepB
      (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0) sf') : False := by
  have hvm0 : VmPreserved s0 (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0) :=
    vmPreserved_hookEntry (hrx0 hFit.1)
  have hInv0' :
      mallocngBudgetPoolInv lim staticIvs ivs0
        (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0) := by
    intro henf
    obtain ⟨⟨hStLen, hStSum, hStVa, hMap0⟩, hPhys0⟩ := hInv0 henf
    have hpprw0 :
        physPlusRw (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0) =
          physPlusRw s0 := by
      unfold physPlusRw; rw [hvm0.2.1, rwBytes_congr hvm0.2.2.1]
    refine ⟨⟨hStLen, hStSum, hStVa, fun a ha => hMap0 a (by rwa [← hvm0.2.2.1 a])⟩, hpprw0.symm ▸ hPhys0⟩
  exact mallocng_oom_false hFit hInv0' hIvsLen hIvsSum hpprw' hOom

theorem mallocngHookBudgetPool_mapped_lt_userVa {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {s0 : State} {Rest : SepProp} {a : BitVec 64}
    (henf : lim.enforced = true)
    (hsat : s0.mem ⊨ mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗ Rest)
    (hmap : (s0.mem.perm a).mapped = true) :
    a.toNat < Arm64.USER_VA_LIMIT := by
  unfold mallocngHookBudgetPool at hsat
  have hsat' : s0.mem ⊨
      mallocngBudgetPool M I γ mpl tp brkStart lim st s0 ∗
        (VerifiedLibraries.mallocngLib.codeRO mpl ∗
          ⌜lim.enforced = true → CodeBlocksPermRX mpl s0⌝ ∗ Rest) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsat
  exact mallocngBudgetPool_mapped_lt_userVa hS henf hsat' hmap

theorem fineHookRustCliAllocBudget_mapped_lt_userVa
    {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : fineCostModel.σ} {s0 : State} {Rest : SepProp} {a : BitVec 64}
    (henf : lim.enforced = true)
    (hsat : s0.mem ⊨ (fineHookRustCliAllocBudget γ mpl tp brkStart).pool lim st s0 ∗ Rest)
    (hmap : (s0.mem.perm a).mapped = true) :
    a.toNat < Arm64.USER_VA_LIMIT :=
  mallocngHookBudgetPool_mapped_lt_userVa fineCostModelSound henf hsat hmap

end LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
