/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Spec.Top
public import VerifiedLibraries.Mallocng.Proofs.Accounting
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocHelpers
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocEntryProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedCallocProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAlignedAllocProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedPosixMemalignProof
public import VerifiedLibraries.RustStd.Proofs.MallocngInst
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
public import ProofLib.MallocngBridge
public import ProofLib.SyscallModels
public import ProofLib.ProgramReflection
public import ProofLib.CType
public import ProofLib.StdStartup.MemOps
public import ProofLib.SepLogic.WP.StepsProcess
public import LibsignalBinary.Heap.IfaceBudget

/-!
# Cost-Model-Parametric `mallocng` Budget Bridge

Instantiates `LibsignalBinary.Heap.IfaceBudget` over `VerifiedLibraries.mallocngLib`:
* `coarseCostModel` and `MallocngCostModelSound` constructors from `MallocngIfaceFacts` and placed
  entry contracts;
* `allocMallocng` syscall lifting (`runPlacedAllocCall`) conserving `physPlusRw` across both
  `.Running` and `.OutOfMemory` outcomes;
* `VmPreserved`-preserving `memcpy` (`allocMemcpyVmSpec`);
* `mallocngRustCliAllocBudgetAt`, non-OOM discharge (`mallocng_oom_false`), and program-level
  budgeted C allocator contracts (`MallocngProgBudgetCContracts`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap

open Arm64 Arm64.CType Arm64.Obj ProofLib.SepLogic ProofLib.ProgramReflection ProofLib.StdStartup
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open VerifiedLibraries.Mallocng (
  IsPow2Align MallocngAddrs MallocngAuxvAt MallocngBlock MallocngBrkStartWf MallocngBudget
  MallocngCallAccounting MallocngEnv MallocngFreeableBlock MallocngHasGap MallocngIface
  MallocngIfaceFacts MallocngInIntervals MallocngInitBlock MallocngLinearFactor
  MallocngBaseOverhead MallocngMappedDelta MallocngMaxAllocSize MallocngMinBlockCost
  MallocngMremapStep MallocngNoGapOrPhys MallocngNoOrphanMappings MallocngOomCond
  MallocngPlacedEntryContracts MallocngPostEnv MallocngProcPreserved MallocngRuntime
  MallocngSanitizedSvc MallocngStartupResources MallocngStepBound MallocngSvcValid
  MallocngTopFacts MallocngZeroedBlock MaxAlignedAllocAlign MALLOCNG_SYS_MREMAP
  alignedAllocAlignOk isPow2Align
  mallocngAddrsOfPlacement mallocngAlignedAllocOk mallocngAlignedAllocSpec
  mallocngAlignedBudget mallocngAlignedEffSize mallocngAllocBudget mallocngBlockProg
  mallocngCallocSpec mallocngFreeBudget mallocngFreeSpec mallocngMallocSpec
  mallocngMultiEntryOk mallocngPosixMemalignOk mallocngPosixMemalignRet
  mallocngPosixMemalignSpec mallocngReallocBudget mallocngReallocSpec mallocngStackBytes
  mallocngZeroBudget
)
open VerifiedLibraries.Mallocng.Proofs (
  AllocSlotPlacedFullStmt DefaultMallocPlacedTightStmt HooksUnfetched LibcFreePlacedStmt
  LibcMallocImplPlaced24Stmt LibcMallocImplPlacedTightKStmt LibcMallocImplPlacedTightStmt
  ProgContainsMallocng
  alignedAllocPlaced_entry_tight_ok callocPlaced_entry_tight_ok
  libcMallocImplPlacedSpec24 libcMallocImplPlacedSpec24B2
  mallocImplSuccessBody24 mallocImplSuccessPost24
  mallocPlaced_entry_uncond_ok
  mallocngAlignedAllocTightSpec mallocngBlockTokenK_to_token mallocngCallocTightSpec
  mallocngPosixMemalignTightSpec
  memRegion_entails_exists_pointsToBytes memcpySymWords
  memcpy_allInstrs_noSvc_noMsr memcpy_pureWords_ok
  placed_allocMeta_full_ok placed_allocSlot_full_ok
  placed_defaultMalloc_tight_of_impl placed_libcMallocImpl24B2_uncond_ok
  placed_libcMallocImpl_tightK_uncond_ok placed_libcMallocImpl_tight_uncond_ok
  posixMemalignPlaced_entry_tight_ok reallocPlaced_entry_ok
  steps_prog_of_pureMem_outcome withCL
)
open VerifiedLibraries.RustStd (
  MallocngCEntryAddrs allocCallPreserved_of_mallocngProcPreserved allocMemcpySpec
  mallocngPlacedCAddrs mallocngRustCliIfaceFacts
)

/-! ## Coarse `AllocCostModel` and `MallocngCostModelSound` Constructors -/

def coarseStep : AllocEvent → MallocngBudget → MallocngBudget
  | .alloc req, b => mallocngAllocBudget true req b
  | .aligned align req, b => mallocngAlignedBudget true align req b
  | .free _ n, b => mallocngFreeBudget false n b
  | .realloc _ oldSize newSize, b => mallocngReallocBudget true (some (oldSize, [])) newSize b

def coarseStepReserve : AllocEvent → MallocngBudget → Nat
  | .alloc req, b => MallocngStepBound req b.peakCount
  | .aligned align req, b => MallocngStepBound (mallocngAlignedEffSize align req) b.peakCount
  | .free _ _, b => MallocngStepBound 0 b.peakCount
  | .realloc _ _ newSize, b => MallocngStepBound (newSize + MaxAlignedAllocAlign) b.peakCount

private theorem coarseStep_peakCost_mono (ev : AllocEvent) (b : MallocngBudget) :
    b.peakCost ≤ (coarseStep ev b).peakCost := by
  cases ev <;>
    simp only [coarseStep, mallocngAllocBudget, mallocngAlignedBudget,
      mallocngFreeBudget, mallocngReallocBudget, ↓reduceIte, Bool.false_eq_true] <;>
    omega

private theorem coarseStep_peakCount_mono (ev : AllocEvent) (b : MallocngBudget) :
    b.peakCount ≤ (coarseStep ev b).peakCount := by
  cases ev <;>
    simp only [coarseStep, mallocngAllocBudget, mallocngAlignedBudget,
      mallocngFreeBudget, mallocngReallocBudget, ↓reduceIte, Bool.false_eq_true] <;>
    omega

private theorem mallocngStepBound_mono_count {r p₁ p₂ : Nat} (hp : p₁ ≤ p₂) :
    MallocngStepBound r p₁ ≤ MallocngStepBound r p₂ := by
  unfold MallocngStepBound
  have hmul : 4096 * p₁ ≤ 4096 * p₂ := Nat.mul_le_mul_left 4096 hp
  omega

/-- Coarse `AllocCostModel` backed by `VerifiedLibraries.Mallocng.MallocngBudget`
    (`32 MiB + 48 * peakCost`, `48 + 2 * peakCount`, and `MallocngStepBound`, charging
    `MaxAlignedAllocAlign = 2 GiB` in `stepReserve` on `.realloc`). -/
def coarseCostModel : AllocCostModel where
  σ := MallocngBudget
  init := mallocngZeroBudget
  step := coarseStep
  footprint b := MallocngBaseOverhead + MallocngLinearFactor * b.peakCost
  maxDynIvs b := 48 + 2 * b.peakCount
  stepReserve := coarseStepReserve
  liveBytes b := b.liveCost
  footprint_mono ev b := by
    have hmul : MallocngLinearFactor * b.peakCost ≤
        MallocngLinearFactor * (coarseStep ev b).peakCost :=
      Nat.mul_le_mul_left MallocngLinearFactor (coarseStep_peakCost_mono ev b)
    omega
  maxDynIvs_mono ev b := by
    have hp := coarseStep_peakCount_mono ev b
    omega
  stepReserve_mono ev₀ ev b := by
    have hp := coarseStep_peakCount_mono ev b
    cases ev₀ <;> exact mallocngStepBound_mono_count hp
  req_le_stepReserve ev b := by
    cases ev with
    | alloc req =>
      dsimp only [AllocEvent.reqBytes, coarseStepReserve]
      unfold MallocngStepBound pageAlignUp PAGE_SIZE MallocngBaseOverhead
      omega
    | aligned align req =>
      dsimp only [AllocEvent.reqBytes, coarseStepReserve]
      unfold MallocngStepBound pageAlignUp PAGE_SIZE MallocngBaseOverhead
      omega
    | free _ _ =>
      exact Nat.zero_le _
    | realloc _ _ newSize =>
      dsimp only [AllocEvent.reqBytes, coarseStepReserve]
      unfold MallocngStepBound pageAlignUp PAGE_SIZE MallocngBaseOverhead
      omega
  liveBytes_free_le _ n b := by
    simp only [coarseStep, mallocngFreeBudget, Bool.false_eq_true, ↓reduceIte]
    omega

def coarseCostModelIface (J : MallocngIface) : MallocngCostModelIface coarseCostModel where
  HeapM := J.MallocngHeap
  CoreM := J.MallocngCore
  BlockM γ p n _ := J.Block γ p n
  block_noWrap γ p n _ := J.block_noWrap γ p n

private theorem withCodeLoaded_reparam {α β : Type} (lib : Obj.MultiPlacedLib)
    (mpl : Obj.MultiPlacement) {P : Program} {entry : BitVec 64}
    {s1 : Spec α} {s2 : Spec β} (f : α → β)
    (hpre : ∀ x, s1.pre x = s2.pre (f x))
    (hpost : ∀ x, s1.post x = s2.post (f x))
    (hpan : ∀ x, s1.onPanic x = s2.onPanic (f x))
    (hex : ∀ x, s1.onExit x = s2.onExit (f x))
    (hoom : ∀ x, s1.onOom x = s2.onOom (f x))
    (h : subroutine_ok P entry (lib.withCodeLoaded mpl s2)) :
    subroutine_ok P entry (lib.withCodeLoaded mpl s1) := by
  have hs : s1 = Spec.mk
      (fun x => s2.pre (f x))
      (fun x => s2.post (f x))
      (fun x => s2.onPanic (f x))
      (fun x => s2.onExit (f x))
      (fun x => s2.onOom (f x)) := by
    cases s1
    simp only [Spec.mk.injEq]
    exact ⟨funext hpre, funext hpost, funext hpan, funext hex, funext hoom⟩
  rw [hs]
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hp hsp _
  exact subroutine_ok.mono_outcome h (f x) R s0 hpc hrun hp hsp fun _ hout => hout

private theorem mallocngMultiEntryOk_reparam {S₁ S₂ α β : Type}
    [ToBaseSpec S₁ α] [ToBaseSpec S₂ β]
    {mpl : Obj.MultiPlacement} {svc : State → State} {fnName : String}
    {spec₁ : S₁} {spec₂ : S₂} (f : α → β)
    (hpre : ∀ b x, (ToBaseSpec.toSpec spec₁ b).pre x = (ToBaseSpec.toSpec spec₂ b).pre (f x))
    (hpost : ∀ b x, (ToBaseSpec.toSpec spec₁ b).post x = (ToBaseSpec.toSpec spec₂ b).post (f x))
    (hpan : ∀ b x, (ToBaseSpec.toSpec spec₁ b).onPanic x = (ToBaseSpec.toSpec spec₂ b).onPanic (f x))
    (hex : ∀ b x, (ToBaseSpec.toSpec spec₁ b).onExit x = (ToBaseSpec.toSpec spec₂ b).onExit (f x))
    (hoom : ∀ b x, (ToBaseSpec.toSpec spec₁ b).onOom x = (ToBaseSpec.toSpec spec₂ b).onOom (f x))
    (h : mallocngMultiEntryOk mpl svc fnName spec₂) :
    mallocngMultiEntryOk mpl svc fnName spec₁ := by
  rcases h with ⟨hexp, i, off, hfn, hsub⟩
  refine ⟨hexp, i, off, hfn, ?_⟩
  exact withCodeLoaded_reparam VerifiedLibraries.mallocngLib mpl f
    (hpre (mpl.base i)) (hpost (mpl.base i)) (hpan (mpl.base i))
    (hex (mpl.base i)) (hoom (mpl.base i)) hsub

private def projReallocOldBlk :
    Option (Nat × Nat × List (BitVec 8)) → Option (Nat × List (BitVec 8))
  | none => none
  | some (sz, _, bs) => some (sz, bs)

theorem coarseModelPlacedEntries_of_placed {J : MallocngIface}
    {mpl : Obj.MultiPlacement} {svc : State → State}
    (h : MallocngPlacedEntryContracts J mpl svc) :
    MallocngModelPlacedEntryContracts coarseCostModel (coarseCostModelIface J) mpl svc where
  malloc_ok γ := by
    refine mallocngMultiEntryOk_reparam
      (spec₂ := mallocngMallocSpec J svc γ (mallocngAddrsOfPlacement mpl)) id
      (fun _ _ => rfl)
      (fun _ ⟨req, _, _, _, _, _⟩ => by
        dsimp only [mallocngModelMallocSpec, mallocngMallocSpec, ToBaseSpec.toSpec, id]
        cases decide (req.toNat ≤ MallocngMaxAllocSize) <;> rfl)
      (fun _ _ => rfl)
      (fun _ _ => rfl)
      (fun _ ⟨req, _, _, _, _, _⟩ => by
        dsimp only [mallocngModelMallocSpec, mallocngMallocSpec, ToBaseSpec.toSpec, id]
        cases decide (req.toNat ≤ MallocngMaxAllocSize) <;> rfl)
      (h.malloc_ok γ)
  free_ok γ := by
    refine mallocngMultiEntryOk_reparam
      (spec₂ := mallocngFreeSpec J γ (mallocngAddrsOfPlacement mpl))
      (fun (p, sp, n, _align, tp, brkStart, st, ivs0) => (p, sp, n, tp, brkStart, st, ivs0))
      (fun _ ⟨_, _, _, _, _, _, _, _⟩ => rfl)
      (fun _ ⟨p, _, _, _, _, _, _, _⟩ => by
        dsimp only [mallocngModelFreeSpec, mallocngFreeSpec, ToBaseSpec.toSpec]
        cases p == 0#64 <;> rfl)
      (fun _ _ => rfl)
      (fun _ _ => rfl)
      (fun _ _ => rfl)
      (h.free_ok γ)
  calloc_ok γ := by
    refine mallocngMultiEntryOk_reparam
      (spec₂ := mallocngCallocSpec J svc γ (mallocngAddrsOfPlacement mpl)) id
      (fun _ _ => rfl)
      (fun _ ⟨nmemb, size, _, _, _, _⟩ => by
        dsimp only [mallocngModelCallocSpec, mallocngCallocSpec, ToBaseSpec.toSpec, id]
        cases decide (nmemb.toNat * size.toNat ≤ MallocngMaxAllocSize) <;> rfl)
      (fun _ _ => rfl)
      (fun _ _ => rfl)
      (fun _ ⟨nmemb, size, _, _, _, _⟩ => by
        dsimp only [mallocngModelCallocSpec, mallocngCallocSpec, ToBaseSpec.toSpec, id]
        cases decide (nmemb.toNat * size.toNat ≤ MallocngMaxAllocSize) <;> rfl)
      (h.calloc_ok γ)
  realloc_ok γ := by
    refine mallocngMultiEntryOk_reparam
      (spec₂ := mallocngReallocSpec J svc γ (mallocngAddrsOfPlacement mpl))
      (fun (p, newSize, sp, oldBlk, tp, brkStart, st, ivs0) =>
        (p, newSize, sp, projReallocOldBlk oldBlk, tp, brkStart, st, ivs0))
      (fun _ ⟨_, _, _, oldBlk, _, _, _, _⟩ => by
        dsimp only [mallocngModelReallocSpec, mallocngReallocSpec, ToBaseSpec.toSpec]
        cases oldBlk <;> rfl)
      (fun _ ⟨_, newSize, _, oldBlk, _, _, _, _⟩ => by
        dsimp only [mallocngModelReallocSpec, mallocngReallocSpec, ToBaseSpec.toSpec]
        cases decide (newSize.toNat ≤ MallocngMaxAllocSize) <;> cases oldBlk <;> rfl)
      (fun _ _ => rfl)
      (fun _ _ => rfl)
      (fun _ ⟨_, newSize, _, oldBlk, _, _, _, _⟩ => by
        dsimp only [mallocngModelReallocSpec, mallocngReallocSpec, ToBaseSpec.toSpec]
        cases decide (newSize.toNat ≤ MallocngMaxAllocSize) <;> cases oldBlk <;> rfl)
      (h.realloc_ok γ)
  alignedAlloc_ok γ := by
    refine mallocngMultiEntryOk_reparam
      (spec₂ := mallocngAlignedAllocSpec J svc γ (mallocngAddrsOfPlacement mpl)) id
      (fun _ _ => rfl)
      (fun _ ⟨align, len, _, _, _, _⟩ => by
        dsimp only [mallocngModelAlignedAllocSpec, mallocngAlignedAllocSpec, ToBaseSpec.toSpec, id]
        cases mallocngAlignedAllocOk align len <;> rfl)
      (fun _ _ => rfl)
      (fun _ _ => rfl)
      (fun _ ⟨align, len, _, _, _, _⟩ => by
        dsimp only [mallocngModelAlignedAllocSpec, mallocngAlignedAllocSpec, ToBaseSpec.toSpec, id]
        cases mallocngAlignedAllocOk align len <;> rfl)
      (h.alignedAlloc_ok γ)
  posixMemalign_ok γ := by
    refine mallocngMultiEntryOk_reparam
      (spec₂ := mallocngPosixMemalignSpec J svc γ (mallocngAddrsOfPlacement mpl)) id
      (fun _ _ => rfl)
      (fun _ ⟨_, align, len, _, _, _, _⟩ => by
        dsimp only [mallocngModelPosixMemalignSpec, mallocngPosixMemalignSpec, ToBaseSpec.toSpec, id]
        cases mallocngPosixMemalignOk align len <;> rfl)
      (fun _ _ => rfl)
      (fun _ _ => rfl)
      (fun _ ⟨_, align, len, _, _, _, _⟩ => by
        dsimp only [mallocngModelPosixMemalignSpec, mallocngPosixMemalignSpec, ToBaseSpec.toSpec, id]
        cases mallocngPosixMemalignOk align len <;> rfl)
      (h.posixMemalign_ok γ)

/-- Construct `MallocngCostModelSound coarseCostModel (coarseCostModelIface J)` from
    `MallocngIfaceFacts J` and placed C entry contracts. -/
theorem coarseCostModelSound_of_if_entries {J : MallocngIface}
    (hIf : MallocngIfaceFacts J)
    (hEntries : ∀ (mpl : Obj.MultiPlacement) (svc : State → State),
      VerifiedLibraries.mallocngLib.Placeable mpl →
      MallocngSvcValid svc →
      MallocngPlacedEntryContracts J mpl svc) :
    MallocngCostModelSound coarseCostModel (coarseCostModelIface J) where
  init := hIf.init
  init_resources := hIf.init_resources
  heap_split_runtime := hIf.heap_split_runtime
  block_nonnull γ p n _ := hIf.block_nonnull γ p n
  block_exclusive γ p₁ n₁ _ p₂ n₂ _ := hIf.block_exclusive γ p₁ n₁ p₂ n₂
  heap_footprint_bound γ A tp brkStart brk st ivs h hH :=
    (hIf.heap_footprint_bound γ A tp brkStart brk st ivs h hH).2.1
  entries_ok mpl svc hPl hSvc :=
    coarseModelPlacedEntries_of_placed (hEntries mpl svc hPl hSvc)

/-- Construct `MallocngCostModelSound coarseCostModel (coarseCostModelIface J)` from `MallocngTopFacts J`. -/
theorem coarseCostModelSound_of_topFacts {J : MallocngIface}
    (hTop : MallocngTopFacts J) :
    MallocngCostModelSound coarseCostModel (coarseCostModelIface J) :=
  coarseCostModelSound_of_if_entries hTop.toMallocngIfaceFacts hTop.entries_ok

/-- Construct `MallocngCostModelSound coarseCostModel` over the sealed `mallocngIface` from placed
    entry contracts (assembling `MallocngIfaceFacts` inside `module` space via
    `mallocngRustCliIfaceFacts`). -/
theorem coarseCostModelSound_of_placedEntries
    (hEntries : ∀ (mpl : Obj.MultiPlacement) (svc : State → State),
      VerifiedLibraries.mallocngLib.Placeable mpl →
      MallocngSvcValid svc →
      MallocngPlacedEntryContracts VerifiedLibraries.Mallocng.Proofs.mallocngIface mpl svc) :
    MallocngCostModelSound coarseCostModel
      (coarseCostModelIface VerifiedLibraries.Mallocng.Proofs.mallocngIface) :=
  coarseCostModelSound_of_if_entries mallocngRustCliIfaceFacts hEntries

private theorem placed_libcMallocImpl24_module_ok : LibcMallocImplPlaced24Stmt := by
  intro _ γ tp brkStart b ivs0 req
  have hB2 :=
    placed_libcMallocImpl24B2_uncond_ok
      placed_allocMeta_full_ok
      (placed_allocSlot_full_ok placed_allocMeta_full_ok)
      γ tp brkStart b ivs0 req
  refine subroutine_ok_mono hB2 (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
    (hoom := fun _ _ _ _ ho => ?_)
  · dsimp only [libcMallocImplPlacedSpec24B2, libcMallocImplPlacedSpec24, withCL] at hq ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hq
    refine sepConj_mono_left ?_
    by_cases hReq : req ≤ MallocngMaxAllocSize
    · simp only [hReq, ↓reduceIte]
      unfold mallocImplSuccessPost24 mallocImplSuccessBody24
      refine sepConj_mono (Entails.refl _) (sepConj_mono_right ?_)
      apply Entails.sepExists_elim; intro p
      apply Entails.sepExists_elim; intro bs
      apply Entails.sepExists_elim; intro st'
      refine Entails.trans ?_ (Entails.sepExists_intro p)
      refine Entails.trans ?_ (Entails.sepExists_intro bs)
      refine Entails.trans ?_ (Entails.sepExists_intro st')
      apply Entails.pure_left
      rintro ⟨h1, h2, h3, h4, h5, h6, h7, g', hg', idx, hIdx, hSl, hOff, hMm, hSc24_26, _hSc24, hSc63⟩
      exact Entails.pure_right
        ⟨h1, h2, h3, h4, h5, h6, h7, g', hg', idx, hIdx, hSl, hOff, hMm, hSc24_26, hSc63⟩
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (mallocngBlockTokenK_to_token γ p req 0)))))
    · simp only [hReq, ↓reduceIte]
      exact Entails.refl _
  · dsimp only [libcMallocImplPlacedSpec24B2, libcMallocImplPlacedSpec24, withCL] at ho ⊢
    exact ho

private theorem alignedAllocPlaced_entry_ok (hMalloc : LibcMallocImplPlaced24Stmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "aligned_alloc"
      (mallocngAlignedAllocSpec VerifiedLibraries.Mallocng.Proofs.mallocngIface svc γ
        (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ := alignedAllocPlaced_entry_tight_ok hMalloc mpl svc hPl hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_mono hsub (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
    (hoom := fun _ _ _ _ ho => ?_)⟩
  · dsimp only [Obj.MultiPlacedLib.withCodeLoaded, mallocngAlignedAllocTightSpec,
      mallocngAlignedAllocSpec, ToBaseSpec.toSpec] at hq ⊢
    simp only [sepConj_assoc] at hq ⊢
    rw [satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, VerifiedLibraries.Mallocng.Proofs.MallocngCallAccounting.tight_to_step hq.1.2⟩,
      hq.2⟩
  · dsimp only [Obj.MultiPlacedLib.withCodeLoaded, mallocngAlignedAllocTightSpec,
      mallocngAlignedAllocSpec, ToBaseSpec.toSpec] at ho ⊢
    rw [satisfies_pure_sepConj] at ho ⊢
    exact ⟨ho.1.to_oomCond (Nat.le_refl _), ho.2⟩

private theorem posixMemalignPlaced_entry_ok (hMalloc : LibcMallocImplPlaced24Stmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "posix_memalign"
      (mallocngPosixMemalignSpec VerifiedLibraries.Mallocng.Proofs.mallocngIface svc γ
        (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ := posixMemalignPlaced_entry_tight_ok hMalloc mpl svc hPl hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_mono hsub (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
    (hoom := fun _ _ _ _ ho => ?_)⟩
  · dsimp only [Obj.MultiPlacedLib.withCodeLoaded, mallocngPosixMemalignTightSpec,
      mallocngPosixMemalignSpec, ToBaseSpec.toSpec] at hq ⊢
    simp only [sepConj_assoc] at hq ⊢
    rw [satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.1,
      VerifiedLibraries.Mallocng.Proofs.MallocngCallAccounting.tight_to_step hq.1.2.2⟩, hq.2⟩
  · dsimp only [Obj.MultiPlacedLib.withCodeLoaded, mallocngPosixMemalignTightSpec,
      mallocngPosixMemalignSpec, ToBaseSpec.toSpec] at ho ⊢
    rw [satisfies_pure_sepConj] at ho ⊢
    exact ⟨ho.1.to_oomCond (Nat.le_refl _), ho.2⟩

private theorem callocPlaced_entry_ok (hDefMalloc : DefaultMallocPlacedTightStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "calloc"
      (mallocngCallocSpec VerifiedLibraries.Mallocng.Proofs.mallocngIface svc γ
        (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ := callocPlaced_entry_tight_ok hDefMalloc mpl svc hPl hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_mono hsub (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
    (hoom := fun _ _ _ _ ho => ?_)⟩
  · dsimp only [Obj.MultiPlacedLib.withCodeLoaded, mallocngCallocTightSpec, mallocngCallocSpec,
      ToBaseSpec.toSpec] at hq ⊢
    simp only [sepConj_assoc] at hq ⊢
    rw [satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, VerifiedLibraries.Mallocng.Proofs.MallocngCallAccounting.tight_to_step hq.1.2⟩,
      hq.2⟩
  · dsimp only [Obj.MultiPlacedLib.withCodeLoaded, mallocngCallocTightSpec, mallocngCallocSpec,
      ToBaseSpec.toSpec] at ho ⊢
    rw [satisfies_pure_sepConj] at ho ⊢
    exact ⟨ho.1.to_oomCond (Nat.le_refl _), ho.2⟩

/-- Pure-`module` constructor for `MallocngCostModelSound coarseCostModel` over `mallocngIface`:
    assembles `malloc`, `calloc`, `realloc`, `aligned_alloc`, and `posix_memalign` from their
    `module` proofs, parameterized only by `LibcFreePlacedStmt` (for `realloc`'s out-of-place `free`
    tail) and the `"free"` placed entry contract. -/
theorem coarseCostModelSound_of_free
    (hFreeInternal : LibcFreePlacedStmt)
    (hFreeEntry : ∀ (mpl : Obj.MultiPlacement) (svc : State → State),
      VerifiedLibraries.mallocngLib.Placeable mpl →
      MallocngSvcValid svc →
      ∀ γ : GhostName,
        mallocngMultiEntryOk mpl svc "free"
          (mallocngFreeSpec VerifiedLibraries.Mallocng.Proofs.mallocngIface γ
            (mallocngAddrsOfPlacement mpl))) :
    MallocngCostModelSound coarseCostModel
      (coarseCostModelIface VerifiedLibraries.Mallocng.Proofs.mallocngIface) := by
  refine coarseCostModelSound_of_placedEntries fun mpl svc hPl hSvc => ?_
  let hSlot : AllocSlotPlacedFullStmt := placed_allocSlot_full_ok placed_allocMeta_full_ok
  let hImpl : LibcMallocImplPlacedTightStmt :=
    placed_libcMallocImpl_tight_uncond_ok placed_allocMeta_full_ok hSlot
  let hImplK : LibcMallocImplPlacedTightKStmt :=
    placed_libcMallocImpl_tightK_uncond_ok placed_allocMeta_full_ok hSlot
  let hDefMalloc : DefaultMallocPlacedTightStmt :=
    placed_defaultMalloc_tight_of_impl hImpl
  exact
    { malloc_ok :=
        mallocPlaced_entry_uncond_ok placed_allocMeta_full_ok hSlot mpl svc hPl hSvc
      free_ok := hFreeEntry mpl svc hPl hSvc
      calloc_ok := callocPlaced_entry_ok hDefMalloc mpl svc hPl hSvc
      realloc_ok := reallocPlaced_entry_ok hImplK hFreeInternal mpl svc hPl hSvc
      alignedAlloc_ok := alignedAllocPlaced_entry_ok placed_libcMallocImpl24_module_ok mpl svc hPl hSvc
      posixMemalign_ok :=
        posixMemalignPlaced_entry_ok placed_libcMallocImpl24_module_ok mpl svc hPl hSvc }

/-! ## `allocMallocng` Validity, Syscall Lifting, and `runPlacedAllocCall` -/

private theorem execMremap_mremapStep (s : State) : MallocngMremapStep s (execMremap s) := by
  intro hflags hal holdPos hnewPos hnewMax holdFit hrw hanon
  dsimp only [execMremap]
  have hf_flags : (s.readReg64 Reg.x3 != MREMAP_MAYMOVE) = false := by rw [hflags]; decide
  have hf_al : ((s.readReg64 Reg.x0).toNat % PAGE_SIZE != 0 || (s.readReg64 Reg.x2).toNat == 0 ||
      !decide ((s.readReg64 Reg.x2).toNat ≤ 2 ^ 64 - PAGE_SIZE)) = false := by
    have h2 : ((s.readReg64 Reg.x2).toNat == 0) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hnewPos)
    simp [hal, h2, hnewMax]
  have hf_old0 : ((s.readReg64 Reg.x1).toNat == 0) = false :=
    beq_eq_false_iff_ne.mpr (Nat.ne_of_gt holdPos)
  have hf_lim :
      (!decide ((s.readReg64 Reg.x0).toNat + pageAlignUp (s.readReg64 Reg.x1).toNat ≤
        USER_VA_LIMIT)) = false := by
    have hfit' :
        (s.readReg64 Reg.x0).toNat + pageAlignUp (s.readReg64 Reg.x1).toNat ≤ USER_VA_LIMIT := by
      simpa [USER_VA_LIMIT] using holdFit
    simp [hfit']
  have hf_nf : (!s.mem.allPerm (fun p => !p.frozen) (s.readReg64 Reg.x0)
      (pageAlignUp (s.readReg64 Reg.x1).toNat)) = false := by
    have hall : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 Reg.x0)
        (pageAlignUp (s.readReg64 Reg.x1).toNat) = true := by
      rw [Memory.allPerm_iff]; intro i hi
      rw [beq_iff_eq.mp ((Memory.allPerm_iff _ _ _ _).mp hrw i hi)]; decide
    simp [hall]
  have hf_can :
      s.mem.canMap (s.readReg64 Reg.x0) (pageAlignUp (s.readReg64 Reg.x1).toNat) = false := by
    apply Bool.eq_false_iff.mpr; intro hcan
    have hpos_al : 0 < pageAlignUp (s.readReg64 Reg.x1).toNat := by
      unfold pageAlignUp PAGE_SIZE; omega
    have h0_unmap := (Memory.allPerm_iff _ _ _ _).mp hcan 0 hpos_al
    rw [beq_iff_eq.mp ((Memory.allPerm_iff _ _ _ _).mp hrw 0 hpos_al)] at h0_unmap
    revert h0_unmap; decide
  have hf_rw : (!s.mem.allPerm (· == some Perm.rw) (s.readReg64 Reg.x0)
      (pageAlignUp (s.readReg64 Reg.x1).toNat)) = false := by simp [hrw]
  have hf_anon : (!s.mem.allAnon (s.readReg64 Reg.x0)
      (pageAlignUp (s.readReg64 Reg.x1).toNat)) = false := by simp [hanon]
  simp only [hf_flags, hf_al, hf_old0, hf_lim, hf_nf, hf_can, hf_rw, hf_anon,
    Bool.false_eq_true, ↓reduceIte]
  split
  · exact Or.inl rfl
  · cases hsan : sanitizeMmapAddr
        (s.mem.unmapNonFrozen (s.readReg64 Reg.x0) (pageAlignUp (s.readReg64 Reg.x1).toNat))
        (s.oracle.mmap s.oracleIdx) (pageAlignUp (s.readReg64 Reg.x2).toNat) with
    | none => exact Or.inl rfl
    | some newBase =>
      simp only []; split
      · next hphys =>
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hphys
        exact Or.inr (Or.inl ⟨by omega, rfl⟩)
      · obtain ⟨hne, hnbAl, hnbFit, hcan⟩ := sanitizeMmapAddr_spec hsan
        exact Or.inr (Or.inr ⟨newBase, hne, hnbAl, by simpa [USER_VA_LIMIT] using hnbFit, hcan, rfl⟩)

theorem allocMallocng_svcValid : MallocngSvcValid allocMallocng := by
  intro s; refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hx8
    simp [allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable, hx8,
      SYS_BRK, SYS_MPROTECT]
  · intro hx8
    simp [allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable, hx8,
      SYS_MUNMAP, SYS_MPROTECT, SYS_BRK]
  · intro hx8
    simp [allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable, hx8,
      SYS_MMAP, SYS_MPROTECT, SYS_BRK, SYS_MUNMAP, SYS_MREMAP]
  · intro hx8 hx2
    simp [allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable, hx8, hx2,
      SYS_MPROTECT, SYS_BRK, SYS_MUNMAP, SYS_MREMAP, SYS_MMAP]
  · intro hx8
    have heq : allocMallocng s = execMremap s := by
      simp [allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable, hx8,
        MALLOCNG_SYS_MREMAP, SYS_MREMAP, SYS_MPROTECT, SYS_BRK, SYS_MUNMAP]
    rw [heq]; exact execMremap_mremapStep s

theorem allocMallocng_sanitizedSvc : MallocngSanitizedSvc allocMallocng := by
  intro s hrun hx8 hprot hflags hoff hlen hoom
  rw [(allocMallocng_svcValid s).2.2.1 hx8] at hoom
  dsimp only [execMmap] at hoom
  have hf_prot : ((s.readReg64 Reg.x2 != MMAP_PROT_RW && s.readReg64 Reg.x2 != MMAP_PROT_NONE ||
      (s.readReg64 Reg.x3 != MMAP_FLAGS_PRIVATE_ANON &&
        s.readReg64 Reg.x3 != MMAP_FLAGS_PRIVATE_ANON_STACK &&
        s.readReg64 Reg.x3 != MMAP_FLAGS_PRIVATE_ANON_FIXED) ||
      s.readReg64 Reg.x5 != 0#64)) = false := by
    rcases hprot with hp | hp <;> simp [hp, hflags, hoff, MMAP_PROT_NONE, MMAP_PROT_RW,
      MMAP_FLAGS_PRIVATE_ANON, MMAP_FLAGS_PRIVATE_ANON_STACK, MMAP_FLAGS_PRIVATE_ANON_FIXED]
  have h1_pos : 0 < (s.readReg64 Reg.x1).toNat :=
    Nat.pos_of_ne_zero fun h0 => hlen (BitVec.eq_of_toNat_eq (by simpa using h0))
  have hf_len0 : ((s.readReg64 Reg.x1).toNat == 0) = false :=
    beq_eq_false_iff_ne.mpr (Nat.ne_of_gt h1_pos)
  have hf_fix : (s.readReg64 Reg.x3 == MMAP_FLAGS_PRIVATE_ANON_FIXED) = false := by
    rw [hflags]; decide
  simp only [hf_prot, hf_len0, hf_fix, Bool.false_eq_true, ↓reduceIte] at hoom
  cases hsan :
      sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx) (pageAlignUp (s.readReg64 Reg.x1).toNat) with
  | none =>
    left; rintro ⟨gap, hmin, hgapAl, hfit, hcan⟩
    have hpos : 0 < pageAlignUp (s.readReg64 Reg.x1).toNat := by unfold pageAlignUp PAGE_SIZE; omega
    have hal : pageAlignUp (s.readReg64 Reg.x1).toNat % PAGE_SIZE = 0 := by
      unfold pageAlignUp PAGE_SIZE; omega
    obtain ⟨base, hsome⟩ := sanitizeMmapAddr_exists_of_gap
      (s.oracle.mmap s.oracleIdx) hpos hal hmin hgapAl (by simpa [USER_VA_LIMIT] using hfit) hcan
    rw [hsan] at hsome; nomatch hsome
  | some base =>
    rw [hsan] at hoom; dsimp only at hoom; split at hoom
    · simp only [State.status_advancePC, State.status_writeReg64, State.status_nextOracle,
        State.status_setMem, hrun] at hoom
      nomatch hoom
    · split at hoom
      · next hphys =>
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hphys
        exact Or.inr (Nat.lt_of_not_ge hphys)
      · simp only [State.status_advancePC, State.status_writeReg64, State.status_nextOracle,
          State.status_setPhysMemAvail, State.status_setMem, hrun] at hoom
        nomatch hoom

/-- Whenever `allocMallocng s` produces `.Running` or `.OutOfMemory`, it agrees identically with
    `Syscall.standard s`. -/
theorem alloc_eq_standard_of_running_or_oom {s : State}
    (hr : (allocMallocng s).status = .Running ∨ (allocMallocng s).status = .OutOfMemory) :
    allocMallocng s = Syscall.standard s := by
  unfold allocMallocng at hr ⊢
  by_cases hcond : (s.readReg64 Reg.x8 == SYS_MPROTECT && s.readReg64 Reg.x2 != MMAP_PROT_RW) = true
  · simp only [hcond, ↓reduceIte, State.setStatus] at hr
    rcases hr with hr | hr <;> nomatch hr
  · simp only [Bool.not_eq_true] at hcond
    simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hr ⊢
    have hstd : Syscall.standard = execSyscall := rfl
    rw [hstd]
    unfold Syscall.alloc Syscall.dispatch at hr
    cases hfind : Syscall.allocTable.find? (·.1 == s.readReg64 Reg.x8) with
    | none =>
      simp only [hfind, State.setStatus] at hr
      rcases hr with hr | hr <;> nomatch hr
    | some p =>
      rcases p with ⟨nr, fn⟩
      have hmem := List.mem_of_find?_eq_some hfind
      have hpred : (nr == s.readReg64 Reg.x8) = true :=
        List.find?_some (p := fun x : BitVec 64 × (State → State) => x.1 == s.readReg64 Reg.x8) hfind
      have hx8 : s.readReg64 .x8 = nr := (beq_iff_eq.mp hpred).symm
      simp only [Syscall.allocTable, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h | h | h <;> injection h with hnr _ <;> subst hnr
      · rw [alloc_brk s hx8, execSyscall_brk s hx8]
      · rw [alloc_munmap s hx8, execSyscall_munmap s hx8]
      · rw [alloc_mremap s hx8, execSyscall_mremap s hx8]
      · rw [alloc_mmap s hx8, execSyscall_mmap s hx8]
      · rw [alloc_mprotect s hx8, execSyscall_mprotect s hx8]
      · rw [alloc_madvise s hx8]
        unfold execSyscall Syscall.standard Syscall.dispatch Syscall.standardTable
          Syscall.stdioTable Syscall.fileIoOnlyTable Syscall.pollTable Syscall.allocTable
        simp [hx8, SYS_BRK, SYS_MUNMAP, SYS_MREMAP, SYS_MMAP, SYS_MPROTECT, SYS_MADVISE]

private theorem steps_start_running_or_oom {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running ∨ sf.status = .OutOfMemory) :
    s.status = .Running ∨ s.status = .OutOfMemory := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> exact Or.inl ‹_›

/-- Lift `Steps (baseProg.withSvc allocMallocng) s0 sf` to `Steps baseProg s0 sf` whenever `sf`
    ends in `.Running` or `.OutOfMemory`. -/
theorem steps_of_withSvc_alloc_running_or_oom {baseProg : Program} {s0 sf : State}
    (h_base_no : ∀ pc, baseProg.externAt? pc = none)
    (h_base_svc : baseProg.svc = Syscall.standard)
    (h : Steps (baseProg.withSvc allocMallocng) s0 sf)
    (h_end : sf.status = .Running ∨ sf.status = .OutOfMemory) :
    Steps baseProg s0 sf := by
  induction h with
  | refl s => exact Steps.refl s
  | @step s1 s2 s3 h1 hrest ih =>
    have hr2 : s2.status = .Running ∨ s2.status = .OutOfMemory :=
      steps_start_running_or_oom hrest h_end
    have hsteps_rest : Steps baseProg s2 s3 := ih h_end
    have hf_eq : (baseProg.withSvc allocMallocng).fetchMem s1.mem s1.pc =
        baseProg.fetchMem s1.mem s1.pc := by
      unfold Program.fetchMem; rw [Program.withSvc_externAt?]
    cases h1 with
    | @exec inst hr1 hfe =>
      by_cases hsvc0 : inst.isSvc0 = true
      · have hinst : inst = .system false 0#16 := by
          cases inst <;> simp [Instr.isSvc0] at hsvc0
          rcases hsvc0 with ⟨rfl, rfl⟩; rfl
        subst hinst
        have hr_svc :
            (allocMallocng s1).status = .Running ∨ (allocMallocng s1).status = .OutOfMemory := by
          rwa [Program.evalInst_svc0, Program.withSvc_svc, evalSvc_allocMallocng] at hr2
        have hev_eq : (baseProg.withSvc allocMallocng).evalInst (.system false 0#16) s1 =
            baseProg.evalInst (.system false 0#16) s1 := by
          rw [Program.evalInst_svc0, Program.withSvc_svc, evalSvc_allocMallocng,
              Program.evalInst_svc0, h_base_svc, evalSvc_standard,
              alloc_eq_standard_of_running_or_oom hr_svc]
        rw [hev_eq] at hsteps_rest
        exact Steps.step (Step.exec hr1 (hf_eq ▸ hfe)) hsteps_rest
      · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
        have hev_eq : (baseProg.withSvc allocMallocng).evalInst inst s1 =
            baseProg.evalInst inst s1 := by
          rw [evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0,
              evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0]
        rw [hev_eq] at hsteps_rest
        exact Steps.step (Step.exec hr1 (hf_eq ▸ hfe)) hsteps_rest
    | halt_unmapped _ _ _ =>
      cases s1
      rcases hr2 with hr2 | hr2 <;> cases hr2
    | extern _ he _ _ => rw [Program.withSvc_externAt?, h_base_no] at he; nomatch he
    | extern_fault _ he _ => rw [Program.withSvc_externAt?, h_base_no] at he; nomatch he

/-- Placement-generic, hook-stub-compatible (`ProgContainsMallocng P mpl`) call bridge from
    `mallocngMultiEntryOk mpl allocMallocng fnName innerSpec` to `subroutine_ok P entryAddr callerSpec`,
    giving the refinement callbacks `physPlusRw sf = physPlusRw s0` on **both** normal return and
    `.OutOfMemory`. -/
theorem runPlacedAllocCall {S β α : Type} [ToBaseSpec S β]
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    {fnName : String} {entryAddr : BitVec 64}
    {innerSpec : S} {callerSpec : Spec α}
    (hentry : mallocngMultiEntryOk mpl allocMallocng fnName innerSpec)
    (hAddr : VerifiedLibraries.mallocngLib.fnAddr mpl fnName = entryAddr)
    (href : ∀ (x : α) (R : SepProp) (s0 : State) (b_base : BitVec 64),
      (s0.mem ⊨ callerSpec.pre x s0 ∗ R) →
      ∃ (y : β) (R_inner : SepProp),
        (s0.mem ⊨ (ToBaseSpec.toSpec innerSpec b_base).pre y s0 ∗ R_inner) ∧
        (∀ sf : State, physPlusRw sf = physPlusRw s0 →
          (sf.mem ⊨ (ToBaseSpec.toSpec innerSpec b_base).onOom y s0 sf ∗ R_inner) →
          (sf.mem ⊨ callerSpec.onOom x s0 sf ∗ R)) ∧
        (∀ sf : State, physPlusRw sf = physPlusRw s0 → s0.mem.KeepsFrozen sf.mem →
          (sf.mem ⊨ (ToBaseSpec.toSpec innerSpec b_base).post y s0 sf ∗ R_inner) →
          (sf.mem ⊨ callerSpec.post x s0 sf ∗ R)))
    (hNoPanic : ∀ (y : β) (b : BitVec 64) (R' : SepProp) (s0 sf : State),
      sf.status = .Panicked → ¬(sf.mem ⊨ (ToBaseSpec.toSpec innerSpec b).onPanic y s0 sf ∗ R') := by
        intro _ _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (hNoExit : ∀ (y : β) (b : BitVec 64) (code : BitVec 64) (R' : SepProp) (s0 sf : State),
      sf.status = .Exited code →
        ¬(sf.mem ⊨ (ToBaseSpec.toSpec innerSpec b).onExit y code s0 sf ∗ R') := by
        intro _ _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok P entryAddr callerSpec := by
  obtain ⟨_hexp, i, _off, hlookup, hsub_blk⟩ := hentry
  obtain ⟨hi, _⟩ := Obj.lookupBlockSym_some hlookup
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hclP
  rw [← hAddr] at hpc
  have hclLib : VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem :=
    hP.codeLoaded s0.mem hclP
  have hcl_i : (mallocngBlockProg mpl i allocMallocng).CodeLoaded s0.mem :=
    (hclLib i hi).of_base_code rfl rfl
  obtain ⟨y, R_inner, hpre_inner, hOomMap, hPostMap⟩ := href x R s0 (mpl.base i) hpre
  have hpre_wcl : s0.mem ⊨
      (VerifiedLibraries.mallocngLib.withCodeLoaded mpl
        (ToBaseSpec.toSpec innerSpec (mpl.base i))).pre y s0 ∗ R_inner := by
    show s0.mem ⊨
      ((ToBaseSpec.toSpec innerSpec (mpl.base i)).pre y s0 ∗
        ⌜VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem⌝) ∗ R_inner
    rw [sepConj_comm _ ⌜_⌝, pure_sepConj_of_true hclLib]
    exact hpre_inner
  obtain ⟨sf, hsteps_blk, hout⟩ :=
    subroutine_ok_elim_steps_outcome hsub_blk y R_inner s0 hpc hrun hpre_wcl hsp hcl_i
  have hblk_no : ∀ pc, (mallocngBlockProg mpl i allocMallocng).externAt? pc = none := by
    intro pc
    simp [mallocngBlockProg, Obj.MultiPlacedLib.blockProgram, Obj.PlacedLib.program,
      Program.externAt?, Program.hookAtOff?]
  have hpure_no : ∀ pc, Program.pureMem.externAt? pc = none := fun _ => rfl
  have hsteps_alloc : Steps (Program.pureMem.withSvc allocMallocng) s0 sf :=
    steps_withSvc_alloc_of_noHooks hblk_no rfl hpure_no hsteps_blk
  have hpprw : physPlusRw sf = physPlusRw s0 :=
    physPlusRw_steps_withSvc_alloc hpure_no hsteps_alloc
  have hkf : s0.mem.KeepsFrozen sf.mem := hsteps_alloc.keepsFrozen
  rcases hout with ⟨hret, hcc, hpost_wcl⟩ | ⟨hp_st, hp_wcl⟩ | ⟨code, he_st, he_wcl⟩ | ⟨ho_st, ho_wcl⟩
  · have hsteps_pm : Steps Program.pureMem s0 sf :=
      steps_of_withSvc_alloc_running_or_oom hpure_no rfl hsteps_alloc (Or.inl hret.2.2)
    have hsteps_P : Steps P s0 sf :=
      steps_prog_of_pureMem_outcome hP.svc_eq (hP.hooks_unfetched s0.mem hclP)
        (Memory.KeepsFrozen.refl s0.mem) hsteps_pm (Or.inl hret.2.2)
    have hpost_inner : sf.mem ⊨ (ToBaseSpec.toSpec innerSpec (mpl.base i)).post y s0 sf ∗ R_inner :=
      hpost_wcl
    exact reaches_outcome_steps hsteps_P
      (reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hPostMap sf hpprw hkf hpost_inner⟩))
  · have hp_inner : sf.mem ⊨ (ToBaseSpec.toSpec innerSpec (mpl.base i)).onPanic y s0 sf ∗ R_inner :=
      hp_wcl
    exact False.elim (hNoPanic y (mpl.base i) R_inner s0 sf hp_st hp_inner)
  · have he_inner :
        sf.mem ⊨ (ToBaseSpec.toSpec innerSpec (mpl.base i)).onExit y code s0 sf ∗ R_inner :=
      he_wcl
    exact False.elim (hNoExit y (mpl.base i) code R_inner s0 sf he_st he_inner)
  · have hsteps_pm : Steps Program.pureMem s0 sf :=
      steps_of_withSvc_alloc_running_or_oom hpure_no rfl hsteps_alloc (Or.inr ho_st)
    have hsteps_P : Steps P s0 sf :=
      steps_prog_of_pureMem_outcome hP.svc_eq (hP.hooks_unfetched s0.mem hclP)
        (Memory.KeepsFrozen.refl s0.mem) hsteps_pm (Or.inr (Or.inr (Or.inr ho_st)))
    have ho_inner : sf.mem ⊨ (ToBaseSpec.toSpec innerSpec (mpl.base i)).onOom y s0 sf ∗ R_inner :=
      ho_wcl
    exact reaches_outcome_steps hsteps_P
      (reaches_outcome.of_outcome
        (Or.inr (Or.inr (Or.inr ⟨ho_st, hOomMap sf hpprw ho_inner⟩))))

/-! ## `VmPreserved`-Preserving `memcpy` Contract -/

/-- Total-correctness contract for `void *memcpy(void *dst, const void *src, size_t n)` strengthened
    from `sf.brk = s0.brk` (`allocMemcpySpec`) to full `VmPreserved s0 sf` (`brkStart`, `brk`,
    `tpidrEl0`, `physMemAvail`, and `mem.perm`), so `A.pool lim st` transports across `memcpy` in
    `__rdl_realloc`. -/
def allocMemcpyVmSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
      bs.length < 2 ^ 64⌝ ∗
    (memRegion dst bs.length ∗ (src ↦ₛ bs))
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem allocMemcpyVm_len_le_2pow63 {m : Memory} {dst src : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp} (hlen : bs.length ≤ 2 ^ 64)
    (h : m ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ R) :
    bs.length ≤ 2 ^ 63 := by
  have hro : m ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    refine Satisfies.pointsToBytes_to_ro ?_
    rwa [sepConj_comm (memRegion dst bs.length), sepConj_assoc] at h
  have hsep : ∀ a, InRegion src bs.length a → ¬InRegion dst bs.length a := fun a hs hd =>
    not_satisfies_ownsRO_ownsRW (ownsRO_pointsToBytesRO_at hlen hs)
      (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length a hd)) hro
  have hself : ∀ b : BitVec 64, bs.length > 2 ^ 63 → InRegion b bs.length b := fun b hgt => by
    simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine Classical.byContradiction fun hgt => ?_
  by_cases hsd : InRegion dst bs.length src
  · exact hsep src (hself src (by omega)) hsd
  · refine hsep dst ?_ (hself dst (by omega))
    simp only [InRegion] at hsd ⊢
    bv_omega

/-- Discharge `subroutine_ok P memcpyAddr allocMemcpyVmSpec` for any hook-free program `P`
    containing `musl` v1.2.5's AArch64 `memcpySymWords` at `memcpyAddr`. -/
theorem allocMemcpyVm_ok_of_hasWords (P : Program) (memcpyAddr : BitVec 64)
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (h_words : P.hasWords memcpyAddr memcpySymWords) :
    subroutine_ok P memcpyAddr allocMemcpyVmSpec := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp _hL
  simp only [allocMemcpyVmSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  have hm_assoc : s0.mem ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ R := by
    rwa [← sepConj_assoc] at hm
  have hn63 : bs.length ≤ 2 ^ 63 := allocMemcpyVm_len_le_2pow63 (Nat.le_of_lt hlt) hm_assoc
  have hn_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hm_ex : s0.mem ⊨
      (∃∗ dstBs : List (BitVec 8), ⌜dstBs.length = bs.length⌝ ∗ (dst ↦ₛ dstBs)) ∗
        ((src ↦ₛ bs) ∗ R) :=
    Satisfies.mono
      (sepConj_mono_left (memRegion_entails_exists_pointsToBytes bs.length dst (Nat.le_of_lt hlt))) hm
  rw [sepExists_sepConj_left] at hm_ex
  obtain ⟨dstBs, hm_dst⟩ := (satisfies_sepExists _ _).mp hm_ex
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_dst
  obtain ⟨hdstLen, hm_pts⟩ := hm_dst
  have hLift := subroutine_ok_lift_pureWords_process
    (P := P)
    (memcpy_pureWords_ok memcpyAddr dst src dstBs bs (BitVec.ofNat 64 bs.length)
      (hdstLen.trans hn_nat.symm) hn_nat.symm (by rw [hn_nat]; exact hn63))
    (memcpy_allInstrs_noSvc_noMsr memcpyAddr)
    h_words h_no_ext
    (h_pre_mem := fun _ _ _ => rfl)
    (h_post_mem := fun _ _ _ _ _ => rfl)
  refine hLift.mono_outcome () R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, hm_pts⟩
  · rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      dsimp only [allocMemcpyVmSpec]
      refine Entails.pure_left fun hpf => Entails.pure_left fun ⟨horc, hsym, hx0f⟩ => ?_
      rcases hpf with ⟨hfs, htr, htp, hsig, hbrk, hbrks, hphys, hperm⟩
      exact Entails.pure_right
        ⟨hx0f, ⟨hfs, htr, hsig, htp, hbrks, horc, hsym⟩,
          ⟨⟨hbrks, hbrk, htp⟩, hphys, hperm, FdsHiFrame.of_fs_eq hfs⟩⟩
        (Entails.refl _)
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

/-- Discharge `subroutine_ok P memcpyAddr allocMemcpyVmSpec` on any linked ELF `Program` via
    `decide +kernel` over its `WordTree`. -/
theorem allocMemcpyVm_ok_of_wordTree {P : Program} {t : WordTree} {memcpyAddr : BitVec 64}
    {baseOff : Nat} (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (hoff : (memcpyAddr - P.base).toNat = baseOff)
    (hbnd : baseOff + 4 * memcpySymWords.length ≤ 2 ^ 64)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hok : checkWordsAt t baseOff memcpySymWords = true) :
    subroutine_ok P memcpyAddr allocMemcpyVmSpec :=
  allocMemcpyVm_ok_of_hasWords P memcpyAddr h_no_ext
    (hasWords_of_wordTree n hcode hwf hoff hbnd hstubs hsyms hok)

theorem allocMemcpy_of_vm {P : Program} {memcpyAddr : BitVec 64}
    (h : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    subroutine_ok P memcpyAddr allocMemcpySpec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  refine Satisfies.mono (sepConj_mono_left ?_) hq
  dsimp only [allocMemcpyVmSpec, allocMemcpySpec]
  exact Entails.pure_left fun ⟨hx0, hacp, hvm⟩ => Entails.pure_right ⟨hx0, hacp, hvm.1.2.1⟩ (Entails.refl _)

/-! ## Budget-Threaded Pool, `RustCliAllocBudget` Instance, and Startup Initialization -/

/-- Every mapped byte of `m` is covered by either `staticIvs` (at most `lim.staticCount` intervals
    of total byte length `≤ lim.staticBytes`) or the allocator's dynamic interval list `ivs`. -/
def StaticMappedCover (lim : BudgetLimits) (staticIvs ivs : List (BitVec 64 × Nat))
    (m : Memory) : Prop :=
  staticIvs.length ≤ lim.staticCount ∧
  (staticIvs.map Prod.snd).sum ≤ lim.staticBytes ∧
  (∀ iv ∈ staticIvs, iv.1.toNat + iv.2 ≤ Arm64.USER_VA_LIMIT) ∧
  ∀ a : BitVec 64, (m.perm a).mapped = true →
    MallocngInIntervals staticIvs a ∨ MallocngInIntervals ivs a

/-- Enforced virtual-memory and physical-memory pool invariant:
    trivial (`True`) when `lim.enforced = false` (`zeroBudgetLimits`), and tracks
    `StaticMappedCover lim staticIvs ivs s.mem ∧ lim.physCap ≤ physPlusRw s` when
    `lim.enforced = true`. -/
def mallocngBudgetPoolInv (lim : BudgetLimits) (staticIvs ivs : List (BitVec 64 × Nat))
    (s : State) : Prop :=
  lim.enforced = true → StaticMappedCover lim staticIvs ivs s.mem ∧ lim.physCap ≤ physPlusRw s

/-- Placement-address-generic budget-threaded `mallocng` pool at `(M, I)`. -/
def mallocngBudgetPoolAt (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) : SepProp :=
  ∃∗ staticIvs : List (BitVec 64 × Nat),
  ∃∗ ivs : List (BitVec 64 × Nat),
    ⌜mallocngBudgetPoolInv lim staticIvs ivs s⌝ ∗
    MallocngModelEnv M I γ A tp brkStart st ivs s

def mallocngBudgetPool (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) : SepProp :=
  mallocngBudgetPoolAt M I γ (mallocngAddrsOfPlacement mpl) tp brkStart lim st s

/-- Live allocation token for `mallocngRustCliAllocBudgetAt`: pairs `I.BlockM γ p n (max al 16)`
    with layout and alignment metadata so `dealloc` and `realloc` recover `effAlign = max al 16`
    and `RustLayoutOk n al` directly from `A.live p n al`. -/
def mallocngLiveM (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (p : BitVec 64) (n al : Nat) : SepProp :=
  I.BlockM γ p n (max al 16) ∗
    ⌜p ≠ 0#64 ∧ al ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝

theorem mallocngBudgetPoolInv_transport_mem {lim : BudgetLimits}
    {staticIvs ivs : List (BitVec 64 × Nat)} {s s' : State}
    (hvm : VmMemPreserved s s') :
    mallocngBudgetPoolInv lim staticIvs ivs s' = mallocngBudgetPoolInv lim staticIvs ivs s := by
  rcases hvm with ⟨_, hphys, hperm⟩
  have hpprw : physPlusRw s' = physPlusRw s := by
    unfold physPlusRw; rw [hphys, rwBytes_congr hperm]
  apply propext
  unfold mallocngBudgetPoolInv StaticMappedCover
  simp only [hpprw, hperm]

theorem mallocngBudgetPoolInv_transport {lim : BudgetLimits}
    {staticIvs ivs : List (BitVec 64 × Nat)} {s s' : State}
    (hvm : VmPreserved s s') :
    mallocngBudgetPoolInv lim staticIvs ivs s' = mallocngBudgetPoolInv lim staticIvs ivs s :=
  mallocngBudgetPoolInv_transport_mem hvm.toVmMemPreserved

theorem mallocngBudgetPoolAt_transport_mem (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) {s s' : State}
    (hvm : VmMemPreserved s s') :
    mallocngBudgetPoolAt M I γ A tp brkStart lim st s' =
      mallocngBudgetPoolAt M I γ A tp brkStart lim st s := by
  have hinv : ∀ staticIvs ivs,
      mallocngBudgetPoolInv lim staticIvs ivs s' = mallocngBudgetPoolInv lim staticIvs ivs s :=
    fun staticIvs ivs => mallocngBudgetPoolInv_transport_mem hvm
  rcases hvm with ⟨⟨hbs, hbrk, htp⟩, _, _⟩
  unfold mallocngBudgetPoolAt MallocngModelEnv
  simp only [hinv, htp, hbs, hbrk]

theorem mallocngBudgetPoolAt_transport (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) {s s' : State}
    (hvm : VmPreserved s s') :
    mallocngBudgetPoolAt M I γ A tp brkStart lim st s' =
      mallocngBudgetPoolAt M I γ A tp brkStart lim st s :=
  mallocngBudgetPoolAt_transport_mem M I γ A tp brkStart lim st hvm.toVmMemPreserved

theorem mallocngBudgetPoolAt_zero_transport (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (st : M.σ) {s s' : State}
    (hp : PoolPreserved s s') :
    mallocngBudgetPoolAt M I γ A tp brkStart zeroBudgetLimits st s' =
      mallocngBudgetPoolAt M I γ A tp brkStart zeroBudgetLimits st s := by
  rcases hp with ⟨hbs, hbrk, htp⟩
  have hinv : ∀ staticIvs ivs (st0 : State),
      mallocngBudgetPoolInv zeroBudgetLimits staticIvs ivs st0 = True := by
    intro staticIvs ivs st0
    apply propext
    constructor
    · intro _; trivial
    · intro _ h; cases h
  unfold mallocngBudgetPoolAt MallocngModelEnv
  simp only [hinv, htp, hbs, hbrk]

/-- Placement-address-generic `RustCliAllocBudget M` instance over any `(M, I)` satisfying
    `MallocngCostModelSound M I`. -/
def mallocngRustCliAllocBudgetAt (M : AllocCostModel) (I : MallocngCostModelIface M)
    (_hS : MallocngCostModelSound M I)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64) :
    RustCliAllocBudget M where
  pool := mallocngBudgetPoolAt M I γ A tp brkStart
  live := mallocngLiveM M I γ
  block_valid p n al := by
    unfold mallocngLiveM
    rw [sepConj_comm (I.BlockM γ p n (max al 16)) ⌜_⌝]
    refine Entails.pure_left fun ⟨hpNe, hAlDvd, h16, hFit, hLay⟩ => ?_
    have hMod : p.toNat % al = 0 := Nat.mod_eq_zero_of_dvd hAlDvd
    refine Entails.pure_right ⟨hpNe, hMod, hFit, hLay⟩ ?_
    exact Entails.pure_right ⟨hpNe, hAlDvd, h16, hFit, hLay⟩
      (Entails.refl (I.BlockM γ p n (max al 16)))
  pool_transport lim st s s' hvm :=
    mallocngBudgetPoolAt_transport M I γ A tp brkStart lim st hvm
  pool_zero_transport st s s' hp :=
    mallocngBudgetPoolAt_zero_transport M I γ A tp brkStart st hp

def mallocngRustCliAllocBudget (M : AllocCostModel) (I : MallocngCostModelIface M)
    (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    RustCliAllocBudget M :=
  mallocngRustCliAllocBudgetAt M I hS γ (mallocngAddrsOfPlacement mpl) tp brkStart

/-- At `zeroBudgetLimits`, `mallocngBudgetPoolAt` equals `∃∗ ivs, MallocngModelEnv ...`. -/
theorem mallocngBudgetPoolAt_zero_eq (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (st : M.σ) (s : State) :
    mallocngBudgetPoolAt M I γ A tp brkStart zeroBudgetLimits st s =
      (∃∗ ivs : List (BitVec 64 × Nat), MallocngModelEnv M I γ A tp brkStart st ivs s) := by
  have hTrue : ∀ staticIvs ivs,
      mallocngBudgetPoolInv zeroBudgetLimits staticIvs ivs s = True := by
    intro staticIvs ivs
    apply propext
    exact ⟨fun _ => trivial, fun _ h => by cases h⟩
  apply Entails.antisymm
  · unfold mallocngBudgetPoolAt
    refine Entails.sepExists_elim fun staticIvs => Entails.sepExists_elim fun ivs => ?_
    rw [hTrue staticIvs ivs, pure_true_sepConj]
    exact @Entails.sepExists_intro (List (BitVec 64 × Nat))
      (fun y => MallocngModelEnv M I γ A tp brkStart st y s) ivs
  · refine Entails.sepExists_elim fun ivs => ?_
    unfold mallocngBudgetPoolAt
    refine Entails.trans ?_
      (@Entails.sepExists_intro (List (BitVec 64 × Nat))
        (fun staticIvs => ∃∗ ivs' : List (BitVec 64 × Nat),
          ⌜mallocngBudgetPoolInv zeroBudgetLimits staticIvs ivs' s⌝ ∗
          MallocngModelEnv M I γ A tp brkStart st ivs' s) [])
    refine Entails.trans ?_
      (@Entails.sepExists_intro (List (BitVec 64 × Nat))
        (fun ivs' =>
          ⌜mallocngBudgetPoolInv zeroBudgetLimits [] ivs' s⌝ ∗
          MallocngModelEnv M I γ A tp brkStart st ivs' s) ivs)
    rw [hTrue [] ivs, pure_true_sepConj]
    exact Entails.refl _

/-- On `coarseCostModelIface J`, `.toRustCliAlloc.pool s` is equal to the unbudgeted
    `∃∗ b, ∃∗ ivs, MallocngEnv J γ A tp brkStart b ivs s` (`mallocngPoolAt`). -/
theorem toRustCliAlloc_pool_coarse_eq {J : MallocngIface}
    (hS : MallocngCostModelSound coarseCostModel (coarseCostModelIface J))
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64) (s : State) :
    (mallocngRustCliAllocBudgetAt coarseCostModel (coarseCostModelIface J) hS γ A tp brkStart).toRustCliAlloc.pool s =
      (∃∗ b : MallocngBudget, ∃∗ ivs : List (BitVec 64 × Nat),
        MallocngEnv J γ A tp brkStart b ivs s) := by
  dsimp only [RustCliAllocBudget.toRustCliAlloc, mallocngRustCliAllocBudgetAt]
  exact congrArg SepProp.sepExists (funext fun b =>
    mallocngBudgetPoolAt_zero_eq coarseCostModel (coarseCostModelIface J) γ A tp brkStart b s)

/-- Split `MallocngRuntime A tp` out of `mallocngBudgetPoolAt` for callers that access `errno` or
    `__libc` between allocator calls. -/
theorem mallocngBudgetPoolAt_split_runtime {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    mallocngBudgetPoolAt M I γ A tp brkStart lim st s =
      ((∃∗ staticIvs : List (BitVec 64 × Nat),
        ∃∗ ivs : List (BitVec 64 × Nat),
          ⌜mallocngBudgetPoolInv lim staticIvs ivs s ∧ s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
          I.CoreM γ A brkStart s.brk st ivs) ∗
       MallocngRuntime A tp) := by
  unfold mallocngBudgetPoolAt MallocngModelEnv
  simp only [hS.heap_split_runtime, sepExists_sepConj_left]
  apply Entails.antisymm
  · refine Entails.sepExists_mono fun staticIvs => Entails.sepExists_mono fun ivs => ?_
    refine Entails.pure_left fun hinv => ?_
    refine Entails.pure_left fun ⟨htp, hbs⟩ => ?_
    exact sepConj_mono_left
      (Entails.pure_right ⟨hinv, htp, hbs⟩ (Entails.refl (I.CoreM γ A brkStart s.brk st ivs)))
  · refine Entails.sepExists_mono fun staticIvs => Entails.sepExists_mono fun ivs => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hinv, htp, hbs⟩ => ?_
    exact Entails.pure_right hinv
      (Entails.pure_right ⟨htp, hbs⟩
        (Entails.refl (I.CoreM γ A brkStart s.brk st ivs ∗ MallocngRuntime A tp)))

/-- Startup initialization from `MallocngStartupResources A s.tpidrEl0` into
    `mallocngBudgetPoolAt M I γ A s.tpidrEl0 s.brkStart lim M.init s` (`|==>`-eliminated). -/
theorem mallocngBudgetPoolAt_of_init_resources {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {A : MallocngAddrs} {lim : BudgetLimits} {staticIvs : List (BitVec 64 × Nat)}
    {s : State} {R : SepProp}
    (htpLo : 0xa4 ≤ s.tpidrEl0.toNat)
    (htpHi : s.tpidrEl0.toNat ≤ 2 ^ 48)
    (hbrk : s.brk = s.brkStart)
    (hBrkWf : MallocngBrkStartWf s.brkStart)
    (hInv : mallocngBudgetPoolInv lim staticIvs [] s)
    (hsat : s.mem ⊨ MallocngStartupResources A s.tpidrEl0 ∗ R) :
    ∃ γ : GhostName,
      s.mem ⊨ mallocngBudgetPoolAt M I γ A s.tpidrEl0 s.brkStart lim M.init s ∗ R := by
  have hbupd := hS.init_resources A s.tpidrEl0 s.brkStart htpLo htpHi hBrkWf
  have hsat1 := Satisfies.of_bupd_frame_left hbupd hsat
  rw [sepExists_sepConj_left, satisfies_sepExists] at hsat1
  obtain ⟨γ, hsat1⟩ := hsat1
  refine ⟨γ, ?_⟩
  refine Satisfies.mono (sepConj_mono_left ?_) hsat1
  unfold mallocngBudgetPoolAt MallocngModelEnv
  rw [hbrk]
  refine Entails.trans ?_
    (@Entails.sepExists_intro (List (BitVec 64 × Nat))
      (fun stIvs => ∃∗ ivs : List (BitVec 64 × Nat),
        ⌜mallocngBudgetPoolInv lim stIvs ivs s⌝ ∗
        (⌜s.tpidrEl0 = s.tpidrEl0 ∧ s.brkStart = s.brkStart⌝ ∗
          I.HeapM γ A s.tpidrEl0 s.brkStart s.brkStart M.init ivs)) staticIvs)
  refine Entails.trans ?_
    (@Entails.sepExists_intro (List (BitVec 64 × Nat))
      (fun ivs =>
        ⌜mallocngBudgetPoolInv lim staticIvs ivs s⌝ ∗
        (⌜s.tpidrEl0 = s.tpidrEl0 ∧ s.brkStart = s.brkStart⌝ ∗
          I.HeapM γ A s.tpidrEl0 s.brkStart s.brkStart M.init ivs)) [])
  exact Entails.pure_right hInv
    (Entails.pure_right ⟨rfl, rfl⟩
      (Entails.refl (I.HeapM γ A s.tpidrEl0 s.brkStart s.brkStart M.init [])))

/-- Multi-block-placement startup initialization from `VerifiedLibraries.mallocngLib.dataInit mpl`
    into `mallocngBudgetPool M I γ mpl s.tpidrEl0 s.brkStart lim M.init s` (`|==>`-eliminated). -/
theorem mallocngBudgetPool_of_init {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {mpl : Obj.MultiPlacement} {auxvPtr : BitVec 64} {lim : BudgetLimits}
    {staticIvs : List (BitVec 64 × Nat)} {s : State} {R : SepProp}
    (htpLo : 0xa4 ≤ s.tpidrEl0.toNat)
    (htpHi : s.tpidrEl0.toNat ≤ 2 ^ 48)
    (hbrk : s.brk = s.brkStart)
    (hBrkWf : MallocngBrkStartWf s.brkStart)
    (hInv : mallocngBudgetPoolInv lim staticIvs [] s)
    (hsat : s.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
      MallocngRuntime (mallocngAddrsOfPlacement mpl) s.tpidrEl0 ∗
      (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
      MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      s.mem ⊨ mallocngBudgetPool M I γ mpl s.tpidrEl0 s.brkStart lim M.init s ∗ R := by
  obtain ⟨γ, hsat1⟩ := hS.init mpl s.tpidrEl0 s.brkStart auxvPtr R s.mem htpLo htpHi hBrkWf hsat
  rw [satisfies_bupd] at hsat1
  refine ⟨γ, ?_⟩
  refine Satisfies.mono (sepConj_mono_left ?_) hsat1
  unfold mallocngBudgetPool mallocngBudgetPoolAt MallocngModelEnv
  rw [hbrk]
  refine Entails.trans ?_
    (@Entails.sepExists_intro (List (BitVec 64 × Nat))
      (fun stIvs => ∃∗ ivs : List (BitVec 64 × Nat),
        ⌜mallocngBudgetPoolInv lim stIvs ivs s⌝ ∗
        (⌜s.tpidrEl0 = s.tpidrEl0 ∧ s.brkStart = s.brkStart⌝ ∗
          I.HeapM γ (mallocngAddrsOfPlacement mpl) s.tpidrEl0 s.brkStart s.brkStart M.init ivs))
      staticIvs)
  refine Entails.trans ?_
    (@Entails.sepExists_intro (List (BitVec 64 × Nat))
      (fun ivs =>
        ⌜mallocngBudgetPoolInv lim staticIvs ivs s⌝ ∗
        (⌜s.tpidrEl0 = s.tpidrEl0 ∧ s.brkStart = s.brkStart⌝ ∗
          I.HeapM γ (mallocngAddrsOfPlacement mpl) s.tpidrEl0 s.brkStart s.brkStart M.init ivs)) [])
  exact Entails.pure_right hInv
    (Entails.pure_right ⟨rfl, rfl⟩
      (Entails.refl (I.HeapM γ (mallocngAddrsOfPlacement mpl) s.tpidrEl0 s.brkStart s.brkStart M.init [])))

/-! ## Non-OOM Discharge and Program-Level Budgeted C Contracts -/

/-- Under `FitsStep lim stepB (M.maxDynIvs st) (M.footprint st)`,
`mallocngBudgetPoolInv lim staticIvs ivs0 s0`, dynamic interval bounds, and
`physPlusRw sf = physPlusRw s0`, `MallocngStepOomCond allocMallocng stepB s0 sf` is impossible. -/
theorem mallocng_oom_false {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {stepB : Nat}
    {staticIvs ivs0 : List (BitVec 64 × Nat)} {s0 sf : State}
    (hFit : FitsStep lim stepB (M.maxDynIvs st) (M.footprint st))
    (hInv0 : mallocngBudgetPoolInv lim staticIvs ivs0 s0)
    (hIvsLen : ivs0.length ≤ M.maxDynIvs st)
    (hIvsSum : (ivs0.map Prod.snd).sum ≤ M.footprint st)
    (hpprw : physPlusRw sf = physPlusRw s0)
    (hOom : MallocngStepOomCond allocMallocng stepB s0 sf) : False := by
  rcases hFit with ⟨henf, hram, hva⟩
  obtain ⟨⟨hStLen, hStSum, _, hMap0⟩, hPhys0⟩ := hInv0 henf
  obtain ⟨_, _, _, ⟨deltaIvs, hDeltaLen, hDeltaSum, hDeltaCov⟩, hSanImp⟩ := hOom
  obtain ⟨sz, hSzPos, hSzAl, hSzBound, hNoGapOrPhys⟩ := hSanImp allocMallocng_sanitizedSvc
  let totIvs := staticIvs ++ ivs0 ++ deltaIvs
  have hTotCov : ∀ a : BitVec 64, (sf.mem.perm a).mapped = true →
      ∃ iv ∈ totIvs, (a - iv.1).toNat < iv.2 := by
    intro a haMap
    rcases hDeltaCov a haMap with haMap0 | ⟨iv, hiv, hin⟩
    · rcases hMap0 a haMap0 with ⟨iv, hiv, hin⟩ | ⟨iv, hiv, hin⟩
      · exact ⟨iv, List.mem_append_left _ (List.mem_append_left _ hiv), hin⟩
      · exact ⟨iv, List.mem_append_left _ (List.mem_append_right _ hiv), hin⟩
    · exact ⟨iv, List.mem_append_right _ hiv, hin⟩
  have hTotSum : (totIvs.map Prod.snd).sum ≤ lim.staticBytes + M.footprint st + stepB := by
    have hEq : (totIvs.map Prod.snd).sum =
        (staticIvs.map Prod.snd).sum + (ivs0.map Prod.snd).sum + (deltaIvs.map Prod.snd).sum := by
      simp [totIvs, List.map_append, List.sum_append, Nat.add_assoc]
    omega
  have hTotLen : totIvs.length ≤ lim.staticCount + M.maxDynIvs st + 16 := by
    have hEq : totIvs.length = staticIvs.length + ivs0.length + deltaIvs.length := by
      simp [totIvs, List.length_append, Nat.add_assoc]
    omega
  rcases hNoGapOrPhys with hNoGap | hNoPhys
  · have hMul :
        totIvs.length * (sz + PAGE_SIZE) ≤
          (lim.staticCount + M.maxDynIvs st + 16) * (stepB + PAGE_SIZE) :=
      Nat.mul_le_mul hTotLen (Nat.add_le_add_right hSzBound PAGE_SIZE)
    have hFitGap :
        MMAP_MIN_ADDR + (totIvs.map Prod.snd).sum +
          totIvs.length * (sz + PAGE_SIZE) + sz ≤ 2 ^ 48 := by
      omega
    exact hNoGap (hasGap_of_mappedIntervals hTotCov hSzPos hSzAl hFitGap)
  · have hrwLe : rwBytes sf.mem ≤ (totIvs.map Prod.snd).sum := rwBytes_le_intervals_sum hTotCov
    unfold physPlusRw at hpprw hPhys0
    omega

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
    have hEq :
        (⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
          (⌜φ⌝ ∗ I.HeapM γ A tp brkStart s0.brk st ivs0)) ∗ R =
        ⌜φ⌝ ∗ ((⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
          I.HeapM γ A tp brkStart s0.brk st ivs0) ∗ R) := by ac_rfl
    exact Entails.trans (sepConj_mono_left (sepConj_mono_right hh)) (Entails.of_eq hEq)
  have hsat' := Satisfies.mono hent hsat
  rw [satisfies_pure_sepConj] at hsat'
  exact hsat'.1

private theorem unpackBudgetPool {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {γ : GhostName} {A : MallocngAddrs} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {s0 : State} {Rest : SepProp}
    (hsat : s0.mem ⊨ mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗ Rest) :
    ∃ staticIvs ivs0,
      mallocngBudgetPoolInv lim staticIvs ivs0 s0 ∧
      ivs0.length ≤ M.maxDynIvs st ∧
      (ivs0.map Prod.snd).sum ≤ M.footprint st ∧
      (s0.mem ⊨ MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ Rest) := by
  unfold mallocngBudgetPoolAt at hsat
  simp only [sepExists_sepConj_left] at hsat
  obtain ⟨staticIvs, hsat⟩ := (satisfies_sepExists _ _).mp hsat
  obtain ⟨ivs0, hsat⟩ := (satisfies_sepExists _ _).mp hsat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsat
  obtain ⟨hInv0, hsat⟩ := hsat
  obtain ⟨hlen, hsum⟩ := extractModelEnvBounds hS hsat
  exact ⟨staticIvs, ivs0, hInv0, hlen, hsum, hsat⟩

private theorem packBudgetPostEnv {M : AllocCostModel} (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    {lim : BudgetLimits} {st' : M.σ} {staticIvs ivs0 : List (BitVec 64 × Nat)}
    {s0 sf : State}
    (hInv0 : mallocngBudgetPoolInv lim staticIvs ivs0 s0)
    (hpprw : physPlusRw sf = physPlusRw s0) :
    MallocngModelPostEnv M I γ A tp brkStart st' ivs0 s0 sf ⊢
      mallocngBudgetPoolAt M I γ A tp brkStart lim st' sf := by
  unfold MallocngModelPostEnv
  refine Entails.sepExists_elim fun ivsf => ?_
  refine Entails.pure_left fun hNoOrphan => ?_
  have hInvF : mallocngBudgetPoolInv lim staticIvs ivsf sf := by
    intro henf
    obtain ⟨⟨hStLen, hStSum, hStVa, hMap0⟩, hPhys0⟩ := hInv0 henf
    refine ⟨⟨hStLen, hStSum, hStVa, fun a haMapF => ?_⟩, hpprw.symm ▸ hPhys0⟩
    cases hm0 : (s0.mem.perm a).mapped with
    | false => exact Or.inr (hNoOrphan a haMapF (Or.inl hm0))
    | true =>
      exact (hMap0 a hm0).elim Or.inl fun hDyn0 => Or.inr (hNoOrphan a haMapF (Or.inr hDyn0))
  unfold mallocngBudgetPoolAt
  refine Entails.trans ?_
    (@Entails.sepExists_intro (List (BitVec 64 × Nat))
      (fun stIvs => ∃∗ ivs : List (BitVec 64 × Nat),
        ⌜mallocngBudgetPoolInv lim stIvs ivs sf⌝ ∗
        MallocngModelEnv M I γ A tp brkStart st' ivs sf) staticIvs)
  refine Entails.trans ?_
    (@Entails.sepExists_intro (List (BitVec 64 × Nat))
      (fun ivs =>
        ⌜mallocngBudgetPoolInv lim staticIvs ivs sf⌝ ∗
        MallocngModelEnv M I γ A tp brkStart st' ivs sf) ivsf)
  exact Entails.pure_right hInvF (Entails.refl _)

theorem inIntervals_lt_userVa {ivs : List (BitVec 64 × Nat)} {a : BitVec 64}
    (hva : ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ Arm64.USER_VA_LIMIT)
    (hin : MallocngInIntervals ivs a) :
    a.toNat < Arm64.USER_VA_LIMIT := by
  rcases hin with ⟨iv, hm, hlt⟩
  have hiv := hva iv hm
  have ha64 := a.isLt
  have hiv64 := iv.1.isLt
  have hLim : Arm64.USER_VA_LIMIT = 2 ^ 48 := rfl
  rw [BitVec.toNat_sub] at hlt
  by_cases hge : iv.1.toNat ≤ a.toNat
  · have hmod : (2 ^ 64 - iv.1.toNat + a.toNat) % 2 ^ 64 = a.toNat - iv.1.toNat := by
      have h1 : 2 ^ 64 - iv.1.toNat + a.toNat = 2 ^ 64 + (a.toNat - iv.1.toNat) := by omega
      rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at hlt
    omega
  · exfalso
    have hmod : (2 ^ 64 - iv.1.toNat + a.toNat) % 2 ^ 64 = 2 ^ 64 - iv.1.toNat + a.toNat :=
      Nat.mod_eq_of_lt (by omega)
    rw [hmod] at hlt
    omega

theorem mallocngBudgetPoolAt_mapped_lt_userVa {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {γ : GhostName} {A : MallocngAddrs} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {s0 : State} {Rest : SepProp} {a : BitVec 64}
    (henf : lim.enforced = true)
    (hsat : s0.mem ⊨ mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗ Rest)
    (hmap : (s0.mem.perm a).mapped = true) :
    a.toNat < Arm64.USER_VA_LIMIT := by
  unfold mallocngBudgetPoolAt at hsat
  simp only [sepExists_sepConj_left] at hsat
  obtain ⟨staticIvs, hsat⟩ := (satisfies_sepExists _ _).mp hsat
  obtain ⟨ivs0, hsat⟩ := (satisfies_sepExists _ _).mp hsat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsat
  obtain ⟨hInv0, hsat⟩ := hsat
  obtain ⟨⟨_, _, hStVa, hCov⟩, _⟩ := hInv0 henf
  let φ := ∀ iv ∈ ivs0, iv.1.toNat + iv.2 ≤ Arm64.USER_VA_LIMIT
  have hent : MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ Rest ⊢
      ⌜φ⌝ ∗ (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ Rest) := by
    unfold MallocngModelEnv
    have hh : I.HeapM γ A tp brkStart s0.brk st ivs0 ⊢
        ⌜φ⌝ ∗ I.HeapM γ A tp brkStart s0.brk st ivs0 :=
      Entails.extract_heap_fact fun hp hhp =>
        (hS.heap_footprint_bound γ A tp brkStart s0.brk st ivs0 hp hhp).2.2
    have hEq :
        (⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
          (⌜φ⌝ ∗ I.HeapM γ A tp brkStart s0.brk st ivs0)) ∗ Rest =
        ⌜φ⌝ ∗ ((⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
          I.HeapM γ A tp brkStart s0.brk st ivs0) ∗ Rest) := by ac_rfl
    exact Entails.trans (sepConj_mono_left (sepConj_mono_right hh)) (Entails.of_eq hEq)
  have hsat' := Satisfies.mono hent hsat
  rw [satisfies_pure_sepConj] at hsat'
  rcases hCov a hmap with hSt | hDyn
  · exact inIntervals_lt_userVa hStVa hSt
  · exact inIntervals_lt_userVa hsat'.1 hDyn

theorem mallocngBudgetPool_mapped_lt_userVa {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {s0 : State} {Rest : SepProp} {a : BitVec 64}
    (henf : lim.enforced = true)
    (hsat : s0.mem ⊨ mallocngBudgetPool M I γ mpl tp brkStart lim st s0 ∗ Rest)
    (hmap : (s0.mem.perm a).mapped = true) :
    a.toNat < Arm64.USER_VA_LIMIT :=
  mallocngBudgetPoolAt_mapped_lt_userVa hS henf hsat hmap

theorem stackAt_sp_le_userVa_of_mapped {m : Memory} {sp : BitVec 64} {stk : Nat} {R : SepProp}
    (hpos : 0 < stk) (hle : stk ≤ 2 ^ 64)
    (hmapVa : ∀ a : BitVec 64, (m.perm a).mapped = true → a.toNat < Arm64.USER_VA_LIMIT)
    (hsat : m ⊨ stackAt sp stk ∗ R) :
    sp.toNat ≤ Arm64.USER_VA_LIMIT := by
  by_cases hsp0 : sp = 0#64
  · subst hsp0; decide
  · have hspPos : 1 ≤ sp.toNat := by
      rcases Nat.eq_zero_or_pos sp.toNat with hz | hp
      · exact False.elim (hsp0 (BitVec.eq_of_toNat_eq hz))
      · exact hp
    have hcw : m.canWrite ((sp - BitVec.ofNat 64 stk) + BitVec.ofNat 64 (stk - 1)) 1 = true :=
      memRegion_canWrite1 hsat (by omega) hle
    have hAddr : (sp - BitVec.ofNat 64 stk) + BitVec.ofNat 64 (stk - 1) = sp - 1#64 := by
      have hstkEq : BitVec.ofNat 64 stk = 1#64 + BitVec.ofNat 64 (stk - 1) := by
        change BitVec.ofNat 64 stk = BitVec.ofNat 64 1 + BitVec.ofNat 64 (stk - 1)
        rw [← BitVec.ofNat_add]; congr 1; omega
      rw [hstkEq, ← BitVec.sub_sub, BitVec.sub_add_cancel]
    rw [hAddr] at hcw
    have hmap : (m.perm (sp - 1#64)).mapped = true := by
      unfold Memory.canWrite Memory.allPerm at hcw
      cases hp : m.perm (sp - 1#64) with
      | none => rw [hp] at hcw; cases hcw
      | some _ => rfl
    have hlt := hmapVa (sp - 1#64) hmap
    have hsub : (sp - 1#64).toNat = sp.toNat - 1 := by
      have h64 := sp.isLt
      rw [BitVec.toNat_sub]
      change (2 ^ 64 - 1 + sp.toNat) % 2 ^ 64 = sp.toNat - 1
      have h1 : 2 ^ 64 - 1 + sp.toNat = 2 ^ 64 + (sp.toNat - 1) := by omega
      rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega

theorem stackAt_bounds_of_mapped {m : Memory} {sp : BitVec 64} {stk : Nat} {R : SepProp}
    (hpos : 0 < stk) (hle : stk ≤ 2 ^ 64)
    (hmapVa : ∀ a : BitVec 64, (m.perm a).mapped = true → a.toNat < Arm64.USER_VA_LIMIT)
    (hsat : m ⊨ stackAt sp stk ∗ R) :
    stk ≤ sp.toNat ∧ sp.toNat ≤ Arm64.USER_VA_LIMIT := by
  refine ⟨?_, stackAt_sp_le_userVa_of_mapped hpos hle hmapVa hsat⟩
  exact Classical.byContradiction fun hlt_stk => by
    have hsp_lt : sp.toNat < stk := Nat.lt_of_not_ge hlt_stk
    let k := stk - 1 - sp.toNat
    have hk_lt : k < stk := by omega
    have hcw : m.canWrite ((sp - BitVec.ofNat 64 stk) + BitVec.ofNat 64 k) 1 = true :=
      memRegion_canWrite1 hsat hk_lt hle
    have hspEq : sp = BitVec.ofNat 64 sp.toNat :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sp.isLt])
    have hstkEq : BitVec.ofNat 64 stk = (sp + 1#64) + BitVec.ofNat 64 k := by
      conv => rhs; arg 1; arg 1; rw [hspEq]
      change BitVec.ofNat 64 stk =
        (BitVec.ofNat 64 sp.toNat + BitVec.ofNat 64 1) + BitVec.ofNat 64 k
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 1; omega
    have hSubSelf : sp - sp = 0#64 := BitVec.eq_of_toNat_eq (by simp)
    have hAddr : (sp - BitVec.ofNat 64 stk) + BitVec.ofNat 64 k = 0#64 - 1#64 := by
      rw [hstkEq, ← BitVec.sub_sub, BitVec.sub_add_cancel, ← BitVec.sub_sub, hSubSelf]
    rw [hAddr] at hcw
    have hmap : (m.perm (0#64 - 1#64)).mapped = true := by
      unfold Memory.canWrite Memory.allPerm at hcw
      cases hp : m.perm (0#64 - 1#64) with
      | none => rw [hp] at hcw; cases hcw
      | some _ => rfl
    have hlt := hmapVa (0#64 - 1#64) hmap
    have hLim : Arm64.USER_VA_LIMIT = 2 ^ 48 := rfl
    have hVal : (0#64 - 1#64 : BitVec 64).toNat = 2 ^ 64 - 1 := by decide
    omega

def mallocngBudgetMallocCSpec (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) : Spec (BitVec 64 × M.σ) where
  pre := fun (req, st) s0 =>
    ⌜s0.readReg64 .x0 = req⌝ ∗
    mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗
    stackFrameAt s0.sp mallocngStackBytes
  post := fun (req, st) s0 sf =>
    let ok := decide (req.toNat ≤ MallocngMaxAllocSize)
    let st' := if ok then M.step (.alloc req.toNat) st else st
    ⌜AllocCallPreserved s0 sf⌝ ∗
    mallocngBudgetPoolAt M I γ A tp brkStart lim st' sf ∗
    stackFrameAt s0.sp mallocngStackBytes ∗
    (if ok then
      ⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
        (sf.readReg64 .x0).toNat + req.toNat < 2 ^ 64⌝ ∗
      I.BlockM γ (sf.readReg64 .x0) req.toNat 16 ∗
      memRegion (sf.readReg64 .x0) req.toNat
     else
      ⌜sf.readReg64 .x0 = 0#64⌝)
  onOom := fun (req, st) s0 sf =>
    ⌜¬ FitsEvent M lim st (.alloc req.toNat) ∧ OomPreserved s0 sf⌝

def mallocngBudgetFreeCSpec (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := fun (p, n, align, st) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ (if p = 0#64 then n = 0 else 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64)⌝ ∗
    mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗
    (if p = 0#64 then emp else I.BlockM γ p n (max align 16) ∗ memRegion p n) ∗
    stackFrameAt s0.sp mallocngStackBytes
  post := fun (p, n, align, st) s0 sf =>
    let st' := if p == 0#64 then st else M.step (.free align n) st
    ⌜AllocCallPreserved s0 sf⌝ ∗
    mallocngBudgetPoolAt M I γ A tp brkStart lim st' sf ∗
    stackFrameAt s0.sp mallocngStackBytes

def mallocngBudgetCallocCSpec (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × M.σ) where
  pre := fun (nmemb, size, st) s0 =>
    ⌜s0.readReg64 .x0 = nmemb ∧ s0.readReg64 .x1 = size⌝ ∗
    mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗
    stackFrameAt s0.sp mallocngStackBytes
  post := fun (nmemb, size, st) s0 sf =>
    let total := nmemb.toNat * size.toNat
    let ok := decide (total ≤ MallocngMaxAllocSize)
    let st' := if ok then M.step (.alloc total) st else st
    ⌜AllocCallPreserved s0 sf⌝ ∗
    mallocngBudgetPoolAt M I γ A tp brkStart lim st' sf ∗
    stackFrameAt s0.sp mallocngStackBytes ∗
    (if ok then
      ⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
        (sf.readReg64 .x0).toNat + total < 2 ^ 64⌝ ∗
      I.BlockM γ (sf.readReg64 .x0) total 16 ∗
      (sf.readReg64 .x0 ↦ₛ List.replicate total 0#8)
     else
      ⌜sf.readReg64 .x0 = 0#64⌝)
  onOom := fun (nmemb, size, st) s0 sf =>
    ⌜¬ FitsEvent M lim st (.alloc (nmemb.toNat * size.toNat)) ∧ OomPreserved s0 sf⌝

def mallocngBudgetReallocSomeCSpec (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × Nat × Nat × List (BitVec 8) × M.σ) where
  pre := fun (p, newSize, oldSize, align, bs, st) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧
      p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + oldSize < 2 ^ 64 ∧ bs.length ≤ oldSize⌝ ∗
    mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗
    I.BlockM γ p oldSize (max align 16) ∗
    (p ↦ₛ bs) ∗
    memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
    stackFrameAt s0.sp mallocngStackBytes
  post := fun (p, newSize, oldSize, align, bs, st) s0 sf =>
    let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
    let keptBs := bs.take newSize.toNat
    let st' := if ok then M.step (.realloc align oldSize newSize.toNat) st else st
    ⌜AllocCallPreserved s0 sf⌝ ∗
    mallocngBudgetPoolAt M I γ A tp brkStart lim st' sf ∗
    stackFrameAt s0.sp mallocngStackBytes ∗
    (if ok then
      ⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
        (sf.readReg64 .x0).toNat + newSize.toNat < 2 ^ 64 ∧
        keptBs.length ≤ newSize.toNat⌝ ∗
      I.BlockM γ (sf.readReg64 .x0) newSize.toNat (max align 16) ∗
      (sf.readReg64 .x0 ↦ₛ keptBs) ∗
      memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 keptBs.length) (newSize.toNat - keptBs.length)
     else
      ⌜sf.readReg64 .x0 = 0#64⌝ ∗
      I.BlockM γ p oldSize (max align 16) ∗
      (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length))
  onOom := fun (_, newSize, oldSize, align, _, st) s0 sf =>
    ⌜¬ FitsEvent M lim st (.realloc align oldSize newSize.toNat) ∧ OomPreserved s0 sf⌝

def mallocngBudgetAlignedAllocCSpec (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × M.σ) where
  pre := fun (align, len, st) s0 =>
    ⌜s0.readReg64 .x0 = align ∧ s0.readReg64 .x1 = len ∧
      align.toNat ≤ MaxAlignedAllocAlign⌝ ∗
    mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗
    stackFrameAt s0.sp mallocngStackBytes
  post := fun (align, len, st) s0 sf =>
    let ok := mallocngAlignedAllocOk align len
    let st' := if ok then M.step (.aligned align.toNat len.toNat) st else st
    ⌜AllocCallPreserved s0 sf⌝ ∗
    mallocngBudgetPoolAt M I γ A tp brkStart lim st' sf ∗
    stackFrameAt s0.sp mallocngStackBytes ∗
    (if ok then
      ⌜sf.readReg64 .x0 ≠ 0#64 ∧ max align.toNat 16 ∣ (sf.readReg64 .x0).toNat ∧
        (sf.readReg64 .x0).toNat + len.toNat < 2 ^ 64⌝ ∗
      I.BlockM γ (sf.readReg64 .x0) len.toNat (max align.toNat 16) ∗
      memRegion (sf.readReg64 .x0) len.toNat
     else
      ⌜sf.readReg64 .x0 = 0#64⌝)
  onOom := fun (align, len, st) s0 sf =>
    ⌜¬ (alignedAllocAlignOk align = true ∧
        FitsEvent M lim st (.aligned align.toNat len.toNat)) ∧
      OomPreserved s0 sf⌝

def mallocngBudgetPosixMemalignCSpec (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × BitVec 64 × M.σ) where
  pre := fun (res, align, len, st) s0 =>
    ⌜s0.readReg64 .x0 = res ∧ s0.readReg64 .x1 = align ∧ s0.readReg64 .x2 = len ∧
      align.toNat ≤ MaxAlignedAllocAlign⌝ ∗
    mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗
    memRegion res 8 ∗
    stackFrameAt s0.sp mallocngStackBytes
  post := fun (res, align, len, st) s0 sf =>
    let ok := mallocngPosixMemalignOk align len
    let st' := if ok then M.step (.aligned align.toNat len.toNat) st else st
    ⌜AllocCallPreserved s0 sf ∧
      sf.readReg32 .x0 = mallocngPosixMemalignRet align len⌝ ∗
    mallocngBudgetPoolAt M I γ A tp brkStart lim st' sf ∗
    stackFrameAt s0.sp mallocngStackBytes ∗
    (if ok then
      ∃∗ outPtr : BitVec 64,
        ⌜outPtr ≠ 0#64 ∧ max align.toNat 16 ∣ outPtr.toNat ∧
          outPtr.toNat + len.toNat < 2 ^ 64⌝ ∗
        (res ↦₆₄ outPtr) ∗
        I.BlockM γ outPtr len.toNat (max align.toNat 16) ∗
        memRegion outPtr len.toNat
     else
      memRegion res 8)
  onOom := fun (_, align, len, st) s0 sf =>
    ⌜¬ (8 ≤ align.toNat ∧ alignedAllocAlignOk align = true ∧
        FitsEvent M lim st (.aligned align.toNat len.toNat)) ∧
      OomPreserved s0 sf⌝

/-- Program-level budget-threaded `subroutine_ok P` bundle for `malloc`, `free`, `calloc`,
    `realloc`, `aligned_alloc`, and `posix_memalign` over `(M, I)`. -/
structure MallocngProgBudgetCContracts (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (P : Program) (cAddrs : MallocngCEntryAddrs) (callocAddr : BitVec 64) : Prop where
  malloc_ok : ∀ lim : BudgetLimits,
    subroutine_ok P cAddrs.malloc (mallocngBudgetMallocCSpec M I γ A tp brkStart lim)
  free_ok : ∀ lim : BudgetLimits,
    subroutine_ok P cAddrs.free (mallocngBudgetFreeCSpec M I γ A tp brkStart lim)
  calloc_ok : ∀ lim : BudgetLimits,
    subroutine_ok P callocAddr (mallocngBudgetCallocCSpec M I γ A tp brkStart lim)
  realloc_some_ok : ∀ lim : BudgetLimits,
    subroutine_ok P cAddrs.realloc (mallocngBudgetReallocSomeCSpec M I γ A tp brkStart lim)
  alignedAlloc_ok : ∀ lim : BudgetLimits,
    subroutine_ok P cAddrs.alignedAlloc (mallocngBudgetAlignedAllocCSpec M I γ A tp brkStart lim)
  posixMemalign_ok : ∀ lim : BudgetLimits,
    subroutine_ok P cAddrs.posixMemalign (mallocngBudgetPosixMemalignCSpec M I γ A tp brkStart lim)

/-- Instantiate `MallocngProgBudgetCContracts` for any program `P` satisfying
    `ProgContainsMallocng P mpl` and any cost model `(M, I)` satisfying `MallocngCostModelSound M I`
    via `allocMallocng` physical+RW conservation (`runPlacedAllocCall`) and `mallocng_oom_false`. -/
theorem mallocngProgBudgetCContracts_of_placed {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64) :
    MallocngProgBudgetCContracts M I γ (mallocngAddrsOfPlacement mpl) tp brkStart
      P (mallocngPlacedCAddrs mpl) (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc") := by
  have hEntries := hS.entries_ok mpl allocMallocng hP.placeable allocMallocng_svcValid
  let A := mallocngAddrsOfPlacement mpl
  refine
    { malloc_ok := fun lim => ?_
      free_ok := fun lim => ?_
      calloc_ok := fun lim => ?_
      realloc_some_ok := fun lim => ?_
      alignedAlloc_ok := fun lim => ?_
      posixMemalign_ok := fun lim => ?_ }
  · -- malloc
    refine runPlacedAllocCall hP (hEntries.malloc_ok γ) rfl ?_
    rintro ⟨req, st⟩ R s0 b_base hpre
    dsimp only [mallocngBudgetMallocCSpec] at hpre
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨hx0, hpre⟩ := hpre
    obtain ⟨staticIvs, ivs0, hInv0, hIvsLen, hIvsSum, hpreEnv⟩ := unpackBudgetPool hS hpre
    refine ⟨(req, s0.sp, tp, brkStart, st, ivs0), R, ?_, ?_, ?_⟩
    · dsimp only [mallocngModelMallocSpec, ToBaseSpec.toSpec]
      simp only [ctype_simp, sepConj_assoc]
      have harg : s0.readReg64 (.gpr 0#5) = req := hx0
      rw [pure_sepConj_of_true (by simp [harg])]
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpreEnv
    · intro sf hpprw hoom
      dsimp only [mallocngModelMallocSpec, ToBaseSpec.toSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      obtain ⟨hOomCond, hR⟩ := hoom
      have hOomPres : OomPreserved s0 sf := ⟨hOomCond.1, hOomCond.2.1, hOomCond.2.2.1⟩
      have hNotFit : ¬ FitsEvent M lim st (.alloc req.toNat) := by
        rintro ⟨hMax, hFitStep⟩
        have hok : decide (req.toNat ≤ MallocngMaxAllocSize) = true := decide_eq_true hMax
        simp only [hok, ↓reduceIte] at hOomCond
        exact mallocng_oom_false hFitStep hInv0 hIvsLen hIvsSum hpprw hOomCond
      dsimp only [mallocngBudgetMallocCSpec]
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hNotFit, hOomPres⟩, hR⟩
    · intro sf hpprw _hkf hpost
      dsimp only [mallocngModelMallocSpec, ToBaseSpec.toSpec] at hpost
      cases hok : decide (req.toNat ≤ MallocngMaxAllocSize) with
      | true =>
        have hPack := packBudgetPostEnv I γ A tp brkStart
          (st' := M.step (.alloc req.toNat) st) hInv0 hpprw
        simp only [hok, ↓reduceIte, ctype_simp, MallocngModelBlock, sepConj_assoc] at hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨⟨⟨_, hne, hal16, hfit64⟩, hacc⟩, hpost⟩ := hpost
        have hacp : AllocCallPreserved s0 sf := allocCallPreserved_of_mallocngProcPreserved hacc.1
        change sf.readReg64 .x0 ≠ 0#64 at hne
        change 16 ∣ (sf.readReg64 .x0).toNat at hal16
        change (sf.readReg64 .x0).toNat + req.toNat < 2 ^ 64 at hfit64
        dsimp only [mallocngBudgetMallocCSpec]
        simp only [hok, ↓reduceIte]
        have hpost1 : sf.mem ⊨
            I.BlockM γ (sf.readReg64 .x0) req.toNat 16 ∗
              (memRegion (sf.readReg64 .x0) req.toNat ∗
                (mallocngBudgetPoolAt M I γ A tp brkStart lim (M.step (.alloc req.toNat) st) sf ∗
                  (stackFrameAt s0.sp mallocngStackBytes ∗ R))) :=
          Satisfies.mono
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hPack))) hpost
        have hGoalEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗
              mallocngBudgetPoolAt M I γ A tp brkStart lim (M.step (.alloc req.toNat) st) sf ∗
              stackFrameAt s0.sp mallocngStackBytes ∗
              (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                  (sf.readReg64 .x0).toNat + req.toNat < 2 ^ 64⌝ ∗
                I.BlockM γ (sf.readReg64 .x0) req.toNat 16 ∗
                memRegion (sf.readReg64 .x0) req.toNat)) ∗ R =
            ⌜AllocCallPreserved s0 sf⌝ ∗
              (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                  (sf.readReg64 .x0).toNat + req.toNat < 2 ^ 64⌝ ∗
                (I.BlockM γ (sf.readReg64 .x0) req.toNat 16 ∗
                  (memRegion (sf.readReg64 .x0) req.toNat ∗
                    (mallocngBudgetPoolAt M I γ A tp brkStart lim
                        (M.step (.alloc req.toNat) st) sf ∗
                      (stackFrameAt s0.sp mallocngStackBytes ∗ R))))) := by ac_rfl
        rw [hGoalEq, satisfies_pure_sepConj]
        refine ⟨hacp, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hne, hal16, hfit64⟩, hpost1⟩
      | false =>
        have hPack := packBudgetPostEnv I γ A tp brkStart (st' := st) hInv0 hpprw
        simp only [hok, Bool.false_eq_true, ↓reduceIte, ctype_simp, sepConj_assoc] at hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨⟨_, hacc⟩, hpost⟩ := hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨hnull, hpost⟩ := hpost
        have hacp : AllocCallPreserved s0 sf := allocCallPreserved_of_mallocngProcPreserved hacc.1
        change sf.readReg64 .x0 = 0#64 at hnull
        dsimp only [mallocngBudgetMallocCSpec]
        simp only [hok, Bool.false_eq_true, ↓reduceIte]
        have hpost1 : sf.mem ⊨
            mallocngBudgetPoolAt M I γ A tp brkStart lim st sf ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗ R) :=
          Satisfies.mono (sepConj_mono_left hPack) hpost
        have hGoalEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗
              mallocngBudgetPoolAt M I γ A tp brkStart lim st sf ∗
              stackFrameAt s0.sp mallocngStackBytes ∗
              ⌜sf.readReg64 .x0 = 0#64⌝) ∗ R =
            ⌜AllocCallPreserved s0 sf⌝ ∗
              (⌜sf.readReg64 .x0 = 0#64⌝ ∗
                (mallocngBudgetPoolAt M I γ A tp brkStart lim st sf ∗
                  (stackFrameAt s0.sp mallocngStackBytes ∗ R))) := by ac_rfl
        rw [hGoalEq, satisfies_pure_sepConj]
        refine ⟨hacp, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hnull, hpost1⟩
  · -- free
    refine runPlacedAllocCall hP (hEntries.free_ok γ) rfl ?_
    rintro ⟨p, n, align, st⟩ R s0 b_base hpre
    dsimp only [mallocngBudgetFreeCSpec] at hpre
    have hpreEq :
        (⌜s0.readReg64 .x0 = p ∧
            (if p = 0#64 then n = 0 else 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64)⌝ ∗
          mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗
          (if p = 0#64 then emp else I.BlockM γ p n (max align 16) ∗ memRegion p n) ∗
          stackFrameAt s0.sp mallocngStackBytes) ∗ R =
        ⌜s0.readReg64 .x0 = p ∧
            (if p = 0#64 then n = 0 else 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64)⌝ ∗
          (mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗
            ((if p = 0#64 then emp else I.BlockM γ p n (max align 16) ∗ memRegion p n) ∗
              stackFrameAt s0.sp mallocngStackBytes ∗ R)) := by ac_rfl
    rw [hpreEq, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx0, hpWf⟩, hpre⟩ := hpre
    obtain ⟨staticIvs, ivs0, hInv0, _hIvsLen, _hIvsSum, hpreEnv⟩ := unpackBudgetPool hS hpre
    refine ⟨(p, s0.sp, n, align, tp, brkStart, st, ivs0), R, ?_,
      (fun _ _ ho => False.elim (not_satisfies_false_sepConj ho)), ?_⟩
    · dsimp only [mallocngModelFreeSpec, ToBaseSpec.toSpec, MallocngModelFreeableBlock]
      simp only [ctype_simp, sepConj_assoc]
      have harg : s0.readReg64 (.gpr 0#5) = p := hx0
      rw [pure_sepConj_of_true (by simp [harg, hpWf])]
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpreEnv
    · intro sf hpprw _hkf hpost
      dsimp only [mallocngModelFreeSpec, ToBaseSpec.toSpec] at hpost
      simp only [ctype_simp, sepConj_assoc] at hpost
      rw [satisfies_pure_sepConj] at hpost
      obtain ⟨hacc, hpost⟩ := hpost
      have hacp : AllocCallPreserved s0 sf := allocCallPreserved_of_mallocngProcPreserved hacc.1
      let st' := if p == 0#64 then st else M.step (.free align n) st
      have hPack := packBudgetPostEnv I γ A tp brkStart (st' := st') hInv0 hpprw
      have hpost1 := Satisfies.mono (sepConj_mono_left hPack) hpost
      dsimp only [mallocngBudgetFreeCSpec]
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngBudgetPoolAt M I γ A tp brkStart lim st' sf ∗
            stackFrameAt s0.sp mallocngStackBytes) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (mallocngBudgetPoolAt M I γ A tp brkStart lim st' sf ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗ R)) := by ac_rfl
      rw [hGoalEq, satisfies_pure_sepConj]
      exact ⟨hacp, hpost1⟩
  · -- calloc
    refine runPlacedAllocCall hP (hEntries.calloc_ok γ) rfl ?_
    rintro ⟨nmemb, size, st⟩ R s0 b_base hpre
    dsimp only [mallocngBudgetCallocCSpec] at hpre
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx0, hx1⟩, hpre⟩ := hpre
    obtain ⟨staticIvs, ivs0, hInv0, hIvsLen, hIvsSum, hpreEnv⟩ := unpackBudgetPool hS hpre
    refine ⟨(nmemb, size, s0.sp, tp, brkStart, st, ivs0), R, ?_, ?_, ?_⟩
    · dsimp only [mallocngModelCallocSpec, ToBaseSpec.toSpec]
      simp only [ctype_simp, sepConj_assoc]
      have h0 : s0.readReg64 (.gpr 0#5) = nmemb := hx0
      have h1 : s0.readReg64 (.gpr 1#5) = size := hx1
      rw [pure_sepConj_of_true (by simp [h0, h1])]
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpreEnv
    · intro sf hpprw hoom
      dsimp only [mallocngModelCallocSpec, ToBaseSpec.toSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      obtain ⟨hOomCond, hR⟩ := hoom
      have hOomPres : OomPreserved s0 sf := ⟨hOomCond.1, hOomCond.2.1, hOomCond.2.2.1⟩
      have hNotFit : ¬ FitsEvent M lim st (.alloc (nmemb.toNat * size.toNat)) := by
        rintro ⟨hMax, hFitStep⟩
        have hok : decide (nmemb.toNat * size.toNat ≤ MallocngMaxAllocSize) = true :=
          decide_eq_true hMax
        simp only [hok, ↓reduceIte] at hOomCond
        exact mallocng_oom_false hFitStep hInv0 hIvsLen hIvsSum hpprw hOomCond
      dsimp only [mallocngBudgetCallocCSpec]
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hNotFit, hOomPres⟩, hR⟩
    · intro sf hpprw _hkf hpost
      dsimp only [mallocngModelCallocSpec, ToBaseSpec.toSpec] at hpost
      let total := nmemb.toNat * size.toNat
      cases hok : decide (nmemb.toNat * size.toNat ≤ MallocngMaxAllocSize) with
      | true =>
        have hPack := packBudgetPostEnv I γ A tp brkStart
          (st' := M.step (.alloc total) st) hInv0 hpprw
        simp only [hok, ↓reduceIte, ctype_simp, MallocngModelZeroedBlock, sepConj_assoc] at hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨⟨⟨_, hne, hal16, hfit64⟩, hacc⟩, hpost⟩ := hpost
        have hacp : AllocCallPreserved s0 sf := allocCallPreserved_of_mallocngProcPreserved hacc.1
        change sf.readReg64 .x0 ≠ 0#64 at hne
        change 16 ∣ (sf.readReg64 .x0).toNat at hal16
        change (sf.readReg64 .x0).toNat + total < 2 ^ 64 at hfit64
        dsimp only [mallocngBudgetCallocCSpec]
        simp only [hok, ↓reduceIte]
        have hpost1 : sf.mem ⊨
            I.BlockM γ (sf.readReg64 .x0) total 16 ∗
              ((sf.readReg64 .x0 ↦ₛ List.replicate total 0#8) ∗
                (mallocngBudgetPoolAt M I γ A tp brkStart lim (M.step (.alloc total) st) sf ∗
                  (stackFrameAt s0.sp mallocngStackBytes ∗ R))) :=
          Satisfies.mono
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hPack))) hpost
        have hGoalEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗
              mallocngBudgetPoolAt M I γ A tp brkStart lim (M.step (.alloc total) st) sf ∗
              stackFrameAt s0.sp mallocngStackBytes ∗
              (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                  (sf.readReg64 .x0).toNat + total < 2 ^ 64⌝ ∗
                I.BlockM γ (sf.readReg64 .x0) total 16 ∗
                (sf.readReg64 .x0 ↦ₛ List.replicate total 0#8))) ∗ R =
            ⌜AllocCallPreserved s0 sf⌝ ∗
              (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                  (sf.readReg64 .x0).toNat + total < 2 ^ 64⌝ ∗
                (I.BlockM γ (sf.readReg64 .x0) total 16 ∗
                  ((sf.readReg64 .x0 ↦ₛ List.replicate total 0#8) ∗
                    (mallocngBudgetPoolAt M I γ A tp brkStart lim (M.step (.alloc total) st) sf ∗
                      (stackFrameAt s0.sp mallocngStackBytes ∗ R))))) := by ac_rfl
        rw [hGoalEq, satisfies_pure_sepConj]
        refine ⟨hacp, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hne, hal16, hfit64⟩, hpost1⟩
      | false =>
        have hPack := packBudgetPostEnv I γ A tp brkStart (st' := st) hInv0 hpprw
        simp only [hok, Bool.false_eq_true, ↓reduceIte, ctype_simp, sepConj_assoc] at hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨⟨_, hacc⟩, hpost⟩ := hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨hnull, hpost⟩ := hpost
        have hacp : AllocCallPreserved s0 sf := allocCallPreserved_of_mallocngProcPreserved hacc.1
        change sf.readReg64 .x0 = 0#64 at hnull
        dsimp only [mallocngBudgetCallocCSpec]
        simp only [hok, Bool.false_eq_true, ↓reduceIte]
        have hpost1 := Satisfies.mono (sepConj_mono_left hPack) hpost
        have hGoalEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗
              mallocngBudgetPoolAt M I γ A tp brkStart lim st sf ∗
              stackFrameAt s0.sp mallocngStackBytes ∗
              ⌜sf.readReg64 .x0 = 0#64⌝) ∗ R =
            ⌜AllocCallPreserved s0 sf⌝ ∗
              (⌜sf.readReg64 .x0 = 0#64⌝ ∗
                (mallocngBudgetPoolAt M I γ A tp brkStart lim st sf ∗
                  (stackFrameAt s0.sp mallocngStackBytes ∗ R))) := by ac_rfl
        rw [hGoalEq, satisfies_pure_sepConj]
        refine ⟨hacp, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hnull, hpost1⟩
  · -- realloc (some)
    refine runPlacedAllocCall hP (hEntries.realloc_ok γ) rfl ?_
    rintro ⟨p, newSize, oldSize, align, bs, st⟩ R s0 b_base hpre
    dsimp only [mallocngBudgetReallocSomeCSpec] at hpre
    have hpreEq :
        (⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧
            p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + oldSize < 2 ^ 64 ∧ bs.length ≤ oldSize⌝ ∗
          mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗
          I.BlockM γ p oldSize (max align 16) ∗
          (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
          stackFrameAt s0.sp mallocngStackBytes) ∗ R =
        ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧
            p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + oldSize < 2 ^ 64 ∧ bs.length ≤ oldSize⌝ ∗
          (mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗
            (I.BlockM γ p oldSize (max align 16) ∗
              (p ↦ₛ bs) ∗
              memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
              stackFrameAt s0.sp mallocngStackBytes ∗ R)) := by ac_rfl
    rw [hpreEq, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx0, hx1, hpNe, hp16, hpFit, hbsLe⟩, hpre⟩ := hpre
    obtain ⟨staticIvs, ivs0, hInv0, hIvsLen, hIvsSum, hpreEnv⟩ := unpackBudgetPool hS hpre
    refine ⟨(p, newSize, s0.sp, some (oldSize, align, bs), tp, brkStart, st, ivs0), R, ?_, ?_, ?_⟩
    · dsimp only [mallocngModelReallocSpec, ToBaseSpec.toSpec, MallocngModelInitBlock]
      simp only [ctype_simp, sepConj_assoc]
      have h0 : s0.readReg64 (.gpr 0#5) = p := hx0
      have h1 : s0.readReg64 (.gpr 1#5) = newSize := hx1
      rw [pure_sepConj_of_true (by simp [h0, h1, hpNe, hp16, hpFit, hbsLe])]
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpreEnv
    · intro sf hpprw hoom
      dsimp only [mallocngModelReallocSpec, ToBaseSpec.toSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      obtain ⟨hOomCond, hR⟩ := hoom
      have hOomPres : OomPreserved s0 sf := ⟨hOomCond.1, hOomCond.2.1, hOomCond.2.2.1⟩
      have hNotFit : ¬ FitsEvent M lim st (.realloc align oldSize newSize.toNat) := by
        rintro ⟨hMax, hFitStep⟩
        have hok : decide (newSize.toNat ≤ MallocngMaxAllocSize) = true := decide_eq_true hMax
        simp only [hok, ↓reduceIte] at hOomCond
        exact mallocng_oom_false hFitStep hInv0 hIvsLen hIvsSum hpprw hOomCond
      dsimp only [mallocngBudgetReallocSomeCSpec]
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hNotFit, hOomPres⟩, hR⟩
    · intro sf hpprw _hkf hpost
      dsimp only [mallocngModelReallocSpec, ToBaseSpec.toSpec] at hpost
      let keptBs := bs.take newSize.toNat
      cases hok : decide (newSize.toNat ≤ MallocngMaxAllocSize) with
      | true =>
        have hPack := packBudgetPostEnv I γ A tp brkStart
          (st' := M.step (.realloc align oldSize newSize.toNat) st) hInv0 hpprw
        simp only [hok, ↓reduceIte, ctype_simp, MallocngModelInitBlock,
          Option.map_some, Option.getD_some, emp_sepConj, sepConj_assoc] at hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨⟨_, ⟨_, hne, hal16, hfit64, hkeptLe⟩, hacc⟩, hpost⟩ := hpost
        have hacp : AllocCallPreserved s0 sf := allocCallPreserved_of_mallocngProcPreserved hacc.1
        change sf.readReg64 .x0 ≠ 0#64 at hne
        change 16 ∣ (sf.readReg64 .x0).toNat at hal16
        change (sf.readReg64 .x0).toNat + newSize.toNat < 2 ^ 64 at hfit64
        change keptBs.length ≤ newSize.toNat at hkeptLe
        dsimp only [mallocngBudgetReallocSomeCSpec]
        simp only [hok, ↓reduceIte]
        have hmax16 : max (max align 16) 16 = max align 16 := by omega
        rw [hmax16] at hpost
        have hpost1 : sf.mem ⊨
            I.BlockM γ (sf.readReg64 .x0) newSize.toNat (max align 16) ∗
              ((sf.readReg64 .x0 ↦ₛ keptBs) ∗
                (memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 keptBs.length)
                    (newSize.toNat - keptBs.length) ∗
                  (mallocngBudgetPoolAt M I γ A tp brkStart lim
                      (M.step (.realloc align oldSize newSize.toNat) st) sf ∗
                    (stackFrameAt s0.sp mallocngStackBytes ∗ R)))) :=
          Satisfies.mono
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hPack))))
            hpost
        have hGoalEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗
              mallocngBudgetPoolAt M I γ A tp brkStart lim
                (M.step (.realloc align oldSize newSize.toNat) st) sf ∗
              stackFrameAt s0.sp mallocngStackBytes ∗
              (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                  (sf.readReg64 .x0).toNat + newSize.toNat < 2 ^ 64 ∧
                  keptBs.length ≤ newSize.toNat⌝ ∗
                I.BlockM γ (sf.readReg64 .x0) newSize.toNat (max align 16) ∗
                (sf.readReg64 .x0 ↦ₛ keptBs) ∗
                memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 keptBs.length)
                  (newSize.toNat - keptBs.length))) ∗ R =
            ⌜AllocCallPreserved s0 sf⌝ ∗
              (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                  (sf.readReg64 .x0).toNat + newSize.toNat < 2 ^ 64 ∧
                  keptBs.length ≤ newSize.toNat⌝ ∗
                (I.BlockM γ (sf.readReg64 .x0) newSize.toNat (max align 16) ∗
                  ((sf.readReg64 .x0 ↦ₛ keptBs) ∗
                    (memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 keptBs.length)
                        (newSize.toNat - keptBs.length) ∗
                      (mallocngBudgetPoolAt M I γ A tp brkStart lim
                          (M.step (.realloc align oldSize newSize.toNat) st) sf ∗
                        (stackFrameAt s0.sp mallocngStackBytes ∗ R)))))) := by ac_rfl
        rw [hGoalEq, satisfies_pure_sepConj]
        refine ⟨hacp, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hne, hal16, hfit64, hkeptLe⟩, hpost1⟩
      | false =>
        have hPack := packBudgetPostEnv I γ A tp brkStart (st' := st) hInv0 hpprw
        simp only [hok, Bool.false_eq_true, ↓reduceIte, ctype_simp, MallocngModelInitBlock,
          sepConj_assoc] at hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨⟨_, _, hacc⟩, hpost⟩ := hpost
        have hacp : AllocCallPreserved s0 sf := allocCallPreserved_of_mallocngProcPreserved hacc.1
        have hPullNull :
            I.BlockM γ p oldSize (max align 16) ∗
              ((p ↦ₛ bs) ∗
                (memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
                  (⌜sf.readReg64 (.gpr 0#5) = 0#64⌝ ∗
                    (MallocngModelPostEnv M I γ A tp brkStart st ivs0 s0 sf ∗
                      (stackFrameAt s0.sp mallocngStackBytes ∗ R))))) =
            ⌜sf.readReg64 .x0 = 0#64⌝ ∗
              (I.BlockM γ p oldSize (max align 16) ∗
                ((p ↦ₛ bs) ∗
                  (memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
                    (MallocngModelPostEnv M I γ A tp brkStart st ivs0 s0 sf ∗
                      (stackFrameAt s0.sp mallocngStackBytes ∗ R))))) := by ac_rfl
        rw [hPullNull, satisfies_pure_sepConj] at hpost
        obtain ⟨hnull, hpost⟩ := hpost
        dsimp only [mallocngBudgetReallocSomeCSpec]
        simp only [hok, Bool.false_eq_true, ↓reduceIte]
        have hpost1 : sf.mem ⊨
            I.BlockM γ p oldSize (max align 16) ∗
              ((p ↦ₛ bs) ∗
                (memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
                  (mallocngBudgetPoolAt M I γ A tp brkStart lim st sf ∗
                    (stackFrameAt s0.sp mallocngStackBytes ∗ R)))) :=
          Satisfies.mono
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hPack))))
            hpost
        have hGoalEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗
              mallocngBudgetPoolAt M I γ A tp brkStart lim st sf ∗
              stackFrameAt s0.sp mallocngStackBytes ∗
              (⌜sf.readReg64 .x0 = 0#64⌝ ∗
                I.BlockM γ p oldSize (max align 16) ∗
                (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length))) ∗ R =
            ⌜AllocCallPreserved s0 sf⌝ ∗
              (⌜sf.readReg64 .x0 = 0#64⌝ ∗
                (I.BlockM γ p oldSize (max align 16) ∗
                  ((p ↦ₛ bs) ∗
                    (memRegion (p + BitVec.ofNat 64 bs.length) (oldSize - bs.length) ∗
                      (mallocngBudgetPoolAt M I γ A tp brkStart lim st sf ∗
                        (stackFrameAt s0.sp mallocngStackBytes ∗ R)))))) := by ac_rfl
        rw [hGoalEq, satisfies_pure_sepConj]
        refine ⟨hacp, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hnull, hpost1⟩
  · -- aligned_alloc
    refine runPlacedAllocCall hP (hEntries.alignedAlloc_ok γ) rfl ?_
    rintro ⟨align, len, st⟩ R s0 b_base hpre
    dsimp only [mallocngBudgetAlignedAllocCSpec] at hpre
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx0, hx1, halMax⟩, hpre⟩ := hpre
    obtain ⟨staticIvs, ivs0, hInv0, hIvsLen, hIvsSum, hpreEnv⟩ := unpackBudgetPool hS hpre
    refine ⟨(align, len, s0.sp, tp, brkStart, st, ivs0), R, ?_, ?_, ?_⟩
    · dsimp only [mallocngModelAlignedAllocSpec, ToBaseSpec.toSpec]
      simp only [ctype_simp, sepConj_assoc]
      have h0 : s0.readReg64 (.gpr 0#5) = align := hx0
      have h1 : s0.readReg64 (.gpr 1#5) = len := hx1
      rw [pure_sepConj_of_true (by simp [h0, h1, halMax])]
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpreEnv
    · intro sf hpprw hoom
      dsimp only [mallocngModelAlignedAllocSpec, ToBaseSpec.toSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      obtain ⟨hOomCond, hR⟩ := hoom
      have hOomPres : OomPreserved s0 sf := ⟨hOomCond.1, hOomCond.2.1, hOomCond.2.2.1⟩
      have hNotFit :
          ¬ (alignedAllocAlignOk align = true ∧
              FitsEvent M lim st (.aligned align.toNat len.toNat)) := by
        rintro ⟨halOk, hMax, hFitStep⟩
        change mallocngAlignedEffSize align.toNat len.toNat ≤ MallocngMaxAllocSize at hMax
        have hok : mallocngAlignedAllocOk align len = true := by
          unfold mallocngAlignedAllocOk
          simp [halOk, decide_eq_true hMax]
        simp only [hok, ↓reduceIte] at hOomCond
        exact mallocng_oom_false hFitStep hInv0 hIvsLen hIvsSum hpprw hOomCond
      dsimp only [mallocngBudgetAlignedAllocCSpec]
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hNotFit, hOomPres⟩, hR⟩
    · intro sf hpprw _hkf hpost
      dsimp only [mallocngModelAlignedAllocSpec, ToBaseSpec.toSpec] at hpost
      cases hok : mallocngAlignedAllocOk align len with
      | true =>
        have hPack := packBudgetPostEnv I γ A tp brkStart
          (st' := M.step (.aligned align.toNat len.toNat) st) hInv0 hpprw
        simp only [hok, ↓reduceIte, ctype_simp, MallocngModelBlock, sepConj_assoc] at hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨⟨⟨_, hne, hal, hfit64⟩, hacc⟩, hpost⟩ := hpost
        have hacp : AllocCallPreserved s0 sf := allocCallPreserved_of_mallocngProcPreserved hacc.1
        change sf.readReg64 .x0 ≠ 0#64 at hne
        change max align.toNat 16 ∣ (sf.readReg64 .x0).toNat at hal
        change (sf.readReg64 .x0).toNat + len.toNat < 2 ^ 64 at hfit64
        dsimp only [mallocngBudgetAlignedAllocCSpec]
        simp only [hok, ↓reduceIte]
        have hpost1 : sf.mem ⊨
            I.BlockM γ (sf.readReg64 .x0) len.toNat (max align.toNat 16) ∗
              (memRegion (sf.readReg64 .x0) len.toNat ∗
                (mallocngBudgetPoolAt M I γ A tp brkStart lim
                    (M.step (.aligned align.toNat len.toNat) st) sf ∗
                  (stackFrameAt s0.sp mallocngStackBytes ∗ R))) :=
          Satisfies.mono
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hPack))) hpost
        have hGoalEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗
              mallocngBudgetPoolAt M I γ A tp brkStart lim
                (M.step (.aligned align.toNat len.toNat) st) sf ∗
              stackFrameAt s0.sp mallocngStackBytes ∗
              (⌜sf.readReg64 .x0 ≠ 0#64 ∧ max align.toNat 16 ∣ (sf.readReg64 .x0).toNat ∧
                  (sf.readReg64 .x0).toNat + len.toNat < 2 ^ 64⌝ ∗
                I.BlockM γ (sf.readReg64 .x0) len.toNat (max align.toNat 16) ∗
                memRegion (sf.readReg64 .x0) len.toNat)) ∗ R =
            ⌜AllocCallPreserved s0 sf⌝ ∗
              (⌜sf.readReg64 .x0 ≠ 0#64 ∧ max align.toNat 16 ∣ (sf.readReg64 .x0).toNat ∧
                  (sf.readReg64 .x0).toNat + len.toNat < 2 ^ 64⌝ ∗
                (I.BlockM γ (sf.readReg64 .x0) len.toNat (max align.toNat 16) ∗
                  (memRegion (sf.readReg64 .x0) len.toNat ∗
                    (mallocngBudgetPoolAt M I γ A tp brkStart lim
                        (M.step (.aligned align.toNat len.toNat) st) sf ∗
                      (stackFrameAt s0.sp mallocngStackBytes ∗ R))))) := by ac_rfl
        rw [hGoalEq, satisfies_pure_sepConj]
        refine ⟨hacp, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hne, hal, hfit64⟩, hpost1⟩
      | false =>
        have hPack := packBudgetPostEnv I γ A tp brkStart (st' := st) hInv0 hpprw
        simp only [hok, Bool.false_eq_true, ↓reduceIte, ctype_simp, sepConj_assoc] at hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨⟨_, hacc⟩, hpost⟩ := hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨hnull, hpost⟩ := hpost
        have hacp : AllocCallPreserved s0 sf := allocCallPreserved_of_mallocngProcPreserved hacc.1
        change sf.readReg64 .x0 = 0#64 at hnull
        dsimp only [mallocngBudgetAlignedAllocCSpec]
        simp only [hok, Bool.false_eq_true, ↓reduceIte]
        have hpost1 := Satisfies.mono (sepConj_mono_left hPack) hpost
        have hGoalEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗
              mallocngBudgetPoolAt M I γ A tp brkStart lim st sf ∗
              stackFrameAt s0.sp mallocngStackBytes ∗
              ⌜sf.readReg64 .x0 = 0#64⌝) ∗ R =
            ⌜AllocCallPreserved s0 sf⌝ ∗
              (⌜sf.readReg64 .x0 = 0#64⌝ ∗
                (mallocngBudgetPoolAt M I γ A tp brkStart lim st sf ∗
                  (stackFrameAt s0.sp mallocngStackBytes ∗ R))) := by ac_rfl
        rw [hGoalEq, satisfies_pure_sepConj]
        refine ⟨hacp, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hnull, hpost1⟩
  · -- posix_memalign
    refine runPlacedAllocCall hP (hEntries.posixMemalign_ok γ) rfl ?_
    rintro ⟨res, align, len, st⟩ R s0 b_base hpre
    dsimp only [mallocngBudgetPosixMemalignCSpec] at hpre
    have hpreEq :
        (⌜s0.readReg64 .x0 = res ∧ s0.readReg64 .x1 = align ∧ s0.readReg64 .x2 = len ∧
            align.toNat ≤ MaxAlignedAllocAlign⌝ ∗
          mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗
          memRegion res 8 ∗
          stackFrameAt s0.sp mallocngStackBytes) ∗ R =
        ⌜s0.readReg64 .x0 = res ∧ s0.readReg64 .x1 = align ∧ s0.readReg64 .x2 = len ∧
            align.toNat ≤ MaxAlignedAllocAlign⌝ ∗
          (mallocngBudgetPoolAt M I γ A tp brkStart lim st s0 ∗
            (memRegion res 8 ∗ stackFrameAt s0.sp mallocngStackBytes ∗ R)) := by ac_rfl
    rw [hpreEq, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx0, hx1, hx2, halMax⟩, hpre⟩ := hpre
    obtain ⟨staticIvs, ivs0, hInv0, hIvsLen, hIvsSum, hpreEnv⟩ := unpackBudgetPool hS hpre
    refine ⟨(res, align, len, s0.sp, tp, brkStart, st, ivs0), R, ?_, ?_, ?_⟩
    · dsimp only [mallocngModelPosixMemalignSpec, ToBaseSpec.toSpec, OptOutPtr]
      simp only [ctype_simp, sepConj_assoc]
      have h0 : s0.readReg64 (.gpr 0#5) = res := hx0
      have h1 : s0.readReg64 (.gpr 1#5) = align := hx1
      have h2 : s0.readReg64 (.gpr 2#5) = len := hx2
      rw [pure_sepConj_of_true (by simp [h0, h1, h2, halMax])]
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpreEnv
    · intro sf hpprw hoom
      dsimp only [mallocngModelPosixMemalignSpec, ToBaseSpec.toSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      obtain ⟨hOomCond, hR⟩ := hoom
      have hOomPres : OomPreserved s0 sf := ⟨hOomCond.1, hOomCond.2.1, hOomCond.2.2.1⟩
      have hNotFit :
          ¬ (8 ≤ align.toNat ∧ alignedAllocAlignOk align = true ∧
              FitsEvent M lim st (.aligned align.toNat len.toNat)) := by
        rintro ⟨h8, halOk, hMax, hFitStep⟩
        change mallocngAlignedEffSize align.toNat len.toNat ≤ MallocngMaxAllocSize at hMax
        have hok : mallocngPosixMemalignOk align len = true := by
          unfold mallocngPosixMemalignOk mallocngAlignedAllocOk
          simp [decide_eq_true h8, halOk, decide_eq_true hMax]
        simp only [hok, ↓reduceIte] at hOomCond
        exact mallocng_oom_false hFitStep hInv0 hIvsLen hIvsSum hpprw hOomCond
      dsimp only [mallocngBudgetPosixMemalignCSpec]
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hNotFit, hOomPres⟩, hR⟩
    · intro sf hpprw _hkf hpost
      dsimp only [mallocngModelPosixMemalignSpec, ToBaseSpec.toSpec] at hpost
      cases hok : mallocngPosixMemalignOk align len with
      | true =>
        have hPack := packBudgetPostEnv I γ A tp brkStart
          (st' := M.step (.aligned align.toNat len.toNat) st) hInv0 hpprw
        simp only [hok, ↓reduceIte, ctype_simp, OptOutPtr, outPtrPost,
          sepExists_sepConj_left, sepConj_assoc] at hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨⟨_hresWf, hret32, hacc⟩, hpost⟩ := hpost
        obtain ⟨outPtr, hpost⟩ := (satisfies_sepExists _ _).mp hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨⟨houtNe, houtAl, houtFit⟩, hpost⟩ := hpost
        have hacp : AllocCallPreserved s0 sf := allocCallPreserved_of_mallocngProcPreserved hacc.1
        change sf.readReg32 .x0 = mallocngPosixMemalignRet align len at hret32
        dsimp only [mallocngBudgetPosixMemalignCSpec]
        simp only [hok, ↓reduceIte]
        have hpost1 : sf.mem ⊨
            (res ↦₆₄ outPtr) ∗
              (I.BlockM γ outPtr len.toNat (max align.toNat 16) ∗
                (memRegion outPtr len.toNat ∗
                  (mallocngBudgetPoolAt M I γ A tp brkStart lim
                      (M.step (.aligned align.toNat len.toNat) st) sf ∗
                    (stackFrameAt s0.sp mallocngStackBytes ∗ R)))) :=
          Satisfies.mono
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hPack))))
            hpost
        have hExIntro :
            (⌜outPtr ≠ 0#64 ∧ max align.toNat 16 ∣ outPtr.toNat ∧
                outPtr.toNat + len.toNat < 2 ^ 64⌝ ∗
              (res ↦₆₄ outPtr) ∗
              I.BlockM γ outPtr len.toNat (max align.toNat 16) ∗
              memRegion outPtr len.toNat) ⊢
            ∃∗ q : BitVec 64,
              ⌜q ≠ 0#64 ∧ max align.toNat 16 ∣ q.toNat ∧ q.toNat + len.toNat < 2 ^ 64⌝ ∗
              (res ↦₆₄ q) ∗
              I.BlockM γ q len.toNat (max align.toNat 16) ∗
              memRegion q len.toNat :=
          @Entails.sepExists_intro (BitVec 64)
            (fun q =>
              ⌜q ≠ 0#64 ∧ max align.toNat 16 ∣ q.toNat ∧ q.toNat + len.toNat < 2 ^ 64⌝ ∗
              (res ↦₆₄ q) ∗
              I.BlockM γ q len.toNat (max align.toNat 16) ∗
              memRegion q len.toNat) outPtr
        refine Satisfies.mono
          (Entails.trans ?_
            (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hExIntro)))))
          (show sf.mem ⊨
            ⌜AllocCallPreserved s0 sf ∧
                sf.readReg32 .x0 = mallocngPosixMemalignRet align len⌝ ∗
              (⌜outPtr ≠ 0#64 ∧ max align.toNat 16 ∣ outPtr.toNat ∧
                  outPtr.toNat + len.toNat < 2 ^ 64⌝ ∗
                ((res ↦₆₄ outPtr) ∗
                  (I.BlockM γ outPtr len.toNat (max align.toNat 16) ∗
                    (memRegion outPtr len.toNat ∗
                      (mallocngBudgetPoolAt M I γ A tp brkStart lim
                          (M.step (.aligned align.toNat len.toNat) st) sf ∗
                        (stackFrameAt s0.sp mallocngStackBytes ∗ R)))))) from by
            rw [satisfies_pure_sepConj]
            refine ⟨⟨hacp, hret32⟩, ?_⟩
            rw [satisfies_pure_sepConj]
            exact ⟨⟨houtNe, houtAl, houtFit⟩, hpost1⟩)
        exact Entails.of_eq (by ac_rfl)
      | false =>
        have hPack := packBudgetPostEnv I γ A tp brkStart (st' := st) hInv0 hpprw
        simp only [hok, Bool.false_eq_true, ↓reduceIte, ctype_simp, OptOutPtr, sepConj_assoc] at hpost
        rw [satisfies_pure_sepConj] at hpost
        obtain ⟨⟨_hresWf, hret32, hacc⟩, hpost⟩ := hpost
        have hacp : AllocCallPreserved s0 sf := allocCallPreserved_of_mallocngProcPreserved hacc.1
        change sf.readReg32 .x0 = mallocngPosixMemalignRet align len at hret32
        dsimp only [mallocngBudgetPosixMemalignCSpec]
        simp only [hok, Bool.false_eq_true, ↓reduceIte]
        have hpost1 : sf.mem ⊨
            memRegion res 8 ∗
              (mallocngBudgetPoolAt M I γ A tp brkStart lim st sf ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ R)) :=
          Satisfies.mono (sepConj_mono_right (sepConj_mono_left hPack)) hpost
        have hGoalEq :
            (⌜AllocCallPreserved s0 sf ∧
                sf.readReg32 .x0 = mallocngPosixMemalignRet align len⌝ ∗
              mallocngBudgetPoolAt M I γ A tp brkStart lim st sf ∗
              stackFrameAt s0.sp mallocngStackBytes ∗
              memRegion res 8) ∗ R =
            ⌜AllocCallPreserved s0 sf ∧
                sf.readReg32 .x0 = mallocngPosixMemalignRet align len⌝ ∗
              (memRegion res 8 ∗
                (mallocngBudgetPoolAt M I γ A tp brkStart lim st sf ∗
                  (stackFrameAt s0.sp mallocngStackBytes ∗ R))) := by ac_rfl
        rw [hGoalEq, satisfies_pure_sepConj]
        exact ⟨⟨hacp, hret32⟩, hpost1⟩

end LibsignalBinary.Heap
