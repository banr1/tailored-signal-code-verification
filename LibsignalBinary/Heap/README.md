# LibsignalBinary/Heap: State-Indexed & Cost-Model-Parametric Budget-Threaded Rust Global-Allocator Layer

**Not trusted.** No headline theorem or statement specification in `Computational/` or `Symbolic/`
imports or mentions any declaration under `LibsignalBinary/Heap/`. Checked by Lean (`0` `sorry` and
`0` `axiom` declarations across `LibsignalBinary/Heap/**`): across all top-level and `Fine/`
modules (`Iface`, `IfaceLemmas`, `IfaceDecide`, `IfaceSimp`, `IfaceBudgetBase`,
`IfaceBudgetBaseBridges`, `IfaceBudget`, `IfaceBudgetLemmas`, `MallocngBridgeBudget`,
`MallocngRustBudget`, `RustStdAllocBudgetBridge`, `GrowOneSpecs`, `SpecBudget`, `NonVacBudget`, and
`Fine/*`), every public and `private` constant in `env.constants` has `0` `sorry` and axiom cone
strictly within `{propext, Classical.choice, Quot.sound}`.

## Architecture: Two Coexisting Layers (`RustCliAlloc` & `RustCliAllocBudget M`)

1. **Unbudgeted state-indexed layer (`RustCliAlloc`, [`Iface.lean`](Iface.lean)):**
   - `pool : State → SepProp` transports across `PoolPreserved s s'`
     (`s'.brkStart = s.brkStart ∧ s'.brk = s.brk ∧ s'.tpidrEl0 = s.tpidrEl0`).
   - Allocating contracts carry `onOom := fun _ s0 sf => ⌜OomPreserved s0 sf⌝` and allow normal-return
     `0#64` only under `NullAllowed size align` (`2 ^ 62 < size + align`).
2. **Cost-model-parametric budget-threaded layer (`RustCliAllocBudget M`, [`IfaceBudget.lean`](IfaceBudget.lean)):**
   - Parameterized over an abstract `M : AllocCostModel` (`init`, `step`, `footprint`, `maxDynIvs`,
     `stepReserve`, `liveBytes`, and monotonicity laws) and process-level `lim : BudgetLimits`
     (`staticCount`, `staticBytes`, `physCap`, `enforced`).
   - Callers never mention `coarseCostModel` (`MallocngBudget` / `MallocngStepBound`) directly in
     their specs or proofs, so upgrading from Tier T1 (`coarseCostModel`, charging
     `MaxAlignedAllocAlign = 2 GiB` on `realloc`) to Tier T2 (`fineCostModel`, eliminating the
     `2 GiB` `realloc` reserve when `align ≤ 16`) requires zero caller migration.
   - **Conditional-OOM contracts (`rustCli{Alloc,Dealloc,Realloc}BudgetSpec`):** `.OutOfMemory`
     carries the budget-exhaustion witness `¬ FitsEvents M lim st evs ∧ OomPreserved s0 sf`.
   - **Total-correctness (`NoOom`) contracts (`rustCli{Alloc,Dealloc,Realloc}NoOomSpec`):** under
     `FitsEvents M lim st evs` (`rustAllocEvents` / `rustReallocEvents`), **both `.OutOfMemory` and
     `0#64` null returns are discharged to `False`** (`onOom := ⌜False⌝`, non-null return), while
     `dealloc` needs zero `FitsEvents` (`FreeOnlyEvs`).
   - **`new ⇒ old` coexistence (`A.toRustCliAlloc`):** existentially quantifies `st : M.σ` at
     `zeroBudgetLimits` (`enforced = false`), recovering `RustCliAlloc`, `RustCliAllocHooks`, and
     `RustCliAllocEntries` via `rustCliAllocEntries_of_budget` (and `RustCliAllocBudgetHooks.*`
     in [`IfaceBudgetLemmas.lean`](IfaceBudgetLemmas.lean)).

## Module Map

| Module | `module` Status | Role | Key Declarations & Entry Points |
|---|---|---|---|
| [`Iface.lean`](Iface.lean) | `module` | Frozen unbudgeted state-indexed Rust global-allocator interface | `PoolPreserved`, `AllocCallPreserved`, `OomPreserved`, `RustLayoutOk`, `NullAllowed`, `RustCliAlloc`, `rustCli{Alloc,Dealloc,Realloc}Spec`, `RustCliAlloc{Hooks,Entries}` |
| [`IfaceLemmas.lean`](IfaceLemmas.lean) | `module` | Unbudgeted WP transport, OOM-preserving stack wrappers, and `.inImage` combinators | `SepWP.transport_pool`, `SepWP.transport_oom`, `Spec.withHookStackOom`, `RustCliAllocHooks.toEntries` |
| [`IfaceBudgetBase.lean`](IfaceBudgetBase.lean) | `module` | Core `AllocEvent`, `AllocCostModel`, `BudgetLimits`, and `Fits*` envelope foundations | `AllocEvent`, `AllocCostModel`, `BudgetLimits`, `zeroBudgetLimits`, `FitsStep`, `FitsEvent`, `FitsEvents`, `FitsTrace`, `FitsTraceOf`, `FitsEnv`, `SeqEnv`, `LoopFreeEnv` |
| [`IfaceBudget.lean`](IfaceBudget.lean) | `module` | Cost-model-parametric budget-threaded Rust global-allocator interface | `VmPreserved`, `RustCliAllocBudget` (`toRustCliAlloc`, `repAlloc`), `rustCli{Alloc,Dealloc,Realloc}{Budget,NoOom}Spec`, `RustCliAllocBudget{Hooks,Entries}`, `RustCliAllocNoOomEntries`, `RustCliAllocBudgetEntries.toNoOom`, `rustCliAllocEntries_of_budget` |
| [`IfaceBudgetLemmas.lean`](IfaceBudgetLemmas.lean) | `module` | Caller-side WP transport, trace/envelope slicing, and `.inImage` / stack combinators for `RustCliAllocBudget M` | `RustCliAllocBudget.{atState,atBudget}`, `SepWP.transport_budgetPool`, `SepWPp.transport_budgetPool`, `SepWP.transport_atStatePool`, `SepWPp.transport_atStatePool`, `FitsEnv.{seq_left,seq_right}`, `RustCliAllocBudgetHooks.*`, `RustCliAlloc{Budget,NoOom}Entries.*` |
| [`MallocngBridgeBudget.lean`](MallocngBridgeBudget.lean) | `module` | Model-parametric C-entry budget bridge, `coarseCostModel`, `allocMemcpyVmSpec`, and `mallocng_oom_false` | `coarseCostModel`, `coarseCostModelIface`, `MallocngCostModelIface`, `MallocngCostModelSound`, `coarseCostModelSound_of_topFacts`, `allocMemcpyVmSpec`, `allocMemcpyVm_ok_of_{hasWords,wordTree}`, `StaticMappedCover`, `mallocngBudgetPoolInv`, `mallocngBudgetPool{At,}`, `mallocngRustCliAllocBudget{At,}`, `mallocngBudgetPool{At_of_init_resources,_of_init}`, `mallocng_oom_false`, `MallocngProgBudgetCContracts`, `mallocngProgBudgetCContracts_of_placed` |
| [`MallocngRustBudget.lean`](MallocngRustBudget.lean) | `module` | Model-parametric placed `__rustc::__rdl_*` shim and `__rustc::__rust_*` `B`-thunk proofs for `RustCliAllocBudget M` | `rdl{Alloc,Dealloc,Realloc}_budget_placed_ok`, `rustCli{Alloc,Dealloc,Realloc}Budget_of_b_thunk`, `RustCliAllocBudgetEntries.of_thunks`, `mallocngRustCliAllocBudget{At,}Entries{,_thunks}`, `mallocngRustCliAllocNoOomEntries{,_thunks}` |
| [`SpecBudget.lean`](SpecBudget.lean) | `module` | Budget-threaded counterparts of trusted `AllocHooks`, `TripleRatchetHooks`, `PublicApiHooks`, and CLI extern contracts | `AllocHooksBudget`, `TripleRatchetHooksBudget`, `PublicApiHooksBudget`, `SpqrHooksBudget`, `CliExternsBudgetOk` |
| [`NonVacBudget.lean`](NonVacBudget.lean) | `module` | Pure `module` total-correctness (`onOom := ⌜False⌝`) smoke clients and worked multi-call caller recipe | `smokeAlloc72NoOomSpec`, `rustCliAllocNoOom_smoke_alloc72_{at,subroutine_ok}`, `rustCliAllocBudget_smoke_alloc72`, `smokeAlloc72ConditionalSpec`, `rustCliAllocBudget_smoke_alloc72_conditional`, `rustCliAllocNoOom_worked_{trace_obligations,seqEnv}` |
| [`Fine/CostModel.lean`](Fine/CostModel.lean) | `module` | Tier T2 `fineCostModel` (`AllocCostModel` eliminating the `2 GiB` `realloc` reserve when `align ≤ 16`) | `fineCostModel`, `FineAllocState` |
| [`Fine/RustEntriesFine.lean`](Fine/RustEntriesFine.lean) | `module` | Closed placed `__rustc::__rdl_*` and `__rustc::__rust_*` `RustCliAllocBudget fineCostModel` entries | `fineRustCliAllocBudget`, `fineRustCliAllocBudgetEntries{,_thunks}`, `fineHookRustCliAllocBudgetEntries{,_thunks}` |
| [`Fine/SpecBudgetFine.lean`](Fine/SpecBudgetFine.lean) | `module` | Closed `SpecBudget` hook & CLI-extern bundle instantiations at `(fineCostModel, fineHookRustCliAllocBudget)` | `fineAllocHooksBudget_of_b2`, `fineTripleRatchetHooksBudget_of_b2`, `fineSpqrHooksBudget_of_b2`, `fineCliExternsBudgetOk` |
| [`Fine/NonVacFine.lean`](Fine/NonVacFine.lean) | `module` | Closed `< 1 GiB` (`512 MiB`) non-vacuity and total-correctness (`onOom := ⌜False⌝`) smoke witnesses | `fineRustCliAllocBudgetEntries_nonVacuous`, `fineRustCliAllocBudget_smoke_alloc72_nonVacuous` |

## Concrete Tier T2 (`Fine/`) Instantiation (`0` Entry-Contract Premises)

All modules under `LibsignalBinary/Heap/` and `LibsignalBinary/Heap/Fine/` are strict `module`
files (`0` `import all`, `0` rows in `scripts/non_module_allowlist.txt`):

1. [`Fine/RustEntriesFine.lean`](Fine/RustEntriesFine.lean) and
   [`Fine/ElfInitFine.lean`](Fine/ElfInitFine.lean) discharge the placed `mallocng` C/Rust entry
   contracts directly for Tier T2's `fineCostModel` (`0` open `MallocngPlacedEntryContracts`
   premises).
2. [`Fine/SpecBudgetFine.lean`](Fine/SpecBudgetFine.lean) and
   [`Fine/ClientIntegration.lean`](Fine/ClientIntegration.lean) instantiate the full `SpecBudget`
   hook and CLI-extern bundles for the placed `signal-session` binary.
3. [`Fine/NonVacFine.lean`](Fine/NonVacFine.lean) proves closed, `0`-hypothesis execution and
   joint-satisfiability witnesses (`fineRustCliAllocBudgetEntries_nonVacuous`,
   `fineRustCliAllocBudget_smoke_alloc72_nonVacuous`) under a `512 MiB` physical memory cap.

## Caller Budget-Threading Recipe (`RustCliAllocBudget M`)

1. **Parameterize over `(M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)`:**
   - Exact known event sequence `evs`: carry `FitsEvents M lim st evs` in `pre` and advance `st` to
     `M.stepEvents evs st` in `post` (use `RustCliAllocNoOomEntries` or `RustCliAllocBudgetHooks`
     `NoOom` projections so every `alloc`, `realloc`, and `dealloc` has `onOom = ⌜False⌝` and
     non-null return).
   - Data-dependent / branchy callees: carry `FitsEnv M lim st E` in `pre`, existentially return
     `evs` with `E evs` and `A.pool lim (M.stepEvents evs st) sf` in `post`, and compose sequential
     callees via `SeqEnv E₁ E₂` (`FitsEnv.seq_left`, `FitsEnv.seq_right` in
     [`IfaceBudgetLemmas.lean`](IfaceBudgetLemmas.lean); worked example:
     `rustCliAllocNoOom_worked_seqEnv` in [`NonVacBudget.lean`](NonVacBudget.lean)).
   - Top-level entry point: assume a single `FitsTraceOf M lim fullLog` (or `FitsTrace M lim maxStep fullLog`)
     and slice out every intermediate call's `FitsEvents` via `fitsEvents_of_subtrace_fitsTrace`
     (worked example: `rustCliAllocNoOom_worked_trace_obligations` in [`NonVacBudget.lean`](NonVacBudget.lean)).
2. **Transport `A.pool lim st` across non-allocating caller steps:**
   - Use `A.atState lim st s` (`RustAlloc` view with `.pool = A.pool lim st s` and `.live = A.live`)
     to call existing `RustAlloc`-parameterized data-structure specs (`Vec`, `Box`, `BTreeMap`, ...),
     and rewrite `(A.atState lim st s).pool` across `VmPreserved s s'` steps via `A.pool_transport`,
     `SepWP.transport_budgetPool`, or `SepWP.transport_atStatePool`.
3. **Free-only cleanup paths (`Drop`):**
   - `rustCliDeallocNoOomSpec` / `rustCliDeallocBudgetSpec` requires **no `FitsEvents` hypothesis**,
     and `FreeOnlyEvs` bounds `M.liveBytes` monotonically downward (`M.liveBytes_free_le`).
