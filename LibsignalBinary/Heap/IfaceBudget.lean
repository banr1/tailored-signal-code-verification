/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Spec.Top
public import ProofLib.StdStartup.NonVmSteps
public import LibsignalBinary.Heap.Iface
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Cost-Model-Parametric Budget-Threaded Rust Allocator Interface

Extends `LibsignalBinary.Heap.Iface` with a stateful allocation cost model (`AllocCostModel`),
physical-memory and 48-bit virtual-address admissibility predicates (`BudgetLimits`, `FitsStep`,
`FitsEvents`, `FitsTrace`), budget-threaded Rust global allocator contracts (`RustCliAllocBudget`),
and a cost-model-parametric soundness interface (`MallocngCostModelIface`, `MallocngCostModelSound`)
for `musl` 1.2.5 `mallocng`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap

open Arm64 Arm64.CType ProofLib ProofLib.StdStartup
open CryptoVerification.RustHeap (RustAlloc LayoutOk allocHookStack)
open VerifiedLibraries.Mallocng (
  MallocngAddrs MallocngAuxvAt MallocngBrkStartWf MallocngCallAccounting
  MallocngMappedDelta MallocngMaxAllocSize MallocngNoGapOrPhys MallocngNoOrphanMappings
  MallocngOomCond MallocngRuntime MallocngSanitizedSvc MallocngStartupResources
  MallocngStepBound MallocngSvcValid MaxAlignedAllocAlign
  mallocngAddrsOfPlacement mallocngAlignedAllocOk mallocngAlignedEffSize
  mallocngMultiEntryOk mallocngPosixMemalignOk mallocngPosixMemalignRet mallocngStackBytes
)

/-! ## Virtual-Memory-Preserving Transitions -/

/-- File-descriptor frame on `fd ∈ [3, 2 ^ 31)`: holds across all non-syscall CPU steps,
    `read_stdin` (which only advances `fd = 0`), `writeFileHook` / `writeStdoutHook`, and
    `read_file`'s composite `openat + read* + close` transition when `fd ≥ 3` starts closed. -/
def FdsHiFrame (s s' : State) : Prop :=
  ∀ fd : Nat, 3 ≤ fd → fd < 2 ^ 31 →
    s'.fs.fds (BitVec.ofNat 64 fd) = s.fs.fds (BitVec.ofNat 64 fd)

theorem FdsHiFrame.refl (s : State) : FdsHiFrame s s :=
  fun _ _ _ => rfl

@[simp]
theorem FdsHiFrame.refl_iff (s : State) : FdsHiFrame s s ↔ True :=
  ⟨fun _ => trivial, fun _ => FdsHiFrame.refl s⟩

theorem FdsHiFrame.symm {s₁ s₂ : State} (h : FdsHiFrame s₁ s₂) : FdsHiFrame s₂ s₁ :=
  fun fd hlo hhi => (h fd hlo hhi).symm

theorem FdsHiFrame.trans {s₁ s₂ s₃ : State}
    (h12 : FdsHiFrame s₁ s₂) (h23 : FdsHiFrame s₂ s₃) : FdsHiFrame s₁ s₃ :=
  fun fd hlo hhi => (h23 fd hlo hhi).trans (h12 fd hlo hhi)

theorem FdsHiFrame.of_fs_eq {s s' : State} (h : s'.fs = s.fs) : FdsHiFrame s s' :=
  fun _ _ _ => by rw [h]

theorem FdsHiFrame.of_fds_eq {s s' : State} (h : s'.fs.fds = s.fs.fds) : FdsHiFrame s s' :=
  fun _ _ _ => by rw [h]

/-- Virtual- and physical-memory fields preserved across allocator-compatible steps, including non-VM syscalls (`openat`, `read`, `close`) that mutate `fs.fds`. -/
def VmMemPreserved (s s' : State) : Prop :=
  PoolPreserved s s' ∧ s'.physMemAvail = s.physMemAvail ∧
    ∀ a : BitVec 64, s'.mem.perm a = s.mem.perm a

theorem VmMemPreserved.refl (s : State) : VmMemPreserved s s :=
  ⟨PoolPreserved.refl s, rfl, fun _ => rfl⟩

theorem VmMemPreserved.symm {s₁ s₂ : State} (h : VmMemPreserved s₁ s₂) : VmMemPreserved s₂ s₁ :=
  ⟨⟨h.1.1.symm, h.1.2.1.symm, h.1.2.2.symm⟩, h.2.1.symm, fun a => (h.2.2 a).symm⟩

theorem VmMemPreserved.trans {s₁ s₂ s₃ : State}
    (h12 : VmMemPreserved s₁ s₂) (h23 : VmMemPreserved s₂ s₃) : VmMemPreserved s₁ s₃ :=
  ⟨h12.1.trans h23.1, h23.2.1.trans h12.2.1, fun a => (h23.2.2 a).trans (h12.2.2 a)⟩

theorem VmMemPreserved.of_vm_tpidr {s s' : State}
    (hvm : VmFieldsPreserved s s') (htp : s'.tpidrEl0 = s.tpidrEl0) :
    VmMemPreserved s s' :=
  ⟨⟨hvm.brkStart_eq, hvm.brk_eq, htp⟩, hvm.physMemAvail_eq, hvm.perm_eq⟩

/-- State fields preserved across budget-threaded caller transitions:
    `PoolPreserved s s'` (`brkStart`, `brk`, `tpidrEl0`), `physMemAvail`, per-byte page
    permissions `mem.perm`, and `FdsHiFrame s s'` (`fs.fds` on `fd ∈ [3, 2 ^ 31)`). -/
def VmPreserved (s s' : State) : Prop :=
  PoolPreserved s s' ∧ s'.physMemAvail = s.physMemAvail ∧
    (∀ a : BitVec 64, s'.mem.perm a = s.mem.perm a) ∧ FdsHiFrame s s'

theorem VmPreserved.toVmMemPreserved {s s' : State} (h : VmPreserved s s') : VmMemPreserved s s' :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem VmPreserved.refl (s : State) : VmPreserved s s :=
  ⟨PoolPreserved.refl s, rfl, fun _ => rfl, FdsHiFrame.refl s⟩

theorem VmPreserved.trans {s₁ s₂ s₃ : State}
    (h12 : VmPreserved s₁ s₂) (h23 : VmPreserved s₂ s₃) : VmPreserved s₁ s₃ :=
  ⟨h12.1.trans h23.1, h23.2.1.trans h12.2.1,
    fun a => (h23.2.2.1 a).trans (h12.2.2.1 a), h12.2.2.2.trans h23.2.2.2⟩

theorem VmPreserved.toPoolPreserved {s s' : State} (h : VmPreserved s s') : PoolPreserved s s' :=
  h.1

theorem VmPreserved.perm_eq {s s' : State} (h : VmPreserved s s') :
    ∀ a : BitVec 64, s'.mem.perm a = s.mem.perm a :=
  h.2.2.1

theorem VmPreserved.fdsHiFrame {s s' : State} (h : VmPreserved s s') : FdsHiFrame s s' :=
  h.2.2.2

theorem VmPreserved.of_vm_tpidr {s s' : State}
    (hvm : VmFieldsPreserved s s') (htp : s'.tpidrEl0 = s.tpidrEl0)
    (hfds : FdsHiFrame s s') :
    VmPreserved s s' :=
  ⟨⟨hvm.brkStart_eq, hvm.brk_eq, htp⟩, hvm.physMemAvail_eq, hvm.perm_eq, hfds⟩

/-! ## Abstract Allocator Events and Cost Models -/

/-- Abstract allocator operation in a ghost allocation trace, carrying `align` on aligned
allocations, `free`, and `realloc` so alignment-aware cost models can track size classes and avoid
`MaxAlignedAllocAlign` over-charges on small-alignment `realloc`. -/
inductive AllocEvent where
  | alloc (req : Nat)
  | aligned (align req : Nat)
  | free (align req : Nat)
  | realloc (align old new : Nat)
  deriving DecidableEq, Repr

/-- Whether `ev`'s request size fits within `musl` 1.2.5 `mallocng`'s `MallocngMaxAllocSize`
    (`SIZE_MAX / 2 - 4097`). -/
def AllocEvent.withinMaxAlloc : AllocEvent → Prop
  | .alloc req => req ≤ MallocngMaxAllocSize
  | .aligned align req => mallocngAlignedEffSize align req ≤ MallocngMaxAllocSize
  | .free _ _ => True
  | .realloc _ _ new => new ≤ MallocngMaxAllocSize

instance (ev : AllocEvent) : Decidable ev.withinMaxAlloc := by
  cases ev <;> unfold AllocEvent.withinMaxAlloc <;> infer_instance

/-- User-requested payload byte count of `ev` (bounded by `M.stepReserve ev st` via
    `M.req_le_stepReserve`, ruling out `NullAllowed` whenever `FitsEvents` holds). -/
def AllocEvent.reqBytes : AllocEvent → Nat
  | .alloc req => req
  | .aligned align req => mallocngAlignedEffSize align req
  | .free _ _ => 0
  | .realloc _ _ new => new

/-- Deterministic `AllocEvent` list emitted by `__rustc::__rdl_alloc(size, align)`:
    `malloc(size)` when `align ≤ 16 ∧ align ≤ size`, else `posix_memalign(&slot, max align 8, size)`. -/
def rustAllocEvents (size align : Nat) : List AllocEvent :=
  if align ≤ 16 ∧ align ≤ size then
    [.alloc size]
  else
    [.aligned (max align 8) size]

/-- Deterministic `AllocEvent` list emitted by `__rustc::__rdl_dealloc(p, size, align)`:
    `free(p)`. -/
def rustDeallocEvents (size align : Nat) : List AllocEvent :=
  [.free align size]

/-- Deterministic `AllocEvent` list emitted by `__rustc::__rdl_realloc(p, old, align, new)`:
    `realloc(p, new)` when `align ≤ 16 ∧ align ≤ new`, else `posix_memalign(&slot, max align 8, new)`
    (while `old` is still live), `memcpy`, and `free(p)` — two events in execution order so
    peak-sensitive models capture the transient overlap accurately. -/
def rustReallocEvents (old new align : Nat) : List AllocEvent :=
  if align ≤ 16 ∧ align ≤ new then
    [.realloc align old new]
  else
    [.aligned (max align 8) new, .free align old]

/-- Stateful allocator cost model bundling state transitions, dynamic byte and interval bounds, single-call step reserves, and monotonicity laws. -/
structure AllocCostModel : Type 1 where
  /-- Abstract cost-model state. -/
  σ : Type
  /-- Initial state for an empty allocator heap (`ivs = []`) at startup. -/
  init : σ
  /-- Deterministic abstract transition for one `AllocEvent`. -/
  step : AllocEvent → σ → σ
  /-- Upper bound on dynamic mapped bytes `(ivs.map Prod.snd).sum`. -/
  footprint : σ → Nat
  /-- Upper bound on dynamic mapped interval count `ivs.length`. -/
  maxDynIvs : σ → Nat
  /-- Upper bound on newly mapped bytes and any failing `mmap` request (`sz ≤ stepReserve ev st`) when executing `ev` from `st`. -/
  stepReserve : AllocEvent → σ → Nat
  /-- Live-byte cost metric guaranteed not to increase on `.free`. -/
  liveBytes : σ → Nat
  /-- `footprint` is non-decreasing across every `step`. -/
  footprint_mono : ∀ (ev : AllocEvent) (st : σ), footprint st ≤ footprint (step ev st)
  /-- `maxDynIvs` is non-decreasing across every `step`. -/
  maxDynIvs_mono : ∀ (ev : AllocEvent) (st : σ), maxDynIvs st ≤ maxDynIvs (step ev st)
  /-- `stepReserve ev₀` is non-decreasing across every `step ev`. -/
  stepReserve_mono : ∀ (ev₀ ev : AllocEvent) (st : σ),
    stepReserve ev₀ st ≤ stepReserve ev₀ (step ev st)
  /-- `stepReserve ev st` covers at least `ev.reqBytes`, discharging `NullAllowed` automatically
      whenever `FitsEvents` holds. -/
  req_le_stepReserve : ∀ (ev : AllocEvent) (st : σ), ev.reqBytes ≤ stepReserve ev st
  /-- `liveBytes` is non-increasing on `.free`. -/
  liveBytes_free_le : ∀ (al n : Nat) (st : σ), liveBytes (step (.free al n) st) ≤ liveBytes st

namespace AllocCostModel

variable (M : AllocCostModel)

def stepEvents (evs : List AllocEvent) (st : M.σ) : M.σ :=
  evs.foldl (fun acc ev => M.step ev acc) st

def evalLog (log : List AllocEvent) : M.σ :=
  M.stepEvents log M.init

@[simp] theorem stepEvents_nil (st : M.σ) : M.stepEvents [] st = st := rfl

@[simp] theorem stepEvents_cons (ev : AllocEvent) (evs : List AllocEvent) (st : M.σ) :
    M.stepEvents (ev :: evs) st = M.stepEvents evs (M.step ev st) := rfl

theorem stepEvents_append (evs₁ evs₂ : List AllocEvent) (st : M.σ) :
    M.stepEvents (evs₁ ++ evs₂) st = M.stepEvents evs₂ (M.stepEvents evs₁ st) := by
  unfold stepEvents
  exact List.foldl_append

theorem evalLog_append (log₁ log₂ : List AllocEvent) :
    M.evalLog (log₁ ++ log₂) = M.stepEvents log₂ (M.evalLog log₁) :=
  M.stepEvents_append log₁ log₂ M.init

theorem footprint_mono_events : ∀ (evs : List AllocEvent) (st : M.σ),
    M.footprint st ≤ M.footprint (M.stepEvents evs st)
  | [], _ => Nat.le_refl _
  | ev :: evs, st =>
    Nat.le_trans (M.footprint_mono ev st) (footprint_mono_events evs (M.step ev st))

theorem maxDynIvs_mono_events : ∀ (evs : List AllocEvent) (st : M.σ),
    M.maxDynIvs st ≤ M.maxDynIvs (M.stepEvents evs st)
  | [], _ => Nat.le_refl _
  | ev :: evs, st =>
    Nat.le_trans (M.maxDynIvs_mono ev st) (maxDynIvs_mono_events evs (M.step ev st))

theorem stepReserve_mono_events (ev₀ : AllocEvent) : ∀ (evs : List AllocEvent) (st : M.σ),
    M.stepReserve ev₀ st ≤ M.stepReserve ev₀ (M.stepEvents evs st)
  | [], _ => Nat.le_refl _
  | ev :: evs, st =>
    Nat.le_trans (M.stepReserve_mono ev₀ ev st) (stepReserve_mono_events ev₀ evs (M.step ev st))

end AllocCostModel

/-! ## Budget Limits and Admissibility Predicates -/

/-- Process-level static virtual-memory and physical-memory bounds for non-OOM discharge:
* `staticCount`: upper bound on static mapped interval count (ELF segments, stack, initial `brk`);
* `staticBytes`: upper bound on static mapped byte count;
* `physCap`: conserved initial `physPlusRw`;
* `enforced`: `false` only in `zeroBudgetLimits` for projecting to unbudgeted `RustCliAlloc`. -/
structure BudgetLimits where
  staticCount : Nat
  staticBytes : Nat
  physCap     : Nat
  enforced    : Bool := true
  deriving DecidableEq, Repr

/-- Unenforced sentinel `BudgetLimits` used to project `RustCliAllocBudget M` down to unbudgeted
    `RustCliAlloc` (`enforced = false`, so `PoolPreserved` suffices and `FitsEvent` is `False`). -/
def zeroBudgetLimits : BudgetLimits :=
  { staticCount := 0, staticBytes := 0, physCap := 0, enforced := false }

/-- Exact physical-RAM and 48-bit user-VA-gap inequalities discharging `MallocngNoGapOrPhys sf sz`
    via `ProofLib.rwBytes_le_intervals_sum` + `ProofLib.physPlusRw_steps_withSvc_alloc` and
    `ProofLib.hasGap_of_mappedIntervals` (`arm64-semantics/ProofLib/MallocngBridge.lean`). -/
def FitsStep (lim : BudgetLimits) (stepB dynIvs fp : Nat) : Prop :=
  lim.enforced = true ∧
  lim.staticBytes + fp + 2 * stepB ≤ lim.physCap ∧
  MMAP_MIN_ADDR + lim.staticBytes + fp + stepB +
    (lim.staticCount + dynIvs + 16) * (stepB + PAGE_SIZE) + stepB ≤ 2 ^ 48

theorem FitsStep.mono {lim : BudgetLimits} {step₁ step₂ dyn₁ dyn₂ fp₁ fp₂ : Nat}
    (h : FitsStep lim step₂ dyn₂ fp₂)
    (hstep : step₁ ≤ step₂) (hdyn : dyn₁ ≤ dyn₂) (hfp : fp₁ ≤ fp₂) :
    FitsStep lim step₁ dyn₁ fp₁ := by
  rcases h with ⟨henf, hram, hva⟩
  have hmul :
      (lim.staticCount + dyn₁ + 16) * (step₁ + PAGE_SIZE) ≤
        (lim.staticCount + dyn₂ + 16) * (step₂ + PAGE_SIZE) :=
    Nat.mul_le_mul (by omega) (by omega)
  exact ⟨henf, by omega, by omega⟩

/-- Single-event budget admissibility at cost-model state `st`. -/
def FitsEvent (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ) (ev : AllocEvent) : Prop :=
  ev.withinMaxAlloc ∧
  FitsStep lim (M.stepReserve ev st) (M.maxDynIvs st) (M.footprint st)

theorem not_fitsEvent_zeroBudgetLimits (M : AllocCostModel) (st : M.σ) (ev : AllocEvent) :
    ¬ FitsEvent M zeroBudgetLimits st ev := by
  rintro ⟨_, henf, _, _⟩
  cases henf

/-- Sequential event-list budget admissibility along `M.stepEvents evs st`. -/
def FitsEvents (M : AllocCostModel) (lim : BudgetLimits) : M.σ → List AllocEvent → Prop
  | _, [] => True
  | st, ev :: evs => FitsEvent M lim st ev ∧ FitsEvents M lim (M.step ev st) evs

@[simp] theorem fitsEvents_nil (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ) :
    FitsEvents M lim st [] = True := rfl

@[simp] theorem fitsEvents_cons (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ)
    (ev : AllocEvent) (evs : List AllocEvent) :
    FitsEvents M lim st (ev :: evs) =
      (FitsEvent M lim st ev ∧ FitsEvents M lim (M.step ev st) evs) := rfl

theorem fitsEvents_append (M : AllocCostModel) (lim : BudgetLimits) :
    ∀ (evs₁ evs₂ : List AllocEvent) (st : M.σ),
      FitsEvents M lim st (evs₁ ++ evs₂) ↔
        FitsEvents M lim st evs₁ ∧ FitsEvents M lim (M.stepEvents evs₁ st) evs₂
  | [], _, _ => by simp
  | ev :: evs₁, evs₂, st => by
    simp only [List.cons_append, fitsEvents_cons, AllocCostModel.stepEvents_cons,
      fitsEvents_append M lim evs₁ evs₂ (M.step ev st), and_assoc]

/-- Maximum `M.stepReserve ev st` across a finite event log `log` at state `st`. -/
def maxStepOf (M : AllocCostModel) (st : M.σ) (log : List AllocEvent) : Nat :=
  (log.map (fun ev => M.stepReserve ev st)).foldr max 0

theorem stepReserve_le_maxStepOf {M : AllocCostModel} {st : M.σ} :
    ∀ {log : List AllocEvent} {ev : AllocEvent},
      ev ∈ log → M.stepReserve ev st ≤ maxStepOf M st log
  | [], _, h => nomatch h
  | _ :: _, _, h => by
    unfold maxStepOf
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (stepReserve_le_maxStepOf hmem) (Nat.le_max_right _ _)

/-- Whole-trace admissibility with explicit single-call step reserve cap `maxStep`: checks
    `FitsStep` once at `stFinal = M.evalLog fullLog`. -/
def FitsTrace (M : AllocCostModel) (lim : BudgetLimits) (maxStep : Nat)
    (fullLog : List AllocEvent) : Prop :=
  let stFinal := M.evalLog fullLog
  (∀ ev ∈ fullLog, ev.withinMaxAlloc ∧ M.stepReserve ev stFinal ≤ maxStep) ∧
  FitsStep lim maxStep (M.maxDynIvs stFinal) (M.footprint stFinal)

def FitsTraceOf (M : AllocCostModel) (lim : BudgetLimits) (fullLog : List AllocEvent) : Prop :=
  FitsTrace M lim (maxStepOf M (M.evalLog fullLog) fullLog) fullLog

theorem fitsEvents_of_step_monotone (M : AllocCostModel) (lim : BudgetLimits) (maxStep : Nat) :
    ∀ (evs suf : List AllocEvent) (st : M.σ),
      (let stFinal := M.stepEvents (evs ++ suf) st
       (∀ ev ∈ evs, ev.withinMaxAlloc ∧ M.stepReserve ev stFinal ≤ maxStep) ∧
       FitsStep lim maxStep (M.maxDynIvs stFinal) (M.footprint stFinal)) →
      FitsEvents M lim st evs
  | [], _, _, _ => trivial
  | ev :: evs, suf, st, hAll => by
    dsimp only at hAll
    rw [List.cons_append, AllocCostModel.stepEvents_cons] at hAll
    rcases hAll with ⟨hBnd, hFitFinal⟩
    have ⟨hevMax, hevStep⟩ := hBnd ev List.mem_cons_self
    let stAfterEv := M.step ev st
    let rem := evs ++ suf
    have hStepLe : M.stepReserve ev st ≤ maxStep :=
      Nat.le_trans (M.stepReserve_mono ev ev st)
        (Nat.le_trans (M.stepReserve_mono_events ev rem stAfterEv) hevStep)
    have hDynLe : M.maxDynIvs st ≤ M.maxDynIvs (M.stepEvents rem stAfterEv) :=
      Nat.le_trans (M.maxDynIvs_mono ev st) (M.maxDynIvs_mono_events rem stAfterEv)
    have hFpLe : M.footprint st ≤ M.footprint (M.stepEvents rem stAfterEv) :=
      Nat.le_trans (M.footprint_mono ev st) (M.footprint_mono_events rem stAfterEv)
    refine ⟨⟨hevMax, hFitFinal.mono hStepLe hDynLe hFpLe⟩, ?_⟩
    exact fitsEvents_of_step_monotone M lim maxStep evs suf stAfterEv
      ⟨fun e he => hBnd e (List.mem_cons_of_mem ev he), hFitFinal⟩

/-- If `fullLog = pre ++ evs ++ suf` satisfies `FitsTrace M lim maxStep fullLog`, then `FitsEvents M lim (M.evalLog pre) evs` holds. -/
theorem fitsEvents_of_subtrace_fitsTrace {M : AllocCostModel} {lim : BudgetLimits}
    {maxStep : Nat} {pre evs suf fullLog : List AllocEvent}
    (hLog : fullLog = pre ++ evs ++ suf)
    (hFit : FitsTrace M lim maxStep fullLog) :
    FitsEvents M lim (M.evalLog pre) evs := by
  subst hLog
  rcases hFit with ⟨hBnd, hStepFinal⟩
  have hFinalEq : M.evalLog (pre ++ evs ++ suf) = M.stepEvents (evs ++ suf) (M.evalLog pre) := by
    rw [List.append_assoc, M.evalLog_append]
  refine fitsEvents_of_step_monotone M lim maxStep evs suf (M.evalLog pre) ?_
  dsimp only
  rw [← hFinalEq]
  exact ⟨fun ev hev => hBnd ev (by simp [List.mem_append, hev]), hStepFinal⟩

theorem fitsEvents_of_prefix_fitsTrace {M : AllocCostModel} {lim : BudgetLimits}
    {maxStep : Nat} {pre evs fullLog : List AllocEvent}
    (hPref : pre ++ evs <+: fullLog)
    (hFit : FitsTrace M lim maxStep fullLog) :
    FitsEvents M lim (M.evalLog pre) evs := by
  rcases hPref with ⟨suf, hEq⟩
  exact fitsEvents_of_subtrace_fitsTrace hEq.symm hFit

theorem not_fitsEvents_zeroBudgetLimits_rustAlloc (M : AllocCostModel) (st : M.σ)
    (size align : Nat) :
    ¬ FitsEvents M zeroBudgetLimits st (rustAllocEvents size align) := by
  unfold rustAllocEvents
  split <;> intro h <;> exact not_fitsEvent_zeroBudgetLimits M st _ h.1

theorem not_fitsEvents_zeroBudgetLimits_rustRealloc (M : AllocCostModel) (st : M.σ)
    (old new align : Nat) :
    ¬ FitsEvents M zeroBudgetLimits st (rustReallocEvents old new align) := by
  unfold rustReallocEvents
  split <;> intro h <;> exact not_fitsEvent_zeroBudgetLimits M st _ h.1

theorem not_nullAllowed_of_fitsAllocEvents {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {size align : Nat} (hLayout : RustLayoutOk size align)
    (hFit : FitsEvents M lim st (rustAllocEvents size align)) :
    ¬ NullAllowed size align := by
  have hal : align ≤ 2 ^ 31 := hLayout.2
  unfold rustAllocEvents at hFit
  split at hFit
  · rcases hFit with ⟨⟨_, _, _, hva⟩, _⟩
    have hreq : size ≤ M.stepReserve (.alloc size) st := M.req_le_stepReserve (.alloc size) st
    unfold NullAllowed; omega
  · rcases hFit with ⟨⟨_, _, _, hva⟩, _⟩
    have hsize_eff : size ≤ (AllocEvent.aligned (max align 8) size).reqBytes := by
      dsimp only [AllocEvent.reqBytes, mallocngAlignedEffSize]
      split <;> omega
    have hreq :
        (AllocEvent.aligned (max align 8) size).reqBytes ≤
          M.stepReserve (.aligned (max align 8) size) st :=
      M.req_le_stepReserve (.aligned (max align 8) size) st
    unfold NullAllowed; omega

theorem not_nullAllowed_of_fitsReallocEvents {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {old new align : Nat} (hLayout : RustLayoutOk new align)
    (hFit : FitsEvents M lim st (rustReallocEvents old new align)) :
    ¬ NullAllowed new align := by
  have hal : align ≤ 2 ^ 31 := hLayout.2
  unfold rustReallocEvents at hFit
  split at hFit
  · rcases hFit with ⟨⟨_, _, _, hva⟩, _⟩
    have hreq : new ≤ M.stepReserve (.realloc align old new) st :=
      M.req_le_stepReserve (.realloc align old new) st
    unfold NullAllowed; omega
  · rcases hFit with ⟨⟨_, _, _, hva⟩, _⟩
    have hnew_eff : new ≤ (AllocEvent.aligned (max align 8) new).reqBytes := by
      dsimp only [AllocEvent.reqBytes, mallocngAlignedEffSize]
      split <;> omega
    have hreq :
        (AllocEvent.aligned (max align 8) new).reqBytes ≤
          M.stepReserve (.aligned (max align 8) new) st :=
      M.req_le_stepReserve (.aligned (max align 8) new) st
    unfold NullAllowed; omega

/-! ## Budget-Threaded Rust Global Allocator -/

/-- A Rust global allocator indexed by `BudgetLimits`, cost-model state `st : M.σ`, and machine
    state `s : State`. -/
structure RustCliAllocBudget (M : AllocCostModel) where
  pool : BudgetLimits → M.σ → State → SepProp
  live : BitVec 64 → Nat → Nat → SepProp
  /-- Live blocks are non-null, aligned, fit below `2 ^ 64`, and satisfy `RustLayoutOk`. -/
  block_valid : ∀ p n al, live p n al ⊢
    ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ live p n al
  /-- Across `VmPreserved` steps, `pool lim st` is invariant for every `lim` and `st`. -/
  pool_transport : ∀ (lim : BudgetLimits) (st : M.σ) (s s' : State),
    VmPreserved s s' → pool lim st s' = pool lim st s
  /-- At `zeroBudgetLimits` (`enforced = false`), `PoolPreserved` alone transports `pool`, allowing
      clean projection to `RustCliAlloc` (`toRustCliAlloc`). -/
  pool_zero_transport : ∀ (st : M.σ) (s s' : State),
    PoolPreserved s s' → pool zeroBudgetLimits st s' = pool zeroBudgetLimits st s

namespace RustCliAllocBudget

variable {M : AllocCostModel} (A : RustCliAllocBudget M)

/-- Forget budget tracking (`lim := zeroBudgetLimits`, existentializing `st : M.σ`) to obtain an
    ordinary unbudgeted `RustCliAlloc` (`LibsignalBinary.Heap.Iface`). -/
def toRustCliAlloc : RustCliAlloc where
  pool := fun s => ∃∗ st : M.σ, A.pool zeroBudgetLimits st s
  live := A.live
  block_valid := A.block_valid
  pool_transport := by
    intro s s' h
    have hfun : (fun st : M.σ => A.pool zeroBudgetLimits st s') =
        (fun st : M.σ => A.pool zeroBudgetLimits st s) :=
      funext fun st => A.pool_zero_transport st s s' h
    simp only [hfun]

/-- `A`'s live-block tokens as a `RustAlloc` (for container predicates `vecU8`, `boxAt`, ...). -/
def repAlloc : RustAlloc := { pool := emp, live := A.live }

@[simp] theorem toRustCliAlloc_live : A.toRustCliAlloc.live = A.live := rfl
@[simp] theorem repAlloc_live : A.repAlloc.live = A.live := rfl

variable {A}

theorem pool_of_vmPreserved {lim : BudgetLimits} {st : M.σ} {s0 sf : State}
    (h : VmPreserved s0 sf) : A.pool lim st sf = A.pool lim st s0 :=
  A.pool_transport lim st s0 sf h

@[simp] theorem pool_setPC (lim : BudgetLimits) (st : M.σ) (s : State) (pc : BitVec 64) :
    A.pool lim st (s.setPC pc) = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

@[simp] theorem pool_advancePC (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s.advancePC = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

@[simp] theorem pool_setPState (lim : BudgetLimits) (st : M.σ) (s : State) (ps : PState) :
    A.pool lim st (s.setPState ps) = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

@[simp] theorem pool_writeReg64 (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : Reg) (v : BitVec 64) :
    A.pool lim st (s.writeReg64 r v) = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; cases r <;> rfl, fun _ => by cases s; cases r <;> rfl,
      fun _ _ _ => by cases s; cases r <;> rfl⟩

@[simp] theorem pool_writeReg32 (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : Reg) (v : BitVec 32) :
    A.pool lim st (s.writeReg32 r v) = A.pool lim st s :=
  A.pool_writeReg64 lim st s r _

@[simp] theorem pool_writeReg (lim : BudgetLimits) (st : M.σ) (s : State)
    (w : Width) (r : Reg) (v : BitVec 64) :
    A.pool lim st (s.writeReg w r v) = A.pool lim st s :=
  A.pool_writeReg64 lim st s r _

@[simp] theorem pool_writeVReg128 (lim : BudgetLimits) (st : M.σ) (s : State)
    (i : BitVec 5) (v : BitVec 128) :
    A.pool lim st (s.writeVReg128 i v) = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

@[simp] theorem pool_writeVReg64 (lim : BudgetLimits) (st : M.σ) (s : State)
    (i : BitVec 5) (v : BitVec 64) :
    A.pool lim st (s.writeVReg64 i v) = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

@[simp] theorem pool_writeVReg32 (lim : BudgetLimits) (st : M.σ) (s : State)
    (i : BitVec 5) (v : BitVec 32) :
    A.pool lim st (s.writeVReg32 i v) = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

@[simp] theorem pool_setMem_writeBytes (lim : BudgetLimits) (st : M.σ) (s : State)
    (addr : BitVec 64) (bs : List (BitVec 8)) :
    A.pool lim st (s.setMem (s.mem.writeBytes addr bs)) = A.pool lim st s :=
  A.pool_transport lim st s _ ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun a => by
    have hp := congrFun (Memory.perm_writeBytes s.mem addr bs) a
    cases s; exact hp, fun _ _ _ => by cases s; rfl⟩

@[simp] theorem pool_setMem_write8 (lim : BudgetLimits) (st : M.σ) (s : State)
    (addr : BitVec 64) (v : BitVec 8) :
    A.pool lim st (s.setMem (s.mem.write8 addr v)) = A.pool lim st s :=
  A.pool_transport lim st s _ ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun a => by
    have hp := congrFun (Memory.perm_write8 s.mem addr v) a
    cases s; exact hp, fun _ _ _ => by cases s; rfl⟩

@[simp] theorem pool_setMem_write16 (lim : BudgetLimits) (st : M.σ) (s : State)
    (addr : BitVec 64) (v : BitVec 16) :
    A.pool lim st (s.setMem (s.mem.write16 addr v)) = A.pool lim st s :=
  A.pool_transport lim st s _ ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun a => by
    have hp := congrFun (Memory.perm_write16 s.mem addr v) a
    cases s; exact hp, fun _ _ _ => by cases s; rfl⟩

@[simp] theorem pool_setMem_write32 (lim : BudgetLimits) (st : M.σ) (s : State)
    (addr : BitVec 64) (v : BitVec 32) :
    A.pool lim st (s.setMem (s.mem.write32 addr v)) = A.pool lim st s :=
  A.pool_transport lim st s _ ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun a => by
    have hp := congrFun (Memory.perm_write32 s.mem addr v) a
    cases s; exact hp, fun _ _ _ => by cases s; rfl⟩

@[simp] theorem pool_setMem_write64 (lim : BudgetLimits) (st : M.σ) (s : State)
    (addr : BitVec 64) (v : BitVec 64) :
    A.pool lim st (s.setMem (s.mem.write64 addr v)) = A.pool lim st s :=
  A.pool_transport lim st s _ ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun a => by
    have hp := congrFun (Memory.perm_write64 s.mem addr v) a
    cases s; exact hp, fun _ _ _ => by cases s; rfl⟩

end RustCliAllocBudget

/-! ## Conditional-OOM and Total-Correctness Allocator Contracts -/

open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

/-- Conditional-OOM budget-threaded contract for `__rust_alloc` (`zeroed = false`) and
    `__rust_alloc_zeroed` (`zeroed = true`). Ghost: `(size, align, st)`.
    `.OutOfMemory` is permitted **only** when `¬ FitsEvents M lim st (rustAllocEvents size align)`. -/
def rustCliAllocBudgetSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (zeroed : Bool) : Spec (Nat × Nat × M.σ) where
  pre := fun (size, align, st) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      RustLayoutOk size align ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp allocHookStack
  post := fun (size, align, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustAllocEvents size align) st
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) size align ∗
         (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
          else memRegion (sf.readReg64 .x0) size))
  onOom := fun (size, align, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustAllocEvents size align) ∧ OomPreserved s0 sf⌝

/-- Budget-threaded contract for `__rust_dealloc(ptr = x0, size = x1, align = x2)`.
    Ghost: `(ptr, size, align, st)`. Never hits `.OutOfMemory` (`onOom := ⌜False⌝`) and guarantees
    `M.liveBytes (M.stepEvents (rustDeallocEvents size align) st) ≤ M.liveBytes st`. -/
def rustCliDeallocBudgetSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := fun (p, size, align, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp allocHookStack
  post := fun (_, size, align, st) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents size align) st
    ⌜AllocCallPreserved s0 sf ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp allocHookStack

/-- Conditional-OOM budget-threaded contract for `__rust_realloc(ptr, old, align, new)`.
    Ghost: `(ptr, old, align, new, bs, st)`.
    `.OutOfMemory` is permitted **only** when `¬ FitsEvents M lim st (rustReallocEvents old new align)`. -/
def rustCliReallocBudgetSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) where
  pre := fun (p, old, align, new, bs, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
      bs.length ≤ new ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp allocHookStack
  post := fun (p, old, align, new, bs, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustReallocEvents old new align) st
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜NullAllowed new align⌝ ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) new align ∗
          (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))
  onOom := fun (_, old, align, new, _, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustReallocEvents old new align) ∧ OomPreserved s0 sf⌝

/-- Total-correctness (`onOom := ⌜False⌝`, non-null return) contract for `__rust_alloc` under
    `FitsEvents M lim st (rustAllocEvents size align)`. Both `.OutOfMemory` and `NullAllowed` are
    ruled out by `FitsEvents`. -/
def rustCliAllocNoOomSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (zeroed : Bool) : Spec (Nat × Nat × M.σ) where
  pre := fun (size, align, st) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      RustLayoutOk size align ∧ FitsEvents M lim st (rustAllocEvents size align) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp allocHookStack
  post := fun (size, align, st) s0 sf =>
    let st' := M.stepEvents (rustAllocEvents size align) st
    ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % align = 0⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp allocHookStack ∗
      A.live (sf.readReg64 .x0) size align ∗
      (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
       else memRegion (sf.readReg64 .x0) size)
  onOom := fun _ _ _ => ⌜False⌝

abbrev rustCliDeallocNoOomSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) :=
  rustCliDeallocBudgetSpec M A lim

/-- Total-correctness (`onOom := ⌜False⌝`, non-null return) contract for `__rust_realloc` under
    `FitsEvents M lim st (rustReallocEvents old new align)`. Both `.OutOfMemory` and `NullAllowed`
    are ruled out by `FitsEvents`. -/
def rustCliReallocNoOomSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) where
  pre := fun (p, old, align, new, bs, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
      bs.length ≤ new ∧ FitsEvents M lim st (rustReallocEvents old new align) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp allocHookStack
  post := fun (_, old, align, new, bs, st) s0 sf =>
    let st' := M.stepEvents (rustReallocEvents old new align) st
    ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % align = 0⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp allocHookStack ∗
      A.live (sf.readReg64 .x0) new align ∗
      (sf.readReg64 .x0 ↦ₛ bs) ∗
      memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length)
  onOom := fun _ _ _ => ⌜False⌝

/-! ## Hook and Subroutine Bundles -/

/-- Hook-mode bundle for conditional-OOM budget-threaded allocator contracts across all `lim`. -/
structure RustCliAllocBudgetHooks [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (hooks : String → Option (State → State)) : Prop where
  alloc : ∀ lim : BudgetLimits, HookSat hooks "__rustc::__rust_alloc"
    (rustCliAllocBudgetSpec M A lim false)
  dealloc : ∀ lim : BudgetLimits, HookSat hooks "__rustc::__rust_dealloc"
    (rustCliDeallocBudgetSpec M A lim)
  realloc : ∀ lim : BudgetLimits, HookSat hooks "__rustc::__rust_realloc"
    (rustCliReallocBudgetSpec M A lim)

/-- Native placed subroutine bundle (`subroutine_ok P`) for conditional-OOM budget-threaded
    allocator contracts across all `lim : BudgetLimits`. -/
structure RustCliAllocBudgetEntries [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (P : Program) (addrs : RustAllocAddrs) : Prop where
  alloc : ∀ lim : BudgetLimits,
    subroutine_ok P addrs.alloc (rustCliAllocBudgetSpec M A lim false)
  dealloc : ∀ lim : BudgetLimits,
    subroutine_ok P addrs.dealloc (rustCliDeallocBudgetSpec M A lim)
  realloc : ∀ lim : BudgetLimits,
    subroutine_ok P addrs.realloc (rustCliReallocBudgetSpec M A lim)

/-- Native placed subroutine bundle (`subroutine_ok P`) specialized to `onOom := ⌜False⌝` at `lim`. -/
structure RustCliAllocNoOomEntries [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (P : Program) (addrs : RustAllocAddrs) : Prop where
  alloc : subroutine_ok P addrs.alloc (rustCliAllocNoOomSpec M A lim false)
  dealloc : subroutine_ok P addrs.dealloc (rustCliDeallocNoOomSpec M A lim)
  realloc : subroutine_ok P addrs.realloc (rustCliReallocNoOomSpec M A lim)

theorem subroutine_ok_allocNoOom_of_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {entry : BitVec 64} {zeroed : Bool}
    (h : subroutine_ok P entry (rustCliAllocBudgetSpec M A lim zeroed)) :
    subroutine_ok P entry (rustCliAllocNoOomSpec M A lim zeroed) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨size, align, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [rustCliAllocNoOomSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlay, hFit, hlr⟩, hrest⟩
  have hpreB : s0.mem ⊨ (rustCliAllocBudgetSpec M A lim zeroed).pre (size, align, st) s0 ∗ R := by
    dsimp only [rustCliAllocBudgetSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay, hlr⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (size, align, st) R s0 hpc hrun hpreB hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustCliAllocBudgetSpec] at hpost
    by_cases hnull : sf.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost
      have hna : NullAllowed size align := by
        have hEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
              stackAt s0.sp allocHookStack ∗ ⌜NullAllowed size align⌝) ∗ R =
            ⌜NullAllowed size align⌝ ∗
              (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
                stackAt s0.sp allocHookStack ∗ R) := by ac_rfl
        rw [hEq, satisfies_pure_sepConj] at hpost
        exact hpost.1
      exact False.elim (not_nullAllowed_of_fitsAllocEvents hlay hFit hna)
    · simp only [hnull, ↓reduceIte] at hpost
      dsimp only [rustCliAllocNoOomSpec]
      have hEq1 :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
            stackAt s0.sp allocHookStack ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) size align ∗
              (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
               else memRegion (sf.readReg64 .x0) size))) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
              (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
                stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) size align ∗
                (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
                 else memRegion (sf.readReg64 .x0) size) ∗ R)) := by ac_rfl
      rw [hEq1, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hacp, hpost⟩
      rw [satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hal, hspRest⟩
      have hne0 : sf.readReg64 .x0 ≠ 0#64 := hnull
      have hEq2 :
          (⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % align = 0⌝ ∗
            A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
            stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) size align ∗
            (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
             else memRegion (sf.readReg64 .x0) size)) ∗ R =
          ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
              stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) size align ∗
              (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
               else memRegion (sf.readReg64 .x0) size) ∗ R) := by ac_rfl
      rw [hEq2, satisfies_pure_sepConj]
      exact ⟨⟨hacp, hne0, hal⟩, hspRest⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · dsimp only [rustCliAllocBudgetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hFit)

theorem subroutine_ok_reallocNoOom_of_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok P entry (rustCliReallocNoOomSpec M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨p, old, align, new, bs, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [rustCliReallocNoOomSpec] at hpre
  have hpreEq :
      (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
          (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
          RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new ∧
          FitsEvents M lim st (rustReallocEvents old new align) ∧
          LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
        A.pool lim st s0 ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
        memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
        stackAt s0.sp allocHookStack) ∗ R =
      ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
          (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
          RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new ∧
          FitsEvents M lim st (rustReallocEvents old new align) ∧
          LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
        (A.pool lim st s0 ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
          stackAt s0.sp allocHookStack ∗ R) := by ac_rfl
  rw [hpreEq, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlay, hbo, hbn, hFit, hlr⟩, hrest⟩
  have hpreB : s0.mem ⊨
      (rustCliReallocBudgetSpec M A lim).pre (p, old, align, new, bs, st) s0 ∗ R := by
    dsimp only [rustCliReallocBudgetSpec]
    have hEq :
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
            (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
            RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new ∧
            LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
          A.pool lim st s0 ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
          stackAt s0.sp allocHookStack) ∗ R =
        ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
            (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
            RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new ∧
            LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
          (A.pool lim st s0 ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
            stackAt s0.sp allocHookStack ∗ R) := by ac_rfl
    rw [hEq, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hlay, hbo, hbn, hlr⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (p, old, align, new, bs, st) R s0 hpc hrun hpreB hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustCliReallocBudgetSpec] at hpost
    by_cases hnull : sf.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost
      have hna : NullAllowed new align := by
        have hEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
              stackAt s0.sp allocHookStack ∗
              (⌜NullAllowed new align⌝ ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length))) ∗ R =
            ⌜NullAllowed new align⌝ ∗
              (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
                stackAt s0.sp allocHookStack ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R) := by ac_rfl
        rw [hEq, satisfies_pure_sepConj] at hpost
        exact hpost.1
      exact False.elim (not_nullAllowed_of_fitsReallocEvents hlay hFit hna)
    · simp only [hnull, ↓reduceIte] at hpost
      dsimp only [rustCliReallocNoOomSpec]
      have hEq1 :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
            stackAt s0.sp allocHookStack ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) new align ∗
              (sf.readReg64 .x0 ↦ₛ bs) ∗
              memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
              (A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
                stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) new align ∗
                (sf.readReg64 .x0 ↦ₛ bs) ∗
                memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R)) := by
        ac_rfl
      rw [hEq1, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hacp, hpost⟩
      rw [satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hal, hspRest⟩
      have hne0 : sf.readReg64 .x0 ≠ 0#64 := hnull
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % align = 0⌝ ∗
            A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
            stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) new align ∗
            (sf.readReg64 .x0 ↦ₛ bs) ∗
            memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length)) ∗ R =
          ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
              stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) new align ∗
              (sf.readReg64 .x0 ↦ₛ bs) ∗
              memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R) := by
        simp only [sepConj_assoc]
      rw [hGoalEq, satisfies_pure_sepConj]
      exact ⟨⟨hacp, hne0, hal⟩, hspRest⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · dsimp only [rustCliReallocBudgetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hFit)

/-- Specialize `RustCliAllocBudgetEntries` at any `lim : BudgetLimits` to total-correctness
    `RustCliAllocNoOomEntries` (`onOom := ⌜False⌝`, non-null return). -/
theorem RustCliAllocBudgetEntries.toNoOom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {P : Program} {addrs : RustAllocAddrs}
    (h : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) :
    RustCliAllocNoOomEntries M A lim P addrs where
  alloc := subroutine_ok_allocNoOom_of_budget (h.alloc lim)
  dealloc := h.dealloc lim
  realloc := subroutine_ok_reallocNoOom_of_budget (h.realloc lim)

/-- Unplaced coexistence entry wrapper (`IfaceBudgetBase.rustCliAllocEntries_of_budgetBase`
    provides the `RustCliAllocBudgetEntriesBase → RustCliAllocEntries` projection). -/
theorem rustCliAllocEntries_of_budget {M : AllocCostModel} {A : RustCliAllocBudget M}
    {P : Program} {addrs : RustAllocAddrs}
    (h : RustCliAllocEntries A.toRustCliAlloc P addrs) :
    RustCliAllocEntries A.toRustCliAlloc P addrs :=
  h
/-! ## Cost-Model-Parametric `mallocng` Soundness Interface

`MallocngCostModelIface M` and `MallocngCostModelSound M I` package the separation-logic predicates
and placed C entry contracts of `VerifiedLibraries.mallocngLib` parameterized over
`M : AllocCostModel`, shared by both coarse and per-size-class cost models. -/

/-- Step-bound-parametric generalization of `VerifiedLibraries.Mallocng.MallocngOomCond`
    (definitionally equal to `MallocngOomCond svc reqBytes peakCount s0 sf` when
    `stepBytes = MallocngStepBound reqBytes peakCount`). -/
def MallocngStepOomCond (svc : State → State) (stepBytes : Nat) (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
  sf.trace = s0.trace ∧
  sf.sigActions = s0.sigActions ∧
  MallocngMappedDelta 16 stepBytes s0.mem sf.mem ∧
  (MallocngSanitizedSvc svc →
    ∃ sz : Nat,
      PAGE_SIZE ≤ sz ∧
      sz % PAGE_SIZE = 0 ∧
      sz ≤ stepBytes ∧
      MallocngNoGapOrPhys sf sz)

theorem mallocngStepOomCond_eq_oomCond (svc : State → State) (reqBytes peakCount : Nat)
    (s0 sf : State) :
    MallocngStepOomCond svc (MallocngStepBound reqBytes peakCount) s0 sf =
      MallocngOomCond svc reqBytes peakCount s0 sf :=
  rfl

/-- Separation-logic predicates of a `mallocng` instance indexed by `M : AllocCostModel`.
`BlockM γ p n effAlign` records the effective `mallocng` alignment (`16` for `malloc`/`calloc`,
`max align 16` for `aligned_alloc`/`posix_memalign`) across `free` and `realloc`. -/
structure MallocngCostModelIface (M : AllocCostModel) where
  HeapM :
    GhostName → MallocngAddrs → BitVec 64 → BitVec 64 → BitVec 64 →
      M.σ → List (BitVec 64 × Nat) → SepProp
  CoreM :
    GhostName → MallocngAddrs → BitVec 64 → BitVec 64 →
      M.σ → List (BitVec 64 × Nat) → SepProp
  BlockM : GhostName → BitVec 64 → Nat → Nat → SepProp
  block_noWrap : ∀ (γ : GhostName) (p : BitVec 64) (n effAlign : Nat),
    BlockM γ p n effAlign ⊢ ⌜p.toNat + n ≤ 2 ^ 64⌝ ∗ BlockM γ p n effAlign

def MallocngModelEnv (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (st : M.σ) (ivs : List (BitVec 64 × Nat)) (s : State) : SepProp :=
  ⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
    I.HeapM γ A tp brkStart s.brk st ivs

def MallocngModelPostEnv (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (stf : M.σ) (ivs0 : List (BitVec 64 × Nat)) (s0 sf : State) : SepProp :=
  ∃∗ ivsf : List (BitVec 64 × Nat),
    ⌜MallocngNoOrphanMappings ivs0 ivsf s0.mem sf.mem⌝ ∗
    MallocngModelEnv M I γ A tp brkStart stf ivsf sf

@[reducible] def MallocngModelBlock {M : AllocCostModel} (I : MallocngCostModelIface M)
    (γ : GhostName) : SemType (Nat × Nat) where
  tyName := "void * (mallocng allocated block)"
  interp := fun p (n, effAlign) => I.BlockM γ p n effAlign ∗ memRegion p n
  pureWf := fun p (n, effAlign) => p ≠ 0#64 ∧ effAlign ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

@[reducible] def MallocngModelZeroedBlock {M : AllocCostModel} (I : MallocngCostModelIface M)
    (γ : GhostName) : SemType (Nat × Nat) where
  tyName := "void * (zero-initialized mallocng block)"
  interp := fun p (n, effAlign) => I.BlockM γ p n effAlign ∗ (p ↦ₛ List.replicate n 0#8)
  pureWf := fun p (n, effAlign) => p ≠ 0#64 ∧ effAlign ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

@[reducible] def MallocngModelInitBlock {M : AllocCostModel} (I : MallocngCostModelIface M)
    (γ : GhostName) : SemType (Nat × Nat × List (BitVec 8)) where
  tyName := "void * (mallocng block with initialized prefix)"
  interp := fun p (sz, align, bs) =>
    I.BlockM γ p sz (max align 16) ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (sz - bs.length)
  pureWf := fun p (sz, _, bs) =>
    p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + sz < 2 ^ 64 ∧ bs.length ≤ sz

@[reducible] def MallocngModelFreeableBlock {M : AllocCostModel} (I : MallocngCostModelIface M)
    (γ : GhostName) : SemType (Nat × Nat) where
  tyName := "void * (nullable mallocng allocated block)"
  interp := fun p (n, align) => if p = 0#64 then emp else I.BlockM γ p n (max align 16) ∗ memRegion p n
  pureWf := fun p (n, _) => if p = 0#64 then n = 0 else 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

c_type_spec mallocngModelMallocSpec (ctx M : AllocCostModel) (ctx I : MallocngCostModelIface M)
    (ctx svc : State → State) (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (req : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost st : M.σ)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := decide (req.toNat ≤ MallocngMaxAllocSize)
  let ev := AllocEvent.alloc req.toNat
  let st' := if ok then M.step ev st else st
  let stepB := if ok then M.stepReserve ev st else M.stepReserve (.alloc 0) st
  c_arg req : Val SizeT
  c_ret : Own (OptOwn (MallocngModelBlock I γ))
    (if ok then some (req.toNat, 16) else none)
  c_env (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngModelPostEnv M I γ A tp brkStart st' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when MallocngStepOomCond svc stepB s0 sf

c_type_spec mallocngModelFreeSpec (ctx M : AllocCostModel) (ctx I : MallocngCostModelIface M)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (p : ptr) (sp : sp)
    (ghost n align : Nat) (ghost tp brkStart : BitVec 64) (ghost st : M.σ)
    (ghost ivs0 : List (BitVec 64 × Nat)) where
  let st' := if p == 0#64 then st else M.step (.free align n) st
  c_arg p : Own (MallocngModelFreeableBlock I γ) (n, align)
  c_env (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngModelPostEnv M I γ A tp brkStart st' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 0 0 s0 sf

c_type_spec mallocngModelCallocSpec (ctx M : AllocCostModel) (ctx I : MallocngCostModelIface M)
    (ctx svc : State → State) (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (nmemb : u64) (size : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost st : M.σ)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let total := nmemb.toNat * size.toNat
  let ok := decide (total ≤ MallocngMaxAllocSize)
  let ev := AllocEvent.alloc total
  let st' := if ok then M.step ev st else st
  let stepB := if ok then M.stepReserve ev st else M.stepReserve (.alloc 0) st
  c_arg nmemb : Val SizeT
  c_arg size : Val SizeT
  c_ret : Own (OptOwn (MallocngModelZeroedBlock I γ))
    (if ok then some (total, 16) else none)
  c_env (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngModelPostEnv M I γ A tp brkStart st' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when MallocngStepOomCond svc stepB s0 sf

/-- Model-parametric `void *realloc(void *p, size_t newSize)` contract:
    emits `.alloc newSize.toNat` when `oldBlk = none` (`p = 0#64`) and
    `.realloc align oldSize newSize.toNat` when `oldBlk = some (oldSize, align, bs)`. -/
c_type_spec mallocngModelReallocSpec (ctx M : AllocCostModel) (ctx I : MallocngCostModelIface M)
    (ctx svc : State → State) (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (p : ptr) (newSize : u64) (sp : sp)
    (ghost oldBlk : Option (Nat × Nat × List (BitVec 8)))
    (ghost tp brkStart : BitVec 64) (ghost st : M.σ)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
  let keptBs := ((oldBlk.map fun (_, _, bs) => bs).getD []).take newSize.toNat
  let ev : AllocEvent := match oldBlk with
    | none => .alloc newSize.toNat
    | some (oldSize, align, _) => .realloc align oldSize newSize.toNat
  let evRes : AllocEvent := match oldBlk with
    | none => .realloc 16 0 newSize.toNat
    | some (oldSize, align, _) => .realloc align oldSize newSize.toNat
  let outAlign : Nat := match oldBlk with
    | none => 16
    | some (_, align, _) => max align 16
  let st' := if ok then M.step ev st else st
  let stepB := if ok then M.stepReserve evRes st else M.stepReserve (.alloc 0) st
  c_arg p : MutRef (CondOwn (OptOwn (MallocngModelInitBlock I γ))) (some oldBlk) ⇝
    (if ok then none else some oldBlk)
  c_arg newSize : Val SizeT
  c_ret : Own (OptOwn (MallocngModelInitBlock I γ))
    (if ok then some (newSize.toNat, outAlign, keptBs) else none)
  c_env (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngModelPostEnv M I γ A tp brkStart st' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when MallocngStepOomCond svc stepB s0 sf

c_type_spec mallocngModelAlignedAllocSpec (ctx M : AllocCostModel)
    (ctx I : MallocngCostModelIface M) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (align : u64) (len : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost st : M.σ)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := mallocngAlignedAllocOk align len
  let ev := AllocEvent.aligned align.toNat len.toNat
  let st' := if ok then M.step ev st else st
  let stepB := if ok then M.stepReserve ev st else M.stepReserve (.alloc 0) st
  caveat [API_RESTRICTION] "align ≤ 2^31 avoids musl 1.2.5 set_size int32 reserved overflow" :
    align.toNat ≤ MaxAlignedAllocAlign
  c_arg align : Val SizeT
  c_arg len : Val SizeT
  c_ret : Own (OptOwn (MallocngModelBlock I γ))
    (if ok then some (len.toNat, max align.toNat 16) else none)
  c_env (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngModelPostEnv M I γ A tp brkStart st' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when MallocngStepOomCond svc stepB s0 sf

c_type_spec mallocngModelPosixMemalignSpec (ctx M : AllocCostModel)
    (ctx I : MallocngCostModelIface M) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (res : ptr) (align : u64) (len : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost st : M.σ)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : u32) where
  let ok := mallocngPosixMemalignOk align len
  let ev := AllocEvent.aligned align.toNat len.toNat
  let st' := if ok then M.step ev st else st
  let stepB := if ok then M.stepReserve ev st else M.stepReserve (.alloc 0) st
  caveat [API_RESTRICTION] "align ≤ 2^31 avoids musl 1.2.5 set_size int32 reserved overflow" :
    align.toNat ≤ MaxAlignedAllocAlign
  c_arg res : MutRef (OptOutPtr (MallocngModelBlock I γ)) none ⇝
    (if ok then some (len.toNat, max align.toNat 16) else none)
  c_arg align : Val SizeT
  c_arg len : Val SizeT
  c_env (MallocngModelEnv M I γ A tp brkStart st ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngModelPostEnv M I γ A tp brkStart st' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  returns mallocngPosixMemalignRet align len
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when MallocngStepOomCond svc stepB s0 sf

/-- Placed multi-block entry-point bundle for all 6 exported C allocator functions of
    `VerifiedLibraries.mallocngLib` over `(M, I)`. -/
structure MallocngModelPlacedEntryContracts (M : AllocCostModel) (I : MallocngCostModelIface M)
    (mpl : Obj.MultiPlacement) (svc : State → State) : Prop where
  malloc_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "malloc"
      (mallocngModelMallocSpec M I svc γ (mallocngAddrsOfPlacement mpl))
  free_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "free"
      (mallocngModelFreeSpec M I γ (mallocngAddrsOfPlacement mpl))
  calloc_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "calloc"
      (mallocngModelCallocSpec M I svc γ (mallocngAddrsOfPlacement mpl))
  realloc_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "realloc"
      (mallocngModelReallocSpec M I svc γ (mallocngAddrsOfPlacement mpl))
  alignedAlloc_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "aligned_alloc"
      (mallocngModelAlignedAllocSpec M I svc γ (mallocngAddrsOfPlacement mpl))
  posixMemalign_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "posix_memalign"
      (mallocngModelPosixMemalignSpec M I svc γ (mallocngAddrsOfPlacement mpl))

/-- Soundness record linking `(M, I)` to `VerifiedLibraries.mallocngLib`: startup initialization,
runtime splitting (`errno` and `__libc`), live-block alignment and disjointness, dynamic interval
and byte bounds, and placed C entry contracts for `malloc`, `free`, `calloc`, `realloc`,
`aligned_alloc`, and `posix_memalign`. -/
structure MallocngCostModelSound (M : AllocCostModel) (I : MallocngCostModelIface M) : Prop where
  init :
    ∀ (mpl : Obj.MultiPlacement) (tp brkStart auxvPtr : BitVec 64) (R : SepProp) (m : Memory),
      let A := mallocngAddrsOfPlacement mpl
      0xa4 ≤ tp.toNat →
      tp.toNat ≤ 2 ^ 48 →
      MallocngBrkStartWf brkStart →
      (m ⊨
        VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime A tp ∗
        ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) →
      ∃ γ : GhostName,
        m ⊨ |==> (I.HeapM γ A tp brkStart brkStart M.init [] ∗ R)
  init_resources :
    ∀ (A : MallocngAddrs) (tp brkStart : BitVec 64),
      0xa4 ≤ tp.toNat →
      tp.toNat ≤ 2 ^ 48 →
      MallocngBrkStartWf brkStart →
      MallocngStartupResources A tp ⊢
        |==> (∃∗ γ : GhostName, I.HeapM γ A tp brkStart brkStart M.init [])
  heap_split_runtime :
    ∀ (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
      (st : M.σ) (ivs : List (BitVec 64 × Nat)),
      I.HeapM γ A tp brkStart brk st ivs =
        (I.CoreM γ A brkStart brk st ivs ∗ MallocngRuntime A tp)
  block_nonnull :
    ∀ (γ : GhostName) (p : BitVec 64) (n effAlign : Nat),
      I.BlockM γ p n effAlign ⊢
        ⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + n ≤ 2 ^ 48 ∧ n ≤ MallocngMaxAllocSize⌝ ∗
          I.BlockM γ p n effAlign
  block_exclusive :
    ∀ (γ : GhostName) (p₁ : BitVec 64) (n₁ al₁ : Nat) (p₂ : BitVec 64) (n₂ al₂ : Nat),
      I.BlockM γ p₁ n₁ al₁ ∗ I.BlockM γ p₂ n₂ al₂ ⊢
        ⌜p₁ ≠ p₂⌝ ∗ I.BlockM γ p₁ n₁ al₁ ∗ I.BlockM γ p₂ n₂ al₂
  heap_footprint_bound :
    ∀ (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
      (st : M.σ) (ivs : List (BitVec 64 × Nat)) (h : Heap),
      SepProp.Holds (I.HeapM γ A tp brkStart brk st ivs) h →
      ivs.length ≤ M.maxDynIvs st ∧
      (ivs.map Prod.snd).sum ≤ M.footprint st ∧
      ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48
  entries_ok :
    ∀ (mpl : Obj.MultiPlacement) (svc : State → State),
      VerifiedLibraries.mallocngLib.Placeable mpl →
      MallocngSvcValid svc →
      MallocngModelPlacedEntryContracts M I mpl svc

/-! ## Inhabitation Check

Non-`emp` consistency check for `AllocCostModel` and `RustCliAllocBudget`. -/

private noncomputable def witnessCostModel : AllocCostModel where
  σ := Nat × Nat
  init := (0, 0)
  step := fun ev (live, cum) =>
    match ev with
    | .alloc r => (live + r, cum + r)
    | .aligned a r => (live + r + a, cum + r + a)
    | .free _ r => (live - r, cum)
    | .realloc _ o n => (live - o + n, cum + n)
  footprint := fun (_, cum) => cum
  maxDynIvs := fun (_, cum) => cum
  stepReserve := fun ev (_, cum) => ev.reqBytes + cum + PAGE_SIZE
  liveBytes := fun (live, _) => live
  footprint_mono := by
    intro ev ⟨live, cum⟩; cases ev <;> dsimp only <;> omega
  maxDynIvs_mono := by
    intro ev ⟨live, cum⟩; cases ev <;> dsimp only <;> omega
  stepReserve_mono := by
    intro ev₀ ev ⟨live, cum⟩; cases ev <;> dsimp only <;> omega
  req_le_stepReserve := by
    intro ev ⟨live, cum⟩; dsimp only; omega
  liveBytes_free_le := by
    intro al n ⟨live, cum⟩; dsimp only; omega

private noncomputable def witnessAllocBudget : RustCliAllocBudget witnessCostModel where
  pool := fun lim st s =>
    ⌜s.brk = s.brkStart ∧ s.tpidrEl0 ≠ 0#64 ∧
      (lim.enforced = true → lim.physCap ≤ s.physMemAvail + st.2)⌝
  live := fun p n al =>
    ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ emp
  block_valid := by
    intro p n al
    refine Entails.pure_left fun h => ?_
    exact Entails.pure_right h (Entails.pure_right h (Entails.refl _))
  pool_transport := by
    rintro lim st s s' ⟨⟨hbs, hb, ht⟩, hp, _⟩
    simp only [hbs, hb, ht, hp]
  pool_zero_transport := by
    rintro st s s' ⟨hbs, hb, ht⟩
    simp [zeroBudgetLimits, hbs, hb, ht]

example : ∃ A : RustCliAllocBudget witnessCostModel, A.pool = witnessAllocBudget.pool :=
  ⟨witnessAllocBudget, rfl⟩

end LibsignalBinary.Heap
