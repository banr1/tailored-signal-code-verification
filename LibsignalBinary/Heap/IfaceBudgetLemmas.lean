/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Heap.IfaceLemmas
public import LibsignalBinary.Heap.IfaceSimp
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# Caller-Side Helpers for `IfaceBudget`

`VmPreserved` transport rules, `RustCliAllocBudget.atState` frozen-pool snapshots, allocation event
envelopes (`FitsEnv`, `SeqEnv`, `FreeOnlyEvs`), arbitrary-stack (`WithStack`) and `wp_call` extern
wrappers, and hook/entry-point bundle projections for `LibsignalBinary.Heap.IfaceBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap.IfaceBudgetLemmas

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (RustAlloc LayoutOk allocHookStack)
open LibsignalBinary.Heap (
  PoolPreserved AllocCallPreserved OomPreserved RustLayoutOk NullAllowed
  FdsHiFrame VmPreserved AllocEvent AllocCostModel BudgetLimits zeroBudgetLimits
  FitsStep FitsEvent FitsEvents FitsTrace FitsTraceOf
  fitsEvents_append fitsEvents_of_subtrace_fitsTrace
  rustAllocEvents rustDeallocEvents rustReallocEvents
  RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
  rustCliAllocNoOomSpec rustCliDeallocNoOomSpec rustCliReallocNoOomSpec
  RustCliAllocBudgetHooks RustAllocAddrs RustCliAllocBudgetEntries RustCliAllocNoOomEntries
  subroutine_ok_allocNoOom_of_budget subroutine_ok_reallocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceLemmas (
  withHookStackOom withExternStackFromAllocOom'
  satisfies_drop_mid_entails subroutine_ok_frame_oom' subroutine_ok_inImage_frame_oom'
  subroutine_ok_withExternStackFromAllocOom'
  subroutine_ok_inImage_withExternStackFromAllocOom'
  isPanicSymbol_rust_alloc isPanicSymbol_rust_dealloc isPanicSymbol_rust_realloc
)

/-! ## `VmPreserved` Bridges, `atState`, and Pool Transport -/

theorem fdsHiFrame_right_congr {s s₁ s₂ : State} (h : FdsHiFrame s₁ s₂) :
    FdsHiFrame s s₂ ↔ FdsHiFrame s s₁ :=
  ⟨fun h02 => h02.trans h.symm, fun h01 => h01.trans h⟩

theorem fdsHiFrame_left_congr {s₁ s₂ s' : State} (h : FdsHiFrame s₁ s₂) :
    FdsHiFrame s₁ s' ↔ FdsHiFrame s₂ s' :=
  ⟨fun h1 => h.symm.trans h1, fun h2 => h.trans h2⟩

@[arm64_norm, wp_norm]
theorem fdsHiFrame_refl_norm (s : State) : FdsHiFrame s s ↔ True :=
  FdsHiFrame.refl_iff s

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_setPC (s s' : State) (pc : BitVec 64) :
    FdsHiFrame s (s'.setPC pc) ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_advancePC (s s' : State) :
    FdsHiFrame s s'.advancePC ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_setPState (s s' : State) (ps : PState) :
    FdsHiFrame s (s'.setPState ps) ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_writeReg64 (s s' : State) (r : Reg) (v : BitVec 64) :
    FdsHiFrame s (s'.writeReg64 r v) ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_writeReg32 (s s' : State) (r : Reg) (v : BitVec 32) :
    FdsHiFrame s (s'.writeReg32 r v) ↔ FdsHiFrame s s' :=
  fdsHiFrame_writeReg64 s s' r _

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_writeReg (s s' : State) (w : Width) (r : Reg) (v : BitVec 64) :
    FdsHiFrame s (s'.writeReg w r v) ↔ FdsHiFrame s s' :=
  fdsHiFrame_writeReg64 s s' r _

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_writeVReg128 (s s' : State) (i : BitVec 5) (v : BitVec 128) :
    FdsHiFrame s (s'.writeVReg128 i v) ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_writeVReg64 (s s' : State) (i : BitVec 5) (v : BitVec 64) :
    FdsHiFrame s (s'.writeVReg64 i v) ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_writeVReg32 (s s' : State) (i : BitVec 5) (v : BitVec 32) :
    FdsHiFrame s (s'.writeVReg32 i v) ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_applyWriteback (s s' : State) (wb : Option (Reg × BitVec 64)) :
    FdsHiFrame s (applyWriteback s' wb) ↔ FdsHiFrame s s' := by
  cases wb with
  | none => rfl
  | some p => exact fdsHiFrame_writeReg64 s s' p.1 p.2

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_setMem (s s' : State) (m : Memory) :
    FdsHiFrame s (s'.setMem m) ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_setStatus (s s' : State) (es : ExecStatus) :
    FdsHiFrame s (s'.setStatus es) ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_appendTrace (s s' : State) (evs : List TraceEvent) :
    FdsHiFrame s (s'.appendTrace evs) ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_setFpsr (s s' : State) (f : BitVec 32) :
    FdsHiFrame s (s'.setFpsr f) ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_orFpsr (s s' : State) (f : BitVec 32) :
    FdsHiFrame s (s'.orFpsr f) ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_nextOracle (s s' : State) :
    FdsHiFrame s s'.nextOracle ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_stepExclOracle (s s' : State) :
    FdsHiFrame s s'.stepExclOracle ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_stepExclLoop (s s' : State) :
    FdsHiFrame s s'.stepExclLoop ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_panicked (s s' : State) :
    FdsHiFrame s (Rust.panicked s') ↔ FdsHiFrame s s' :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_setFs_setFile (s s' : State) (f : FsState) (path : String) (e : Option FsEntry) :
    FdsHiFrame s (s'.setFs (f.setFile path e)) ↔ FdsHiFrame s (s'.setFs f) :=
  fdsHiFrame_right_congr fun _ _ _ => by cases s'; rfl

theorem _root_.LibsignalBinary.Heap.VmPreserved.symm {s₁ s₂ : State}
    (h : VmPreserved s₁ s₂) : VmPreserved s₂ s₁ :=
  ⟨h.1.symm, h.2.1.symm, fun a => (h.2.2.1 a).symm, h.2.2.2.symm⟩

theorem _root_.LibsignalBinary.Heap.VmPreserved.of_rustVmPreserved {s₁ s₂ : State}
    (h : Rust.VmPreserved s₁ s₂) (hphys : s₂.physMemAvail = s₁.physMemAvail)
    (hfds : FdsHiFrame s₁ s₂) :
    VmPreserved s₁ s₂ :=
  ⟨⟨h.1, h.2.1, h.2.2.1⟩, hphys, fun a => congrFun h.2.2.2 a, hfds⟩

theorem _root_.LibsignalBinary.Heap.VmPreserved.toRustVmPreserved {s₁ s₂ : State}
    (h : VmPreserved s₁ s₂) : Rust.VmPreserved s₁ s₂ :=
  ⟨h.1.1, h.1.2.1, h.1.2.2, funext h.2.2.1⟩

theorem _root_.ProofLib.ProcessFieldsPreserved.toVmPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2,
    FdsHiFrame.of_fs_eq h.1⟩

theorem _root_.ProofLib.NonSyscallPreserved.toVmPreserved {s0 sf : State}
    (h : ProofLib.NonSyscallPreserved s0 sf) (htp : sf.tpidrEl0 = s0.tpidrEl0) :
    VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.1, h.2.2.1, htp⟩, h.2.2.2.2.1, fun a => congrFun h.2.1 a,
    FdsHiFrame.of_fs_eq h.2.2.2.2.2.2⟩

theorem _root_.LibsignalBinary.Heap.AllocCallPreserved.toVmPreserved_of_brk_phys_perm
    {s0 sf : State} (h : AllocCallPreserved s0 sf)
    (hbrk : sf.brk = s0.brk) (hphys : sf.physMemAvail = s0.physMemAvail)
    (hperm : ∀ a, sf.mem.perm a = s0.mem.perm a) :
    VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.1, hbrk, h.2.2.2.1⟩, hphys, hperm, FdsHiFrame.of_fs_eq h.1⟩

/-- Frozen `RustAlloc` snapshot of `A : RustCliAllocBudget M` at `(lim, st, s)`, allowing
`RustAlloc`-generic spatial predicates to be reused and transported across `VmPreserved` steps via
`A.pool_transport`. -/
def _root_.LibsignalBinary.Heap.RustCliAllocBudget.atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) : RustAlloc where
  pool := A.pool lim st s
  live := A.live

abbrev _root_.LibsignalBinary.Heap.RustCliAllocBudget.atBudget {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) : RustAlloc :=
  A.atState lim st s

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.atState_pool {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    (A.atState lim st s).pool = A.pool lim st s := rfl

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.atState_live {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    (A.atState lim st s).live = A.live := rfl

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_pool {M : AllocCostModel}
    (A : RustCliAllocBudget M) :
    A.repAlloc.pool = emp := rfl

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm {M : AllocCostModel}
    (A : RustCliAllocBudget M) :
    A.repAlloc.live = A.live := rfl

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.atState_live_eq_repAlloc
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    (A.atState lim st s).live = A.repAlloc.live := rfl

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.atState_eq_of_vmPreserved
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {s₁ s₂ : State} (h : VmPreserved s₁ s₂) :
    A.atState lim st s₂ = A.atState lim st s₁ := by
  unfold RustCliAllocBudget.atState
  rw [A.pool_transport lim st s₁ s₂ h]

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.atBudget_pool {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    (A.atBudget lim st s).pool = A.pool lim st s := rfl

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.atBudget_live {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    (A.atBudget lim st s).live = A.live := rfl

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.atBudget_live_eq_repAlloc
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    (A.atBudget lim st s).live = A.repAlloc.live := rfl

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.atBudget_eq_of_vmPreserved
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {s₁ s₂ : State} (h : VmPreserved s₁ s₂) :
    A.atBudget lim st s₂ = A.atBudget lim st s₁ :=
  A.atState_eq_of_vmPreserved lim st h

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_setFpsr {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) (f : BitVec 32) :
    A.pool lim st (s.setFpsr f) = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_orFpsr {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) (f : BitVec 32) :
    A.pool lim st (s.orFpsr f) = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_nextOracle {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s.nextOracle = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_stepExclOracle {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s.stepExclOracle = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_stepExclLoop {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s.stepExclLoop = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_setStatus {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) (stx : ExecStatus) :
    A.pool lim st (s.setStatus stx) = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_appendTrace {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (evs : List TraceEvent) :
    A.pool lim st (s.appendTrace evs) = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_setFs {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) (f : FsState)
    (hfds : FdsHiFrame s (s.setFs f)) :
    A.pool lim st (s.setFs f) = A.pool lim st s :=
  A.pool_transport lim st s _ ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, hfds⟩

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_setFs_setFile {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (path : String) (e : Option FsEntry) :
    A.pool lim st (s.setFs (s.fs.setFile path e)) = A.pool lim st s :=
  A.pool_setFs lim st s _ fun _ _ _ => by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_panicked {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st (Rust.panicked s) = A.pool lim st s :=
  A.pool_transport lim st s _
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_applyWriteback {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (wb : Option (Reg × BitVec 64)) :
    A.pool lim st (applyWriteback s wb) = A.pool lim st s := by
  cases wb <;> simp [applyWriteback]

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC_norm {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) (pc : BitVec 64) :
    A.pool lim st (s.setPC pc) = A.pool lim st s :=
  A.pool_setPC lim st s pc

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC_norm {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s.advancePC = A.pool lim st s :=
  A.pool_advancePC lim st s

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState_norm {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) (ps : PState) :
    A.pool lim st (s.setPState ps) = A.pool lim st s :=
  A.pool_setPState lim st s ps

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64_norm {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : Reg) (v : BitVec 64) :
    A.pool lim st (s.writeReg64 r v) = A.pool lim st s :=
  A.pool_writeReg64 lim st s r v

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32_norm {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : Reg) (v : BitVec 32) :
    A.pool lim st (s.writeReg32 r v) = A.pool lim st s :=
  A.pool_writeReg32 lim st s r v

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg_norm {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (w : Width) (r : Reg) (v : BitVec 64) :
    A.pool lim st (s.writeReg w r v) = A.pool lim st s :=
  A.pool_writeReg lim st s w r v

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_writeVReg128_norm {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (i : BitVec 5) (v : BitVec 128) :
    A.pool lim st (s.writeVReg128 i v) = A.pool lim st s :=
  A.pool_writeVReg128 lim st s i v

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_writeVReg64_norm {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (i : BitVec 5) (v : BitVec 64) :
    A.pool lim st (s.writeVReg64 i v) = A.pool lim st s :=
  A.pool_writeVReg64 lim st s i v

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_writeVReg32_norm {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (i : BitVec 5) (v : BitVec 32) :
    A.pool lim st (s.writeVReg32 i v) = A.pool lim st s :=
  A.pool_writeVReg32 lim st s i v

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_setMem_writeBytes_norm
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (addr : BitVec 64) (bs : List (BitVec 8)) :
    A.pool lim st (s.setMem (s.mem.writeBytes addr bs)) = A.pool lim st s :=
  A.pool_setMem_writeBytes lim st s addr bs

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_setMem_write8_norm
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (addr : BitVec 64) (v : BitVec 8) :
    A.pool lim st (s.setMem (s.mem.write8 addr v)) = A.pool lim st s :=
  A.pool_setMem_write8 lim st s addr v

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_setMem_write16_norm
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (addr : BitVec 64) (v : BitVec 16) :
    A.pool lim st (s.setMem (s.mem.write16 addr v)) = A.pool lim st s :=
  A.pool_setMem_write16 lim st s addr v

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_setMem_write32_norm
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (addr : BitVec 64) (v : BitVec 32) :
    A.pool lim st (s.setMem (s.mem.write32 addr v)) = A.pool lim st s :=
  A.pool_setMem_write32 lim st s addr v

@[arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_setMem_write64_norm
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (addr : BitVec 64) (v : BitVec 64) :
    A.pool lim st (s.setMem (s.mem.write64 addr v)) = A.pool lim st s :=
  A.pool_setMem_write64 lim st s addr v

@[simp, arm64_norm, wp_norm]
theorem perm_write8_norm (m : Memory) (a : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).perm = m.perm :=
  Memory.perm_write8 m a v

@[simp, arm64_norm, wp_norm]
theorem perm_write16_norm (m : Memory) (a : BitVec 64) (v : BitVec 16) :
    (m.write16 a v).perm = m.perm :=
  Memory.perm_write16 m a v

@[simp, arm64_norm, wp_norm]
theorem perm_write32_norm (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    (m.write32 a v).perm = m.perm :=
  Memory.perm_write32 m a v

@[simp, arm64_norm, wp_norm]
theorem perm_write64_norm (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (m.write64 a v).perm = m.perm :=
  Memory.perm_write64 m a v

@[simp, arm64_norm, wp_norm]
theorem perm_write128_norm (m : Memory) (a : BitVec 64) (v : BitVec 128) :
    (m.write128 a v).perm = m.perm :=
  Memory.perm_write128 m a v

@[simp, arm64_norm, wp_norm]
theorem perm_writeSized_norm (m : Memory) (sz : MemWidth) (a v : BitVec 64) :
    (m.writeSized sz a v).perm = m.perm :=
  Memory.perm_writeSized m sz a v

@[simp, arm64_norm, wp_norm]
theorem perm_writeSimdSized_norm (m : Memory) (sz : SimdMemSize) (a : BitVec 64)
    (v : BitVec 128) :
    (m.writeSimdSized sz a v).perm = m.perm :=
  Memory.perm_writeSimdSized m sz a v

@[simp, arm64_norm, wp_norm]
theorem perm_writeBytes_norm (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) :
    (m.writeBytes a bs).perm = m.perm :=
  Memory.perm_writeBytes m a bs

/-- Conditional `@[simp, arm64_norm, wp_norm]` rule stripping `.setMem m` whenever `m.perm = s.mem.perm`
    (discharged automatically by `simp` across interleaved `writeReg*` / `advancePC` / multi-word
    `stp` stores where `arm64_norm` commutes `.setMem` outside register updates). -/
@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAllocBudget.pool_setMem_of_perm
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s : State) (m : Memory) (hperm : m.perm = s.mem.perm) :
    A.pool lim st (s.setMem m) = A.pool lim st s :=
  A.pool_transport lim st s _ ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun a => by
    have hp := congrFun hperm a; cases s; exact hp, fun _ _ _ => by cases s; rfl⟩

/-! ### Event Envelopes -/

/-- Every possible `AllocEvent` list in envelope `E` fits from cost-model state `st`. -/
def _root_.LibsignalBinary.Heap.FitsEnv (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ)
    (E : List AllocEvent → Prop) : Prop :=
  ∀ evs, E evs → FitsEvents M lim st evs

/-- Sequential envelope composition; includes `E₁` alone so `FitsEnv` projects to step 1 without
    requiring an inhabitation witness for `E₂`. -/
def _root_.LibsignalBinary.Heap.SeqEnv (E₁ E₂ : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  E₁ evs ∨ ∃ evs₁ evs₂, evs = evs₁ ++ evs₂ ∧ E₁ evs₁ ∧ E₂ evs₂

/-- Pure deallocation event list (requires zero `FitsEvents` preconditions). -/
def _root_.LibsignalBinary.Heap.FreeOnlyEvs (evs : List AllocEvent) : Prop :=
  ∀ ev ∈ evs, ∃ al sz, ev = .free al sz

abbrev FitsEnv := @_root_.LibsignalBinary.Heap.FitsEnv
abbrev SeqEnv := @_root_.LibsignalBinary.Heap.SeqEnv
abbrev FreeOnlyEvs := @_root_.LibsignalBinary.Heap.FreeOnlyEvs

theorem _root_.LibsignalBinary.Heap.FitsEnv.nil {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} :
    _root_.LibsignalBinary.Heap.FitsEnv M lim st (· = []) := by
  rintro _ rfl; trivial

@[simp]
theorem _root_.LibsignalBinary.Heap.FitsEnv.eq_iff {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {evs₀ : List AllocEvent} :
    _root_.LibsignalBinary.Heap.FitsEnv M lim st (· = evs₀) ↔ FitsEvents M lim st evs₀ :=
  ⟨fun h => h evs₀ rfl, by rintro h _ rfl; exact h⟩

theorem _root_.LibsignalBinary.Heap.FitsEnv.mono {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {E₁ E₂ : List AllocEvent → Prop}
    (hsub : ∀ evs, E₁ evs → E₂ evs)
    (h : _root_.LibsignalBinary.Heap.FitsEnv M lim st E₂) :
    _root_.LibsignalBinary.Heap.FitsEnv M lim st E₁ :=
  fun evs h1 => h evs (hsub evs h1)

theorem _root_.LibsignalBinary.Heap.FitsEnv.or_iff {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {E₁ E₂ : List AllocEvent → Prop} :
    _root_.LibsignalBinary.Heap.FitsEnv M lim st (fun evs => E₁ evs ∨ E₂ evs) ↔
      _root_.LibsignalBinary.Heap.FitsEnv M lim st E₁ ∧
        _root_.LibsignalBinary.Heap.FitsEnv M lim st E₂ :=
  ⟨fun h => ⟨fun evs h1 => h evs (Or.inl h1), fun evs h2 => h evs (Or.inr h2)⟩,
   fun ⟨h1, h2⟩ evs h12 => h12.elim (h1 evs) (h2 evs)⟩

theorem _root_.LibsignalBinary.Heap.SeqEnv.inl {E₁ E₂ : List AllocEvent → Prop}
    {evs : List AllocEvent} (h1 : E₁ evs) :
    _root_.LibsignalBinary.Heap.SeqEnv E₁ E₂ evs :=
  Or.inl h1

theorem _root_.LibsignalBinary.Heap.SeqEnv.append {E₁ E₂ : List AllocEvent → Prop}
    {evs₁ evs₂ : List AllocEvent} (h1 : E₁ evs₁) (h2 : E₂ evs₂) :
    _root_.LibsignalBinary.Heap.SeqEnv E₁ E₂ (evs₁ ++ evs₂) :=
  Or.inr ⟨evs₁, evs₂, rfl, h1, h2⟩

theorem _root_.LibsignalBinary.Heap.FitsEnv.seq_left {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {E₁ E₂ : List AllocEvent → Prop}
    (h : _root_.LibsignalBinary.Heap.FitsEnv M lim st (_root_.LibsignalBinary.Heap.SeqEnv E₁ E₂)) :
    _root_.LibsignalBinary.Heap.FitsEnv M lim st E₁ :=
  fun evs h1 => h evs (Or.inl h1)

theorem _root_.LibsignalBinary.Heap.FitsEnv.seq_right {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {E₁ E₂ : List AllocEvent → Prop} {evs₁ : List AllocEvent}
    (h : _root_.LibsignalBinary.Heap.FitsEnv M lim st (_root_.LibsignalBinary.Heap.SeqEnv E₁ E₂))
    (h1 : E₁ evs₁) :
    _root_.LibsignalBinary.Heap.FitsEnv M lim (M.stepEvents evs₁ st) E₂ :=
  fun evs₂ h2 =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp
      (h (evs₁ ++ evs₂) (Or.inr ⟨evs₁, evs₂, rfl, h1, h2⟩))).2

theorem _root_.LibsignalBinary.Heap.FitsEnv.of_subtrace_fitsTrace {M : AllocCostModel}
    {lim : BudgetLimits} {maxStep : Nat} {pre fullLog : List AllocEvent}
    {E : List AllocEvent → Prop}
    (hSub : ∀ evs, E evs → ∃ suf, fullLog = pre ++ evs ++ suf)
    (hFit : FitsTrace M lim maxStep fullLog) :
    _root_.LibsignalBinary.Heap.FitsEnv M lim (M.evalLog pre) E := by
  intro evs hevs
  obtain ⟨suf, hEq⟩ := hSub evs hevs
  exact fitsEvents_of_subtrace_fitsTrace hEq hFit

theorem _root_.LibsignalBinary.Heap.FreeOnlyEvs.nil :
    _root_.LibsignalBinary.Heap.FreeOnlyEvs [] := by
  intro _ h; nomatch h

theorem _root_.LibsignalBinary.Heap.FreeOnlyEvs.singleton (al sz : Nat) :
    _root_.LibsignalBinary.Heap.FreeOnlyEvs [.free al sz] := by
  intro ev hev
  simp only [List.mem_singleton] at hev
  exact ⟨al, sz, hev⟩

theorem _root_.LibsignalBinary.Heap.FreeOnlyEvs.append {evs₁ evs₂ : List AllocEvent}
    (h1 : _root_.LibsignalBinary.Heap.FreeOnlyEvs evs₁)
    (h2 : _root_.LibsignalBinary.Heap.FreeOnlyEvs evs₂) :
    _root_.LibsignalBinary.Heap.FreeOnlyEvs (evs₁ ++ evs₂) := by
  intro ev hev
  rcases List.mem_append.mp hev with he1 | he2
  · exact h1 ev he1
  · exact h2 ev he2

theorem _root_.LibsignalBinary.Heap.AllocCostModel.liveBytes_stepEvents_freeOnly_le
    (M : AllocCostModel) :
    ∀ {evs : List AllocEvent}, _root_.LibsignalBinary.Heap.FreeOnlyEvs evs →
      ∀ (st : M.σ), M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st
  | [], _, _ => Nat.le_refl _
  | ev :: evs, hf, st => by
    obtain ⟨al, sz, rfl⟩ := hf ev List.mem_cons_self
    have hf' : _root_.LibsignalBinary.Heap.FreeOnlyEvs evs :=
      fun e he => hf e (List.mem_cons_of_mem _ he)
    exact Nat.le_trans
      (M.liveBytes_stepEvents_freeOnly_le hf' (M.step (.free al sz) st))
      (M.liveBytes_free_le al sz st)

/-- Rewrite `A.pool lim st s1` to `A.pool lim st s2` inside a `SepWP` spatial context across a
    `VmPreserved s1 s2` transition. -/
theorem _root_.ProofLib.SepWP.transport_budgetPool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {s1 s2 : State}
    (hvm : VmPreserved s1 s2)
    {prog : Program} {target_pc : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P = A.pool lim st s1 ∗ F := by sep_focus)
    (hnext : SepWP prog target_pc s2 (A.pool lim st s2 ∗ F) post oom) :
    SepWP prog target_pc s2 P post oom :=
  SepWP.focus_weaken (by rw [A.pool_transport lim st s1 s2 hvm]; exact Entails.refl _) hf hnext

/-- Panic-aware (`SepWPp`) counterpart of `SepWP.transport_budgetPool`: rewrite `A.pool lim st s1`
    to `A.pool lim st s2` inside a `SepWPp` spatial context across a `VmPreserved s1 s2`
    transition. -/
theorem _root_.ProofLib.SepWPp.transport_budgetPool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {s1 s2 : State}
    (hvm : VmPreserved s1 s2)
    {prog : Program} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P = A.pool lim st s1 ∗ F := by sep_focus)
    (hnext : SepWPp prog ret s2 (A.pool lim st s2 ∗ F) Q Qp oom) :
    SepWPp prog ret s2 P Q Qp oom :=
  SepWPp.congr_pre
    (hf.trans (congrArg (· ∗ F) (A.pool_transport lim st s1 s2 hvm).symm))
    hnext

abbrev transport_budgetPool := @ProofLib.SepWP.transport_budgetPool
abbrev wpp_transport_budgetPool := @ProofLib.SepWPp.transport_budgetPool

/-- Rewrite `(A.atState lim st s1).pool` directly to `A.pool lim st s2` inside a `SepWP` spatial
    context across a `VmPreserved s1 s2` transition. -/
theorem _root_.ProofLib.SepWP.transport_atStatePool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {s1 s2 : State}
    (hvm : VmPreserved s1 s2)
    {prog : Program} {target_pc : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P = (A.atState lim st s1).pool ∗ F := by sep_focus)
    (hnext : SepWP prog target_pc s2 (A.pool lim st s2 ∗ F) post oom) :
    SepWP prog target_pc s2 P post oom :=
  SepWP.focus_weaken
    (by rw [RustCliAllocBudget.atState_pool, A.pool_transport lim st s1 s2 hvm]; exact Entails.refl _)
    hf hnext

/-- Panic-aware (`SepWPp`) counterpart of `SepWP.transport_atStatePool`: rewrite
    `(A.atState lim st s1).pool` directly to `A.pool lim st s2` inside a `SepWPp` spatial context
    across a `VmPreserved s1 s2` transition. -/
theorem _root_.ProofLib.SepWPp.transport_atStatePool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {s1 s2 : State}
    (hvm : VmPreserved s1 s2)
    {prog : Program} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P = (A.atState lim st s1).pool ∗ F := by sep_focus)
    (hnext : SepWPp prog ret s2 (A.pool lim st s2 ∗ F) Q Qp oom) :
    SepWPp prog ret s2 P Q Qp oom :=
  SepWPp.congr_pre
    (hf.trans (congrArg (· ∗ F)
      ((RustCliAllocBudget.atState_pool A lim st s1).trans (A.pool_transport lim st s1 s2 hvm).symm)))
    hnext

abbrev _root_.ProofLib.SepWP.transport_atBudgetPool := @ProofLib.SepWP.transport_atStatePool
abbrev _root_.ProofLib.SepWPp.transport_atBudgetPool := @ProofLib.SepWPp.transport_atStatePool
abbrev transport_atStatePool := @ProofLib.SepWP.transport_atStatePool
abbrev wpp_transport_atStatePool := @ProofLib.SepWPp.transport_atStatePool
abbrev transport_atBudgetPool := @ProofLib.SepWP.transport_atStatePool
abbrev wpp_transport_atBudgetPool := @ProofLib.SepWPp.transport_atStatePool

/-- Drop an intermediate call frame `F`, weaken `¬ FitsEvents ...` to an outer budget negation `¬ φ`,
    and compose `OomPreserved s0 s1` with `OomPreserved s1 sf` on an `.OutOfMemory` branch. -/
theorem satisfies_budgetOom_frame {φ ψ : Prop} {s0 s1 sf : State} {F R : SepProp}
    (hfit : φ → ψ)
    (h01 : OomPreserved s0 s1 := by refine ⟨rfl, rfl, rfl⟩)
    (ho : sf.mem ⊨ ⌜¬ ψ ∧ OomPreserved s1 sf⌝ ∗ (F ∗ R)) :
    sf.mem ⊨ ⌜¬ φ ∧ OomPreserved s0 sf⌝ ∗ R := by
  have ho' : sf.mem ⊨ ⌜¬ ψ ∧ OomPreserved s1 sf⌝ ∗ R := Satisfies.drop_mid ho
  rw [satisfies_pure_sepConj] at ho' ⊢
  exact ⟨⟨fun hφ => ho'.1.1 (hfit hφ), h01.trans ho'.1.2⟩, ho'.2⟩

/-- Transport a conditional-OOM `SepWP` obligation `⌜¬ φ ∧ OomPreserved s0 sf⌝` across an
    intermediate state `s1` satisfying `OomPreserved s0 s1`, optionally weakening `¬ ψ → ¬ φ`. -/
theorem _root_.ProofLib.SepWP.transport_budgetOom {φ ψ : Prop} {s0 s1 : State}
    (hfit : φ → ψ) (h01 : OomPreserved s0 s1)
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hnext : SepWP prog target_pc s P post (fun sf => ⌜¬ ψ ∧ OomPreserved s1 sf⌝)) :
    SepWP prog target_pc s P post (fun sf => ⌜¬ φ ∧ OomPreserved s0 sf⌝) :=
  SepWP.of_reaches_pc fun _ hm =>
    reaches_pc_mono (SepWP.to_reaches_pc hnext hm)
      (fun _ _ _ hq => hq)
      (fun _ _ hoom_mem => by
        rw [satisfies_pure_sepConj] at hoom_mem ⊢
        exact ⟨⟨fun hφ => hoom_mem.1.1 (hfit hφ), h01.trans hoom_mem.1.2⟩, hoom_mem.2⟩)

/-- Panic-aware (`SepWPp`) counterpart of `SepWP.transport_budgetOom`. -/
theorem _root_.ProofLib.SepWPp.transport_budgetOom {φ ψ : Prop} {s0 s1 : State}
    (hfit : φ → ψ) (h01 : OomPreserved s0 s1)
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hnext : SepWPp prog ret s P Q Qp (fun sf => ⌜¬ ψ ∧ OomPreserved s1 sf⌝)) :
    SepWPp prog ret s P Q Qp (fun sf => ⌜¬ φ ∧ OomPreserved s0 sf⌝) := by
  intro R hm hL
  rcases hnext R hm hL with ⟨sf, hsteps, hok | hpan | ⟨hoom_st, hoom_mem⟩⟩
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · rw [satisfies_pure_sepConj] at hoom_mem
    refine ⟨sf, hsteps, Or.inr (Or.inr ⟨hoom_st, ?_⟩)⟩
    rw [satisfies_pure_sepConj]
    exact ⟨⟨fun hφ => hoom_mem.1.1 (hfit hφ), h01.trans hoom_mem.1.2⟩, hoom_mem.2⟩

/-- Lift a total-correctness `SepWP` proved under `prog.withSvc noSyscalls` to `prog` (with
    `prog.svc = Syscall.standard` and `hext : ∀ pc, prog.externAt? pc = none`), automatically
    delivering `VmPreserved s0 sf` whenever `sf.tpidrEl0 = s0.tpidrEl0` holds at `target_pc`. -/
theorem _root_.ProofLib.SepWP.lift_noSyscalls_vmPreserved {prog : Program} {target_pc : BitVec 64}
    {s0 : State} {P : SepProp} {post : State → SepProp → Prop}
    (hext : ∀ pc, prog.externAt? pc = none)
    (hwp : SepWP (prog.withSvc noSyscalls) target_pc s0 P
      (fun sf Q => sf.tpidrEl0 = s0.tpidrEl0 ∧ post sf Q))
    (hsvc : prog.svc = Syscall.standard := by rfl) :
    SepWP prog target_pc s0 P (fun sf Q => VmPreserved s0 sf ∧ post sf Q) := by
  have hlift := SepWP.lift_noSyscalls hext hwp hsvc
  exact SepWP.of_reaches_pc fun R hm =>
    reaches_pc_mono (SepWP.to_reaches_pc hlift hm)
      (fun sf _ _ ⟨Q, hQ, hnsp, htp, hp⟩ => ⟨Q, hQ, hnsp.toVmPreserved htp, hp⟩)
      (fun _ _ ho => ho)

/-! ## Arbitrary-Stack Contracts -/

private theorem stackAt_split_from_allocHookStack (sp : BitVec 64) {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗ stackAt sp allocHookStack := by
  have hsplit : stk = allocHookStack + (stk - allocHookStack) := by
    dsimp only [allocHookStack] at hle ⊢; omega
  have h0 := ProofLib.stackAt_split_bottom sp allocHookStack (stk - allocHookStack)
    (by dsimp only [allocHookStack] at hle ⊢; omega)
  rwa [← hsplit] at h0

open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

section WithLsPlacement
variable [LibsignalPlacement]
set_option linter.unusedSectionVars false

def rustCliAllocBudgetSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (zeroed : Bool) (stk : Nat) : Spec (Nat × Nat × M.σ) where
  pre := fun (size, align, st) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      RustLayoutOk size align ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (size, align, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustAllocEvents size align) st
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      (if sf.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) size align ∗
         (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
          else memRegion (sf.readReg64 .x0) size))
  onOom := fun (size, align, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustAllocEvents size align) ∧ OomPreserved s0 sf⌝

def rustCliDeallocBudgetSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := fun (p, size, align, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp stk
  post := fun (_, size, align, st) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents size align) st
    ⌜AllocCallPreserved s0 sf ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp stk

def rustCliReallocBudgetSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) where
  pre := fun (p, old, align, new, bs, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
      bs.length ≤ new ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp stk
  post := fun (p, old, align, new, bs, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustReallocEvents old new align) st
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜NullAllowed new align⌝ ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) new align ∗
          (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))
  onOom := fun (_, old, align, new, _, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustReallocEvents old new align) ∧ OomPreserved s0 sf⌝

def rustCliAllocNoOomSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (zeroed : Bool) (stk : Nat) : Spec (Nat × Nat × M.σ) where
  pre := fun (size, align, st) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      RustLayoutOk size align ∧ FitsEvents M lim st (rustAllocEvents size align) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (size, align, st) s0 sf =>
    let st' := M.stepEvents (rustAllocEvents size align) st
    ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % align = 0⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      A.live (sf.readReg64 .x0) size align ∗
      (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
       else memRegion (sf.readReg64 .x0) size)
  onOom := fun _ _ _ => ⌜False⌝

abbrev rustCliDeallocNoOomSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (BitVec 64 × Nat × Nat × M.σ) :=
  rustCliDeallocBudgetSpecWithStack M A lim stk

def rustCliReallocNoOomSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) where
  pre := fun (p, old, align, new, bs, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
      bs.length ≤ new ∧ FitsEvents M lim st (rustReallocEvents old new align) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp stk
  post := fun (_, old, align, new, bs, st) s0 sf =>
    let st' := M.stepEvents (rustReallocEvents old new align) st
    ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % align = 0⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      A.live (sf.readReg64 .x0) new align ∗
      (sf.readReg64 .x0 ↦ₛ bs) ∗
      memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length)
  onOom := fun _ _ _ => ⌜False⌝

theorem subroutine_ok_rustCliAllocBudget_withStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (rustCliAllocBudgetSpec M A lim zeroed)) :
    subroutine_ok prog entry (rustCliAllocBudgetSpecWithStack M A lim zeroed stk) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    dsimp only [rustCliAllocBudgetSpec, rustCliAllocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [rustCliAllocBudgetSpec, rustCliAllocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_inImage_rustCliAllocBudget_withStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {img : Obj.Image} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((rustCliAllocBudgetSpec M A lim zeroed).inImage img)) :
    subroutine_ok prog entry ((rustCliAllocBudgetSpecWithStack M A lim zeroed stk).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    dsimp only [Spec.inImage, rustCliAllocBudgetSpec, rustCliAllocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [Spec.inImage, rustCliAllocBudgetSpec, rustCliAllocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_rustCliDeallocBudget_withStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (rustCliDeallocBudgetSpecWithStack M A lim stk) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, size, align, st⟩ s0
    dsimp only [rustCliDeallocBudgetSpec, rustCliDeallocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, size, align, st⟩ s0 sf
    dsimp only [rustCliDeallocBudgetSpec, rustCliDeallocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_inImage_rustCliDeallocBudget_withStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {img : Obj.Image} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((rustCliDeallocBudgetSpec M A lim).inImage img)) :
    subroutine_ok prog entry ((rustCliDeallocBudgetSpecWithStack M A lim stk).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, size, align, st⟩ s0
    dsimp only [Spec.inImage, rustCliDeallocBudgetSpec, rustCliDeallocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, size, align, st⟩ s0 sf
    dsimp only [Spec.inImage, rustCliDeallocBudgetSpec, rustCliDeallocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_rustCliReallocBudget_withStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (rustCliReallocBudgetSpecWithStack M A lim stk) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [rustCliReallocBudgetSpec, rustCliReallocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [rustCliReallocBudgetSpec, rustCliReallocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_inImage_rustCliReallocBudget_withStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {img : Obj.Image} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((rustCliReallocBudgetSpec M A lim).inImage img)) :
    subroutine_ok prog entry ((rustCliReallocBudgetSpecWithStack M A lim stk).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [Spec.inImage, rustCliReallocBudgetSpec, rustCliReallocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [Spec.inImage, rustCliReallocBudgetSpec, rustCliReallocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_rustCliAllocNoOom_withStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (rustCliAllocNoOomSpec M A lim zeroed)) :
    subroutine_ok prog entry (rustCliAllocNoOomSpecWithStack M A lim zeroed stk) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    dsimp only [rustCliAllocNoOomSpec, rustCliAllocNoOomSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [rustCliAllocNoOomSpec, rustCliAllocNoOomSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_inImage_rustCliAllocNoOom_withStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {img : Obj.Image} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((rustCliAllocNoOomSpec M A lim zeroed).inImage img)) :
    subroutine_ok prog entry ((rustCliAllocNoOomSpecWithStack M A lim zeroed stk).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    dsimp only [Spec.inImage, rustCliAllocNoOomSpec, rustCliAllocNoOomSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [Spec.inImage, rustCliAllocNoOomSpec, rustCliAllocNoOomSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_rustCliReallocNoOom_withStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok prog entry (rustCliReallocNoOomSpecWithStack M A lim stk) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [rustCliReallocNoOomSpec, rustCliReallocNoOomSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [rustCliReallocNoOomSpec, rustCliReallocNoOomSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_inImage_rustCliReallocNoOom_withStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {img : Obj.Image} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((rustCliReallocNoOomSpec M A lim).inImage img)) :
    subroutine_ok prog entry ((rustCliReallocNoOomSpecWithStack M A lim stk).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [Spec.inImage, rustCliReallocNoOomSpec, rustCliReallocNoOomSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [Spec.inImage, rustCliReallocNoOomSpec, rustCliReallocNoOomSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ### `wp_call`-Compatible Extern Contracts -/

/-- `wp_call`-compatible extern wrapper for `rustCliAllocBudgetSpecWithStack` (`AllocCallPreserved`
    projected to `sf.trace = s0.trace` on normal return, matching `Hooks2.rustAllocSpecWithStack`). -/
def _root_.LibsignalBinary.Heap.rustCliAllocBudgetExternSpecWithStack
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (zeroed : Bool) (stk : Nat := 16384) : Spec (Nat × Nat × M.σ) where
  pre := (rustCliAllocBudgetSpecWithStack M A lim zeroed stk).pre
  post := fun (size, align, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustAllocEvents size align) st
    ⌜sf.trace = s0.trace⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      (if sf.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) size align ∗
         (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
          else memRegion (sf.readReg64 .x0) size))
  onOom := fun (size, align, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustAllocEvents size align) ∧ OomPreserved s0 sf⌝

/-- `wp_call`-compatible extern wrapper for `rustCliDeallocBudgetSpecWithStack` (`AllocCallPreserved`
    projected to `sf.trace = s0.trace`, matching `Hooks2.rustDeallocExternSpecWithStack`). -/
def _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := 16384) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := fun (p, size, align, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧
      (s.readReg64 .x2).toNat = align ∧ RustLayoutOk size align ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp stk
  post := fun (_, size, align, st) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents size align) st
    ⌜sf.trace = s0.trace⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp stk
  onOom := fun _ _ _ => ⌜False⌝

/-- `wp_call`-compatible extern wrapper for `rustCliReallocBudgetSpecWithStack` (adds
    `RustLayoutOk old align` in `pre` and projects `AllocCallPreserved` to `sf.trace = s0.trace`,
    matching `Hooks2.rustReallocExternSpecWithStack`). -/
def _root_.LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := 16384) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) where
  pre := fun (p, old, align, new, bs, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk old align ∧ RustLayoutOk new align ∧
      bs.length ≤ old ∧ bs.length ≤ new ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp stk
  post := fun (p, old, align, new, bs, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustReallocEvents old new align) st
    A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜sf.trace = s0.trace ∧ NullAllowed new align⌝ ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) new align ∗ (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))
  onOom := fun (_, old, align, new, _, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustReallocEvents old new align) ∧ OomPreserved s0 sf⌝

/-- `wp_call`-compatible total-correctness (`NoOom`) extern wrapper for `__rust_alloc`. -/
def _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (zeroed : Bool) (stk : Nat := 16384) : Spec (Nat × Nat × M.σ) where
  pre := (rustCliAllocNoOomSpecWithStack M A lim zeroed stk).pre
  post := fun (size, align, st) s0 sf =>
    let st' := M.stepEvents (rustAllocEvents size align) st
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % align = 0⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      A.live (sf.readReg64 .x0) size align ∗
      (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
       else memRegion (sf.readReg64 .x0) size)
  onOom := fun _ _ _ => ⌜False⌝

abbrev _root_.LibsignalBinary.Heap.rustCliDeallocNoOomExternSpecWithStack
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := 16384) : Spec (BitVec 64 × Nat × Nat × M.σ) :=
  _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack M A lim stk

/-- `wp_call`-compatible total-correctness (`NoOom`) extern wrapper for `__rust_realloc`. -/
def _root_.LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := 16384) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) where
  pre := fun (p, old, align, new, bs, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk old align ∧ RustLayoutOk new align ∧
      bs.length ≤ old ∧ bs.length ≤ new ∧ FitsEvents M lim st (rustReallocEvents old new align) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp stk
  post := fun (_, old, align, new, bs, st) s0 sf =>
    let st' := M.stepEvents (rustReallocEvents old new align) st
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % align = 0⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      A.live (sf.readReg64 .x0) new align ∗
      (sf.readReg64 .x0 ↦ₛ bs) ∗
      memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length)
  onOom := fun _ _ _ => ⌜False⌝

abbrev rustCliAllocBudgetExternSpecWithStack
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (zeroed : Bool) (stk : Nat := 16384) :=
  _root_.LibsignalBinary.Heap.rustCliAllocBudgetExternSpecWithStack M A lim zeroed stk
abbrev rustCliDeallocBudgetExternSpecWithStack
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := 16384) :=
  _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack M A lim stk
abbrev rustCliReallocBudgetExternSpecWithStack
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := 16384) :=
  _root_.LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack M A lim stk
abbrev rustCliAllocNoOomExternSpecWithStack
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (zeroed : Bool) (stk : Nat := 16384) :=
  _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack M A lim zeroed stk
abbrev rustCliDeallocNoOomExternSpecWithStack
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := 16384) :=
  _root_.LibsignalBinary.Heap.rustCliDeallocNoOomExternSpecWithStack M A lim stk
abbrev rustCliReallocNoOomExternSpecWithStack
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := 16384) :=
  _root_.LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack M A lim stk

private theorem pure_sepConj_imp {P Q : Prop} {R : SepProp} (h : P → Q) :
    ⌜P⌝ ∗ R ⊢ ⌜Q⌝ ∗ R :=
  Entails.pure_left fun hp => Entails.pure_right (h hp) (Entails.refl R)

theorem subroutine_ok_rustCliAllocBudget_externWithStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide)
    (h : subroutine_ok prog entry (rustCliAllocBudgetSpec M A lim zeroed)) :
    subroutine_ok prog entry (rustCliAllocBudgetExternSpecWithStack M A lim zeroed stk) := by
  refine subroutine_ok_frame_oom' (fun _ _ => emp)
    (subroutine_ok_rustCliAllocBudget_withStack hle hbound h) ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    rw [sepConj_emp]
    exact Entails.refl _
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [rustCliAllocBudgetSpecWithStack, rustCliAllocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliAllocBudgetExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun hacp => hacp.2.1)

theorem subroutine_ok_rustCliDeallocBudget_externWithStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide)
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (rustCliDeallocBudgetExternSpecWithStack M A lim stk) := by
  refine subroutine_ok_frame_oom' (fun _ _ => emp)
    (subroutine_ok_rustCliDeallocBudget_withStack hle hbound h) ?_ ?_
  · rintro ⟨p, size, align, st⟩ s0
    dsimp only [rustCliDeallocBudgetSpecWithStack, rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun ⟨h0, h1, h2, _hl, hlr⟩ => ⟨h0, h1, h2, hlr⟩)
  · rintro ⟨p, size, align, st⟩ s0 sf
    dsimp only [rustCliDeallocBudgetSpecWithStack, rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun ⟨hacp, _⟩ => hacp.2.1)

theorem subroutine_ok_rustCliReallocBudget_externWithStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide)
    (h : subroutine_ok prog entry (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (rustCliReallocBudgetExternSpecWithStack M A lim stk) := by
  refine subroutine_ok_frame_oom' (fun _ _ => emp)
    (subroutine_ok_rustCliReallocBudget_withStack hle hbound h) ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [rustCliReallocBudgetSpecWithStack, rustCliReallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp
      (fun ⟨h0, h1, h2, h3, _hold, hnew, hblo, hbln, hlr⟩ =>
        ⟨h0, h1, h2, h3, hnew, hblo, hbln, hlr⟩)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [rustCliReallocBudgetSpecWithStack, rustCliReallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack]
    rw [sepConj_emp]
    by_cases h0 : sf.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte]
      refine Entails.pure_left fun hacp => ?_
      refine Entails.trans
        (Q := ⌜NullAllowed new align⌝ ∗
          (A.pool lim st sf ∗ stackAt s0.sp stk ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine Entails.trans
        (pure_sepConj_imp (fun hnull => (⟨hacp.2.1, hnull⟩ : sf.trace = s0.trace ∧ NullAllowed new align))) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    · simp only [h0, ↓reduceIte]
      refine Entails.pure_left fun hacp => ?_
      refine Entails.trans
        (Q := ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
          (A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
            stackAt s0.sp stk ∗ A.live (sf.readReg64 .x0) new align ∗
            (sf.readReg64 .x0 ↦ₛ bs) ∗
            memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length)))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine Entails.trans
        (pure_sepConj_imp (fun hal =>
          (⟨hal, hacp.2.1⟩ : (sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace))) ?_
      exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_rustCliAllocNoOom_externWithStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide)
    (h : subroutine_ok prog entry (rustCliAllocNoOomSpec M A lim zeroed)) :
    subroutine_ok prog entry (rustCliAllocNoOomExternSpecWithStack M A lim zeroed stk) := by
  refine subroutine_ok_frame_oom' (fun _ _ => emp)
    (subroutine_ok_rustCliAllocNoOom_withStack hle hbound h) ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    rw [sepConj_emp]
    exact Entails.refl _
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [rustCliAllocNoOomSpecWithStack, rustCliAllocNoOomExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun ⟨hacp, hne, hal⟩ => ⟨hacp.2.1, hne, hal⟩)

theorem subroutine_ok_rustCliReallocNoOom_externWithStack {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide)
    (h : subroutine_ok prog entry (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok prog entry (rustCliReallocNoOomExternSpecWithStack M A lim stk) := by
  refine subroutine_ok_frame_oom' (fun _ _ => emp)
    (subroutine_ok_rustCliReallocNoOom_withStack hle hbound h) ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [rustCliReallocNoOomSpecWithStack, rustCliReallocNoOomExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp
      (fun ⟨h0, h1, h2, h3, _hold, hnew, hblo, hbln, hfit, hlr⟩ =>
        ⟨h0, h1, h2, h3, hnew, hblo, hbln, hfit, hlr⟩)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [rustCliReallocNoOomSpecWithStack, rustCliReallocNoOomExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun ⟨hacp, hne, hal⟩ => ⟨hacp.2.1, hne, hal⟩)

/-! ## Hook and Entry-Bundle Projections -/

private theorem hookSat_withPanics {α : Type} {hooks : String → Option (State → State)}
    {hname : String} {spec : Spec α}
    (hnp : Rust.isPanicSymbol hname = false) (hsat : HookSat hooks hname spec) :
    HookSat (Rust.withPanics hooks) hname spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact ⟨f, by simp [Rust.withPanics, hnp, hf], hok⟩

private theorem subroutine_ok_of_hookSat {α : Type} {prog : Program} {entry : BitVec 64}
    {hooks : String → Option (State → State)} {hname : String} {spec : Spec α}
    (hext : prog.externAt? entry = hooks hname) (hsat : HookSat hooks hname spec) :
    subroutine_ok prog entry spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk (hext.trans hf) hok

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.withPanics {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) :
    RustCliAllocBudgetHooks M A (Rust.withPanics hooks) where
  alloc lim := hookSat_withPanics isPanicSymbol_rust_alloc (hH.alloc lim)
  dealloc lim := hookSat_withPanics isPanicSymbol_rust_dealloc (hH.dealloc lim)
  realloc lim := hookSat_withPanics isPanicSymbol_rust_realloc (hH.realloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.alloc_ok {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits)
    {prog : Program} {entry : BitVec 64}
    (hext : prog.externAt? entry = hooks "__rustc::__rust_alloc") :
    subroutine_ok prog entry (rustCliAllocBudgetSpec M A lim false) :=
  subroutine_ok_of_hookSat hext (hH.alloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.dealloc_ok {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits)
    {prog : Program} {entry : BitVec 64}
    (hext : prog.externAt? entry = hooks "__rustc::__rust_dealloc") :
    subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim) :=
  subroutine_ok_of_hookSat hext (hH.dealloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.realloc_ok {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits)
    {prog : Program} {entry : BitVec 64}
    (hext : prog.externAt? entry = hooks "__rustc::__rust_realloc") :
    subroutine_ok prog entry (rustCliReallocBudgetSpec M A lim) :=
  subroutine_ok_of_hookSat hext (hH.realloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.allocNoOom_ok {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits)
    {prog : Program} {entry : BitVec 64}
    (hext : prog.externAt? entry = hooks "__rustc::__rust_alloc") :
    subroutine_ok prog entry (rustCliAllocNoOomSpec M A lim false) :=
  subroutine_ok_allocNoOom_of_budget (hH.alloc_ok lim hext)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.reallocNoOom_ok {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits)
    {prog : Program} {entry : BitVec 64}
    (hext : prog.externAt? entry = hooks "__rustc::__rust_realloc") :
    subroutine_ok prog entry (rustCliReallocNoOomSpec M A lim) :=
  subroutine_ok_reallocNoOom_of_budget (hH.realloc_ok lim hext)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.alloc_ok_stub {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits)
    {code : Program} {b : BitVec 64} {stub : Nat}
    (hs : stub < 2 ^ 64)
    (hstub : ∀ X, (code.rebase 0 X).hookAtOff? stub = X "__rustc::__rust_alloc") :
    subroutine_ok (code.rebase b hooks) (b + BitVec.ofNat 64 stub)
      (rustCliAllocBudgetSpec M A lim false) :=
  hook_ok_stub hs hstub (hH.alloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.dealloc_ok_stub {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits)
    {code : Program} {b : BitVec 64} {stub : Nat}
    (hs : stub < 2 ^ 64)
    (hstub : ∀ X, (code.rebase 0 X).hookAtOff? stub = X "__rustc::__rust_dealloc") :
    subroutine_ok (code.rebase b hooks) (b + BitVec.ofNat 64 stub)
      (rustCliDeallocBudgetSpec M A lim) :=
  hook_ok_stub hs hstub (hH.dealloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.realloc_ok_stub {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits)
    {code : Program} {b : BitVec 64} {stub : Nat}
    (hs : stub < 2 ^ 64)
    (hstub : ∀ X, (code.rebase 0 X).hookAtOff? stub = X "__rustc::__rust_realloc") :
    subroutine_ok (code.rebase b hooks) (b + BitVec.ofNat 64 stub)
      (rustCliReallocBudgetSpec M A lim) :=
  hook_ok_stub hs hstub (hH.realloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.alloc_ok_at {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits)
    {P : Program} {b : BitVec 64} {name : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H "__rustc::__rust_alloc") :
    subroutine_ok (P.rebase b (Rust.withPanics hooks))
      ((P.rebase b (Rust.withPanics hooks)).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocBudgetSpec M A lim false) :=
  hook_ok_at hfn hk hs hstub isPanicSymbol_rust_alloc (hH.alloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.dealloc_ok_at {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits)
    {P : Program} {b : BitVec 64} {name : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H "__rustc::__rust_dealloc") :
    subroutine_ok (P.rebase b (Rust.withPanics hooks))
      ((P.rebase b (Rust.withPanics hooks)).fnAddr name + BitVec.ofNat 64 k)
      (rustCliDeallocBudgetSpec M A lim) :=
  hook_ok_at hfn hk hs hstub isPanicSymbol_rust_dealloc (hH.dealloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.realloc_ok_at {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits)
    {P : Program} {b : BitVec 64} {name : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H "__rustc::__rust_realloc") :
    subroutine_ok (P.rebase b (Rust.withPanics hooks))
      ((P.rebase b (Rust.withPanics hooks)).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocBudgetSpec M A lim) :=
  hook_ok_at hfn hk hs hstub isPanicSymbol_rust_realloc (hH.realloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.allocNoOom_ok_at {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits)
    {P : Program} {b : BitVec 64} {name : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H "__rustc::__rust_alloc") :
    subroutine_ok (P.rebase b (Rust.withPanics hooks))
      ((P.rebase b (Rust.withPanics hooks)).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocNoOomSpec M A lim false) :=
  subroutine_ok_allocNoOom_of_budget (hH.alloc_ok_at lim hfn hk hs hstub)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.reallocNoOom_ok_at {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits)
    {P : Program} {b : BitVec 64} {name : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H "__rustc::__rust_realloc") :
    subroutine_ok (P.rebase b (Rust.withPanics hooks))
      ((P.rebase b (Rust.withPanics hooks)).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocNoOomSpec M A lim) :=
  subroutine_ok_reallocNoOom_of_budget (hH.realloc_ok_at lim hfn hk hs hstub)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.toEntries {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks)
    {prog : Program} {addrs : RustAllocAddrs}
    (halloc : prog.externAt? addrs.alloc = hooks "__rustc::__rust_alloc")
    (hdealloc : prog.externAt? addrs.dealloc = hooks "__rustc::__rust_dealloc")
    (hrealloc : prog.externAt? addrs.realloc = hooks "__rustc::__rust_realloc") :
    RustCliAllocBudgetEntries M A prog addrs where
  alloc lim := hH.alloc_ok lim halloc
  dealloc lim := hH.dealloc_ok lim hdealloc
  realloc lim := hH.realloc_ok lim hrealloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetHooks.toEntries_stubs {M : AllocCostModel}
    {A : RustCliAllocBudget M} {hooks : String → Option (State → State)}
    (hH : RustCliAllocBudgetHooks M A hooks)
    {code : Program} {b : BitVec 64} {allocStub deallocStub reallocStub : Nat}
    (hsA : allocStub < 2 ^ 64)
    (hstubA : ∀ X, (code.rebase 0 X).hookAtOff? allocStub = X "__rustc::__rust_alloc")
    (hsD : deallocStub < 2 ^ 64)
    (hstubD : ∀ X, (code.rebase 0 X).hookAtOff? deallocStub = X "__rustc::__rust_dealloc")
    (hsR : reallocStub < 2 ^ 64)
    (hstubR : ∀ X, (code.rebase 0 X).hookAtOff? reallocStub = X "__rustc::__rust_realloc") :
    RustCliAllocBudgetEntries M A (code.rebase b hooks)
      ⟨b + BitVec.ofNat 64 allocStub,
       b + BitVec.ofNat 64 deallocStub,
       b + BitVec.ofNat 64 reallocStub⟩ where
  alloc lim := hH.alloc_ok_stub lim hsA hstubA
  dealloc lim := hH.dealloc_ok_stub lim hsD hstubD
  realloc lim := hH.realloc_ok_stub lim hsR hstubR

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.alloc_inImage {M : AllocCostModel}
    {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) (img : Obj.Image) :
    subroutine_ok P addrs.alloc ((rustCliAllocBudgetSpec M A lim false).inImage img) :=
  subroutine_ok_inImage img (hE.alloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.dealloc_inImage {M : AllocCostModel}
    {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) (img : Obj.Image) :
    subroutine_ok P addrs.dealloc ((rustCliDeallocBudgetSpec M A lim).inImage img) :=
  subroutine_ok_inImage img (hE.dealloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.realloc_inImage {M : AllocCostModel}
    {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) (img : Obj.Image) :
    subroutine_ok P addrs.realloc ((rustCliReallocBudgetSpec M A lim).inImage img) :=
  subroutine_ok_inImage img (hE.realloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.alloc_externStack {M : AllocCostModel}
    {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) :
    subroutine_ok P addrs.alloc (rustCliAllocBudgetSpec M A lim false).withExternStackFromAllocOom' :=
  subroutine_ok_withExternStackFromAllocOom' (hE.alloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.dealloc_externStack {M : AllocCostModel}
    {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) :
    subroutine_ok P addrs.dealloc (rustCliDeallocBudgetSpec M A lim).withExternStackFromAllocOom' :=
  subroutine_ok_withExternStackFromAllocOom' (hE.dealloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.realloc_externStack {M : AllocCostModel}
    {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) :
    subroutine_ok P addrs.realloc (rustCliReallocBudgetSpec M A lim).withExternStackFromAllocOom' :=
  subroutine_ok_withExternStackFromAllocOom' (hE.realloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.alloc_externStack_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) (img : Obj.Image) :
    subroutine_ok P addrs.alloc
      (((rustCliAllocBudgetSpec M A lim false).withExternStackFromAllocOom').inImage img) :=
  subroutine_ok_inImage img (hE.alloc_externStack lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.dealloc_externStack_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) (img : Obj.Image) :
    subroutine_ok P addrs.dealloc
      (((rustCliDeallocBudgetSpec M A lim).withExternStackFromAllocOom').inImage img) :=
  subroutine_ok_inImage img (hE.dealloc_externStack lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.realloc_externStack_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) (img : Obj.Image) :
    subroutine_ok P addrs.realloc
      (((rustCliReallocBudgetSpec M A lim).withExternStackFromAllocOom').inImage img) :=
  subroutine_ok_inImage img (hE.realloc_externStack lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.alloc_withStack
    {M : AllocCostModel} {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.alloc (rustCliAllocBudgetSpecWithStack M A lim false stk) :=
  subroutine_ok_rustCliAllocBudget_withStack hle hbound (hE.alloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.dealloc_withStack
    {M : AllocCostModel} {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.dealloc (rustCliDeallocBudgetSpecWithStack M A lim stk) :=
  subroutine_ok_rustCliDeallocBudget_withStack hle hbound (hE.dealloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.realloc_withStack
    {M : AllocCostModel} {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.realloc (rustCliReallocBudgetSpecWithStack M A lim stk) :=
  subroutine_ok_rustCliReallocBudget_withStack hle hbound (hE.realloc lim)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.alloc_withStack_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) (img : Obj.Image) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.alloc ((rustCliAllocBudgetSpecWithStack M A lim false stk).inImage img) :=
  subroutine_ok_inImage img (hE.alloc_withStack lim hle hbound)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.dealloc_withStack_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) (img : Obj.Image) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.dealloc ((rustCliDeallocBudgetSpecWithStack M A lim stk).inImage img) :=
  subroutine_ok_inImage img (hE.dealloc_withStack lim hle hbound)

theorem _root_.LibsignalBinary.Heap.RustCliAllocBudgetEntries.realloc_withStack_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocBudgetEntries M A P addrs) (lim : BudgetLimits) (img : Obj.Image) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.realloc ((rustCliReallocBudgetSpecWithStack M A lim stk).inImage img) :=
  subroutine_ok_inImage img (hE.realloc_withStack lim hle hbound)

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.alloc_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) (img : Obj.Image) :
    subroutine_ok P addrs.alloc ((rustCliAllocNoOomSpec M A lim false).inImage img) :=
  subroutine_ok_inImage img hE.alloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.dealloc_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) (img : Obj.Image) :
    subroutine_ok P addrs.dealloc ((rustCliDeallocNoOomSpec M A lim).inImage img) :=
  subroutine_ok_inImage img hE.dealloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.realloc_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) (img : Obj.Image) :
    subroutine_ok P addrs.realloc ((rustCliReallocNoOomSpec M A lim).inImage img) :=
  subroutine_ok_inImage img hE.realloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.alloc_externStack
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) :
    subroutine_ok P addrs.alloc (rustCliAllocNoOomSpec M A lim false).withExternStackFromAllocOom' :=
  subroutine_ok_withExternStackFromAllocOom' hE.alloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.dealloc_externStack
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) :
    subroutine_ok P addrs.dealloc (rustCliDeallocNoOomSpec M A lim).withExternStackFromAllocOom' :=
  subroutine_ok_withExternStackFromAllocOom' hE.dealloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.realloc_externStack
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) :
    subroutine_ok P addrs.realloc (rustCliReallocNoOomSpec M A lim).withExternStackFromAllocOom' :=
  subroutine_ok_withExternStackFromAllocOom' hE.realloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.alloc_externStack_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) (img : Obj.Image) :
    subroutine_ok P addrs.alloc
      (((rustCliAllocNoOomSpec M A lim false).withExternStackFromAllocOom').inImage img) :=
  subroutine_ok_inImage img hE.alloc_externStack

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.dealloc_externStack_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) (img : Obj.Image) :
    subroutine_ok P addrs.dealloc
      (((rustCliDeallocNoOomSpec M A lim).withExternStackFromAllocOom').inImage img) :=
  subroutine_ok_inImage img hE.dealloc_externStack

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.realloc_externStack_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) (img : Obj.Image) :
    subroutine_ok P addrs.realloc
      (((rustCliReallocNoOomSpec M A lim).withExternStackFromAllocOom').inImage img) :=
  subroutine_ok_inImage img hE.realloc_externStack

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.alloc_withStack
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.alloc (rustCliAllocNoOomSpecWithStack M A lim false stk) :=
  subroutine_ok_rustCliAllocNoOom_withStack hle hbound hE.alloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.dealloc_withStack
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.dealloc (rustCliDeallocNoOomSpecWithStack M A lim stk) :=
  subroutine_ok_rustCliDeallocBudget_withStack hle hbound hE.dealloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.realloc_withStack
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.realloc (rustCliReallocNoOomSpecWithStack M A lim stk) :=
  subroutine_ok_rustCliReallocNoOom_withStack hle hbound hE.realloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.alloc_withStack_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) (img : Obj.Image) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.alloc ((rustCliAllocNoOomSpecWithStack M A lim false stk).inImage img) :=
  subroutine_ok_inImage img (hE.alloc_withStack hle hbound)

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.dealloc_withStack_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) (img : Obj.Image) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.dealloc ((rustCliDeallocNoOomSpecWithStack M A lim stk).inImage img) :=
  subroutine_ok_inImage img (hE.dealloc_withStack hle hbound)

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.realloc_withStack_inImage
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) (img : Obj.Image) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.realloc ((rustCliReallocNoOomSpecWithStack M A lim stk).inImage img) :=
  subroutine_ok_inImage img (hE.realloc_withStack hle hbound)

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.alloc_externWithStack
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.alloc (rustCliAllocNoOomExternSpecWithStack M A lim false stk) :=
  subroutine_ok_rustCliAllocNoOom_externWithStack hle hbound hE.alloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.dealloc_externWithStack
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.dealloc (rustCliDeallocNoOomExternSpecWithStack M A lim stk) :=
  subroutine_ok_rustCliDeallocBudget_externWithStack hle hbound hE.dealloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocNoOomEntries.realloc_externWithStack
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocNoOomEntries M A lim P addrs) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.realloc (rustCliReallocNoOomExternSpecWithStack M A lim stk) :=
  subroutine_ok_rustCliReallocNoOom_externWithStack hle hbound hE.realloc

theorem subroutine_ok_deallocBudget_withStack_of_hookSat {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hooks : String → Option (State → State)} {hname : String}
    {prog : Program} {entry : BitVec 64} {stk : Nat}
    (hsat : HookSat hooks hname (rustCliDeallocBudgetSpec M A lim))
    (hext : prog.externAt? entry = hooks hname)
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok prog entry (rustCliDeallocBudgetSpecWithStack M A lim stk) :=
  subroutine_ok_rustCliDeallocBudget_withStack hle hbound (subroutine_ok_of_hookSat hext hsat)

theorem subroutine_ok_deallocBudget_externWithStack_of_hookSat {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hooks : String → Option (State → State)} {hname : String}
    {prog : Program} {entry : BitVec 64} {stk : Nat}
    (hsat : HookSat hooks hname (rustCliDeallocBudgetSpec M A lim))
    (hext : prog.externAt? entry = hooks hname)
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok prog entry (rustCliDeallocBudgetExternSpecWithStack M A lim stk) :=
  subroutine_ok_rustCliDeallocBudget_externWithStack hle hbound (subroutine_ok_of_hookSat hext hsat)

theorem subroutine_ok_allocNoOom_withStack_of_hookSat {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool}
    {hooks : String → Option (State → State)} {hname : String}
    {prog : Program} {entry : BitVec 64} {stk : Nat}
    (hsat : HookSat hooks hname (rustCliAllocBudgetSpec M A lim zeroed))
    (hext : prog.externAt? entry = hooks hname)
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok prog entry (rustCliAllocNoOomSpecWithStack M A lim zeroed stk) :=
  subroutine_ok_rustCliAllocNoOom_withStack hle hbound
    (subroutine_ok_allocNoOom_of_budget (subroutine_ok_of_hookSat hext hsat))

theorem subroutine_ok_allocNoOom_externWithStack_of_hookSat {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool}
    {hooks : String → Option (State → State)} {hname : String}
    {prog : Program} {entry : BitVec 64} {stk : Nat}
    (hsat : HookSat hooks hname (rustCliAllocBudgetSpec M A lim zeroed))
    (hext : prog.externAt? entry = hooks hname)
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok prog entry (rustCliAllocNoOomExternSpecWithStack M A lim zeroed stk) :=
  subroutine_ok_rustCliAllocNoOom_externWithStack hle hbound
    (subroutine_ok_allocNoOom_of_budget (subroutine_ok_of_hookSat hext hsat))

theorem subroutine_ok_reallocNoOom_withStack_of_hookSat {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hooks : String → Option (State → State)} {hname : String}
    {prog : Program} {entry : BitVec 64} {stk : Nat}
    (hsat : HookSat hooks hname (rustCliReallocBudgetSpec M A lim))
    (hext : prog.externAt? entry = hooks hname)
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok prog entry (rustCliReallocNoOomSpecWithStack M A lim stk) :=
  subroutine_ok_rustCliReallocNoOom_withStack hle hbound
    (subroutine_ok_reallocNoOom_of_budget (subroutine_ok_of_hookSat hext hsat))

theorem subroutine_ok_reallocNoOom_externWithStack_of_hookSat {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hooks : String → Option (State → State)} {hname : String}
    {prog : Program} {entry : BitVec 64} {stk : Nat}
    (hsat : HookSat hooks hname (rustCliReallocBudgetSpec M A lim))
    (hext : prog.externAt? entry = hooks hname)
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok prog entry (rustCliReallocNoOomExternSpecWithStack M A lim stk) :=
  subroutine_ok_rustCliReallocNoOom_externWithStack hle hbound
    (subroutine_ok_reallocNoOom_of_budget (subroutine_ok_of_hookSat hext hsat))

end WithLsPlacement

/-! ## Normalization and Transport Checks -/

section SmokeCheck

example {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s : State) (r : Reg) (v : BitVec 64)
    (a1 a2 : BitVec 64) (w1 w2 : BitVec 64) :
    A.pool lim st
      (applyWriteback
        ((s.setMem ((s.mem.write64 a1 w1).write64 a2 w2)).writeReg64 r v).advancePC
        (some (.sp, s.sp - 32#64))) =
      A.pool lim st s := by
  simp only [arm64_norm]

example {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s : State) (r : Reg) (v : BitVec 64) (wb : Option (Reg × BitVec 64)) :
    (A.atState lim st (applyWriteback (s.writeReg64 r v) wb)).pool = A.pool lim st s := by
  cases wb <;> simp only [wp_norm]

example {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s1 s2 : State) (hvm : VmPreserved s1 s2)
    (prog : Program) (pc : BitVec 64) (X Y : SepProp)
    (post : State → SepProp → Prop) (oom : State → SepProp)
    (h : SepWP prog pc s2 (A.pool lim st s2 ∗ (X ∗ Y)) post oom) :
    SepWP prog pc s2 (X ∗ A.pool lim st s1 ∗ Y) post oom :=
  SepWP.transport_budgetPool hvm (hnext := h)

example {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s1 s2 : State) (hvm : VmPreserved s1 s2)
    (prog : Program) (ret : BitVec 64) (X Y : SepProp)
    (Q Qp : State → SepProp → Prop) (oom : State → SepProp)
    (h : SepWPp prog ret s2 (A.pool lim st s2 ∗ (X ∗ Y)) Q Qp oom) :
    SepWPp prog ret s2 (X ∗ A.pool lim st s1 ∗ Y) Q Qp oom :=
  SepWPp.transport_budgetPool hvm (hnext := h)

example {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s1 s2 : State) (hvm : VmPreserved s1 s2)
    (prog : Program) (pc : BitVec 64) (X Y : SepProp)
    (post : State → SepProp → Prop) (oom : State → SepProp)
    (h : SepWP prog pc s2 (A.pool lim st s2 ∗ (X ∗ Y)) post oom) :
    SepWP prog pc s2 (X ∗ (A.atState lim st s1).pool ∗ Y) post oom :=
  SepWP.transport_atStatePool hvm (hnext := h)

example {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s1 s2 : State) (hvm : VmPreserved s1 s2)
    (prog : Program) (ret : BitVec 64) (X Y : SepProp)
    (Q Qp : State → SepProp → Prop) (oom : State → SepProp)
    (h : SepWPp prog ret s2 (A.pool lim st s2 ∗ (X ∗ Y)) Q Qp oom) :
    SepWPp prog ret s2 (X ∗ (A.atState lim st s1).pool ∗ Y) Q Qp oom :=
  SepWPp.transport_atStatePool hvm (hnext := h)

example {M : AllocCostModel} (lim : BudgetLimits) (st : M.σ)
    (E₁ E₂ : List AllocEvent → Prop) (evs₁ : List AllocEvent)
    (h : FitsEnv M lim st (SeqEnv E₁ E₂)) (h1 : E₁ evs₁) :
    FitsEnv M lim st E₁ ∧ FitsEnv M lim (M.stepEvents evs₁ st) E₂ :=
  ⟨h.seq_left, h.seq_right h1⟩

end SmokeCheck

end LibsignalBinary.Heap.IfaceBudgetLemmas
