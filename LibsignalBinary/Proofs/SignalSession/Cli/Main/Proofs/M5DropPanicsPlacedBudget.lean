/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPanicsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Deallocation Helper for M5 Drop Paths (Block `617`)

Re-exports allocator-free M5 drop step combinators from `M5DropPanicsPlaced` and provides the
budget-threaded `step_dealloc_placed` advancing `A.pool` by `rustDeallocEvents size align`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.MainHops
  (LsCodeInv mProgPlaced main_call_rocl stackAt_split_ge)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPanicsPlacedBudget

open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
  (main_dealloc_fs_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

/-- Execute a budget-threaded `dealloc` call at `lsρ lsRustDeallocSymCli` inside `SepWPp`,
preserving `CodeOk`, `sm.fs = s.fs`, `sm.trace = s.trace`, and `CalleeSavedPreserved s sm`, and
advancing `A.pool lim st s` to `A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sm`. -/
theorem step_dealloc_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {ret retPc : BitVec 64} {s : State}
    {ptr : BitVec 64} {size align sub : Nat}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hext : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hinv : CodeOk s.mem)
    (hpc : s.pc = lsρ lsRustDeallocSymCli) (hrun : s.status = .Running)
    (hal : s.spAligned = true) (hlr : s.readReg64 .lr = retPc)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hlay : LayoutOk size align)
    (hal_le : align ≤ 2 ^ 31 := by decide)
    (hP : P ⊢ A.live ptr size align ∗ memRegion ptr size ∗ A.pool lim st s ∗ stackAt s.sp sub ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = retPc → sm.status = .Running → sm.sp = s.sp →
      CalleeSavedPreserved s sm → CodeOk sm.mem →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sm ∗ stackAt s.sp sub ∗ F)
        Q Qp oom)
    (hlr_ls : LsRetAddr624 retPc := by simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp (mProgPlaced H) ret s P Q Qp oom := by
  let slack := memRegion (s.sp - BitVec.ofNat 64 sub) (sub - extHookStack)
  have hsplit := stackAt_split_ge s.sp hext hsub64
  refine main_call_rocl (x := (ptr, size, align, st)) (main_dealloc_fs_placed_ok hA)
    hinv hpc hrun hal hlr (F := slack ∗ F) ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    simp only [sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2, ⟨hlay, hal_le⟩, by rwa [hlr]⟩
    exact Entails.of_eq (by dsimp +zetaDelta only [slack]; sep_ac_rfl)
  · intro sm hinv' hpcm hrunm hspm hcsm
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hfsm => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm hcsm hinv' hfsm htrm)
    rw [hsplit]
    exact Entails.of_eq (by dsimp +zetaDelta only [slack]; sep_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPanicsPlacedBudget
