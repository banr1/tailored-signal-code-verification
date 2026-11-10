/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `main_ret` Epilogue (`M+0xb80 .. M+0xba0`, Block `617`)

Verifies `main`'s shared return epilogue (`M+0xb80 .. M+0xba0`) on Block `617` under
`[LibsignalPlacement]` and `RustCliAllocBudget M`, transporting `A.pool lim st` via `VmPreserved`
and providing `ExitKPoolPlaced` and `NeedLocks` return projections.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtRetPlaced calleeSavedPreserved_of_regs mProgPlaced mProgPlaced_eq mainFrameSize mainOom
   mainSaved mainSaved_eq_sub retMem retMem_entails_post sepWPp_with_stk_le_two_pow_64)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (ExitKPlaced retMem_of_pool)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-- Pool-retaining early-return continuation from `M+0xb80` under `[LibsignalPlacement]` and
`RustCliAllocBudget M`, keeping `(A.atState lim st s).pool = A.pool lim st s` intact so
`main_ret_placed_needLocks_proof` can project `((libcAddr + 3#64) ↦₈ 0#8)` (`NeedLocks`). -/
def ExitKPoolPlaced [LibsignalPlacement] {M : AllocCostModel} (CodeOk : Memory → Prop)
    (H : LibsignalHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits) (s0 : State) (stk : Nat)
    (G : Nat → State → Prop) (Q Qp : State → SepProp → Prop) : Prop :=
  ∀ (s : State) (st : M.σ) (code : Nat), AtRetPlaced CodeOk s0 s code → G code s →
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (retMem (A.atState lim st s) s0 stk) Q Qp (mainOom s0)

/-- Any pool-erasing `HopsPlacedBudget.ExitKPlaced` continuation lifts to `ExitKPoolPlaced` by
absorbing `(A.atState lim st s).pool = A.pool lim st s` into `anyHeap`. -/
theorem exitKPoolPlaced_of_exitKPlaced [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {s0 : State} {stk : Nat}
    {G : Nat → State → Prop} {Q Qp : State → SepProp → Prop}
    (hexit : ExitKPlaced CodeOk H A s0 stk G Q Qp) :
    ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp := by
  intro s st code hs hG R hm hL
  refine hexit s code hs hG R (Satisfies.mono (sepConj_mono_left ?_) hm) hL
  unfold retMem
  rw [RustCliAllocBudget.atState_pool]
  exact retMem_of_pool A lim st s0 s stk

@[local simp, local arm64_norm]
private theorem sp_sub_96_add_96_bp (sp0 : BitVec 64) : (sp0 - 96#64) + 96#64 = sp0 := by
  calc
    (sp0 - 96#64) + 96#64 = sp0 + (-96#64 + 96#64) := by
      rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    _ = sp0 := BitVec.add_zero sp0

private theorem sepWPp_of_sepWP_ret_any_bp {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog ret s P Q) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, hout | ⟨_, hmo⟩⟩
  · exact ⟨sf, hsteps, Or.inl hout⟩
  · exact (not_satisfies_false_sepConj hmo).elim

private theorem main_ret_placed_vm [LibsignalPlacement] {CodeOk : Memory → Prop}
    {H : LibsignalHooks} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {s0 s : State} {stk code : Nat}
    (hstk : mainFrameSize ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hs : AtRetPlaced CodeOk s0 s code) :
    SepWP ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (retMem (A.atState lim st s) s0 stk)
      (fun sf Pf => VmPreserved s sf ∧
        (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code ∧ sf.trace = s.trace ∧
          sf.fs = s.fs ∧
          (Pf ⊢ stackAt s0.sp stk ∗ (A.atState lim st s).pool ∗ anyHeap))) := by
  have hpc : s.pc = (blkPl_617).base + 2944#64 := hs.base.pc
  have hrun : s.status = .Running := hs.base.run
  have hsp : s.sp = s0.sp - 0x4e0#64 := hs.base.sp
  have hsp0 : s0.spAligned = true := hs.base.spAligned
  have hsp_al : s.spAligned = true := hs.base.spAligned_state
  have hsp60_al : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0
  have hw26 : (s.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code := hs.w26
  have hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := hs.base.vregs
  unfold retMem
  rw [mainSaved_eq_sub s0]
  simp only [sepConj_assoc]
  by_vm_steps
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    refine ⟨by simp only [arm64_norm],
      by simp only [arm64_norm, *], ?_, by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], ?_⟩
    · refine calleeSavedPreserved_of_regs
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (Eq.trans (by simp only [calleeSavedVRegs, arm64_norm]) hvregs)
    · refine Entails.trans ?_ (retMem_entails_post (A.atState lim st s) s0 hstk hstk64)
      unfold retMem
      rw [mainSaved_eq_sub s0]
      simp only [sepConj_assoc]
      exact Entails.refl _

/-- Budget-threaded return epilogue (`M+0xb80 → lr` on Block `617`): returns `code` with `sp`,
`x19..x29` (from `mainSaved`), and `d8..d15` restored, `VmPreserved s sf`, trace and files
unchanged, and `A.pool lim st s` transported to `A.pool lim st sf`. -/
theorem main_ret_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    {H : LibsignalHooks} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {s0 s : State} {stk code : Nat} {Qp : State → SepProp → Prop}
    (hstk : mainFrameSize ≤ stk) (hs : AtRetPlaced CodeOk s0 s code) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s (retMem (A.atState lim st s) s0 stk)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code ∧ sf.trace = s.trace ∧
        sf.fs = s.fs ∧ VmPreserved s sf ∧
        (Pf ⊢ stackAt s0.sp stk ∗ A.pool lim st sf ∗ anyHeap))
      Qp (mainOom s0) := by
  refine sepWPp_with_stk_le_two_pow_64 hstk
    (F := memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
      (A.atState lim st s).pool ∗ anyHeap)
    (Entails.of_eq (by
      unfold retMem
      dsimp only [mainFrameSize]
      sep_ac_rfl))
    fun hstk64 => ?_
  apply sepWPp_of_sepWP_ret_any_bp
  rw [mProgPlaced_eq]
  refine SepWP.mono (main_ret_placed_vm hstk hstk64 hs) ?_
  rintro sf Pf _ _ ⟨hvm, hsp, hcs, hx0, htr, hfs, hmem⟩
  refine ⟨hsp, hcs, hx0, htr, hfs, hvm, ?_⟩
  rw [RustCliAllocBudget.atState_pool, ← A.pool_of_vmPreserved hvm] at hmem
  exact hmem

/-- Variant of `main_ret_placed_proof` absorbing `A.pool lim st sf` into `anyHeap` so the memory
postcondition matches `SpecsPlacedBudget.mainSpecPlaced` / `mainSpecTightPlaced`
(`stackAt s0.sp stk ∗ anyHeap`). -/
theorem main_ret_placed_anyHeap_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    {H : LibsignalHooks} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {s0 s : State} {stk code : Nat} {Qp : State → SepProp → Prop}
    (hstk : mainFrameSize ≤ stk) (hs : AtRetPlaced CodeOk s0 s code) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s (retMem (A.atState lim st s) s0 stk)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code ∧ sf.trace = s.trace ∧
        sf.fs = s.fs ∧ VmPreserved s sf ∧
        (Pf ⊢ stackAt s0.sp stk ∗ anyHeap))
      Qp (mainOom s0) := by
  intro R hm hL
  rcases main_ret_placed_proof (A := A) (lim := lim) (st := st) hstk hs R hm hL with
    ⟨sf, hsteps, ⟨hpc, hrun, Pf, hPf, hsp, hcs, hx0, htr, hfs, hvm, hmem⟩ | hpan | hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hPf, hsp, hcs, hx0, htr, hfs, hvm, ?_⟩⟩
    exact Entails.trans hmem (sepConj_mono_right (entails_anyHeap _))
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- `NeedLocks` corollary of `main_ret_placed_proof`: given any pool-to-`NeedLocks` projection
`hneed : ∀ st' sf, A.pool lim st' sf ⊢ ((libcAddr + 3#64) ↦₈ 0#8) ∗ anyHeap` (for instance
`PoolNeedLocks.hookPool_entails_needLocks_anyHeap`), projects
`((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap` on normal return from `main`. -/
theorem main_ret_placed_needLocks_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    {H : LibsignalHooks} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {libcAddr : BitVec 64} {lim : BudgetLimits} {st : M.σ}
    {s0 s : State} {stk code : Nat} {Qp : State → SepProp → Prop}
    (hneed : ∀ (st' : M.σ) (sf : State),
      A.pool lim st' sf ⊢ ((libcAddr + 3#64) ↦₈ 0#8) ∗ anyHeap)
    (hstk : mainFrameSize ≤ stk) (hs : AtRetPlaced CodeOk s0 s code) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s (retMem (A.atState lim st s) s0 stk)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code ∧ sf.trace = s.trace ∧
        sf.fs = s.fs ∧ VmPreserved s sf ∧
        (Pf ⊢ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap))
      Qp (mainOom s0) := by
  intro R hm hL
  rcases main_ret_placed_proof (A := A) (lim := lim) (st := st) hstk hs R hm hL with
    ⟨sf, hsteps, ⟨hpc, hrun, Pf, hPf, hsp, hcs, hx0, htr, hfs, hvm, hmem⟩ | hpan | hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hPf, hsp, hcs, hx0, htr, hfs, hvm, ?_⟩⟩
    refine Entails.trans hmem ?_
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (hneed st sf))) ?_
    have hEq :
        stackAt s0.sp stk ∗ (((libcAddr + 3#64) ↦₈ 0#8) ∗ anyHeap) ∗ anyHeap =
        ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ (anyHeap ∗ anyHeap) := by
      sep_ac_rfl
    rw [hEq]
    exact sepConj_mono_right (sepConj_mono_right (entails_anyHeap _))
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
