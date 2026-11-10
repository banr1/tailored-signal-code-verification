/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cHelpersPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Placed Helpers for Arm `R1c`

Provides budget-threaded `r1c_call_lscro`, `r1c_dealloc_ok`, and `r1c_call_dealloc` under
`RunHooksPlaced A lim H` on Block `579` (`signal_session::run`), re-exporting pure word-packing and
framing helpers from `R1cHelpersPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cHelpersPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.RunCompose (runFsp runPcPlaced runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers
  (R1cCodeOk r1c_sepWPp_pure_left r1c_sepWPp_weaken_pre r1c_spAligned r1c_stackAt_split_ge)
open CryptoVerification.SignalSession.Cli.RunSkeleton (runFrame)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
  (AllocContractsFsPlaced.dealloc_rocl)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)

theorem r1c_call_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {callee retAddr ret : BitVec 64} {spec : Spec α} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (x : α)
    (hcall : subroutine_ok prog callee (withLsCodeRoLoaded lsmpl spec))
    (hinv : R1cCodeOk s.mem)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = retAddr)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sm : State,
      Steps prog s sm →
      R1cCodeOk sm.mem →
      sm.pc = retAddr →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hm_pre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  have hpre :
      s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) :=
    satisfies_lscro_pre hinv hm_pre
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hinv.of_keepsFrozen hsteps.keepsFrozen) hpcm hrunm hspm hcsm R hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

theorem r1c_dealloc_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    subroutine_ok (runProgPlaced H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs) := by
  have hrocl := AllocContractsFsPlaced.dealloc_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

theorem r1c_call_dealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s1 : State}
    {ptr : BitVec 64} {sz resStack retOff : Nat} {Rest : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hsp0 : s0.spAligned = true)
    (hinv1 : R1cCodeOk s1.mem)
    (hpc1 : s1.pc = lsρ lsRustDeallocSymCli)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = runFsp s0)
    (hlr1 : s1.readReg64 .lr = runPcPlaced retOff)
    (hx0 : s1.readReg64 .x0 = ptr)
    (hx1 : (s1.readReg64 .x1).toNat = sz)
    (hx2 : s1.readReg64 .x2 = 1#64)
    (hlay : LayoutOk sz 1)
    (hnext : ∀ s2 : State,
      R1cCodeOk s2.mem → s2.pc = runPcPlaced retOff → s2.status = .Running →
      s2.sp = runFsp s0 → CalleeSavedPreserved s1 s2 →
      s2.fs = s1.fs → s2.trace = s1.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents sz 1) st) s2 ∗ Rest)
        Q Qp oom)
    (hlr_ls : LsRetAddr624 (runPcPlaced retOff) := by
      first | assumption | simp (config := { decide := true })
        [_root_.CryptoVerification.SignalSession.Cli.RunCompose.runPcPlaced, wp_norm, arm64_norm,
         _root_.LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen, *]) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
      ((A.live ptr sz 1 ∗ memRegion ptr sz) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1 ∗ Rest)
      Q Qp oom := by
  refine r1c_call_lscro
    (F := memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
      (resStack - runFrame - extHookStack) ∗ Rest)
    (ptr, sz, 1, st) (r1c_dealloc_ok hh) hinv1 hpc1 hrun1
    (r1c_spAligned hsp0 hsp1) hlr1 ?_
    (hnext := fun s2 _ hinv2 hpc2 hrun2 hsp2 hcs2 => ?_)
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    have hpure : s1.readReg64 .x0 = ptr ∧ (s1.readReg64 .x1).toNat = sz ∧
        (s1.readReg64 .x2).toNat = 1 ∧ RustLayoutOk sz 1 ∧
        LsRetAddr624 (s1.readReg64 .lr) :=
      ⟨hx0, hx1, by rw [hx2]; decide, ⟨hlay, by decide⟩, hlr1 ▸ hlr_ls⟩
    rw [hsp1, r1c_stackAt_split_ge (runFsp s0) hext_le hsub64]
    conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right hpure ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · refine r1c_sepWPp_weaken_pre
      (P' := ⌜s2.fs = s1.fs ∧ s2.trace = s1.trace⌝ ∗
        (stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents sz 1) st) s2 ∗ Rest))
      (by
        dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        rw [hsp1, r1c_stackAt_split_ge (runFsp s0) hext_le hsub64]
        simp only [← sepConj_assoc, pure_sepConj_pure]
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    apply r1c_sepWPp_pure_left; rintro ⟨hfs2, htr2⟩
    exact hnext s2 hinv2 hpc2 hrun2 (hsp2.trans hsp1) hcs2 hfs2 htr2

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cHelpersPlacedBudget
