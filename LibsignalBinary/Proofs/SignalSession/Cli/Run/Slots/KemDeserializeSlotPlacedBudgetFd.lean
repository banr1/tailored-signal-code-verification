/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserializePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# File-Descriptor-Threaded `kem::Key<Public>::deserialize` Slot Adapter (Placed)

Lifts `cliKemDeserialize_placed_at_block` across `AllocWithFds.withFds` when `lim.enforced = true`,
discharging `withFdsGe3Closed` for Block `590` (`kem::Key<Public>::deserialize`) on `lsProg_579 H`
both for `slotsOfPlaced` and `slotsOfSigPkFrozenPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName)
open CryptoVerification.SignalSession.Cli.Main.Placed (instIsLsBlockProg_617)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_590)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (RunNeeds RunSem)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (hookOk_allocBudget_withFds hookOk_deallocBudget_withFds hookOk_reallocBudget_withFds
   withFds withFds_pool_enforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
  (hookOk_rustAllocWithStack hookOk_rustDeallocExternWithStack hookOk_rustReallocExternWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
  (cliKemDeserializeSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserializePlacedBudget
  (cliKemDeserializeSpecPlaced cliKemDeserialize_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd (slotWithFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)

theorem subroutine_ok_of_pre_post {α : Type} {P : Program} {entry : BitVec 64}
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

theorem codecHooksPlaced_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : CodecHooksPlaced M A lim H) :
    CodecHooksPlaced M (withFds A) lim H where
  shim := h.shim
  alloc := let ⟨f, hf, hok⟩ := h.alloc; ⟨f, hf, hookOk_allocBudget_withFds hok⟩
  realloc := let ⟨f, hf, hok⟩ := h.realloc; ⟨f, hf, hookOk_reallocBudget_withFds hok⟩
  dealloc := let ⟨f, hf, hok⟩ := h.dealloc; ⟨f, hf, hookOk_deallocBudget_withFds hok⟩
  memcpy := h.memcpy
  panic_alloc := h.panic_alloc
  panic_raw := h.panic_raw

/-- Lifts `AllocContractsXCliPlaced` from `A` to `withFds A` via `RunHooksPlaced A lim H`. -/
theorem allocContractsXCliPlaced_withFds_of_runHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    AllocContractsXCliPlaced (withFds A) lim H := by
  have hc := codecHooksPlaced_withFds hh.codecHooks
  rcases hc.alloc with ⟨fa, hfa, hoka⟩
  rcases hc.dealloc with ⟨fd, hfd, hokd⟩
  rcases hc.realloc with ⟨fr, hfr, hokr⟩
  exact
    { hh.alloc with
      alloc := subroutine_ok_withLsCodeRoLoaded_of_plain
        (ls_hook_ok_ultra_of_mem
          ⟨fa, hfa, hookOk_rustAllocWithStack hoka (by decide) (by decide)⟩ (by decide))
      dealloc := subroutine_ok_withLsCodeRoLoaded_of_plain
        (ls_hook_ok_ultra_of_mem
          ⟨fd, hfd, hookOk_rustDeallocExternWithStack hokd (by decide) (by decide)⟩ (by decide))
      realloc := subroutine_ok_withLsCodeRoLoaded_of_plain
        (ls_hook_ok_ultra_of_mem
          ⟨fr, hfr, hookOk_rustReallocExternWithStack hokr (by decide) (by decide)⟩ (by decide)) }

private theorem kem_pre_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 P2 P3 P4 P5 R : SepProp} {st : M.σ} {s0 : State}
    (hClosed0 : FdsGe3Closed s0.fs)
    (h : s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ A.pool lim st s0 ∗ P4) ∗ P5) ∗ R) :
    s0.mem ⊨ ((P1 ∗ P2 ∗ P3 ∗ (withFds A).pool lim st s0 ∗ P4) ∗ P5) ∗ R := by
  rw [withFds_pool_enforced A henf]
  have hEq :
      ((P1 ∗ P2 ∗ P3 ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗ P4) ∗ P5) ∗ R =
      ⌜FdsGe3Closed s0.fs⌝ ∗ (((P1 ∗ P2 ∗ P3 ∗ A.pool lim st s0 ∗ P4) ∗ P5) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj]
  exact ⟨hClosed0, h⟩

private theorem kem_post_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 P2 P3 P4 R : SepProp} {st : M.σ} {sf : State}
    (h : sf.mem ⊨ (P1 ∗ P2 ∗ P3 ∗ (withFds A).pool lim st sf ∗ P4) ∗ R) :
    sf.mem ⊨ (⌜FdsGe3Closed sf.fs⌝ ∗ (P1 ∗ P2 ∗ P3 ∗ A.pool lim st sf ∗ P4)) ∗ R := by
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (P1 ∗ P2 ∗ P3 ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim st sf) ∗ P4) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗ ((P1 ∗ P2 ∗ P3 ∗ A.pool lim st sf ∗ P4) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact h

/-- Converts `subroutine_ok` for `cliKemDeserializeSpecPlaced M (withFds A) lim stk` to
`withFdsGe3Closed (cliKemDeserializeSpecPlaced M A lim stk)` when `lim.enforced = true`. -/
theorem subroutine_ok_kemDeserialize_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64} {stk : Nat}
    (hok : subroutine_ok P entry (cliKemDeserializeSpecPlaced M (withFds A) lim stk)) :
    subroutine_ok P entry (withFdsGe3Closed (cliKemDeserializeSpecPlaced M A lim stk)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [cliKemDeserializeSpecPlaced, withLsCodeRoLoaded, cliKemDeserializeSpec,
      withFds_repAlloc] at hpreA ⊢
    exact ⟨trivial, kem_pre_enforced henf hClosed0 hpreA⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, cliKemDeserializeSpecPlaced, withLsCodeRoLoaded,
      cliKemDeserializeSpec, withFds_repAlloc] at hpost ⊢
    exact kem_post_enforced henf hpost

/-- Transfers `withFdsGe3Closed` for Block `590` (`kem::Key<Public>::deserialize`) to any caller block `i < 619`. -/
theorem cliKemDeserialize_placed_at_block_withFdsGe3Closed [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [hcaller : IsLsBlockProg callerProg i H]
    (henf : lim.enforced = true)
    (hA : AllocContractsXCliPlaced (withFds A) lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (stk : Nat) (hstk : 48 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_590).base
      (withFdsGe3Closed (cliKemDeserializeSpecPlaced M A lim stk)) :=
  subroutine_ok_kemDeserialize_withFdsGe3Closed_of_withFds henf
    (cliKemDeserialize_placed_at_block (callerProg := callerProg) (i := i)
      (A := withFds A) hA hRO stk hstk hstk64 hi)

/-- Discharges `(slotWithFdsGe3Closed (slotsOfPlaced A lim sEnvs S needs).kemDeserialize).OkPlaced` on `lsProg_579 H`. -/
theorem kemDeserialize_slot_withFdsGe3Closed_okPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (sEnvs : RunSlotEnvs) (S : RunSem) (needs : RunNeeds)
    (henf : lim.enforced = true)
    (hA : AllocContractsXCliPlaced (withFds A) lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec)) :
    (slotWithFdsGe3Closed (slotsOfPlaced A lim sEnvs S needs).kemDeserialize).OkPlaced
      (lsProg_579 H) (blkPl_590).base :=
  fun stk hlo hhi =>
    cliKemDeserialize_placed_at_block_withFdsGe3Closed (callerProg := lsProg_579 H) (i := 579)
      henf hA hRO stk hlo (Nat.le_trans hhi (by decide))

/-- Discharges `(slotWithFdsGe3Closed (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).kemDeserialize).OkPlaced` on `lsProg_579 H`. -/
theorem kemDeserialize_frozenSlot_withFdsGe3Closed_okPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (sEnvs : RunSlotEnvs) (S : RunSem) (needs : RunNeeds)
    (henf : lim.enforced = true)
    (hA : AllocContractsXCliPlaced (withFds A) lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec)) :
    (slotWithFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).kemDeserialize).OkPlaced
      (lsProg_579 H) (blkPl_590).base :=
  kemDeserialize_slot_withFdsGe3Closed_okPlaced sEnvs S needs henf hA hRO

theorem kemDeserialize_slot_withFdsGe3Closed_of_runHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (sEnvs : RunSlotEnvs) (S : RunSem) (needs : RunNeeds)
    (henf : lim.enforced = true)
    (hh : RunHooksPlaced A lim H) :
    (slotWithFdsGe3Closed (slotsOfPlaced A lim sEnvs S needs).kemDeserialize).OkPlaced
      (lsProg_579 H) (blkPl_590).base :=
  kemDeserialize_slot_withFdsGe3Closed_okPlaced sEnvs S needs henf
    (allocContractsXCliPlaced_withFds_of_runHooks hh) hh.memcpyRO

/-- `RunHooksPlaced` wrapper for `kemDeserialize_frozenSlot_withFdsGe3Closed_okPlaced`. -/
theorem kemDeserialize_frozenSlot_withFdsGe3Closed_of_runHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (sEnvs : RunSlotEnvs) (S : RunSem) (needs : RunNeeds)
    (henf : lim.enforced = true)
    (hh : RunHooksPlaced A lim H) :
    (slotWithFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).kemDeserialize).OkPlaced
      (lsProg_579 H) (blkPl_590).base :=
  kemDeserialize_frozenSlot_withFdsGe3Closed_okPlaced sEnvs S needs henf
    (allocContractsXCliPlaced_withFds_of_runHooks hh) hh.memcpyRO

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudgetFd
