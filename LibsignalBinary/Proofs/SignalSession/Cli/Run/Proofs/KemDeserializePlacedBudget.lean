/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserializePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCalleesBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded `[LibsignalPlacement]` `kem::Key<Public>::deserialize` (Block `590`)

Allocation-budget (`RustCliAllocBudget M`) proof of `kem::Key<Public>::deserialize` (Block `590`,
calling `KeyKind::key_length` at Block `110`) and cross-block transfer to any caller `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserializePlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open AsmConstants (boxSliceLenOff)
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_110 blkPl_110
  ls_hook_ok_ultra_of_mem lsmpl lsρ
)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.LibsignalTripleRatchetRepr (boxU8At)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack memcpyName sessionMemcpyRegionSpec withStack
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded extract_withLsRoCl ls_subroutine_ok_rocl_of_block
  ls_subroutine_ok_rocl_of_plain sepWP_seq_lscro subroutine_ok_rocl_of_plain
  withLsCodeRoLoaded withLsRoCl
)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.Placed (
  blkPl_590 instIsLsBlockProg_590 lsProg_590
)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617 instIsLsBlockProg_617)
open CryptoVerification.SignalSession.Cli.RunProofs (
  KemDeserializeGhost kemDeserResAt kemPkDeserialize kemPkLen
)
open CryptoVerification.SignalSession.Cli.RunProofs.KemDeserializeHelpers (
  cliKemDeserStack stackAt_split_ge
)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt bytesAt_false bytesAt_true)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCalleesBudget (
  kemPublicKeyLengthBudgetSpec kemPublicKeyLength_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget (
  cliKemDeserializeSpec kemDeserializeEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (
  allocNoOomExtern_lscro_of_cli shim_lscro_of_cli
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Budget-form relocatable `[LibsignalPlacement]` counterpart of `cliKemDeserializeSpecPlaced`
(Block `590`). -/
def cliKemDeserializeSpecPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (KemDeserializeGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (cliKemDeserializeSpec M A lim stk)

section KemDeserializePlacedBudgetHelpers

private theorem subroutine_ok_frame_weaken_kem_placed {α : Type} {prog : Program}
    {entry : BitVec 64} {spec spec' : Spec α} (F : α → State → SepProp)
    (h : subroutine_ok prog entry spec)
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, spec.post x s0 sf ∗ F x s0 ⊢ spec'.post x s0 sf)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hexit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog entry spec' := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp => ?_
  have hp' : s0.mem ⊨ spec.pre x s0 ∗ (F x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hp
  refine h.mono_outcome x (F x s0 ∗ R) s0 hpc hrun hp' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hq
  · rw [hpan] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem stackAt_kemDeser_placed (sp : BitVec 64) :
    stackAt sp cliKemDeserStack =
      stackAt (sp - 48#64) extHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗
        ((sp - 32#64) ↦₆₄ v2) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
        ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
  have h1 := ProofLib.stackAt_split_cells sp 16384 6 (by decide)
  have hsum : 16384 + 8 * 6 = cliKemDeserStack := by decide
  rw [hsum] at h1
  change stackAt sp cliKemDeserStack =
    stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 at h1
  have hc6 : cells (sp - 48#64) 6 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗
        ((sp - 32#64) ↦₆₄ v2) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
        ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
    cells_unfold
  rw [h1, hc6]

private theorem memRegion_24_split_8_16_placed (r : BitVec 64) :
    memRegion r 24 = (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗ memRegion (r + 8#64) 16 := by
  rw [show (24 : Nat) = 8 + 16 by rfl, ProofLib.memRegion_split r 8 16 (by decide),
    ProofLib.memRegion_eight]

private theorem memRegion_24_split_badType_placed (r : BitVec 64) :
    memRegion r 24 =
      (∃∗ b1 : BitVec 8, ∃∗ w0 : BitVec 64,
        (r ↦₆₄ w0) ∗ ((r + 8#64) ↦₈ b1) ∗ memRegion (r + 9#64) 15) := by
  rw [memRegion_24_split_8_16_placed r,
    show (16 : Nat) = 1 + 15 by rfl,
    ProofLib.memRegion_split (r + 8#64) 1 15 (by decide),
    ProofLib.memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_24_split_badLen_placed (r : BitVec 64) :
    memRegion r 24 =
      (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (r ↦₆₄ w0) ∗ ((r + 8#64) ↦₆₄ w1) ∗ memRegion (r + 16#64) 8) := by
  rw [memRegion_24_split_8_16_placed r,
    show (16 : Nat) = 8 + 8 by rfl,
    ProofLib.memRegion_split (r + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_24_cells_placed (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem ofNat_beq_zero_false_placed {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

private theorem ofNat_ne_1569_placed {n : Nat} (hne : n ≠ 1569) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 1569#64 := by
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 1569 at ht
  omega

private theorem byte_zext32_ne8_placed {t : BitVec 8} (ht : t ≠ 0x08#8) :
    t.zeroExtend 32 ≠ 8#32 := by
  intro h
  apply ht
  apply BitVec.eq_of_toNat_eq
  have hlt : t.toNat < 256 := t.isLt
  have hn := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : t.toNat < 2 ^ 32)] at hn
  exact hn

private theorem byte_zext64_ne8_placed {t : BitVec 8} (ht : t ≠ 0x08#8) :
    t.zeroExtend 64 ≠ 8#64 := by
  intro h
  apply ht
  apply BitVec.eq_of_toNat_eq
  have hlt : t.toNat < 256 := t.isLt
  have hn := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : t.toNat < 2 ^ 64)] at hn
  exact hn

private theorem ok_post_entails_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (r buf : BitVec 64) (key : List (BitVec 8))
    (hlen : key.length = kemPkLen) (hbuf : buf ≠ 0#64) :
    (r ↦₆₄ 0xfffffffffffffffe#64) ∗ ((r + 8#64) ↦₆₄ buf) ∗ ((r + 16#64) ↦₆₄ 1568#64) ∗
      A.live buf 1568 1 ∗ (buf ↦ₛ key) ⊢
      kemDeserResAt A.repAlloc r (.ok key) := by
  have hne : key ≠ [] := by
    intro h; rw [h] at hlen; simp [kemPkLen] at hlen
  unfold RustCliAllocBudget.live kemDeserResAt
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right buf ?_
  unfold boxU8At
  have hoff : (r + 8#64 + asm64% boxSliceLenOff) = r + 16#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (buf ≠ 0 ∧ 1568 < 2 ^ 63) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨hbuf, by decide⟩⟩
  rw [hoff, hlen]
  dsimp only [kemPkLen]
  simp only [hne, ↓reduceIte, hpure, pure_true, emp_sepConj]
  exact Entails.of_eq (by sep_ac_rfl)

private def cliMemcpyBytesAtSpecPlaced (ro : Bool) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length ∧
     bs.length ≤ 2 ^ 64⌝ ∗
    memRegion dst bs.length ∗
    bytesAt ro src bs ∗
    stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
    (dst ↦ₛ bs) ∗
    bytesAt ro src bs ∗
    stackAt s0.sp extHookStack

private theorem cliMemcpy_bytesAt_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (ro : Bool) :
    subroutine_ok (lsProg_590 H) (lsρ memcpyName)
      (withLsRoCl lsmpl (cliMemcpyBytesAtSpecPlaced ro)) := by
  cases ro
  · have hmc := @ls_subroutine_ok_rocl_of_block _ _ (lsProg_590 H) (lsProg_617 H) 590 617 H
      (instIsLsBlockProg_590 H) (instIsLsBlockProg_617 H) (lsρ memcpyName) _
      (hA.session_memcpy_region extHookStack (Nat.le_refl _) (by decide))
      _ _ _ _ (by decide) (by decide) (by decide)
    refine subroutine_ok_mono hmc ?_ ?_
    · intro ⟨dst, src, bs⟩ R s0 hpre
      obtain ⟨hcrl, hrest⟩ := extract_withLsRoCl hpre
      dsimp only [withLsRoCl, withStack, sessionMemcpyRegionBudgetSpec,
        sessionMemcpyRegionSpec, memcpyRegionSpec]
      dsimp only [cliMemcpyBytesAtSpecPlaced, bytesAt_false] at hrest
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcrl, ?_⟩
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hrest ⊢
      exact ⟨⟨hrest.1.1, hrest.1.2.1, hrest.1.2.2.1⟩, hrest.2⟩
    · intro ⟨dst, src, bs⟩ R s0 sf hpost
      dsimp only [withLsRoCl, cliMemcpyBytesAtSpecPlaced, withStack,
        sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
        bytesAt_false] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, ⟨hpost.2.2.1.1, hpost.2.2.1.2, hpost.2.1⟩, hpost.2.2.2⟩
  · have hmc_plain : subroutine_ok (lsProg_590 H) (lsρ memcpyName)
        (withVmPreserved sessionMemcpyRegionROSpec) :=
      ls_hook_ok_ultra_of_mem (prog := lsProg_590 H) (i := 590)
        (hprog := instIsLsBlockProg_590 H) hRO
    have hmc := subroutine_ok_rocl_of_plain (pl := lsmpl) hmc_plain
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨
        (withLsRoCl lsmpl (withVmPreserved sessionMemcpyRegionROSpec)).pre
          (dst, src, bs) s0 ∗ (stackAt s0.sp extHookStack ∗ R) := by
      obtain ⟨hcrl, hrest⟩ := extract_withLsRoCl hpre
      dsimp only [withLsRoCl, withVmPreserved, sessionMemcpyRegionROSpec]
      dsimp only [cliMemcpyBytesAtSpecPlaced, bytesAt_true] at hrest
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcrl, ?_⟩
      simpa only [sepConj_assoc] using hrest
    refine hmc.mono_outcome (dst, src, bs) (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre' hal ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsRoCl, cliMemcpyBytesAtSpecPlaced, withVmPreserved,
        sessionMemcpyRegionROSpec, bytesAt_true] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, ⟨hpost.2.2.1.1, hpost.2.2.1.2, hpost.2.1⟩, hpost.2.2.2⟩
    · simp only [withVmPreserved, sessionMemcpyRegionROSpec,
        satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [withVmPreserved, sessionMemcpyRegionROSpec,
        satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [withVmPreserved, sessionMemcpyRegionROSpec,
        satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1

private def cliMemcpy1568SpecPlaced (ro : Bool) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     s0.readReg64 .x2 = 1568#64 ∧
     bs.length = 1568⌝ ∗
    memRegion dst 1568 ∗
    bytesAt ro src bs ∗
    stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
    (dst ↦ₛ bs) ∗
    bytesAt ro src bs ∗
    stackAt s0.sp extHookStack

private theorem cliMemcpy1568_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (ro : Bool) :
    subroutine_ok (lsProg_590 H) (lsρ memcpyName)
      (withLsRoCl lsmpl (cliMemcpy1568SpecPlaced ro)) := by
  refine subroutine_ok_mono (cliMemcpy_bytesAt_placed_ok hA hRO ro) ?_ ?_
  · intro ⟨dst, src, bs⟩ R s0 hpre
    obtain ⟨hcrl, hrest⟩ := extract_withLsRoCl hpre
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hrest
    simp only [cliMemcpy1568SpecPlaced, cliMemcpyBytesAtSpecPlaced]
    apply Entails.pure_left
    rintro ⟨hx0, hx1, hx2, hlen⟩
    rw [hx2, hlen]
    exact Entails.pure_right ⟨hx0, hx1, rfl, by decide⟩ (Entails.refl _)
  · intro ⟨dst, src, bs⟩ R s0 sf hpost
    simpa only [withLsRoCl, cliMemcpy1568SpecPlaced, cliMemcpyBytesAtSpecPlaced, sepConj_assoc]
      using hpost

set_option maxHeartbeats 1600000 in
theorem cliKemDeserialize_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec)) :
    subroutine_ok (lsProg_590 H) (blkPl_590).base
      (cliKemDeserializeSpecPlaced M A lim cliKemDeserStack) := by
  unfold cliKemDeserializeSpecPlaced withLsCodeRoLoaded cliKemDeserializeSpec
  simp only [stackAt_kemDeser_placed, sepExists_sepConj_right, sepExists_sepConj_left, sepConj_assoc]
  have h110 : IsLsBlockProg ((blkPC_110).rebase (blkPl_110).base H) 110 H := inferInstance
  have hkeylen : subroutine_ok (lsProg_590 H) (lsmpl.base 110)
      (withLsRoCl lsmpl kemPublicKeyLengthBudgetSpec) :=
    @ls_subroutine_ok_rocl_of_plain _ _ (lsProg_590 H) _ 590 110 H
      (instIsLsBlockProg_590 H) h110 (blkPl_110).base _
      (kemPublicKeyLength_placed_ok H) _ _ _ _ (by decide) (by decide) (by decide)
  have hshim := shim_lscro_of_cli (callerProg := lsProg_590 H) hA (stk := extHookStack) (by decide) (by decide)
  have halloc := allocNoOomExtern_lscro_of_cli (callerProg := lsProg_590 H) hA
  have hmc_any := cliMemcpy1568_placed_ok hA hRO
  clear hA hRO h110
  dsimp only [withLsCodeRoLoaded, lsProg_590, ↓reduceIte] at hshim halloc
  dsimp only [lsProg_590, ↓reduceIte] at hkeylen hmc_any ⊢
  wp_init x s0
  obtain ⟨⟨r, ro, p, bs⟩, st⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  have hfit_evs : FitsEvents M lim st (kemDeserializeEvents bs) := ‹_›
  have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  cases bs with
  | nil =>
    simp only [kemDeserializeEvents, M.stepEvents_nil, List.length_nil,
      kemPkDeserialize, kemDeserResAt, memRegion_24_split_8_16_placed r,
      sepExists_sepConj_left, sepConj_assoc] at *
    refine SepWP.exists_elim fun w0 => ?_
    wp_steps_sync_pool (s0.readReg64 .lr)
    wp_done
  | cons t rest =>
    have hlen_lt63 : (t :: rest).length < 2 ^ 63 := ‹_›
    have hlen_lt64 : rest.length + 1 < 2 ^ 64 := by simp at hlen_lt63; omega
    have hne0 : (BitVec.ofNat 64 (rest.length + 1) == 0#64) = false :=
      ofNat_beq_zero_false_placed (by omega) hlen_lt64
    by_cases ht : t = 0x08#8
    · subst ht
      simp only [kemDeserializeEvents, kemPkDeserialize, ne_eq, not_true_eq_false, ↓reduceIte] at *
      by_cases hrlen : rest.length = kemPkLen
      · have hx2_eq : BitVec.ofNat 64 (rest.length + 1) = 1569#64 := by rw [hrlen]
        rw [List.length_cons] at *
        try rw [hx2_eq] at *
        simp only [hrlen, not_true_eq_false, ↓reduceIte,
          memRegion_24_cells_placed r, sepExists_sepConj_left, sepConj_assoc] at hfit_evs ⊢
        refine SepWP.exists_elim fun w0 => SepWP.exists_elim fun w1 =>
          SepWP.exists_elim fun w2 => ?_
        have hrlay : RustLayoutOk kemPkLen 1 := ⟨⟨by decide, hpow1, by decide⟩, hal1⟩
        have hrlen1568 : rest.length = 1568 := hrlen
        rcases hfit_evs with ⟨⟨hwma, henf, hphys, hva⟩, -⟩
        have hmcall := hmc_any ro
        cases ro
        · simp only [bytesAt_false, ProofLib.pointsToBytes_cons,
            sepConj_assoc] at hmcall ⊢
          apply sepWP_seq_lscro (mid := lsmpl.base 110) hcrl0
          wp_steps_sync_pool (lsmpl.base 110)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl1, hro1⟩
          wp_apply using hkeylen
          refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
          apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) ‹_›
          wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hcrl2
          apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl2
          rcases hcrl2 with ⟨hcl2, hro2⟩
          wp_call hshim ()
          refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
          wp_steps_sync_pool (lsρ lsRustAllocSymCli)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hcrl3
          apply sepWP_seq_lscro (mid := lsρ memcpyName) hcrl3
          rcases hcrl3 with ⟨hcl3, hro3⟩
          wp_call halloc (kemPkLen, 1, st)
          have hoom : sf_2.readReg64 Reg.x0 ≠ 0#64 := by tauto
          have hoom_beq : (sf_2.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
          wp_steps_sync_pool (lsρ memcpyName)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl4, hro4⟩
          wp_apply using hmcall
          refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
          wp_steps_sync_pool (s0.readReg64 .lr)
          apply SepWP.fold (ok_post_entails_placed A r (sf_2.readReg64 Reg.x0) rest
            hrlen hoom) (by sep_focus)
          wp_done
        · simp only [bytesAt_true, ProofLib.pointsToBytesRO_cons,
            sepConj_assoc] at hmcall ⊢
          apply sepWP_seq_lscro (mid := lsmpl.base 110) hcrl0
          wp_steps_sync_pool (lsmpl.base 110)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl1, hro1⟩
          wp_apply using hkeylen
          refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
          apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) ‹_›
          wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hcrl2
          apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl2
          rcases hcrl2 with ⟨hcl2, hro2⟩
          wp_call hshim ()
          refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
          wp_steps_sync_pool (lsρ lsRustAllocSymCli)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hcrl3
          apply sepWP_seq_lscro (mid := lsρ memcpyName) hcrl3
          rcases hcrl3 with ⟨hcl3, hro3⟩
          wp_call halloc (kemPkLen, 1, st)
          have hoom : sf_2.readReg64 Reg.x0 ≠ 0#64 := by tauto
          have hoom_beq : (sf_2.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
          wp_steps_sync_pool (lsρ memcpyName)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl4, hro4⟩
          wp_apply using hmcall
          refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
          wp_steps_sync_pool (s0.readReg64 .lr)
          apply SepWP.fold (ok_post_entails_placed A r (sf_2.readReg64 Reg.x0) rest
            hrlen hoom) (by sep_focus)
          wp_done
      · have hne1569 : BitVec.ofNat 64 (rest.length + 1) ≠ 1569#64 :=
          ofNat_ne_1569_placed (by simp [kemPkLen] at hrlen; omega) hlen_lt64
        have hbeq1569 : (BitVec.ofNat 64 (rest.length + 1) == 1569#64) = false :=
          beq_false_of_ne hne1569
        rw [List.length_cons] at *
        simp only [hrlen, not_false_eq_true, ↓reduceIte, M.stepEvents_nil, kemDeserResAt,
          memRegion_24_split_badLen_placed r, sepExists_sepConj_left, sepConj_assoc] at *
        refine SepWP.exists_elim fun w1 => SepWP.exists_elim fun w0 => ?_
        cases ro
        · simp only [bytesAt_false, ProofLib.pointsToBytes_cons, sepConj_assoc]
          apply sepWP_seq_lscro (mid := lsmpl.base 110) hcrl0
          wp_steps_sync_pool (lsmpl.base 110)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl1, hro1⟩
          wp_apply using hkeylen
          refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
          wp_steps_sync_pool (s0.readReg64 .lr)
          wp_done
        · simp only [bytesAt_true, ProofLib.pointsToBytesRO_cons, sepConj_assoc]
          apply sepWP_seq_lscro (mid := lsmpl.base 110) hcrl0
          wp_steps_sync_pool (lsmpl.base 110)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl1, hro1⟩
          wp_apply using hkeylen
          refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
          wp_steps_sync_pool (s0.readReg64 .lr)
          wp_done
    · have hne32 := byte_zext32_ne8_placed ht
      have hne64 := byte_zext64_ne8_placed ht
      have hsub32 : t.zeroExtend 32 - 8#32 ≠ 0#32 := by bv_omega
      have hsub64 : t.zeroExtend 64 - 8#64 ≠ 0#64 := by bv_omega
      have hbeq_sub32 : (t.zeroExtend 32 - 8#32 == 0#32) = false := beq_false_of_ne hsub32
      have hbeq8_32 : (t.zeroExtend 32 == 8#32) = false := beq_false_of_ne hne32
      have hbeq8_64 : (t.zeroExtend 64 == 8#64) = false := beq_false_of_ne hne64
      rw [List.length_cons] at *
      simp only [kemDeserializeEvents, kemPkDeserialize, ne_eq, ht, not_false_eq_true, ↓reduceIte,
        M.stepEvents_nil, kemDeserResAt, memRegion_24_split_badType_placed r,
        sepExists_sepConj_left, sepConj_assoc] at *
      refine SepWP.exists_elim fun b1 => SepWP.exists_elim fun w0 => ?_
      cases ro
      · simp only [bytesAt_false, ProofLib.pointsToBytes_cons, sepConj_assoc]
        wp_steps_sync_pool (s0.readReg64 .lr)
        wp_done
      · simp only [bytesAt_true, ProofLib.pointsToBytesRO_cons, sepConj_assoc]
        wp_steps_sync_pool (s0.readReg64 .lr)
        wp_done

end KemDeserializePlacedBudgetHelpers

/-- `kem::Key<Public>::deserialize` (Block `590`) satisfies
`cliKemDeserializeSpecPlaced M A lim stk`. -/
theorem cliKemDeserialize_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (stk : Nat) (hstk : 48 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_590 H) (blkPl_590).base
      (cliKemDeserializeSpecPlaced M A lim stk) := by
  refine subroutine_ok_frame_weaken_kem_placed
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliKemDeserStack))
    (cliKemDeserialize_exact_placed_ok hA hRO) ?_ ?_
  · intro x s0
    dsimp only [cliKemDeserializeSpecPlaced, withLsCodeRoLoaded, cliKemDeserializeSpec]
    rw [stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro x s0 sf
    dsimp only [cliKemDeserializeSpecPlaced, withLsCodeRoLoaded, cliKemDeserializeSpec]
    rw [stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Cross-block transfer of `cliKemDeserialize_placed_ok` to any caller block `i < 619`
(e.g. `run` at Block `579`). -/
theorem cliKemDeserialize_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [hcaller : IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (stk : Nat) (hstk : 48 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_590).base
      (cliKemDeserializeSpecPlaced M A lim stk) := by
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_590 H) i 590 H
    hcaller (instIsLsBlockProg_590 H) (blkPl_590).base _
    (cliKemDeserialize_placed_ok hA hRO stk hstk hstk64)
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserializePlacedBudget
