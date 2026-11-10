/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGet
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Post-`last_resort.get` Envelopes & Exact-Capacity `concat`

Defines concrete-capacity post-`last_resort.get` event envelopes (`kpkAfterLrGetPreEvents`,
`KpkAfterLrGetBranchEnv`, `KpkAfterLrGetOkEnv`), exact-capacity `concat [local#3]` on Block `598`
(`kpkConcat2PosAtSpec`), and stack-restoration helpers for Block `578`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (
  SepWP.instantiate_post_exists doReserveStackX extHookStack finishGrowStackX memcpyName withStack
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded
)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (
  DirGhost KpkMarkAns KpkMarkPollGhost KyberGhost baseKeyEntry dirAt kpkMarkBoxAt kpkMarkOutAt le32
)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_598 blkPl_598 lsProg_598)
open CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers (
  Concat2PosCall baseKeyEntry_length kpkMarkRoBundlePlaced kpkMinStk kpkSubMax le32_length
  publicKey_serialize_length restore_kpkMarkStack savedCalleeSlots sepWPp_conseq subStack_split
  vecU8Tail
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk SeqEnv
  fitsEvents_append rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  PublicKeySerializeEnv publicKeySerializeEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (
  allocNoOomExtern_lscro_of_cli session_memcpy_region_lscro_of_cli shim_lscro_of_cli
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesBudget (
  KpkConcat2PosEnv kpkConcat2PosEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudget (
  kpk_call_total_raw_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudget (
  kpkErrCleanupEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudget (
  kpkMalformedEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoopPlacedBudget (
  KpkBcmpLoopEnv
)

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## 1. Concrete-Cap Post-`last_resort.get` Event Envelopes -/

/-- Deterministic pre-dispatch allocator events emitted on `gr = .ok seenBs`:
`<PublicKey>::serialize` (`alloc(33, 1)`), `concat` (`alloc(37, 1)`), and freeing `serPtr`
(`dealloc(33, 1)`). -/
def kpkAfterLrGetPreEvents : List AllocEvent :=
  publicKeySerializeEvents ++ rustAllocEvents 37 1 ++ rustDeallocEvents 33 1

/-- Concrete-cap branch envelope from `+468` after `used` (`cap = usedCap`) is built and `serPtr` is
freed:
- when `seenBs.length % 37 = 0`: `KpkBcmpLoopEnv PutEnv x usedCap seenCap fileCap seenBs`
  (covering both `seenBs = []` direct append and the `bcmp` chunk loop);
- when `seenBs.length % 37 ≠ 0`: `kpkMalformedEvents usedCap seenCap fileCap`. -/
def KpkAfterLrGetBranchEnv
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (x : KpkMarkPollGhost) (usedCap seenCap fileCap : BitVec 64)
    (seenBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  if seenBs.length % 37 = 0 then
    KpkBcmpLoopEnv PutEnv x usedCap seenCap fileCap seenBs evs
  else
    evs = kpkMalformedEvents usedCap seenCap fileCap

/-- Concrete-cap allocator event envelope for `kpk_after_lr_get_174_placed` on `gr = .ok seenBs`:
`kpkAfterLrGetPreEvents` followed by `KpkAfterLrGetBranchEnv PutEnv x 37#64 seenCap fileCap seenBs`. -/
def KpkAfterLrGetOkEnv
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (x : KpkMarkPollGhost) (seenCap fileCap : BitVec 64)
    (seenBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SeqEnv (· = kpkAfterLrGetPreEvents)
    (KpkAfterLrGetBranchEnv PutEnv x 37#64 seenCap fileCap seenBs) evs

theorem KpkAfterLrGetBranchEnv.of_malformed
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : KpkMarkPollGhost} {usedCap seenCap fileCap : BitVec 64} {seenBs : List (BitVec 8)}
    (hmod : seenBs.length % 37 ≠ 0) :
    KpkAfterLrGetBranchEnv PutEnv x usedCap seenCap fileCap seenBs
      (kpkMalformedEvents usedCap seenCap fileCap) := by
  simp only [KpkAfterLrGetBranchEnv, hmod, ↓reduceIte]

theorem KpkAfterLrGetBranchEnv.of_loop
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : KpkMarkPollGhost} {usedCap seenCap fileCap : BitVec 64} {seenBs : List (BitVec 8)}
    {evs : List AllocEvent}
    (hmod : seenBs.length % 37 = 0)
    (hloop : KpkBcmpLoopEnv PutEnv x usedCap seenCap fileCap seenBs evs) :
    KpkAfterLrGetBranchEnv PutEnv x usedCap seenCap fileCap seenBs evs := by
  simpa only [KpkAfterLrGetBranchEnv, hmod, ↓reduceIte] using hloop

theorem KpkAfterLrGetOkEnv.of_branch
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : KpkMarkPollGhost} {seenCap fileCap : BitVec 64} {seenBs : List (BitVec 8)}
    {evs_br : List AllocEvent}
    (hbr : KpkAfterLrGetBranchEnv PutEnv x 37#64 seenCap fileCap seenBs evs_br) :
    KpkAfterLrGetOkEnv PutEnv x seenCap fileCap seenBs
      (kpkAfterLrGetPreEvents ++ evs_br) :=
  SeqEnv.append rfl hbr

theorem KpkAfterLrGetOkEnv.of_malformed
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : KpkMarkPollGhost} {seenCap fileCap : BitVec 64} {seenBs : List (BitVec 8)}
    (hmod : seenBs.length % 37 ≠ 0) :
    KpkAfterLrGetOkEnv PutEnv x seenCap fileCap seenBs
      (kpkAfterLrGetPreEvents ++ kpkMalformedEvents 37#64 seenCap fileCap) :=
  KpkAfterLrGetOkEnv.of_branch (KpkAfterLrGetBranchEnv.of_malformed hmod)

theorem KpkAfterLrGetOkEnv.of_loop
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : KpkMarkPollGhost} {seenCap fileCap : BitVec 64} {seenBs : List (BitVec 8)}
    {evs_loop : List AllocEvent}
    (hmod : seenBs.length % 37 = 0)
    (hloop : KpkBcmpLoopEnv PutEnv x 37#64 seenCap fileCap seenBs evs_loop) :
    KpkAfterLrGetOkEnv PutEnv x seenCap fileCap seenBs
      (kpkAfterLrGetPreEvents ++ evs_loop) :=
  KpkAfterLrGetOkEnv.of_branch (KpkAfterLrGetBranchEnv.of_loop hmod hloop)

theorem KpkAfterLrGetOkEnv.fits_pre {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : KpkMarkPollGhost} {seenCap fileCap : BitVec 64} {seenBs : List (BitVec 8)}
    (hfit : FitsEnv M lim st (KpkAfterLrGetOkEnv PutEnv x seenCap fileCap seenBs)) :
    FitsEvents M lim st kpkAfterLrGetPreEvents :=
  hfit.seq_left _ rfl

theorem KpkAfterLrGetOkEnv.fits_ser {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : KpkMarkPollGhost} {seenCap fileCap : BitVec 64} {seenBs : List (BitVec 8)}
    (hfit : FitsEnv M lim st (KpkAfterLrGetOkEnv PutEnv x seenCap fileCap seenBs)) :
    FitsEnv M lim st PublicKeySerializeEnv := by
  have hpre := KpkAfterLrGetOkEnv.fits_pre hfit
  rw [kpkAfterLrGetPreEvents, List.append_assoc] at hpre
  have hser := ((fitsEvents_append M lim publicKeySerializeEvents
    (rustAllocEvents 37 1 ++ rustDeallocEvents 33 1) st).mp hpre).1
  intro evs hevs
  subst hevs
  exact hser

theorem KpkAfterLrGetOkEnv.fits_cat37 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : KpkMarkPollGhost} {seenCap fileCap : BitVec 64} {seenBs : List (BitVec 8)}
    (hfit : FitsEnv M lim st (KpkAfterLrGetOkEnv PutEnv x seenCap fileCap seenBs)) :
    FitsEvents M lim (M.stepEvents publicKeySerializeEvents st) (rustAllocEvents 37 1) := by
  have hpre := KpkAfterLrGetOkEnv.fits_pre hfit
  rw [kpkAfterLrGetPreEvents, List.append_assoc] at hpre
  have hrest := ((fitsEvents_append M lim publicKeySerializeEvents
    (rustAllocEvents 37 1 ++ rustDeallocEvents 33 1) st).mp hpre).2
  exact ((fitsEvents_append M lim (rustAllocEvents 37 1) (rustDeallocEvents 33 1)
    (M.stepEvents publicKeySerializeEvents st)).mp hrest).1

theorem KpkAfterLrGetOkEnv.fits_branch {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : KpkMarkPollGhost} {seenCap fileCap : BitVec 64} {seenBs : List (BitVec 8)}
    (hfit : FitsEnv M lim st (KpkAfterLrGetOkEnv PutEnv x seenCap fileCap seenBs)) :
    FitsEnv M lim (M.stepEvents kpkAfterLrGetPreEvents st)
      (KpkAfterLrGetBranchEnv PutEnv x 37#64 seenCap fileCap seenBs) :=
  hfit.seq_right (rfl : kpkAfterLrGetPreEvents = _)

theorem KpkAfterLrGetOkEnv.fits_malformed {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : KpkMarkPollGhost} {seenCap fileCap : BitVec 64} {seenBs : List (BitVec 8)}
    (hfit : FitsEnv M lim st (KpkAfterLrGetOkEnv PutEnv x seenCap fileCap seenBs))
    (hmod : seenBs.length % 37 ≠ 0) :
    FitsEvents M lim (M.stepEvents kpkAfterLrGetPreEvents st) (rustAllocEvents 14 1) :=
  ((fitsEvents_append M lim (rustAllocEvents 14 1)
      (kpkErrCleanupEvents 37#64 seenCap fileCap)
      (M.stepEvents kpkAfterLrGetPreEvents st)).mp
    (KpkAfterLrGetOkEnv.fits_branch hfit _ (KpkAfterLrGetBranchEnv.of_malformed hmod))).1

theorem KpkAfterLrGetOkEnv.fits_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : KpkMarkPollGhost} {seenCap fileCap : BitVec 64} {seenBs : List (BitVec 8)}
    (hfit : FitsEnv M lim st (KpkAfterLrGetOkEnv PutEnv x seenCap fileCap seenBs))
    (hmod : seenBs.length % 37 = 0) :
    FitsEnv M lim (M.stepEvents kpkAfterLrGetPreEvents st)
      (KpkBcmpLoopEnv PutEnv x 37#64 seenCap fileCap seenBs) := by
  intro evs hevs
  exact KpkAfterLrGetOkEnv.fits_branch hfit evs (KpkAfterLrGetBranchEnv.of_loop hmod hevs)

/-! ## 2. Exact-Capacity `concat [local#3]` (Block `598`) & Stack Restoration Helpers -/

private abbrev cliConcatStackP : Nat := 96 + extHookStack

private theorem stackAt_split_ge_p (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hlt : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  have h := ProofLib.stackAt_split_bottom sp n (m - n) (by omega)
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using h

private theorem subroutine_ok_frame_weaken_noPanic_p {α : Type} {prog : Program}
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

private theorem memRegion_24_cells_p (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_cliConcat_p (sp : BitVec 64) :
    stackAt sp cliConcatStackP =
      stackAt (sp - 96#64) extHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 16384 12 (by decide)
  have hsum : 16384 + 8 * 12 = cliConcatStackP := by decide
  rw [hsum] at h1
  change stackAt sp cliConcatStackP =
    stackAt (sp - 96#64) extHookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]

private theorem ofNat_getLsbD_63_false_p {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow h

private theorem ofNat_getElem_63_false_p {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false :=
  ofNat_getLsbD_63_false_p h

private theorem ofNat_beq_zero_false_p {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

private theorem ofNat_ult_of_le_p {a b : Nat} (hle : a ≤ b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = false := by
  have ha : a < 2 ^ 64 := by omega
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    decide_eq_false_iff_not]
  omega

/-- Exact-capacity `concat [local#3]` spec preserving `cap = BitVec.ofNat 64 (bs0.length + bs1.length)`
without erasing it into `vecU8` or requiring `CliPanicHooksPlaced`. -/
def kpkConcat2PosAtSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (Concat2PosCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 2#64 ∧
      0 < x.bs0.length ∧ 0 < x.bs1.length ∧ x.bs0.length + x.bs1.length < 2 ^ 63 ∧
      FitsEnv M lim st (KpkConcat2PosEnv x)⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗
      ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      (x.p0 ↦ₛ x.bs0) ∗ (x.p1 ↦ₛ x.bs1) ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜sf.trace = s0.trace ∧ p' ≠ 0#64⌝ ∗
        (x.outVec ↦₆₄ BitVec.ofNat 64 (x.bs0.length + x.bs1.length)) ∗
        ((x.outVec + 8#64) ↦₆₄ p') ∗
        ((x.outVec + 16#64) ↦₆₄ BitVec.ofNat 64 (x.bs0.length + x.bs1.length)) ∗
        A.live p' (x.bs0.length + x.bs1.length) 1 ∗
        (p' ↦ₛ (x.bs0 ++ x.bs1)) ∗
        (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
        ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
        (x.p0 ↦ₛ x.bs0) ∗ (x.p1 ↦ₛ x.bs1) ∗
        A.pool lim (M.stepEvents (kpkConcat2PosEvents x) st) sf ∗ stackAt s0.sp stk

set_option maxHeartbeats 1600000 in
private theorem kpkConcat2_pos_at_exact_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_598 H) (blkPl_598).base
      (withLsCodeRoLoaded lsmpl (kpkConcat2PosAtSpec A lim cliConcatStackP)) := by
  have hshim := shim_lscro_of_cli (callerProg := lsProg_598 H) hA (stk := extHookStack) (by decide) (by decide)
  have halloc := allocNoOomExtern_lscro_of_cli (callerProg := lsProg_598 H) hA
  have hmc := session_memcpy_region_lscro_of_cli (callerProg := lsProg_598 H) hA (stk := extHookStack) (by decide) (by decide)
  clear hA
  dsimp only [withLsCodeRoLoaded, withStack, sessionShimBudgetSpec, lsProg_598] at hshim
  dsimp only [withLsCodeRoLoaded, lsProg_598] at halloc
  dsimp only [withLsCodeRoLoaded, withStack, sessionMemcpyRegionBudgetSpec, lsProg_598] at hmc
  unfold withLsCodeRoLoaded kpkConcat2PosAtSpec
  simp only [memRegion_24_cells_p, stackAt_cliConcat_p, sepExists_sepConj_left, sepExists_sepConj_right]
  change subroutine_ok ((blkPC_598).rebase (blkPl_598).base H) (blkPl_598).base _
  wp_init x s0
  obtain ⟨⟨outVec, slicesA, p0, bs0, p1, bs1⟩, st⟩ := x
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  dsimp only at *
  have hpos0 : 0 < bs0.length := ‹_›
  have hpos1 : 0 < bs1.length := ‹_›
  have hmax : bs0.length + bs1.length < 2 ^ 63 := ‹_›
  have hfit_env : FitsEnv M lim st (KpkConcat2PosEnv ⟨outVec, slicesA, p0, bs0, p1, bs1⟩) := ‹_›
  have hfit_evs : FitsEvents M lim st (rustAllocEvents (bs0.length + bs1.length) 1) :=
    hfit_env _ rfl
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have h0_lt64 : bs0.length < 2 ^ 64 := by omega
  have h1_lt64 : bs1.length < 2 ^ 64 := by omega
  have h0_le64 : bs0.length ≤ 2 ^ 64 := by omega
  have h1_le64 : bs1.length ≤ 2 ^ 64 := by omega
  have hadd_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd01_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by
    rw [← BitVec.ofNat_add]
  have hsub_bv : BitVec.ofNat 64 (bs0.length + bs1.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs1.length := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
      omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hcs1 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le_p (by omega) (by omega)
  have hbit63 : (BitVec.ofNat 64 (bs0.length + bs1.length)).getLsbD 63 = false :=
    ofNat_getLsbD_63_false_p (by omega)
  have helem63 : (BitVec.ofNat 64 (bs0.length + bs1.length))[63] = false :=
    ofNat_getElem_63_false_p (by omega)
  have htot_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length)).toNat = bs0.length + bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0_toNat : (BitVec.ofNat 64 bs0.length).toNat = bs0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64]
  have h1_toNat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
  have hhi0 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le_p (by omega) (by omega)
  have hhi1 : (BitVec.ofNat 64 bs1.length).ult (BitVec.ofNat 64 bs1.length) = false :=
    ProofLib.bitvec_ult_self _
  have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length) == 0#64) = false :=
    ofNat_beq_zero_false_p (by omega) (by omega)
  have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false :=
    ofNat_beq_zero_false_p hpos0 h0_lt64
  have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false :=
    ofNat_beq_zero_false_p hpos1 h1_lt64
  have hrlay : RustLayoutOk (bs0.length + bs1.length) 1 := ⟨⟨by omega, hpow1, by omega⟩, hal1⟩
  apply sepWP_seq_lscro hcrl0 (mid := lsρ lsRustNoAllocShimSymCli)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl1
  apply sepWP_seq_lscro hcrl1 (mid := lsρ lsRustAllocSymCli)
  rcases hcrl1 with ⟨hcl1, hro1⟩
  wp_call hshim ()
  refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl2
  apply sepWP_seq_lscro hcrl2 (mid := lsρ memcpyName)
  rcases hcrl2 with ⟨hcl2, hro2⟩
  wp_call halloc (bs0.length + bs1.length, 1, st)
  have hoom : sf_1.readReg64 Reg.x0 ≠ 0#64 := by tauto
  have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
  rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs0.length bs1.length (by omega)]
  wp_steps_sync_pool (lsρ memcpyName)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl3
  apply sepWP_seq_lscro hcrl3 (mid := (blkPl_598).base + 172#64)
  rcases hcrl3 with ⟨hcl3, hro3⟩
  wp_apply using hmc
  refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl3'
  apply sepWP_seq_lscro hcrl3' (mid := lsρ memcpyName)
  wp_steps_sync_pool (lsρ memcpyName)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rintro ⟨hcl4, hro4⟩
  wp_apply using hmc
  refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 Reg.x0) bs0 bs1).symm)
    (by sep_focus)
  apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  dsimp only [kpkConcat2PosEvents, RustCliAllocBudget.repAlloc_live]
  wp_done

theorem kpkConcat2_pos_at_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_598 H) (lsmpl.base 598)
      (withLsCodeRoLoaded lsmpl (kpkConcat2PosAtSpec A lim stk)) := by
  change subroutine_ok (lsProg_598 H) (blkPl_598).base _
  refine subroutine_ok_frame_weaken_noPanic_p
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliConcatStackP))
    (kpkConcat2_pos_at_exact_placed_ok hA) ?_ ?_
  · intro x s0
    dsimp only [withLsCodeRoLoaded, kpkConcat2PosAtSpec, cliConcatStackP]
    rw [stackAt_split_ge_p s0.sp hstk hstk64]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro x s0 sf
    dsimp only [withLsCodeRoLoaded, kpkConcat2PosAtSpec, cliConcatStackP]
    simp only [sepExists_sepConj_left]
    refine Entails.of_eq (congrArg sepExists (funext fun p' => ?_))
    rw [stackAt_split_ge_p s0.sp hstk hstk64]
    sep_ac_rfl

private theorem entails_withLsCodeRoLoaded_pre_p [LibsignalPlacement]
    {s : State} {P Q F : SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : P ⊢ Q ∗ F) :
    P ⊢ (Q ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ F := by
  refine Entails.trans h ?_
  rw [sepConj_assoc]
  exact sepConj_mono_right (Entails.pure_right hcrl (Entails.refl F))

theorem kpk_call_concat2_at_placed [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (withLsCodeRoLoaded lsmpl (kpkConcat2PosAtSpec A lim stk)))
    (xg : Concat2PosCall) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.outVec) (hx1 : s.readReg64 .x1 = xg.slicesA)
    (hx2 : s.readReg64 .x2 = 2#64)
    (hpos0 : 0 < xg.bs0.length) (hpos1 : 0 < xg.bs1.length)
    (hmax : xg.bs0.length + xg.bs1.length < 2 ^ 63)
    (hfit : FitsEnv M lim st (KpkConcat2PosEnv xg))
    (hpre : P ⊢ (memRegion xg.outVec 24 ∗
      (xg.slicesA ↦₆₄ xg.p0) ∗ ((xg.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 xg.bs0.length) ∗
      ((xg.slicesA + 16#64) ↦₆₄ xg.p1) ∗ ((xg.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 xg.bs1.length) ∗
      (xg.p0 ↦ₛ xg.bs0) ∗ (xg.p1 ↦ₛ xg.bs1) ∗ A.pool lim st s ∗ stackAt s.sp stk) ∗ F)
    (hnext : ∀ (sm : State) (usedPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace → usedPtr ≠ 0#64 →
      SepWPp prog ret sm
        (((xg.outVec ↦₆₄ BitVec.ofNat 64 (xg.bs0.length + xg.bs1.length)) ∗
          ((xg.outVec + 8#64) ↦₆₄ usedPtr) ∗
          ((xg.outVec + 16#64) ↦₆₄ BitVec.ofNat 64 (xg.bs0.length + xg.bs1.length)) ∗
          A.live usedPtr (xg.bs0.length + xg.bs1.length) 1 ∗
          (usedPtr ↦ₛ (xg.bs0 ++ xg.bs1)) ∗
          (xg.slicesA ↦₆₄ xg.p0) ∗ ((xg.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 xg.bs0.length) ∗
          ((xg.slicesA + 16#64) ↦₆₄ xg.p1) ∗ ((xg.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 xg.bs1.length) ∗
          (xg.p0 ↦ₛ xg.bs0) ∗ (xg.p1 ↦ₛ xg.bs1) ∗
          A.pool lim (M.stepEvents (kpkConcat2PosEvents xg) st) sm ∗ stackAt s.sp stk) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_total_raw_placed hcall (xg, st) F hpc hrun hsp_align hlr hcrl ?_ ?_ ?_ ?_ ?_
  · refine entails_withLsCodeRoLoaded_pre_p hcrl (Entails.trans hpre ?_)
    simp only [kpkConcat2PosAtSpec, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hpos0, hpos1, hmax, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [kpkConcat2PosAtSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    simp only [kpkConcat2PosAtSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [kpkConcat2PosAtSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [kpkConcat2PosAtSpec, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun usedPtr => SepWPp.pure_elim fun ⟨htrm, hptr⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm usedPtr hpcm hrunm hspm hcsm hcrlm htrm hptr)

theorem concat_out_37_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (sp usedPtr : BitVec 64) (signedId : BitVec 32) (pk : PublicKey) :
    ((sp - 0x80#64) ↦₆₄ BitVec.ofNat 64 ((le32 signedId).length + pk.serialize.length)) ∗
      ((sp - 0x80#64 + 8#64) ↦₆₄ usedPtr) ∗
      ((sp - 0x80#64 + 16#64) ↦₆₄ BitVec.ofNat 64 ((le32 signedId).length + pk.serialize.length)) ∗
      A.live usedPtr ((le32 signedId).length + pk.serialize.length) 1 ∗
      (usedPtr ↦ₛ (le32 signedId ++ pk.serialize)) =
    ((sp - 0x80#64) ↦₆₄ 37#64) ∗
      ((sp - 0x78#64) ↦₆₄ usedPtr) ∗
      ((sp - 0x70#64) ↦₆₄ 37#64) ∗
      bytesAt false usedPtr (baseKeyEntry signedId pk) ∗
      vecU8Tail A.repAlloc 37#64 usedPtr (baseKeyEntry signedId pk) := by
  have hl0 : (le32 signedId).length = 4 := le32_length signedId
  have hl1 : pk.serialize.length = 33 := publicKey_serialize_length pk
  have he8 : sp - 0x80#64 + 8#64 = sp - 0x78#64 := by bv_omega
  have he16 : sp - 0x80#64 + 16#64 = sp - 0x70#64 := by bv_omega
  have he37 : BitVec.ofNat 64 (4 + 33) = 37#64 := rfl
  have happ : le32 signedId ++ pk.serialize = baseKeyEntry signedId pk := rfl
  have hlen37 : (baseKeyEntry signedId pk).length = 37 := baseKeyEntry_length signedId pk
  have hne : (37#64 : BitVec 64) ≠ 0#64 := by decide
  have hnat : (37#64 : BitVec 64).toNat = 37 := rfl
  rw [hl0, hl1, he8, he16, he37, happ]
  unfold bytesAt vecU8Tail
  simp only [Bool.false_eq_true, hne, ↓reduceIte, hnat, hlen37, Nat.sub_self,
    memRegion_zero, sepConj_emp, RustCliAllocBudget.repAlloc_live]
  sep_ac_rfl

theorem kpkMark_core_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {decStk getStk putStk stk : Nat}
    (hstk : kpkMinStk decStk getStk putStk ≤ stk) (hhi_stk : stk ≤ 2 ^ 64)
    (x : KpkMarkPollGhost) (st_f : M.σ) (s0 sf : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f0 f1 f2 f3 : BitVec 64) (tmp32 : BitVec 32)
    (res : KpkMarkAns × KyberGhost) :
    (kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
      (kpkMarkOutAt A.repAlloc x.out res.1 ∗
        dirAt A.repAlloc x.self res.2.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) res.2.lastResort ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        A.pool lim st_f sf ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xf0#64) extHookStack ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          memRegion (s0.sp - 0x80#64) 24 ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          savedCalleeSlots s0))) ⊢
      kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        (kpkMarkOutAt A.repAlloc x.out res.1 ∗
          dirAt A.repAlloc x.self res.2.oneTime ∗
          dirAt A.repAlloc (x.self + 0x28#64) res.2.lastResort ∗
          kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
          A.pool lim st_f sf ∗
          stackAt s0.sp stk) :=
  sepConj_mono_right <|
    sepConj_mono_right <| sepConj_mono_right <| sepConj_mono_right <|
      sepConj_mono_right <| sepConj_mono_right <| sepConj_mono_right <|
        restore_kpkMarkStack s0 hstk hhi_stk f0 f1 f2 f3 tmp32

theorem kpkMark_core_sub_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {decStk getStk putStk stk : Nat}
    (hstk : kpkMinStk decStk getStk putStk ≤ stk) (hhi_stk : stk ≤ 2 ^ 64)
    (x : KpkMarkPollGhost) (st_f : M.σ) (s0 sf : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f2 f3 : BitVec 64) (tmp32 : BitVec 32)
    (res : KpkMarkAns × KyberGhost) :
    (kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
      (kpkMarkOutAt A.repAlloc x.out res.1 ∗
        dirAt A.repAlloc x.self res.2.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) res.2.lastResort ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        A.pool lim st_f sf ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          memRegion (s0.sp - 0xe8#64) 8 ∗
          memRegion (s0.sp - 0xe0#64) 8 ∗
          ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          memRegion (s0.sp - 0x80#64) 24 ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          savedCalleeSlots s0))) ⊢
      kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        (kpkMarkOutAt A.repAlloc x.out res.1 ∗
          dirAt A.repAlloc x.self res.2.oneTime ∗
          dirAt A.repAlloc (x.self + 0x28#64) res.2.lastResort ∗
          kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
          A.pool lim st_f sf ∗
          stackAt s0.sp stk) := by
  have hmin : kpkMinStk decStk getStk putStk ≤ 2 ^ 64 := by omega
  have hext : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  rw [subStack_split s0.sp hext hmin,
      ProofLib.memRegion_eight (s0.sp - 0xe8#64),
      ProofLib.memRegion_eight (s0.sp - 0xe0#64)]
  kpk_sep_norm
  refine Entails.sepExists_elim fun f0 => Entails.sepExists_elim fun f1 => ?_
  refine Entails.trans (Entails.of_eq ?_)
    (kpkMark_core_ext_placed hstk hhi_stk x st_f s0 sf wDot wR0 wR7 wM0 wM6 f0 f1 f2 f3 tmp32 res)
  sep_ac_rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux
