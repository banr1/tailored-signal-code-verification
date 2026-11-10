/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedHalt -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedDF -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEReds -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProg -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Prog -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Prog -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedCost
import Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest

/-!
# Concrete Clamped Per-Session Reduction Families

Instantiates the clamped paper-semantics family `v1SessionRedsPaperClamped` and the tracker-halted
family `v1SessionRedsHalted` with unconditional `SessionCostedReductionFamilyBounded` proofs, and
proves `hiddenSaltBoundV1` invariance under epoch-cap clamping.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SessionCostedHaltInst

noncomputable section

open scoped ENNReal BigOperators

open _root_.CryptoGames.CKA (DHFun)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.SM (Adversary admissibleLastLeakGuesses)
open _root_.CryptoGames.SM.Construction (healEpoch)
open _root_.CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem Bytes)
open CryptoVerification.E2E
  (SpkCostedReds spkCostedBounds spkSwapHybridCount
   SessionCostedReductions sessionCostedReductionsBounded
   SessionCostedReductionFamily SessionCostedReductionFamilyBounded
   hiddenSaltBoundV1 v1SessionReds v1SessionRedsPaper v1SessionRedsPaper_bounded
   v1SessionReds_fig8 v1SessionReds_fs v1SessionRedsPaper_fig8 v1SessionRedsPaper_fs)
open Computational.Proofs.SessionCostedHalt
  (qepClamp qepClamp_le_add clampSessionCostedReductions
   clampSessionCostedReductions_B_cka_of_lt clampSessionCostedReductions_B_prng_of_lt
   clampSessionCostedReductions_B_fs_of_lt clampSessionCostedReductionFamily
   clampSessionCostedReductionFamily_of_le clampSessionCostedReductionFamily_bounded
   clampSessionCostedReductionFamily_fs clampSessionCostedReductionFamily_qepClamp
   mkSpkCostedRedsHalted mkSpkCostedRedsHalted_bounds
   mkSpkCostedRedsHalted_spkLeakRed mkSpkCostedRedsHalted_spkLeakRedU
   mkSpkCostedRedsHalted_hop2PrgRedK_of_lt mkSpkCostedRedsHalted_hop2PrfRedK_of_lt)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProg
  (spkLeakRedRInProgHalted spkLeakRedRInProgHalted_gRedBounded_tight)
open Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg
  (spkLeakRedU spkLeakRedU_totalCost spkLeakRedU_size_le spkLeakRedU_totalQueries)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
  (atomicPureOps_sizeHonest atomicBaseSamplers_sizeHonest)
open _root_.ReductionDsl (reductionSizeBudget)
open CryptoVerification.LibsignalSession (GRedBounded)
open CryptoVerification.E2E (spkLeakRedUBudget)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg
  (spkHop2PrgProgHalted spkHop2PrgProgHalted_gRedBounded_tight
   spkHop2PrfProgHalted spkHop2PrfProgHalted_gRedBounded_tight)
open Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Prog
  (epoch0DistinguisherProgHalted epoch0DistinguisherProgHalted_gRedBounded_succ)
open Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Prog
  (uniformStartRedHalted uniformStartRedHalted_gRedBounded_succ)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted
  (simFig8RedProgHalted simFig8RedProgHalted_gRedBounded)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase
  (simDeliverForgeRedProgHalted)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedCost
  (simDeliverForgeRedProgHalted_gRedBounded)

theorem hiddenSaltBoundV1_congr
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idA idB : IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (R₁ R₂ : SessionCostedReductions Pt ℓ Z K idA idB Dh encPt encT decT lam)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hfs : R₁.fs = R₂.fs)
    (hsimDF : R₁.simDeliverForge = R₂.simDeliverForge)
    (hchallDF : R₁.challSimDF = R₂.challSimDF)
    (hbCka : ∀ {t : ℕ}, t < (qep + 1) + 2 → ∀ tL, R₁.B_cka tL t = R₂.B_cka tL t)
    (hbPrng : ∀ {t : ℕ}, t < (qep + 1) + 2 → ∀ tL, R₁.B_prng tL t = R₂.B_prng tL t)
    (hbFs : ∀ {t : ℕ}, t < (qep + 1) + 2 → ∀ j tL, R₁.B_fs j tL t = R₂.B_fs j tL t) :
    hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT idA idB lam qep q δ R₁ A =
      hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT idA idB lam qep q δ R₂ A := by
  unfold hiddenSaltBoundV1
  refine congrArg (fun x => x + _ + _) (Finset.sum_congr rfl fun t ht => ?_)
  have hlt : t < (qep + 1) + 2 := Finset.mem_range.mp ht
  simp only [hfs, hsimDF, hchallDF, fun tL => hbCka hlt tL, fun tL => hbPrng hlt tL,
    fun j tL => hbFs hlt j tL]

theorem hiddenSaltBoundV1_clampSessionCostedReductions_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idA idB : IdentityKey) (lam : Pt)
    {qep qep_c : ℕ} (hqep : qep ≤ qep_c) (q : ℕ) (δ : ℝ≥0∞)
    (R : SessionCostedReductions Pt ℓ Z K idA idB Dh encPt encT decT lam)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT idA idB lam qep q δ
        (clampSessionCostedReductions qep_c R) A =
      hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT idA idB lam qep q δ R A :=
  hiddenSaltBoundV1_congr Z K ℓ Dh encPt encT decT idA idB lam qep q δ _ R A rfl rfl rfl
    (fun {_} _ tL => clampSessionCostedReductions_B_cka_of_lt qep_c R (by omega) tL)
    (fun {_} _ tL => clampSessionCostedReductions_B_prng_of_lt qep_c R (by omega) tL)
    (fun {_} _ j tL => clampSessionCostedReductions_B_fs_of_lt qep_c R (by omega) j tL)

@[expose] def v1SessionRedsPaperClamped {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) : SessionCostedReductionFamily Pt ℓ :=
  clampSessionCostedReductionFamily ℓ (v1SessionRedsPaper ℓ)

theorem v1SessionRedsPaperClamped_bounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) : SessionCostedReductionFamilyBounded ℓ (v1SessionRedsPaperClamped (Pt := Pt) ℓ) :=
  clampSessionCostedReductionFamily_bounded ℓ (v1SessionRedsPaper ℓ)
    (fun C K idA idB Dh encPt encT decT lam qep q hqep =>
      v1SessionRedsPaper_bounded ℓ C K idA idB Dh encPt encT decT lam qep q (by omega))

@[simp] theorem v1SessionRedsPaperClamped_of_le
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    {qep q : ℕ} (hqep : qep ≤ q + 4) :
    v1SessionRedsPaperClamped ℓ C K idA idB Dh encPt encT decT lam qep q =
      v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q :=
  clampSessionCostedReductionFamily_of_le ℓ (v1SessionRedsPaper ℓ)
    C K idA idB Dh encPt encT decT lam hqep

@[simp] theorem v1SessionRedsPaperClamped_qepClamp
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    v1SessionRedsPaperClamped ℓ C K idA idB Dh encPt encT decT lam (qepClamp qep q) q =
      v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam (qepClamp qep q) q :=
  clampSessionCostedReductionFamily_qepClamp ℓ (v1SessionRedsPaper ℓ)
    C K idA idB Dh encPt encT decT lam qep q

@[simp] theorem v1SessionRedsPaperClamped_fs
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaperClamped ℓ C K idA idB Dh encPt encT decT lam qep q).fs =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fs := by
  simp [v1SessionRedsPaperClamped]

@[expose] def spkCostedRedsHaltedInst {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ) :
    SpkCostedReds Pt ℓ C K Dh encPt encT decT lam :=
  mkSpkCostedRedsHalted
    (spkLeakRedRInProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
    (spkLeakRedU Pt ℓ)
    (fun k => spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
    (fun k => spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)

section SpkHaltedInstProjections

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)

@[simp] theorem spkCostedRedsHaltedInst_spkLeakRed :
    (spkCostedRedsHaltedInst ℓ C K idA idB Dh encPt encT decT lam q qep).spkLeakRed =
      spkLeakRedRInProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep := rfl

@[simp] theorem spkCostedRedsHaltedInst_spkLeakRedU :
    (spkCostedRedsHaltedInst ℓ C K idA idB Dh encPt encT decT lam q qep).spkLeakRedU =
      spkLeakRedU Pt ℓ := rfl

@[simp] theorem spkCostedRedsHaltedInst_hop2PrgRedK_of_lt {k : ℕ}
    (hk : k < spkSwapHybridCount) :
    (spkCostedRedsHaltedInst ℓ C K idA idB Dh encPt encT decT lam q qep).hop2PrgRedK k =
      spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k :=
  mkSpkCostedRedsHalted_hop2PrgRedK_of_lt _ _ _ _ hk

@[simp] theorem spkCostedRedsHaltedInst_hop2PrfRedK_of_lt {k : ℕ}
    (hk : k < spkSwapHybridCount) :
    (spkCostedRedsHaltedInst ℓ C K idA idB Dh encPt encT decT lam q qep).hop2PrfRedK k =
      spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k :=
  mkSpkCostedRedsHalted_hop2PrfRedK_of_lt _ _ _ _ hk

end SpkHaltedInstProjections

private theorem spkLeakRedU_gRedBounded_tight (Pt : Type) (ℓ q : ℕ) :
    GRedBounded (spkLeakRedU Pt ℓ) (fun _ => 1) (fun _ => 0)
      (q + 1) (q + 1) (spkLeakRedUBudget q) := by
  refine gRedBounded_of_bounds (spkLeakRedU Pt ℓ) (fun _ => 1) (fun _ => 0)
    (q + 1) (q + 1) (spkLeakRedUBudget q)
    ?_ ((spkLeakRedU_size_le Pt ℓ).trans (Nat.le_add_right _ _)) ?_
    (atomicPureOps_sizeHonest ℓ Pt) (atomicBaseSamplers_sizeHonest ℓ Pt)
  · rw [spkLeakRedU_totalCost]
    unfold spkLeakRedUBudget
    omega
  · rw [spkLeakRedU_totalQueries]

theorem spkCostedRedsHaltedInst_bounds {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) {q qep : ℕ}
    (hqep : qep ≤ q + 10) :
    spkCostedBounds q qep (spkCostedRedsHaltedInst ℓ C K idA idB Dh encPt encT decT lam q qep) :=
  mkSpkCostedRedsHalted_bounds
    (spkLeakRedRInProgHalted_gRedBounded_tight C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (spkLeakRedU_gRedBounded_tight Pt ℓ q)
    (fun k _ => spkHop2PrgProgHalted_gRedBounded_tight C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)
    (fun k _ => spkHop2PrfProgHalted_gRedBounded_tight C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)

@[expose] def v1SessionRedsHaltedRaw {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) : SessionCostedReductionFamily Pt ℓ :=
  fun C K idA idB Dh encPt encT decT lam qep q =>
    { v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q with
      spk := spkCostedRedsHaltedInst ℓ C K idA idB Dh encPt encT decT lam q qep
      simFig8 := simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
      simDeliverForge :=
        simDeliverForgeRedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
      epoch0Red :=
        epoch0DistinguisherProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep
      uniformStartRed :=
        uniformStartRedHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep }

section HaltedRawProjections

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)

@[simp] theorem v1SessionRedsHaltedRaw_spk :
    (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).spk =
      spkCostedRedsHaltedInst ℓ C K idA idB Dh encPt encT decT lam q qep := rfl

@[simp] theorem v1SessionRedsHaltedRaw_fig8 :
    (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).fig8 =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fig8 := rfl

@[simp] theorem v1SessionRedsHaltedRaw_fs :
    (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).fs =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fs := rfl

@[simp] theorem v1SessionRedsHaltedRaw_simFig8 :
    (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).simFig8 =
      simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q := rfl

@[simp] theorem v1SessionRedsHaltedRaw_simDeliverForge :
    (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).simDeliverForge =
      simDeliverForgeRedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q := rfl

@[simp] theorem v1SessionRedsHaltedRaw_epoch0Red :
    (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).epoch0Red =
      epoch0DistinguisherProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep := rfl

@[simp] theorem v1SessionRedsHaltedRaw_uniformStartRed :
    (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).uniformStartRed =
      uniformStartRedHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep := rfl

@[simp] theorem v1SessionRedsHaltedRaw_challSimDF :
    (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).challSimDF =
      (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).challSimDF := rfl

@[simp] theorem v1SessionRedsHaltedRaw_B_cka :
    (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).B_cka =
      (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).B_cka := rfl

@[simp] theorem v1SessionRedsHaltedRaw_B_prng :
    (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).B_prng =
      (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).B_prng := rfl

@[simp] theorem v1SessionRedsHaltedRaw_B_fs :
    (v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q).B_fs =
      (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).B_fs := rfl

end HaltedRawProjections

@[expose] def v1SessionRedsHalted {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) : SessionCostedReductionFamily Pt ℓ :=
  clampSessionCostedReductionFamily ℓ (v1SessionRedsHaltedRaw ℓ)

theorem v1SessionRedsHalted_bounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) : SessionCostedReductionFamilyBounded ℓ (v1SessionRedsHalted (Pt := Pt) ℓ) :=
  clampSessionCostedReductionFamily_bounded ℓ (v1SessionRedsHaltedRaw ℓ)
    (fun C K idA idB Dh encPt encT decT lam qep q hqep => by
      have hp := v1SessionRedsPaper_bounded
        ℓ C K idA idB Dh encPt encT decT lam qep q (by omega)
      exact ⟨spkCostedRedsHaltedInst_bounds ℓ C K idA idB Dh encPt encT decT lam (by omega),
        hp.2.1, hp.2.2.1,
        simFig8RedProgHalted_gRedBounded (Pt := Pt)
          ℓ C K idA idB Dh encPt encT decT lam qep q (by omega),
        simDeliverForgeRedProgHalted_gRedBounded (Pt := Pt) (ℓ := ℓ)
          C K idA idB Dh encPt encT decT lam qep q (by omega),
        epoch0DistinguisherProgHalted_gRedBounded_succ (Pt := Pt)
          C K Dh encPt encT decT idA idB lam ℓ q qep (by omega),
        uniformStartRedHalted_gRedBounded_succ (Pt := Pt)
          C K Dh encPt encT decT idA idB lam ℓ q qep (by omega),
        hp.2.2.2.2.2.2.2⟩)

@[simp] theorem v1SessionRedsHalted_of_le
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    {qep q : ℕ} (hqep : qep ≤ q + 4) :
    v1SessionRedsHalted ℓ C K idA idB Dh encPt encT decT lam qep q =
      v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam qep q :=
  clampSessionCostedReductionFamily_of_le ℓ (v1SessionRedsHaltedRaw ℓ)
    C K idA idB Dh encPt encT decT lam hqep

@[simp] theorem v1SessionRedsHalted_qepClamp
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    v1SessionRedsHalted ℓ C K idA idB Dh encPt encT decT lam (qepClamp qep q) q =
      v1SessionRedsHaltedRaw ℓ C K idA idB Dh encPt encT decT lam (qepClamp qep q) q :=
  clampSessionCostedReductionFamily_qepClamp ℓ (v1SessionRedsHaltedRaw ℓ)
    C K idA idB Dh encPt encT decT lam qep q

@[simp] theorem v1SessionRedsHalted_fs
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsHalted ℓ C K idA idB Dh encPt encT decT lam qep q).fs =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fs := by
  simp [v1SessionRedsHalted]

end

end Computational.Proofs.SessionCostedHaltInst
