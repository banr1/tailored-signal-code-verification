/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.Composition.StatementModel
public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Proofs.LibsignalCli.StatementPqSecure
import Computational.Proofs.SpecLemmas.Pqxdh.Security.HeadlineDelta
import Computational.Proofs.LibsignalCli.Oom.Transfer
import VCVio.EvalDist.Monad.Basic

/-!
# Relocatable Main Theorem from Lemmas 1–4, No-OOM, and Halted-Game Composition

**Checked by Lean.** Combines PQXDH key-indistinguishability (`L1`), session and model security
(`L2`, `L3`) with the halted-game composition interface `CliHaltedBoundProp`, relocatable CLI
functional correctness up to `.OutOfMemory` (`L4`, DEV-CLI15), and pointwise OOM-freedom (`hNoOOM`)
to derive `CliPqxdhBinaryCorrectAndSecurePlaced bytes` (`main_of_lemmas_placed`). No proof of
`L1`–`L4` or `hNoOOM` lies in this file's transitive import closure.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.MainOfLemmas

open scoped ENNReal BigOperators
open OracleComp OracleSpec
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh dummyKey)
open CryptoVerification.E2E (CliAdapterCostBounded CliGameAdversary
  CliGameAdversaryPerInstanceBounded CliKemFailProb CliPqxdhAdvantage
  CliToModelAdapterProg CompositionCostedReductionFamily
  CompositionCostedReductionFamilyBounded DhKerUniform LibsignalCliPqSecure
  MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds ModelSecure PEParams SessionCostedReductionFamily
  SessionCostedReductionFamilyBounded SessionSecure UnreachedPqxdhPrimitives
  bhPrefixFullBoundMixV1With cliCoinsTape? cliGameAdversaryReassoc cliPqxdhExpFlagged
  keyIndReductionBudget modelPrims stageOneAsProbComp withExcusedAbortTerm)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.SignalSession (CliHooks CliPqxdhBinaryCorrectPlaced
  CliPqxdhInputs CliReachesOOMPlaced CliRun CliSpecPqxdh CliSpecPqxdhOrExcusedAbort Inputs
  libsignalSessionLib)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open Computational.Proofs.LibsignalCli.Oom.Transfer (cliPqAdvantage_le_add_kemFail)

/-! ## Halted-game CLI composition interface -/

/-- Costed-reduction boundedness predicate for `(L_cli, D, reds)` in `CliHaltedBoundProp`. -/
abbrev CliHaltedRedsBounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (L_cli : ∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CliToModelAdapterProg S ℓ decT encT)
    (D : SessionCostedReductionFamily Pt ℓ)
    (reds : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamily S ℓ P C K qep decT encT) : Prop :=
  SessionCostedReductionFamilyBounded ℓ D ∧
  ((∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
      (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ),
      CliAdapterCostBounded decT encT b qStart qDR (L_cli decT encT)) ∧
   (∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
      (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
      CompositionCostedReductionFamilyBounded P C K qep decT encT (reds P C K qep decT encT)))

/-- Halted-game CLI composition interface packaging costed reductions `(L_cli, D, reds)` that bound
`cliPqxdhExpFlagged` away from `KemFailBad` via a halted experiment. -/
def CliHaltedBoundProp {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) : Prop :=
  ∃ (L_cli : ∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CliToModelAdapterProg S ℓ decT encT)
    (D : SessionCostedReductionFamily Pt ℓ)
    (reds : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamily S ℓ P C K qep decT encT),
    CliHaltedRedsBounded S ℓ L_cli D reds ∧
    ∀ (run : CliRun) (X : UnreachedPqxdhPrimitives) (Wp : PEParams)
      (_hCli : CliSpecPqxdh run X Wp)
      (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds Wp.Q.K)
      (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X Wp))
      (δ_kem : ℝ≥0∞) (_hKemBin : SignalPqxdh.KemDeltaCorrect (modelPrims X Wp) δ_kem)
      (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt) (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
      (_hDh : Dh.Commutes) (_hX : X25519RealizesDh Wp.C Dh encPt encT)
      (_hdec : ∀ T, decT (encT T) = some T)
      (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
      (_hD : ∀ k x, Wp.C.D k (Wp.C.E k x) = x) (_hkerAll : DhKerUniform Dh)
      (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (_hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
      (_hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
      (A : CliGameAdversary S ℓ (BitVec 512))
      (_hA : CliGameAdversaryPerInstanceBounded A b qStart qs),
      let P := modelPrims X Wp
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qInst := Finset.sup (Finset.range qStart) qs
      let qTot := b.q_total + qStart + qDR
      let B_A := (L_cli decT encT).eval (fun _ => cliGameAdversaryReassoc A) ()
      let Re := reds P Wp.C Wp.Q.K qep decT encT b qStart qDR qInst
      let b_ki := keyIndReductionBudget S qStart b
      let advK : SignalPqxdh.KeyIndAdversary S := ⟨Re.kindRed.eval (fun _ => B_A) ()⟩
      let prefixSum :=
        ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
          bhPrefixFullBoundMixV1With S P ℓ D Wp.C Wp.Q.K
            Dh encPt encT decT qep qTot (qs k) δ k flip Re B_A
      SignalPqxdh.QueryBounded advK b_ki ∧
      (∀ k < qStart,
        ∀ o ∈ support (stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false)),
        ∀ flip,
        CryptoGames.SM.MakesAtMostQueries ((Re.prefixRed k).eval2 o.2 flip qTot false) (qs k)) ∧
      ∃ (exp_H : ProbComp Bool) (δ_extra : ℝ≥0∞),
        (∀ v : Bool,
          Pr{let z ← cliPqxdhExpFlagged S run X Wp ℓ qep decT encT A}[
            z.1 = v ∧ ¬ (Wp.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)] ≤
              𝒟[exp_H] {v} + δ_extra) ∧
        𝒟[exp_H].boolBias + 2 * δ_extra ≤
          2 * SignalPqxdh.KeyInd1KeyRealAdvantage S P advK + prefixSum +
            SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem

/-! ## Assembling `LibsignalCliPqSecure` -/

/-- Derives `LibsignalCliPqSecure S ℓ` from `PqxdhCorrectAndSecureδ` and `CliHaltedBoundProp`. -/
theorem libsignalCliPqSecure_of_halted
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (hL1 : SignalPqxdh.Security.PqxdhCorrectAndSecureδ)
    (hHalt : CliHaltedBoundProp (Pt := Pt) S ℓ) :
    LibsignalCliPqSecure (Pt := Pt) S ℓ := by
  rcases hL1.keyInd S with ⟨RK, hCostRK, hSimRK, hKiBound⟩
  rcases hHalt with ⟨L_cli, D, reds, ⟨hSlotD, hBounds⟩, hMainH⟩
  refine ⟨L_cli, RK, D, reds, hCostRK, hSimRK, hSlotD, hBounds, ?_⟩
  intro run X W hCli hK_tot hP δ_kem hKemBin Dh encPt encT decT qep hℓ hDh hX hdec
    hdum hz hD hkerAll b qStart qs hq32 δ hδ A hA P qDR qInst qTot B_A Re b_ki advK
  obtain ⟨hK, hQueries, ⟨exp_H, δ_extra, hPtwise, hBiasH⟩⟩ :=
    hMainH run X W hCli hK_tot hP δ_kem hKemBin Dh encPt encT decT qep hℓ hDh hX hdec
      hdum hz hD hkerAll b qStart qs hq32 δ hδ A hA
  refine ⟨hK, hQueries, ?_⟩
  intro prefixSum
  have hTrans :=
    cliPqAdvantage_le_add_kemFail S run X W ℓ qep decT encT A exp_H δ_extra hPtwise
  have hClause1 :
      CliPqxdhAdvantage S run X W ℓ qep decT encT A ≤
        2 * SignalPqxdh.KeyInd1KeyRealAdvantage S P advK + prefixSum +
          SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem +
          2 * CliKemFailProb S run X W ℓ qep decT encT A :=
    hTrans.trans (add_le_add hBiasH le_rfl)
  refine ⟨hClause1, fun ε_ro hRo => hClause1.trans ?_⟩
  have hGapLe :
      SignalPqxdh.KeyInd1KeyRealAdvantage S P advK ≤
        (let R := RK.eval
         let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
         SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on δ_kem
           (SignalPqxdh.GapSigEufCma P P.isValidDhTriple (R.sig _ Ab))
           (SignalPqxdh.KemShCr P (R.shcr _ Ab))
           (SignalPqxdh.GapDhWithSign P P.isValidDhTriple P.pow8 (R.gdh _ Ab)) + ε_ro) :=
    le_trans hRo (add_le_add (hKiBound P hP δ_kem hKemBin b_ki ⟨advK, hK⟩) le_rfl)
  dsimp only [withExcusedAbortTerm]
  gcongr

/-! ## Relocatable binary security assembly -/

abbrev CliPqxdhElfSecurePlaced {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (mpl mmpl : MultiPlacement) (S : SignalPqxdh.Setup) (ℓ : ℕ) (elf : ElfImage) : Prop :=
  CryptoVerification.LibsignalCli.CliPqxdhElfSecurePlaced (Pt := Pt) mpl mmpl S ℓ elf

abbrev CliPqxdhBinaryCorrectAndSecurePlacedAt (mpl mmpl : MultiPlacement)
    (bytes : List (BitVec 8)) : Prop :=
  CryptoVerification.LibsignalCli.CliPqxdhBinaryCorrectAndSecurePlacedAt mpl mmpl bytes

abbrev CliPqxdhBinaryCorrectAndSecurePlaced (bytes : List (BitVec 8)) : Prop :=
  CryptoVerification.LibsignalCli.CliPqxdhBinaryCorrectAndSecurePlaced bytes

private theorem cliSpecPqxdh_of_orExcusedAbort_placed
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (h : CliSpecPqxdhOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩)
    (hAlloc : ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliSpecPqxdh (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ := by
  intro st hst
  obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := h st hst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    rcases hInit b t hnone with ⟨_, hr, rfl⟩ | ⟨_, hf⟩
    · exact hr
    · exact False.elim (hAlloc _ ⟨st, hst, .inl ⟨hnone, b, t, rfl⟩⟩ hf)
  · intro m r hm
    rcases hSend m r hm with ⟨_, hr, rfl⟩ | ⟨_, hf⟩
    · rw [hr]; split_ifs <;> rfl
    · exact False.elim (hAlloc _ ⟨st, hst, .inr (.inl ⟨m, r, hm, rfl⟩)⟩ hf)
  · intro c rc hc
    rcases hWhisper c rc hc with ⟨_, hr, rfl⟩ | ⟨_, hf⟩
    · rw [hr]; split_ifs <;> rfl
    · exact False.elim (hAlloc _ ⟨st, hst, .inr (.inr (.inl ⟨c, rc, hc, rfl⟩))⟩ hf)
  · intro m rc hm hmatch
    rcases hPrekey m rc hm hmatch with ⟨_, hr, rfl⟩ | ⟨_, hf⟩
    · rw [hr]; split_ifs <;> rfl
    · exact False.elim (hAlloc _ ⟨st, hst, .inr (.inr (.inr (.inl ⟨m, rc, hm, rfl⟩)))⟩ hf)
  · intro c rc hc h2 h3
    rcases hBad c rc hc h2 h3 with ⟨_, hr, rfl⟩ | ⟨_, hf⟩
    · rw [hr]; split_ifs <;> rfl
    · exact False.elim (hAlloc _ ⟨st, hst, .inr (.inr (.inr (.inr ⟨c, rc, hc, h2, h3, rfl⟩)))⟩ hf)

private theorem libsignalCliPqElfSecurePlaced_of_spec_aux
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {mpl mmpl : MultiPlacement} {S : SignalPqxdh.Setup} {ℓ : ℕ} {elf : ElfImage}
    (hSec : LibsignalCliPqSecure (Pt := Pt) S ℓ)
    (hSpec : ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives),
      CliSpecPqxdh (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩) :
    CliPqxdhElfSecurePlaced (Pt := Pt) mpl mmpl S ℓ elf := by
  rcases hSec with ⟨L_cli, RK, D, R_e2e, hCostRK, hSimRK, hSlotD, hCostE2E, hMain⟩
  refine ⟨L_cli, RK, D, R_e2e, hCostRK, hSimRK, hSlotD, hCostE2E, ?_⟩
  intro W X
  exact hMain (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ (hSpec W X)

/-- Derives `CliPqxdhBinaryCorrectAndSecurePlaced bytes` from Lemmas 1–4, pointwise OOM-freedom
`hNoOOM`, and `CliHaltedBoundProp`. -/
theorem main_of_lemmas_placed {bytes : List (BitVec 8)}
    (hL1 : SignalPqxdh.Security.PqxdhCorrectAndSecureδ)
    (_hL2 : ∀ {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] (ℓ : ℕ),
      SessionSecure (Pt := Pt) ℓ)
    (_hL3 : ∀ {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ),
      ModelSecure (Pt := Pt) S ℓ)
    (hL4 : CliPqxdhBinaryCorrectPlaced bytes)
    (hNoOOM : ∀ (mpl mmpl : MultiPlacement), libsignalSessionLib.LinkedAt bytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
      ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf →
      ∀ (W : CliHooks) (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        ¬ CliReachesOOMPlaced mpl mmpl elf W i)
    (hHalt : ∀ {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
      (S : SignalPqxdh.Setup) (ℓ : ℕ), CliHaltedBoundProp (Pt := Pt) S ℓ) :
    CliPqxdhBinaryCorrectAndSecurePlaced bytes := by
  intro mpl mmpl hLink hMLink
  rcases hL4 mpl mmpl hLink hMLink with ⟨elf, hParse, hElfBin⟩
  refine ⟨elf, hParse, hElfBin, ?_⟩
  intro Pt _ _ _ S ℓ
  exact libsignalCliPqElfSecurePlaced_of_spec_aux
    (libsignalCliPqSecure_of_halted S ℓ hL1 (hHalt S ℓ))
    (fun W X =>
      cliSpecPqxdh_of_orExcusedAbort_placed (hElfBin.2 W X).1
        (hNoOOM mpl mmpl hLink hMLink elf hParse W))

end Computational.Proofs.LibsignalCli.MainOfLemmas
