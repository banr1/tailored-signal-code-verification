/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPq
public import Computational.Specifications.Game.StatementPqOomGame
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Specifications.Assumptions.KeyInd1KeyRo
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Computational.Specifications.Pqxdh.Security.HeadlineDelta

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable ELF security statement for the PQXDH CLI

**Trusted: the statement.** Defines `CliPqxdhBinaryCorrectAndSecurePlaced`, the top-level
correctness and cryptographic security predicate instantiated at `cliElfBytes` in
`Computational/Theorems/Main.lean`. Read alongside `StatementPq.lean` (`cliPqExp`,
`CliPqxdhAdvantage`), `StatementPqOomGame.lean` (`CliPqxdhFlagProb`, `CliKemFailProb`),
`StatementPqReds.lean`, and `LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean`
(`CliPqxdhElfCorrectPlaced`, `Placed.cliRunPlacedSig`). See `Computational/docs/TRUSTED_BASE.md`
and `Computational/docs/DEVIATIONS.md`.

`CliPqxdhSecurityFor S ℓ ForRuns` asserts cost- and query-bounded reductions (`L_cli`, `RK`, `D`,
`reds`) and establishes two upper bounds in `ℝ≥0∞` on `CliPqxdhAdvantage` for the runs selected by
`ForRuns`: first against `KeyInd1KeyRealAdvantage`, and second (given the HKDF random-oracle
idealization gap `KeyIndRoGap`, DEV-CLI16) against `pqxdhKeyIndAdvantageBoundActiveδ`
(`GapSigEufCma`, `KemShCr`, `GapDhWithSign`). Both bounds include the Double Ratchet prefix sum
`prefixSum`, the Kyber decapsulation failure term, `2 * CliKemFailProb` evaluated directly on the
adversary `A` (since adversary-chosen send randomness controls the SPQR V1 ML-KEM-768 coins), and,
when `exc? = some exc`, `2 * CliPqxdhFlagProb` for excused aborts (`withExcusedAbortTerm`).

`CliPqxdhElfSecurePlaced` specializes `CliPqxdhSecurityFor` to the relocatable ELF runner
`Placed.cliRunPlacedSig mpl mmpl elf W` under multi-block placements `(mpl, mmpl)` for
`libsignalSessionLib` and `VerifiedLibraries.mallocngLib`, with `exc? := none` and no
`.OutOfMemory` hypothesis on the security clause (under the modelled 1 GiB dynamic physical-memory
budget; the correctness conjunct `CliPqxdhElfCorrectPlaced` still permits `.OutOfMemory` aborts,
DEV-CLI15). Code bytes, relocations, and segment layout are kernel-checked against `bytes`; symbol
labels rest on the trusted object extractor (assumption A-LINK in
`Computational/docs/TRUSTED_BASE.md`).

Scope follows `Computational/docs/DEVIATIONS.md`: unpartnered first-message payload privacy and
authentication are covered by the `Auth` conjunct of Lemma 1 rather than folded into this game
(DEV-C5), and as in `CliBinaryPq.lean`, the statement excludes CPUs with AES/PMULL enabled in
`spqr`'s probe (DEV-CLI10) and subsequent calls after an accepted non-matching pre-key `recv`
(DEV-CLI11).
-/

open OracleComp OracleSpec MeasureTheory ENNReal

/-! ## Canonical CLI PQXDH security proposition -/

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

/-- Holds when `i` is a PQXDH-mode input (`CliPqxdhInputs W`) excused by `exc` on which `run i`
aborts. -/
def CliPqxdhExcusedAbort (exc : Inputs → Prop) (run : CliRun) (W : PEParams) (i : Inputs) : Prop :=
  CliPqxdhInputs W i ∧ exc i ∧ run i = some .aborted

/-- Adds `2 * CliPqxdhFlagProb … (CliPqxdhExcusedAbort exc run W)` to `rhs` when `exc? = some exc`,
or leaves `rhs` unchanged when `exc? = none`. -/
noncomputable abbrev withExcusedAbortTerm {Pt : Type} (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (ℓ qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) : Option (Inputs → Prop) → ℝ≥0∞ → ℝ≥0∞
  | none, rhs => rhs
  | some exc, rhs =>
      rhs + 2 * CliPqxdhFlagProb S run X W ℓ qep decT encT A (CliPqxdhExcusedAbort exc run W)

/-- Canonical CLI PQXDH security statement parameterized by the run quantifier `ForRuns` over
`(run, X, Wp, exc?)`, asserting cost- and query-bounded reductions and bounding `CliPqxdhAdvantage`
against `KeyInd1KeyRealAdvantage` and (given `KeyIndRoGap`) `pqxdhKeyIndAdvantageBoundActiveδ`.
Cost bounds (`CliAdapterCostBounded`, `CompositionCostedReductionFamilyBounded`) track both total
queries `qTot = b.q_total + qStart + qDR` and per-kind counts (`bhKindCounts b qStart qDR`)
separating online queries (`b.q_on`, `qStart`, `qDR`) from offline random-oracle queries
(`b.q_ro`), while the `KeyInd` bound depends only on `b_ki.q_on`. -/
def CliPqxdhSecurityFor {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (ForRuns : (CliRun → UnreachedPqxdhPrimitives → PEParams → Option (Inputs → Prop) → Prop) → Prop) :
    Prop :=
  ∃ (L_cli : ∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CliToModelAdapterProg S ℓ decT encT)
    (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
    (D : SessionCostedReductionFamily Pt ℓ)
    (reds : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamily S ℓ P C K qep decT encT),
    SignalPqxdh.Security.KeyIndCostedReductionBounds S RK ∧
    SignalPqxdh.Security.KeyIndReductionQueryBounds S RK.eval ∧
    SessionCostedReductionFamilyBounded ℓ D ∧
    ((∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
        (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ),
        CliAdapterCostBounded decT encT b qStart qDR (L_cli decT encT)) ∧
     (∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamilyBounded P C K qep decT encT (reds P C K qep decT encT))) ∧
    ForRuns fun run X Wp exc? =>
      ∀ (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds Wp.Q.K)
        (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X Wp))
        (δ_kem : ℝ≥0∞) (_hKemBin : SignalPqxdh.KemDeltaCorrect (modelPrims X Wp) δ_kem)
        (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
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
        ∃ (hK : SignalPqxdh.QueryBounded advK b_ki),
          (∀ k < qStart,
            ∀ o ∈ support (stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false)),
            ∀ flip,
            SM.MakesAtMostQueries ((Re.prefixRed k).eval2 o.2 flip qTot false) (qs k)) ∧
          let prefixSum :=
            ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
              bhPrefixFullBoundMixV1With S P ℓ D Wp.C Wp.Q.K
                Dh encPt encT decT qep qTot (qs k) δ k flip Re B_A
          CliPqxdhAdvantage S run X Wp ℓ qep decT encT A ≤
            withExcusedAbortTerm S run X Wp ℓ qep decT encT A exc?
              (2 * SignalPqxdh.KeyInd1KeyRealAdvantage S P advK + prefixSum +
                SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem +
                2 * CliKemFailProb S run X Wp ℓ qep decT encT A) ∧
          (∀ ε_ro : ℝ≥0∞, SignalPqxdh.KeyIndRoGap S P advK ε_ro →
            CliPqxdhAdvantage S run X Wp ℓ qep decT encT A ≤
              withExcusedAbortTerm S run X Wp ℓ qep decT encT A exc?
                (2 * (let R := RK.eval
                      let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
                      SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on δ_kem
                        (SignalPqxdh.GapSigEufCma P P.isValidDhTriple (R.sig _ Ab))
                        (SignalPqxdh.KemShCr P (R.shcr _ Ab))
                        (SignalPqxdh.GapDhWithSign P P.isValidDhTriple P.pow8 (R.gdh _ Ab)) + ε_ro)
                  + prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem
                  + 2 * CliKemFailProb S run X Wp ℓ qep decT encT A))

end CryptoVerification.E2E

namespace CryptoVerification.LibsignalCli

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.SignalSession

/-! ## Relocatable ELF security statements -/

/-- Specializes `CliPqxdhSecurityFor` to the relocatable ELF runner
`Placed.cliRunPlacedSig mpl mmpl elf W` under placements `(mpl, mmpl)`, with `exc? := none` and no
`.OutOfMemory` hypothesis. -/
abbrev CliPqxdhElfSecurePlaced {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (mpl mmpl : Obj.MultiPlacement) (S : SignalPqxdh.Setup) (ℓ : ℕ) (elf : ElfImage) : Prop :=
  CliPqxdhSecurityFor (Pt := Pt) S ℓ fun Bound =>
    ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives),
      Bound (Placed.cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ none

/-- `bytes` parses as an ELF image satisfying both `CliPqxdhElfCorrectPlaced` and
`CliPqxdhElfSecurePlaced` at placements `(mpl, mmpl)`. -/
def CliPqxdhBinaryCorrectAndSecurePlacedAt (mpl mmpl : Obj.MultiPlacement)
    (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqxdhElfCorrectPlaced mpl mmpl elf ∧
    ∀ {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] (S : SignalPqxdh.Setup) (ℓ : ℕ),
      CliPqxdhElfSecurePlaced (Pt := Pt) mpl mmpl S ℓ elf

/-- `CliPqxdhBinaryCorrectAndSecurePlacedAt` for all placements `mpl` of `libsignalSessionLib` and
`mmpl` of `VerifiedLibraries.mallocngLib` linked at `bytes`. -/
def CliPqxdhBinaryCorrectAndSecurePlaced (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl mmpl : Obj.MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
    CliPqxdhBinaryCorrectAndSecurePlacedAt mpl mmpl bytes

end CryptoVerification.LibsignalCli
