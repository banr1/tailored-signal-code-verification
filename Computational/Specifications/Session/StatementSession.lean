/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import Computational.Specifications.Game.StatementPqOomFlag
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Lemma 2: Double Ratchet + SPQR V1 session security

**Trusted: the statement.** Read this file together with
`Computational/Specifications/Session/StatementComposed.lean`,
`Computational/Specifications/Session/StatementIdsModel.lean`,
`Computational/Specifications/Session/StatementSpkModel.lean`,
`Computational/Specifications/Session/SpkHop2Red.lean`,
`Computational/Specifications/Game/StatementPqOomFlag.lean`, and
`LibsignalBinary/Specifications/LibsignalSpqrV1/KemFailFind.lean`. The theorem `session_secure`
(`Computational/Theorems/Lemmas.lean`) proves `SessionSecure`. See
`Computational/docs/TRUSTED_BASE.md`.

`SessionSecure` is Lemma 2 of *Formally Verifying Signal's Security Using AI* (`docs/PAPER_MAP.md`):
single-session security of the Triple Ratchet (Double Ratchet plus SPQR V1). It plays the
real-or-random game `SM.gameR` (ACD19, Fig. 2) on `sessionSchemeFixedSpk`, with Bob's signed-pre-key
coins `s` fixed and possibly known to the adversary, under `configRefuseEarlyBobCorr`. Quantified
over a mixture `oa : ProbComp α` of session contexts `(ida o, idb o, s o)` and `q`-query
adversaries `A o`, one costed reduction family `D` satisfying `SessionCostedReductionFamilyBounded ℓ D`
bounds the mixed `SM.gameR` bias by `sessionAdvantageBound + 2 * sessionKemFailProb` whenever
`2 * (q + 1) + 25002 < 2 ^ 32`. Inside `sessionAdvantageBound`, `prefixPrfAvg oa` and
`prefixPrgAvg oa` push `oa` into each reduction so the bound matches `bhPrefixFullBoundMixV1With`
definitionally; `α := Unit`, `oa := pure ()` recovers fixed-context security.

Because `SM.gameR` lets the adversary supply send coins (including the ML-KEM-768 key-generation
seed and encapsulation randomness in SPQR V1), the adversary can trigger ML-KEM decryption failure.
The top-level term `2 * sessionKemFailProb` (with factor `2` from `|2 Pr - 1|`) bounds this event in
the game with `A` itself as twice the probability that some ordered pair of send tapes forms a
failing exchange (`MlKem.KemFailBad`); evaluating it on `A` avoids reductions that could inflate the
probability with a hard-coded failing pair. The game `gameRCoinLogged` runs `oracleImplRM` on
`smSchemeCoinLogged` to record every send's coins in a `WriterT` log, and `GameRCoinLoggedFaithful`
states that projecting out the game outcome recovers `SM.gameR`.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1

/-- Per-session Double Ratchet + SPQR V1 advantage bound for a context/adversary mixture
`oa : ProbComp α`: `uniformStartMixtureBound` plus the leaked-pre-key hop-1, hop-3, and hop-2 terms
on the costed reductions `D`. -/
noncomputable def sessionAdvantageBound {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  let R := fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 qep q
  let Rspk := fun o => (R o).spk
  uniformStartMixtureBound C K ℓ Dh encPt encT decT 0 qep q δ oa ida idb R A
    + 2 * (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o =>
          evalSpkLeakRed (Rspk o).spkLeakRed (s o) (A o)))
    + 2 * (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o =>
          evalSpkLeakRedU (Rspk o).spkLeakRedU
            (fun x => evalSpkLeakRed (Rspk o).spkLeakRed x (A o))))
    + 2 * (epoch0ChainForgeryTerm C.F q
        + (∑ j ∈ Finset.range spkSwapHybridCount,
            ((Ratchet.expandPRG C.F).prgAdvantage
                (prefixPrgAvg oa (fun o =>
                  evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) (s o) (A o)))
              + (extractPRF C.F encPt).prfAdvantage
                (prefixPrfAvg oa (fun o =>
                  evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) (s o) (A o)))))
        + hop2CreateCollTerm Dh q + spkSwapSpuriousStepTerm C.F q + spkSwapCreationPointHitTerm Dh q + spkSwapHiddenScalarGuessTerm Dh q)

/-! ## Send-coin-logged R-game and ML-KEM failure term -/

/-- Monadic wrapper around `sm` over `WriterT (List Coins) ProbComp` that appends each `send`'s
coins `r` to the log and leaves `receive` unlogged. -/
def smSchemeCoinLogged {Key St Msg Coins RCoins C : Type} (sm : SMSchemeR Key St Msg Coins RCoins C) :
    SMSchemeRM (WriterT (List Coins) ProbComp) Key St Msg Coins RCoins C where
  initA := sm.initA
  initB := sm.initB
  send st m r := do
    MonadWriter.tell [r]
    return sm.send st m r
  receive st c rc := return sm.receive st c rc

/-- Real-or-random game `SM.gameR` instrumented via `smSchemeCoinLogged` to return both the game
outcome and the ordered list of coins for every honest or adversarial send that reaches `sm.send`
(after `cfg.sendOK`, `win`, and epoch-management checks). -/
def gameRCoinLogged {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (A : SM.Adversary St Msg Coins C) : ProbComp (Bool × List Coins) :=
  WriterT.run do
    let b ← liftM ($ᵗ Bool : ProbComp Bool)
    let k ← liftM ($ᵗ Key : ProbComp Key)
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState St Msg C) (WriterT (List Coins) ProbComp)) +
      oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg
    let (b', s) ← (simulateQ impl A).run ((smSchemeCoinLogged sm).initState k b)
    return (b == b' || s.win)

/-- Faithfulness of `gameRCoinLogged`: projecting to the Boolean outcome yields the exact
distribution of `SM.gameR`. -/
def GameRCoinLoggedFaithful : Prop :=
  ∀ {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (A : SM.Adversary St Msg Coins C),
    𝒟[Prod.fst <$> gameRCoinLogged sm Δ qep cfg A] = 𝒟[SM.gameR sm Δ qep cfg A]

/-- Probability, in `gameRCoinLogged` on `sessionSchemeFixedSpk` mixed over `oa` with adversaries
`A o`, that some ordered pair of 64-byte SPQR V1 send tapes (`coinBytes`) triggers an ML-KEM
decryption failure (`K.KemFailBad`). -/
noncomputable def sessionKemFailProb {α : Type} (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  Pr{let z ← oa >>= fun o =>
      gameRCoinLogged
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) (ida o) (idb o))
          ℓ (s o))
        3 qep (configRefuseEarlyBobCorr decT encT)
        (A o)}[K.KemFailBad (z.2.map LibsignalSpqrV1.coinBytes) = true]

/-- Lemma 2 (Double Ratchet + SPQR V1 session security): existence of a bounded costed reduction
family `D` such that, under the primitive, group, point-fiber (`δ`), and message-counter
(`2 * (q + 1) + 25002 < 2 ^ 32`) hypotheses, every mixture `oa` of contexts `(ida o, idb o, s o)`
and `q`-query adversaries `A o` has `SM.gameR` bias on `sessionSchemeFixedSpk` at most
`sessionAdvantageBound + 2 * sessionKemFailProb`. -/
def SessionSecure {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] (ℓ : ℕ) : Prop :=
  ∃ D : SessionCostedReductionFamily Pt ℓ,
    SessionCostedReductionFamilyBounded ℓ D ∧
    ∀ (C : Crypto) (K : LibsignalSpqrV1.MlKem) (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
      (_hK : Encaps1Total K) (_hD : ∀ k x, C.D k (C.E k x) = x) (_hℓ : ℓ < 10 ^ 6)
      (_hDh : Dh.Commutes) (_hX : X25519RealizesDh C Dh encPt encT)
      (_hdec : ∀ T, decT (encT T) = some T)
      (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
      (_hker : DhKerUniform Dh)
      (qep q : ℕ) (_hq32 : 2 * (q + 1) + 25002 < 2 ^ 32)
      (δ : ℝ≥0∞)
      (_hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
      {α : Type} (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
      (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
      (_hA : ∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q),
      𝒟[oa >>= fun o =>
          SM.gameR
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) (ida o) (idb o))
              ℓ (s o))
            3 qep (configRefuseEarlyBobCorr decT encT) (A o)].boolBias ≤
        sessionAdvantageBound ℓ D C K Dh encPt encT decT qep q δ oa ida idb s A
          + 2 * sessionKemFailProb C K ℓ decT encT qep oa ida idb s A

end CryptoVerification.E2E
