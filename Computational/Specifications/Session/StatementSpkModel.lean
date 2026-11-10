/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.SpkHop2Red
public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs

/-!
# Key, costed reductions and forgery term of the leaked-pre-key statement

**Trusted: the statement.** This file is part of the statements that import it (through
`StatementPqReds.lean`, `LibsignalCliPqSecure` and its ELF form): read it to trust them.
See `Computational/docs/TRUSTED_BASE.md`.

This file defines the statement-level components for the leaked-signed-pre-key hops (hops 1–3 of
`SpkHop2Red.lean`), where Bob's signed-pre-key scalar `s : BitVec 256` is fixed and possibly known
to the adversary: the sampled session key excluding `s`, the first-order
`ReductionDsl.CostedReduction` program types, evaluators, and `GRedBounded` cost budgets for the
three hops, and the epoch-0 chain forgery bound. The hop-1 and hop-2 reductions take `s` through
their explicit input `rIn` instead of an operator table (see
`Computational/docs/REDUCTION_DSL_TUTORIAL.md`).
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession

/-! ## Sampled key with fixed signed-pre-key coins -/

/-- Sampled portion of the initial session state: handshake `(rk, ck)`, Alice's initial ratchet
coins, and `pqr_key` (excluding Bob's fixed signed-pre-key coins `s`). -/
abbrev SampledSessionKey : Type := (LibsignalSession.RootKey × BitVec 256) × BitVec 256 × BitVec 256

/-- Initial session keys built from Bob's fixed signed-pre-key coins `s` and sampled key `k`. -/
def initKeysOfSampled (s : BitVec 256) (k : SampledSessionKey) : InitKeys :=
  ⟨k.1.1, k.1.2, s, k.2.1, k.2.2⟩

/-! ## Costed reduction types, budgets, and forgery bound -/

/-- Costed PRF reduction program for hop 1 with scalar input `s` in `rIn`. -/
abbrev SpkLeakRedProg (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt := 0) : Type :=
  ReductionDsl.CostedReduction
    (ReductionDsl.atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
    (ReductionDsl.extractPtPrfIface ℓ Pt)
    (SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (ReductionDsl.e2eSessionCodec ℓ Pt)
    ReductionDsl.BV256 .unit .bool .bool

/-- Evaluates a costed hop-1 `spkLeakRed` program at scalar `s` on session adversary `A`. -/
def evalSpkLeakRed {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (R : SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam)
    (s : BitVec 256)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    MACScheme.PRFAdversary Pt (BitVec 256) :=
  R.eval (fun _ => A) s

/-- Costed pure reduction program for the hop-3 uniform-scalar wrapper over `atomicPureOps`. -/
abbrev SpkLeakRedUProg (Pt : Type) (ℓ : ℕ := 0) : Type :=
  ReductionDsl.CostedReduction
    (ReductionDsl.atomicPureOps ℓ Pt)
    (ReductionDsl.extractPtPrfBaseIface ℓ Pt)
    (prfSpec Pt (BitVec 256))
    (ReductionDsl.extractPtPrfCodec ℓ Pt)
    .unit ReductionDsl.BV256 .bool .bool

/-- Evaluates a costed hop-3 `spkLeakRedU` program on a scalar-indexed family of PRF adversaries. -/
def evalSpkLeakRedU {Pt : Type} {ℓ : ℕ} (R : SpkLeakRedUProg Pt ℓ)
    (D : BitVec 256 → MACScheme.PRFAdversary Pt (BitVec 256)) :
    MACScheme.PRFAdversary Pt (BitVec 256) :=
  R.eval D ()

/-- Costed PRG hybrid reduction program for hop 2 with input `(s, c12)` in `rIn`. -/
abbrev SpkSwapPrgHybridProg (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt := 0) : Type :=
  ReductionDsl.CostedReduction
    (ReductionDsl.atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
    (ReductionDsl.coinOnlyIface ℓ Pt)
    (SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (ReductionDsl.e2eSessionCodec ℓ Pt)
    (.prod ReductionDsl.BV256 (.prod ReductionDsl.BV256 ReductionDsl.BV256)) .unit .bool .bool

/-- Evaluates a costed hop-2 PRG hybrid program at scalar `s` on session adversary `A`. -/
def evalSpkSwapPrgHybrid {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (R : SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam)
    (s : BitVec 256)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    PRGScheme.PRGAdversary (BitVec 256 × BitVec 256) :=
  fun c12 => R.eval (fun _ => A) (s, c12)

/-- Costed PRF hybrid reduction program for hop 2 with scalar input `s` in `rIn`. -/
abbrev SpkSwapPrfHybridProg (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt := 0) : Type :=
  ReductionDsl.CostedReduction
    (ReductionDsl.atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
    (ReductionDsl.extractPtPrfIface ℓ Pt)
    (SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (ReductionDsl.e2eSessionCodec ℓ Pt)
    ReductionDsl.BV256 .unit .bool .bool

/-- Evaluates a costed hop-2 PRF hybrid program at scalar `s` on session adversary `A`. -/
def evalSpkSwapPrfHybrid {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (R : SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam)
    (s : BitVec 256)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    MACScheme.PRFAdversary Pt (BitVec 256) :=
  R.eval (fun _ => A) s

/-- Bundle of costed reduction programs for the three leaked-signed-pre-key hops. -/
structure SpkCostedReds (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt := 0) where
  spkLeakRed : SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam
  spkLeakRedU : SpkLeakRedUProg Pt ℓ
  hop2PrgRedK : (k : ℕ) → SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam
  hop2PrfRedK : (k : ℕ) → SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam

/-- Step-cost budget for the hop-3 uniform-scalar wrapper `spkLeakRedU` (`O(q)`). -/
def spkLeakRedUBudget (q : ℕ) : ℕ :=
  16 * (q + 2)

/-- Tier-1 quadratic step-cost budget for `spkLeakRed`, `hop2PrgRedK`, and `hop2PrfRedK`
(`O(q^2 + q · (maxForwardJumps + log qep))`). -/
def spkTier1Budget (q qep : ℕ) : ℕ :=
  2 ^ 10 * (q + 1) ^ 2 + 2 ^ 9 * maxForwardJumps * (q + 1) +
    2 ^ 8 * (q + 1) * ReductionDsl.bits qep

/-- Tier-2 quasi-linear step-cost budget for `spkLeakRed`, `hop2PrgRedK`, and `hop2PrfRedK`
(`O(q · (ℓ + log q + log qep + maxForwardJumps))`). -/
def spkTier2Budget (q qep ℓ : ℕ) : ℕ :=
  (q + 1) * (64 * (ℓ + 512) + 64 * ReductionDsl.bits (q + 1) +
    64 * ReductionDsl.bits qep + 2 ^ 9 * maxForwardJumps)

/-- Combined Tier-1 / Tier-2 step-cost budget for `spkLeakRed`, `hop2PrgRedK`, and `hop2PrfRedK`. -/
def spkHopBudget (q qep ℓ : ℕ) : ℕ :=
  min (spkTier1Budget q qep) (spkTier2Budget q qep ℓ)

/-- `GRedBounded` query-count and step-cost bounds for `SpkCostedReds` at query limit `q`, epoch
cap `qep`, and plaintext byte-length `ℓ`. -/
def spkCostedBounds {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (q qep : ℕ)
    (R : SpkCostedReds Pt ℓ C K Dh encPt encT decT lam) : Prop :=
  GRedBounded R.spkLeakRed (fun _ => 1) (fun _ => 0)
    q (q + 1) (spkHopBudget q qep ℓ) ∧
  GRedBounded R.spkLeakRedU (fun _ => 1) (fun _ => 0)
    (q + 1) (q + 1) (spkLeakRedUBudget q) ∧
  (∀ k < spkSwapHybridCount,
    GRedBounded (R.hop2PrgRedK k) Empty.elim (fun _ => 0)
      q 0 (spkHopBudget q qep ℓ)) ∧
  (∀ k < spkSwapHybridCount,
    GRedBounded (R.hop2PrfRedK k) (fun _ => 1) (fun _ => 0)
      q q (spkHopBudget q qep ℓ))

/-- Hop-2 MAC forgery bound for up to `q` adversarial injections on Alice's uniform epoch-0 chain
`ck0`: `q` times the supremum of the ideal wire-MAC acceptance probability over message counters
`c < 2 ^ 32` and serialized ciphertexts of length `< 2 ^ 32`. -/
noncomputable def epoch0ChainForgeryTerm (F : ShaState → List (BitVec 8) → ShaState) (q : ℕ) : ℝ≥0∞ :=
  q * ⨆ (c : ℕ) (_ : c < 2 ^ 32) (salt : Salt) (ids : SerializedIdentityKeys) (ser : List (BitVec 8))
    (_ : ser.length < 2 ^ 32) (tag : BitVec 64),
    𝒟[PRGScheme.prgIdealExperiment (LibsignalSim.wireMacVerifiesTest F c salt ids ser tag)] {true}

end CryptoVerification.E2E
