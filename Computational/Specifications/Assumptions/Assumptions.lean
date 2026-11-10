/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Game

/-!
# Cryptographic assumption games and the primitive oracle for PQXDH

**Trusted: the statement.** The assumption games (`GapDhWithSign`, `GapSigEufCma`, `KemShCr`),
their adversary types, the `.Bounded` predicates, the primitive oracle `primSpec`, the combined
challenger oracle `sigAndDdhSpec`, and the budgets `primQueryBudget` / `gdhPrimQueryBudget` /
`gdhQueryBudget` are used by
the statement (`Security/Headline.lean`, `Security/HeadlineDelta.lean`, `StatementPqElf.lean`).
The standalone two-key and `Auth` assumptions (`GapDH`, `SigEufCma`, `AeadIndCpa`,
`PrfHmac`, `PrfChainKey`, `PrfMsgKeys`) are in
`Computational/Proofs/SignalPqxdh/TwoKeyAndAuthStatements.lean`, and the remaining auxiliary
assumptions (`KemIndCca`, `HkdfRO`, `RootKdfRO`, `AeadIntCtxt`, `AeadMuIntCtxt`, `PrfRk`, `HkdfPRF`,
`IkTwoKeyIdealisation`, `CryptoWellFormedPrimitives`) are in
`Computational/Proofs/SpecLemmas/SignalPqxdh/Assumptions.lean`, both checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Each assumption game is a `ProbComp Bool` experiment over `P : Primitives` against an adversary
carrying declared query budgets `q_*` enforced by `.Bounded`. Assumption adversaries evaluate `P`
through the primitive oracle `primSpec` (counted by `q_prim`), whereas the X25519 decisional
Diffie-Hellman oracle `isValidDhTriple` is exposed on the challenger interface `sigAndDdhSpec`
(counted by `q_ddh`).

`GapDhWithSign` (DEV-PQ17) and `GapSigEufCma` model libsignal's reuse of a single Curve25519
identity scalar across X25519 Diffie-Hellman and XEdDSA pre-key signing (Perrin, 2016; Degabriele
et al., CT-RSA 2012; Thormarker, ePrint 2021/509; Brendel et al., IEEE S&P 2021): in the SHA-512
random-oracle model, a Schnorr simulator guessing the key-fixed Edwards sign bit in `sig[63]`
reduces `GapDhWithSign` to standalone `GapDH` within a factor of 2, and forking-lemma reductions
reduce `GapSigEufCma` to discrete logarithm given the DDH oracle. `KemShCr` models semi-honest
collision resistance of Kyber-1024 (Bhargavan, Jacomme, Kiefer, Schmidt, USENIX Security 2024,
Def. 1 and Thm. 5).
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

open OracleComp OracleSpec ENNReal

/-! ## Primitive oracle -/

/-- Queries to the primitive oracle, with one constructor per `Primitives` operation used by the
    handshake and session games (excluding `isValidDhTriple` and internal leaf primitives). -/
inductive PrimQuery where
  | x25519          (sk pk : Bytes)
  | x25519Base      (sk : Bytes)
  | isCanonical     (pk : Bytes)
  | pow8            (pk : Bytes)
  | sigPkGen        (sk : Bytes)
  | sigSign         (sk msg rand : Bytes)
  | sigVerify       (pk msg sig : Bytes)
  | kemKeyGen       (seed : Bytes)
  | kemEncaps       (pk coins : Bytes)
  | kemDecaps       (sk ct : Bytes)
  | hkdfDerive96    (ikm : Bytes)
  | rootCreateChain (rk dh : Bytes)
  | chainKdfSeed    (ck : Bytes)
  | chainKdfNext    (ck : Bytes)
  | spqrInitSend    (pqr0 coins : Bytes)
  | spqrInitRecv    (pqr0 msg : Bytes)
  | deriveMsgKeys   (mkSeed : Bytes) (spqrSalt? : Option Bytes)
  | aeadEnc         (mk : MessageKeys) (ad pt : Bytes)
  | aeadDec         (mk : MessageKeys) (ad ct : Bytes)

@[reducible] def primSpec : OracleSpec PrimQuery := fun
  | .x25519 _ _          => Bytes
  | .x25519Base _        => Bytes
  | .isCanonical _       => Bool
  | .pow8 _              => Bytes
  | .sigPkGen _          => Bytes
  | .sigSign _ _ _       => Bytes
  | .sigVerify _ _ _     => Bool
  | .kemKeyGen _         => Bytes × Bytes
  | .kemEncaps _ _       => Option (Bytes × Bytes)
  | .kemDecaps _ _       => Option Bytes
  | .hkdfDerive96 _      => DRKey
  | .rootCreateChain _ _ => Bytes × Bytes
  | .chainKdfSeed _      => Bytes
  | .chainKdfNext _      => Bytes
  | .spqrInitSend _ _    => Option (Bytes × Option Bytes × Bytes)
  | .spqrInitRecv _ _    => Option (Bytes × Option Bytes)
  | .deriveMsgKeys _ _   => MessageKeys
  | .aeadEnc _ _ _       => Bytes
  | .aeadDec _ _ _       => Option Bytes

/-- Evaluates `primSpec` queries deterministically using `P`. -/
def primImpl (P : Primitives) : QueryImpl primSpec ProbComp := fun
  | .x25519 sk pk          => pure (P.x25519 sk pk)
  | .x25519Base sk         => pure (P.x25519Base sk)
  | .isCanonical pk        => pure (P.isCanonical pk)
  | .pow8 pk               => pure (P.pow8 pk)
  | .sigPkGen sk           => pure (P.sigPkGen sk)
  | .sigSign sk m r        => pure (P.sigSign sk m r)
  | .sigVerify pk m sg     => pure (P.sigVerify pk m sg)
  | .kemKeyGen seed        => pure (P.kemKeyGen seed)
  | .kemEncaps pk r        => pure (P.kemEncaps pk r)
  | .kemDecaps sk ct       => pure (P.kemDecaps sk ct)
  | .hkdfDerive96 ikm      => pure (P.hkdfDerive96 ikm)
  | .rootCreateChain rk dh => pure (P.rootCreateChain rk dh)
  | .chainKdfSeed ck       => pure (P.chainKdfSeed ck)
  | .chainKdfNext ck       => pure (P.chainKdfNext ck)
  | .spqrInitSend p r      => pure (P.spqrInitSend p r)
  | .spqrInitRecv p m      => pure (P.spqrInitRecv p m)
  | .deriveMsgKeys m s     => pure (P.deriveMsgKeys m s)
  | .aeadEnc mk ad pt      => pure (P.aeadEnc mk ad pt)
  | .aeadDec mk ad ct      => pure (P.aeadDec mk ad ct)

/-- Base oracle interface for assumption adversaries: uniform sampling plus `primSpec`, with
    game-specific challenger oracles added on the right. -/
abbrev PrimBaseSpec : OracleSpec (ℕ ⊕ PrimQuery) := unifSpec + primSpec

def isPrimQuery {ι : Type} : ((ℕ ⊕ PrimQuery) ⊕ ι) → Bool
  | .inl (.inr _) => true
  | _             => false

def isPrimQuery₀ : (ℕ ⊕ PrimQuery) → Bool
  | .inr _ => true
  | .inl _ => false

def primBaseImpl (P : Primitives) : QueryImpl PrimBaseSpec ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp + primImpl P

/-! ## Signing and DDH challenger oracles -/

/-- Decisional Diffie-Hellman query `(X, Y, Z)` testing `pow8(Z) = CDH_subG(pow8(X), pow8(Y))`. -/
abbrev DdhQuery := Bytes × Bytes × Bytes

@[reducible] def gapDhOracleSpec : OracleSpec DdhQuery := fun _ => Bool

inductive SigQuery where
  | sign (msg : Bytes)
  deriving DecidableEq, Repr

@[reducible] def sigOracleSpec : OracleSpec SigQuery := fun _ => Bytes

/-- Combined XEdDSA signing and X25519 DDH challenger interface shared by `GapDhWithSign` and
    `GapSigEufCma`. -/
@[reducible] def sigAndDdhSpec : OracleSpec (SigQuery ⊕ DdhQuery) :=
  sigOracleSpec + gapDhOracleSpec

def isSigChalQuery : ((ℕ ⊕ PrimQuery) ⊕ (SigQuery ⊕ DdhQuery)) → Bool
  | .inr (.inl _) => true
  | _             => false

def isDdhChalQuery : ((ℕ ⊕ PrimQuery) ⊕ (SigQuery ⊕ DdhQuery)) → Bool
  | .inr (.inr _) => true
  | _             => false

/-! ## `GapDhWithSign` -/

/-- Adversary for single-pair X25519 Gap-DH with an XEdDSA signing oracle on the first challenge
    key `U = P.x25519Base u` (DEV-PQ17), carrying query budgets `q_ddh`, `q_sig`, and `q_prim`. -/
structure GapDhWithSignAdv where
  run    : Bytes → Bytes → OracleComp (PrimBaseSpec + sigAndDdhSpec) Bytes
  q_ddh  : Nat
  q_sig  : Nat
  q_prim : Nat

/-- Every run of `A` respects its declared `q_ddh`, `q_sig`, and `q_prim` query budgets. -/
def GapDhWithSignAdv.Bounded (A : GapDhWithSignAdv) : Prop :=
  (∀ U V, OracleComp.IsQueryBoundP (A.run U V) (fun q => isDdhChalQuery q = true) A.q_ddh) ∧
  (∀ U V, OracleComp.IsQueryBoundP (A.run U V) (fun q => isSigChalQuery q = true) A.q_sig) ∧
  (∀ U V, OracleComp.IsQueryBoundP (A.run U V) (fun q => isPrimQuery q = true) A.q_prim)

/-- Single-pair X25519 Gap-DH experiment with signing oracle on `u`: samples scalars `u` and `v`,
    gives `(P.x25519Base u, P.x25519Base v)` to `A` with randomized XEdDSA signing under `u` and
    DDH oracle `isValidDhTriple`, and checks `pow8 Z = pow8 (P.x25519 u V)`. -/
def gapDhWithSignExp (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (A : GapDhWithSignAdv) : ProbComp Bool := do
  let u ← sampleScalar32
  let v ← sampleScalar32
  let U := P.x25519Base u
  let V := P.x25519Base v
  let sigImpl : QueryImpl sigOracleSpec ProbComp := fun (.sign m) => do
    let r ← sampleRandom64
    return P.sigSign u m r
  let ddhImpl : QueryImpl gapDhOracleSpec ProbComp := fun (X, Y, Z) =>
    pure (isValidDhTriple X Y Z)
  let Z ← simulateQ (primBaseImpl P + (sigImpl + ddhImpl)) (A.run U V)
  return (pow8 Z == pow8 (P.x25519 u V))

/-- Success probability of `A` in `gapDhWithSignExp` (DEV-PQ17). -/
noncomputable def GapDhWithSign (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (A : GapDhWithSignAdv) : ℝ≥0∞ :=
  𝒟[gapDhWithSignExp P isValidDhTriple pow8 A] {true}

/-! ## `KemShCr` -/

/-- Two-stage adversary for Kyber-1024 semi-honest collision resistance (BJKS24 Def. 1), with
    per-stage primitive-oracle budget `q_prim`. -/
structure KemShCrAdv where
  State         : Type
  choosePk      : Bytes → Bytes → OracleComp PrimBaseSpec (Bytes × State)
  findCollision : State → Bytes → Bytes → OracleComp PrimBaseSpec Bytes
  q_prim        : Nat

/-- Both stages of `A` make at most `A.q_prim` primitive-oracle queries. -/
def KemShCrAdv.Bounded (A : KemShCrAdv) : Prop :=
  (∀ pk sk,
    OracleComp.IsQueryBoundP (A.choosePk pk sk) (fun q => isPrimQuery₀ q = true) A.q_prim) ∧
  (∀ st ss ct,
    OracleComp.IsQueryBoundP
      (A.findCollision st ss ct) (fun q => isPrimQuery₀ q = true) A.q_prim)

/-- Kyber-1024 semi-honest collision-resistance experiment (BJKS24 Def. 1): `A.choosePk` receives
    an honest key pair `(pk, sk)` and outputs `(pk', st)`; given an honest encapsulation `(ss, ct)`
    under `pk'`, `A.findCollision` wins by outputting `ct'` with `P.kemDecaps sk ct' = some ss`,
    `ct' ≠ ct ∨ pk' ≠ pk`, `ct'.length = kyberCtLen`, and `pk'.length = kyberPkLen`. -/
def kemShCrExp (P : Primitives) (A : KemShCrAdv) : ProbComp Bool := do
  let (pk, sk) ← sampleKemKeyGen P
  let (pk', st) ← simulateQ (primBaseImpl P) (A.choosePk pk sk)
  let r ← sampleCoins32
  let some (ss, ct) := P.kemEncaps pk' r | return false
  let ct' ← simulateQ (primBaseImpl P) (A.findCollision st ss ct)
  return (decide (P.kemDecaps sk ct' = some ss) && decide (ct' ≠ ct ∨ pk' ≠ pk) &&
          decide (ct'.length = kyberCtLen ∧ pk'.length = kyberPkLen))

/-- Success probability of `A` in `kemShCrExp`. -/
noncomputable def KemShCr (P : Primitives) (A : KemShCrAdv) : ℝ≥0∞ :=
  𝒟[kemShCrExp P A] {true}

/-! ## `GapSigEufCma` -/

/-- Adversary for XEdDSA EUF-CMA security in the presence of the X25519 DDH oracle, carrying query
    budgets `q_sig`, `q_ddh`, and `q_prim`. -/
structure GapSigEufCmaAdv where
  run    : Bytes → OracleComp (PrimBaseSpec + sigAndDdhSpec) (Bytes × Bytes)
  q_sig  : Nat
  q_ddh  : Nat
  q_prim : Nat

/-- Every run of `A` respects its declared `q_sig`, `q_ddh`, and `q_prim` query budgets. -/
def GapSigEufCmaAdv.Bounded (A : GapSigEufCmaAdv) : Prop :=
  (∀ pk, OracleComp.IsQueryBoundP (A.run pk) (fun q => isSigChalQuery q = true) A.q_sig) ∧
  (∀ pk, OracleComp.IsQueryBoundP (A.run pk) (fun q => isDdhChalQuery q = true) A.q_ddh) ∧
  (∀ pk, OracleComp.IsQueryBoundP (A.run pk) (fun q => isPrimQuery q = true) A.q_prim)

/-- XEdDSA EUF-CMA experiment with DDH oracle `isValidDhTriple`: gives `pk = P.sigPkGen sk` to `A`,
    answers signing queries under `sk` with fresh 64-byte randomness while recording queried
    messages, and checks that `(m*, sig*)` verifies on an unqueried `m*`. -/
def gapSigEufCmaExp (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (A : GapSigEufCmaAdv) : ProbComp Bool := do
  let sk ← sampleScalar32
  let pk := P.sigPkGen sk
  let sigImpl : QueryImpl sigOracleSpec (StateT (List Bytes) ProbComp) := fun (.sign m) => do
    let r ← liftM sampleRandom64
    let sig := P.sigSign sk m r
    modify (m :: ·)
    return sig
  let ddhImpl : QueryImpl gapDhOracleSpec (StateT (List Bytes) ProbComp) := fun (X, Y, Z) =>
    pure (isValidDhTriple X Y Z)
  let fullImpl :=
    (primBaseImpl P).liftTarget (StateT (List Bytes) ProbComp) + (sigImpl + ddhImpl)
  let ((mStar, sigStar), signedMsgs) ← (simulateQ fullImpl (A.run pk)).run []
  return (P.sigVerify pk mStar sigStar && decide (mStar ∉ signedMsgs))

/-- Success probability of `A` in `gapSigEufCmaExp`. -/
noncomputable def GapSigEufCma (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (A : GapSigEufCmaAdv) : ℝ≥0∞ :=
  𝒟[gapSigEufCmaExp P isValidDhTriple A] {true}

namespace Security

/-! ## Reduction query budgets -/

/-- Specification primitive-oracle budget for an assumption adversary built from a game adversary
    with budget `b`: `16 * (5 * N_dh + N_sess_tot + 12)` primitive calls per game query plus one
    final extraction pass. -/
def primQueryBudget (S : Setup) (b : QueryBudget) : Nat :=
  16 * (b.q_total + 1) * (5 * S.N_dh + S.N_sess_tot + 12)

/-- DDH-oracle budget of the `GapDhWithSign` and `GapSigEufCma` reductions for game budget `b`:
    random-oracle × session consistency checks (`4 * M_ro * M_sess`) plus distinct session-pair
    checks (`2 * M_sess * (M_sess - 1)`), capped at `4 * q_total^2`, plus
    `q_total + N_dh + N_sess_tot` for final extraction (`M_sess` is bounded by `q_on` since only
    online queries create sessions). -/
def gdhQueryBudget (S : Setup) (b : QueryBudget) : Nat :=
  let M_ro := min b.q_ro b.q_total
  let M_sess := min (min b.q_on b.q_total) S.N_sess_tot
  min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) +
    b.q_total + S.N_dh + S.N_sess_tot

/-- Sharper primitive-oracle budget for the one-key `GapDhWithSign` and `GapSigEufCma` reductions:
    charges the full per-query cost `16 * (5 * N_dh + N_sess_tot + 12)` only to the at most
    `M_sess = min (min q_on q_total) N_sess_tot` online session queries (plus final extraction),
    and `32` to every other game query. -/
def gdhPrimQueryBudget (S : Setup) (b : QueryBudget) : Nat :=
  let M_sess := min (min b.q_on b.q_total) S.N_sess_tot
  32 * (b.q_total - M_sess) + 16 * (M_sess + 1) * (5 * S.N_dh + S.N_sess_tot + 12)

end Security

export Security (
  primQueryBudget
  gdhPrimQueryBudget
  gdhQueryBudget
)

end SignalPqxdh
