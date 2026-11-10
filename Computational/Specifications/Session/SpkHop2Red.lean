/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.State
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.CryptoGames.SM.Game
public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalBound

/-!
# Leaked-pre-key game configuration and the terms of its hop 2

**Trusted in part.** The theorems of `Computational/Theorems/` use every definition in this file
except `KeyU`, `initKeysU` and `sessionSchemeU`, which are checked by Lean; the ones they use are
part of what you must read to trust the result. See `Computational/docs/TRUSTED_BASE.md`.

The leaked-pre-key statement bounds the single-session SM game when Bob's signed-pre-key scalar `s`
is fixed and known to the adversary (`sessionSchemeFixedSpk`), under early-corruption refusals
`configRefuseEarlyBobCorr` (`noBobCorrInEpoch0`, `noBobCorrWhileAliceBelowEpoch10`). Its proof
bridges to the uniform-start scheme `sessionSchemeU` in three hops: hop 1 replaces epoch-0 root-key
derivation at `Dh(s, T)` by a PRF oracle; hop 2 couples known `s` with a uniform hidden scalar `x`
by relabelling the random function on `DhKerUniform` fibers; hop 3 undoes hop 1 at `x`.

Refusing `corr-A` (DEV-LS4) and `corr-B` (DEV-LS34) while `epoch A < 10` keeps the first five round
trips leak-free, so shared root keys form a single linear chain `ρ₀, …, ρ₈` until Alice's fifth DH
step evicts the epoch-0 receiver chain `ck0` (`maxReceiverChains = 5`). In hop 2, replacing those
`spkSwapHybridCount = 9` root-KDF steps by random tables leaves spurious-step acceptance
(`spkSwapSpuriousStepTerm`), honest creation-point hits (`spkSwapCreationPointHitTerm`), hybrid
transition collisions (`hop2CreateCollTerm`), and `s`-world queries that hit the hidden public key
`pub x` (`spkSwapHiddenScalarGuessTerm`).
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession

/-! ## Uniform-start scheme and early-corruption refusals -/

/-- Uniform-start session key `((rk, ck), spkCoinsB, ratchetCoinsA₀, pqrKey)`: epoch-0 root and
chain keys, Bob's signed-pre-key coins, Alice's initial ratchet coins, and the post-quantum root
key. -/
abbrev KeyU : Type :=
  (LibsignalSession.RootKey × BitVec 256) × BitVec 256 × BitVec 256 × BitVec 256

/-- Unpacks `KeyU` directly into `InitKeys` without an initial root-KDF step. -/
def initKeysU (k : KeyU) : InitKeys :=
  ⟨k.1.1, k.1.2, k.2.1, k.2.2.1, k.2.2.2⟩

/-- **DEV-LS33 (libsignal): no corruption of Bob in epoch 0.** Refuses `corr-B` while
`epoch B = 0` (beyond `configR1OnCurve`, which refuses only Bob's epoch-0 sends, DEV-LS3). In
libsignal's API, Bob's session exists only after his first successful decryption; earlier
compromise exposes pre-key secrets handled at the PQXDH layer. Subsumed by
`noBobCorrWhileAliceBelowEpoch10` (DEV-LS34), since `epoch B = 0` implies `epoch A ≤ 1`. -/
def noBobCorrInEpoch0 {St Msg C : Type} (st : SM.GameState St Msg C) (P : Party) : Bool :=
  !(P == .B && st.epoch .B == 0)

/-- **DEV-LS34 (formalization): no corruption of Bob while Alice is in epoch `< 10`.** Refuses
`corr-B` while `epoch A < 10`, as Bob's counterpart to DEV-LS4
(`noAliceCorrWhileAliceBelowEpoch10`). Effect: restricts the adversary; Bob compromises during
the first five round trips (while Alice may still store the epoch-0 chain `ck0`) are excluded.
With `s` known, `corr-B` in this window exposes Bob's root key and sending coins, and hence
Alice's subsequent root keys, while `ck0` remains reachable via `pub s`. -/
def noBobCorrWhileAliceBelowEpoch10 {St Msg C : Type} (st : SM.GameState St Msg C) (P : Party) : Bool :=
  !(P == .B && decide (st.epoch .A < 10))

/-- Session game configuration `configR1OnCurve` extended with `noBobCorrInEpoch0` and
`noBobCorrWhileAliceBelowEpoch10` in `corrOK`. -/
def configRefuseEarlyBobCorr {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) {St Msg : Type} :
    SM.ConfigR St Msg Bytes :=
  { configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT) with
    corrOK := fun st P =>
      (configR1OnCurve (St := St) (Msg := Msg)
        (ratchetKeyAdmissible protoSignalCodec decT encT)).corrOK
        st P && noBobCorrInEpoch0 st P && noBobCorrWhileAliceBelowEpoch10 st P }

/-- Single-session `SMSchemeR` keyed directly by uniform-start keys `KeyU` via `initKeysU`,
with plaintexts fitted to `ℓ` bytes. -/
def sessionSchemeU {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC) (ℓ : ℕ) :
    SMSchemeR KeyU (GhostState PQ) (Plain ℓ) PQC (BitVec 256) Bytes where
  initA k := P.initA (initKeysU k)
  initB k := P.initB (initKeysU k)
  send g m r := P.send g m.toList r
  receive g c rc := (P.receive g c rc).map fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain ℓ x.2.2.2)

/-! ## Hop 2 bound terms -/

/-- Number of root-KDF hybrids in hop 2 (`ρ₀` through `ρ₈`, up to Alice's fifth DH step when
`ck0` is evicted). -/
def spkSwapHybridCount : ℕ := 9

/-- Union bound over at most `q` spurious DH steps of Alice while she stores `ck0`, once all
`spkSwapHybridCount` root-KDF tables are random. Each test evaluates `expandPRG` and the ideal
acceptance probability of `wireMacVerifiesTest`, with supremum over chain counters `c < 2 ^ 32`
and wire lengths `ser.length < 2 ^ 32` as in `macForgeryProb` (DEV-LS23). -/
noncomputable def spkSwapSpuriousStepTerm (F : ShaState → List (BitVec 8) → ShaState) (q : ℕ) : ℝ≥0∞ :=
  q * ⨆ (c : ℕ) (_ : c < 2 ^ 32) (salt : Salt) (ids : SerializedIdentityKeys) (ser : List (BitVec 8))
    (_ : ser.length < 2 ^ 32) (tag : BitVec 64),
    ((Ratchet.expandPRG F).prgAdvantage (LibsignalSim.wireMacVerifiesTest F c salt ids ser tag) +
      𝒟[PRGScheme.prgIdealExperiment (LibsignalSim.wireMacVerifiesTest F c salt ids ser tag)] {true})

/-- Bound on the probability that a spurious DH output `Dh.dh a T` equals the honest creation point
`Dh.dh a (Dh.dh r Dh.base)` over at most `q + 1` receives of Bob with fresh scalar `r`. -/
noncomputable def spkSwapCreationPointHitTerm {Pt : Type} (Dh : DHFun (BitVec 256) Pt) (q : ℕ) : ℝ≥0∞ :=
  (q + 1) * ⨆ (a : BitVec 256) (T : Pt),
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {r | Dh.dh a (Dh.dh r Dh.base) = Dh.dh a T}

/-- Collision slack across the `spkSwapHybridCount - 1 = 8` hybrid transitions `k → k + 1`
(table `0`'s creation entry is fixed before any query). Each transition budgets `6 * q` fresh-scalar
point-hit events: `q` against nonzero points already sampled lazily in table `k + 1`, and `5 * q`
against the at most `5` stored receiver-chain public keys (`maxReceiverChains`) per delivery. -/
noncomputable def hop2CreateCollTerm {Pt : Type} [DecidableEq Pt] [Zero Pt]
    (Dh : DHFun (BitVec 256) Pt) (q : ℕ) : ℝ≥0∞ :=
  ((spkSwapHybridCount - 1 : ℕ) : ℝ≥0∞) * ((6 * q : ℕ) : ℝ≥0∞) * ⨆ (T : Pt) (Q : Pt),
    if Q = 0 then 0 else 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {r | Dh.dh r T = Q}

/-- Bound on `s`-world divergence before hop 2's coupling breaks, when a query hits the
independent hidden public key `Dh.dh x Dh.base`. Budgets `6 * q` point-hit events: `q` deliver or
inject sender ratchet keys and `5 * q` stored receiver-chain keys (`maxReceiverChains`) while
`ck0` remains active. -/
noncomputable def spkSwapHiddenScalarGuessTerm {Pt : Type} (Dh : DHFun (BitVec 256) Pt) (q : ℕ) : ℝ≥0∞ :=
  ((6 * q : ℕ) : ℝ≥0∞) *
    ⨆ P : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = P}

end CryptoVerification.E2E
