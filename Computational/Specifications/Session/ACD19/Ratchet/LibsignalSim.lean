/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance

/-!
# Shared types and error terms for the libsignal-to-Double-Ratchet refinement

**Trusted in part.** The theorems of `Computational/Theorems/` use every definition in this file
except `Fig8Comp`, `tagBytes` and `toWire`, which are checked by Lean; the ones they use are part of
what you must read to trust the result. See `Computational/docs/TRUSTED_BASE.md`. `epoch0Term`,
`GhostChain`, `configEpoch0Distinguisher`, `epoch0Distinguisher`, and the refinement theorems are in
`Computational/Proofs/SpecLemmas/Session/ACD19/Ratchet/LibsignalSim.lean`, checked by Lean.

A simulator `sim` playing the secure-messaging game of ACD19 (Alwen, Coretti, Dodis, *The Double
Ratchet*, ePrint 2018/1037) against the Fig. 8 Double Ratchet instance `lFig8` (messages
`LibsignalMsgPublicPart × Plain ℓ`, healing constant `Δ_SM = 3`; DEV-LS32) reproduces the restricted
libsignal session game `configR1OnCurve` on `libsignalSessionScheme`
(`LibsignalBinary/Specifications/CryptoGames/SM/LibsignalGame.lean`; DEV-LS1 to DEV-LS7, with SPQR
fields per DEV-LS24) up to the spurious-step error terms defined here.

The per-test regularity units `rootKdfSpuriousStepUnit` and `rootKdfForgedEpochStartUnit` are named,
non-standard trust assumptions (HKDF/HMAC-SHA256 as a statistical extractor under a worst-case
public salt on correlated clamped-X25519 inputs), justified only in the random-oracle model.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames
namespace Ratchet
namespace LibsignalSim

open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA LibsignalSession LibsignalInst

/-- Little-endian 8-byte serialization of a 64-bit MAC tag (inverse of `bytesToWord64LE` on 8-byte
lists). -/
def tagBytes (t : BitVec 64) : List (BitVec 8) :=
  (List.range 8).map fun j => (t >>> (8 * j)).truncate 8

/-- Party state of the Fig. 8 instance `lFig8`. -/
abbrev Fig8St (Pt : Type) :=
  PartyState (CKA.DDH.State (BitVec 256) Pt) Pt Ratchet.RootKey
    (FSAEAD.RatchetSenderState (BitVec 256))
    (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))

/-- Ciphertext `(header, (counter, wireCtWithSalt))` of `lFig8`. -/
abbrev Fig8C (Pt : Type) := Header Pt × (ℕ × LibsignalCiphertextWithSalt32)

abbrev Fig8Comp (Pt : Type) (ℓ : ℕ) :=
  SM.AdversaryComp (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)

variable {Pt : Type} [DecidableEq Pt] [Zero Pt]

/-- Wire byte representation `ser ‖ tagBytes tag` of a Fig. 8 ciphertext. -/
def toWire (c : Fig8C Pt) : List (BitVec 8) := c.2.2.1.1 ++ tagBytes c.2.2.1.2

/-! ### Spurious-step error terms -/

/-- Spurious DH step of `P` on an evicted honest ratchet key `T_old = dh y base`, viewed as a PRG in
`P`'s sending secret `x`: the eager step `σ = (rootKdf rk (encPt (dh x curCkaMsg))).1` followed by
the receiving half-step `rootKdf σ (encPt (dh x T_old))`. -/
def evictedKeySpuriousStepPrg (F : ShaState → List (BitVec 8) → ShaState) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (rk : Ratchet.RootKey) (curCkaMsg : Pt) (y : BitVec 256) :
    PRGScheme (BitVec 256) (Ratchet.RootKey × BitVec 256) :=
  ⟨fun x =>
    rootKdf F (rootKdf F rk (encPt (Dh.dh x curCkaMsg))).1 (encPt (Dh.dh x (Dh.dh y Dh.base)))⟩

/-- Fixed test checking whether wire `(ser, tag)` verifies at chain counter `c` (with `salt` and
identity keys `ids`) on the chain initialized from `rk.2`. -/
def wireMacVerifiesTest (F : ShaState → List (BitVec 8) → ShaState) (c : ℕ) (salt : Salt) (ids : SerializedIdentityKeys)
    (ser : List (BitVec 8)) (tag : BitVec 64) :
    PRGScheme.PRGAdversary (Ratchet.RootKey × BitVec 256) :=
  fun rk =>
    let ck := (List.range c).foldl (fun k _ => (hmacPRF F).tag k chainKeySeed) rk.2
    let mk := deriveMessageKeys F salt (chainHmac F ck messageKeySeed)
    return ((hmacScheme F).tag mk.2 (ids.toList ++ ser) == tag)

/-- Worst-case root-KDF regularity unit for a spurious DH step on an evicted honest epoch: the
supremum over public root key `rk`, current CKA message `curCkaMsg`, honest ratchet secret `y`, and
fixed MAC test `wireMacVerifiesTest F c salt ids ser tag` (`c < 2 ^ 32`, `ser.length < 2 ^ 32`, as
in `macForgeryProb`; DEV-LS23) of the PRG advantage of `evictedKeySpuriousStepPrg` in `x` plus the
ideal acceptance probability of that test.

Smallness of this unit is a non-standard trust assumption justified only in the random-oracle model
(not implied by HMAC PRF security, `rootPRNG`, or DDH): HKDF-SHA256 must extract under a worst-case
public salt `rk` from the `x`-correlated clamped-X25519 secrets `dh x curCkaMsg` and
`dh x (dh y base)` across a key-dependent second step. The `2 ^ 32` caps prevent the unbounded
supremum over `c` and `ser` from reaching `1`. -/
noncomputable def rootKdfSpuriousStepUnit (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) : ℝ≥0∞ :=
  ⨆ (rk : Ratchet.RootKey) (curCkaMsg : Pt) (y : BitVec 256) (c : ℕ) (_ : c < 2 ^ 32)
    (salt : Salt) (ids : SerializedIdentityKeys) (ser : List (BitVec 8)) (_ : ser.length < 2 ^ 32)
    (tag : BitVec 64),
    ((evictedKeySpuriousStepPrg F encPt Dh rk curCkaMsg y).prgAdvantage (wireMacVerifiesTest F c salt ids ser tag) +
      𝒟[PRGScheme.prgIdealExperiment (wireMacVerifiesTest F c salt ids ser tag)] {true})

/-- Spurious-step error bound `(q * qep) * rootKdfSpuriousStepUnit F encPt Dh` over at most `q * qep`
`(wire, eager key)` pairs.

**DEV-LS11 (libsignal): spurious DH steps on honest messages of evicted epochs.** ACD19 Fig. 8
accepts honest messages from any old epoch, whereas libsignal evicts old chains and runs a fresh DH
step on the old ratchet key whose MAC check fails with high probability. `sim` returns `rejected`;
this term bounds the probability that libsignal accepts instead over `c < 2 ^ 32` and
`ser.length < 2 ^ 32` (DEV-LS23). -/
noncomputable def spuriousStepTerm (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) (q qep : ℕ) : ℝ≥0∞ :=
  (q * qep : ℕ) * rootKdfSpuriousStepUnit F encPt Dh

/-- Point-generalized spurious DH step of `P` on an on-curve ratchet point `T : Pt`, viewed as a PRG
in `P`'s sending secret `x` (`evictedKeySpuriousStepPrg` is the case `T = Dh.dh y Dh.base`). -/
def pointSpuriousStepPrg (F : ShaState → List (BitVec 8) → ShaState) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (rk : Ratchet.RootKey) (curCkaMsg T : Pt) :
    PRGScheme (BitVec 256) (Ratchet.RootKey × BitVec 256) :=
  ⟨fun x => rootKdf F (rootKdf F rk (encPt (Dh.dh x curCkaMsg))).1 (encPt (Dh.dh x T))⟩

/-- Worst-case root-KDF regularity unit for a forged epoch start: as in `rootKdfSpuriousStepUnit`,
taking the supremum over public root key `rk`, non-zero points `curCkaMsg, T : {P : Pt // P ≠ 0}`
(`calculate_agreement` rejects `0`), and `wireMacVerifiesTest` with `c < 2 ^ 32` and
`ser.length < 2 ^ 32` of the PRG advantage of `pointSpuriousStepPrg` plus the ideal test
probability. Smallness is a random-oracle-only statistical-extractor assumption on HKDF-SHA256 for
adversary-chosen `T ≠ 0`. -/
noncomputable def rootKdfForgedEpochStartUnit (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) : ℝ≥0∞ :=
  ⨆ (rk : Ratchet.RootKey) (curCkaMsg : {P : Pt // P ≠ 0})
    (T : {P : Pt // P ≠ 0}) (c : ℕ) (_ : c < 2 ^ 32) (salt : Salt) (ids : SerializedIdentityKeys)
    (ser : List (BitVec 8)) (_ : ser.length < 2 ^ 32) (tag : BitVec 64),
    ((pointSpuriousStepPrg F encPt Dh rk curCkaMsg.1 T.1).prgAdvantage (wireMacVerifiesTest F c salt ids ser tag) +
      𝒟[PRGScheme.prgIdealExperiment (wireMacVerifiesTest F c salt ids ser tag)] {true})

/-- Point-generalized spurious-step error bound `q * rootKdfForgedEpochStartUnit F encPt Dh` over at
most `q` `(wire, eager key)` pairs.

**DEV-LS12 (libsignal): libsignal accepts a forged epoch start inside the window.** ACD19 Def. 7 (E)
and Fig. 8 reject `t > t_P + 1`, whereas after an eager step (DEV-LS1) libsignal holds `P`'s next
sending key and accepts an unseen ratchet key at `t_P + 2`. `sim` rejects it; the session bound
charges `2 * forgedEpochStartSpuriousStepTerm` for an unknown ratchet key inside a window (between
an accepted epoch start and `P`'s next send) plus one extra `fig8ShortBound` copy (via
`Thm1.challSim`) while Bob's signed pre-key chain is unknown. -/
noncomputable def forgedEpochStartSpuriousStepTerm (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) (q : ℕ) : ℝ≥0∞ :=
  (q : ℝ≥0∞) * rootKdfForgedEpochStartUnit F encPt Dh

/-! ### Root-KDF PRG view -/

/-- Single root-KDF step on fixed input `ikm`, viewed as a PRG in the root key. -/
def rootKdfAsPrg (F : ShaState → List (BitVec 8) → ShaState) (ikm : List (BitVec 8)) :
    PRGScheme Ratchet.RootKey (Ratchet.RootKey × BitVec 256) :=
  ⟨fun σ => rootKdf F σ ikm⟩

end LibsignalSim
end Ratchet
end CryptoGames
