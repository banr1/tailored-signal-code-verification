/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM
public import Computational.Proofs.CryptoGames.AEAD.WireAeadProofDefs

/-!
# Restricted wire round-trip and SPQR hypotheses

**Checked by Lean.**

Defines prost's version-4 wire round-trip and length bounds (`SignalRoundTripShort`,
`SignalEncodeFits32`, `LengthsOk`) together with the idealized and reachable-state SPQR correctness
hypotheses (`SpqrOffCorrect`, `SpqrSendTotalReachable`, `SpqrRecvSaltFixed`).
-/

@[expose] public section

namespace CryptoGames
namespace LibsignalSession

open LibsignalAead

/-- Rust slice byte-length bound `2 ^ 63`. -/
def rustLenBound : ℕ := 2 ^ 63

/-- Version-4 `(header, body)` pairs with `pqRatchet`, `addresses`, and `body` shorter than
`rustLenBound`. -/
def SignalWireShort (h : SignalHeader) (body : List (BitVec 8)) : Prop :=
  h.messageVersion = currentVersion ∧ h.pqRatchet.length < rustLenBound ∧
    (∀ a, h.addresses = some a → a.length < rustLenBound) ∧ body.length < rustLenBound

/-- Wire codec round-trip restricted to `SignalWireShort`. -/
def SignalRoundTripShort (codec : SignalMessageProtoCodec) : Prop :=
  (signalWireCodec codec).RoundTripOn SignalWireShort

/-- Encoded wire plus 8-byte MAC tag has byte length `< 2 ^ 32` for short fields and body. -/
def SignalEncodeFits32 (codec : SignalMessageProtoCodec) : Prop :=
  ∀ h body, h.pqRatchet.length < 2 ^ 29 →
    (∀ a, h.addresses = some a → a.length < 2 ^ 29) →
    body.length < 2 ^ 31 + 16 →
    ((signalWireCodec codec).encode h body).length + 8 < 2 ^ 32

/-- **DEV-LS21 (libsignal): prost's codec and a restricted round trip.** Session wire-length bounds
(`ℓ + 16 < 2 ^ 31 + 16`, SPQR messages `< 2 ^ 29`, and address blobs `< 2 ^ 29`) ensuring every
honest message satisfies `SignalWireShort` and fits the `< 2 ^ 32`-byte wire domain. -/
def LengthsOk {PQ PQC : Type} (P : Params PQ PQC) (ℓ : ℕ) : Prop :=
  ℓ + 16 < 2 ^ 31 + 16 ∧
    (∀ st rq st' salt msg, P.spqr.send st rq = some (st', salt, msg) →
      msg.length < 2 ^ 29) ∧
    (∀ a, P.addrAB = some a → a.length < 2 ^ 29) ∧
    (∀ a, P.addrBA = some a → a.length < 2 ^ 29)

end LibsignalSession

/-! ## SPQR hypotheses -/

namespace LibsignalSM.Corr

open LibsignalSession

variable {PQ PQC : Type}

/-- **DEV-LS24 (libsignal): SPQR is abstract, carries no claim, and its correctness is idealized.**
Idealized SPQR correctness assuming `send` is total, every receiver state accepts every sent
message with the sender's salt, and neither `send` nor `recv` panics. -/
def SpqrOffCorrect (S : Spqr PQ PQC) : Prop :=
  (∀ st r, (S.send st r).isSome) ∧
  (∀ st r st' salt msg, S.send st r = some (st', salt, msg) →
    ∀ st₂, ∃ st₂', S.recv st₂ msg = .ok (st₂', salt)) ∧
  (∀ st r, S.sendPanics st r = false) ∧ (∀ st msg, S.recvPanics st msg = false)

/-- SPQR states reachable from `init` in at most `n` successful `send` or `recv` steps. -/
inductive SpqrReachIn (S : Spqr PQ PQC) : ℕ → PQ → Prop
  | init (n : ℕ) (d : SpqrDirection) (k : BitVec 256) : SpqrReachIn S n (S.init d k)
  | send {n : ℕ} {st st' : PQ} {r : PQC} {salt : HKDF.Salt} {msg : List (BitVec 8)} :
      SpqrReachIn S n st → S.send st r = some (st', salt, msg) → SpqrReachIn S (n + 1) st'
  | recv {n : ℕ} {st st' : PQ} {msg : List (BitVec 8)} {salt : HKDF.Salt} :
      SpqrReachIn S n st → S.recv st msg = .ok (st', salt) → SpqrReachIn S (n + 1) st'

/-- `S.send` succeeds without panicking on every state reachable in `< 2 ^ 32 - 1` steps. -/
def SpqrSendTotalReachable (S : Spqr PQ PQC) : Prop :=
  ∀ n st, n + 1 < 2 ^ 32 → SpqrReachIn S n st →
    ∀ r, (S.send st r).isSome ∧ S.sendPanics st r = false

/-- Reflexive-transitive closure of successful `send` and `recv` transitions from `st₀`. -/
inductive SpqrReachFrom (S : Spqr PQ PQC) : PQ → PQ → Prop
  | refl (st : PQ) : SpqrReachFrom S st st
  | send {st₀ st st' : PQ} {r : PQC} {salt : HKDF.Salt} {msg : List (BitVec 8)} :
      SpqrReachFrom S st₀ st → S.send st r = some (st', salt, msg) → SpqrReachFrom S st₀ st'
  | recv {st₀ st st' : PQ} {msg : List (BitVec 8)} {salt : HKDF.Salt} :
      SpqrReachFrom S st₀ st → S.recv st msg = .ok (st', salt) → SpqrReachFrom S st₀ st'

/-- Link-fixed receive salt: any reachable `recv` success witnesses a link predicate `linkPresent`
that fixes the returned salt across all subsequent reachable states. -/
def SpqrRecvSaltFixed (S : Spqr PQ PQC) : Prop :=
  ∃ (linkPresent : PQ → List (BitVec 8) → Prop)
    (evalSalt : PQ → List (BitVec 8) → HKDF.Salt),
    (∀ n st st' msg salt, SpqrReachIn S n st →
      S.recv st msg = .ok (st', salt) → linkPresent st msg) ∧
    (∀ st st' st'' msg salt, SpqrReachFrom S st st' → linkPresent st msg →
      S.recv st' msg = .ok (st'', salt) → salt = evalSalt st msg)

end LibsignalSM.Corr
end CryptoGames
