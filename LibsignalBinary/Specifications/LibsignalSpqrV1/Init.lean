/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model

/-!
# SPQR V1: initial state (`spqrV1Init`) and session instances

**Trusted: definitions used by the statement.** `SpqrModel.spqr` (`LibsignalTripleRatchet.lean`)
sets `Spqr.init` to the empty state of `spqr::Version::V0`, whereas libsignal initializes SPQR with
`version = V1` and `min_version = V1` (`rust/protocol/src/ratchet.rs:83–89, 146–152`). This file
defines libsignal's V1 initial state (`spqrV1Init`) and the resulting `Spqr` instances
(`spqrV1Session` and `spqrV1SessionUniformCoins`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open CryptoGames.LibsignalSession (Spqr SpqrDirection ShaCompress)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)

/-- Converts the session model's `SpqrDirection` to `spqr::Direction`. -/
def Direction.ofSpqrDirection : SpqrDirection → Direction
  | .a2b => .a2b
  | .b2a => .b2a

/-- `spqr_chain_params(self_connection)` (`rust/protocol/src/ratchet.rs:27–38`). -/
def libsignalChainParams (selfSession : Bool) : ChainParams :=
  { maxJump := if selfSession then BitVec.allOnes 32 else 25000#32, maxOooKeys := 2000#32 }

theorem libsignalChainParams_false : libsignalChainParams false = ChainParams.default := rfl

/-- `spqr::Params` passed by libsignal's session constructors (`ratchet.rs:83–89, 146–152`). -/
def libsignalSpqrParams (selfSession : Bool) (dir : SpqrDirection) (k : BitVec 256) : Params where
  direction := Direction.ofSpqrDirection dir
  version := .v1
  minVersion := .v1
  authKey := CryptoGames.HMAC.keyToBytes32 k
  chainParams := libsignalChainParams selfSession

/-- V1 initial SPQR state for a non-self libsignal session (`spqr::initial_state`,
`spqr/src/lib.rs:211–235`), falling back to `[]` only on unreachable `init_inner` errors. -/
def spqrV1InitialStateFor (D : SpqrApiDeps) (dir : SpqrDirection) (k : BitVec 256) : List (BitVec 8) :=
  match initialState D (libsignalSpqrParams false dir k) with
  | .ok st => st
  | .error _ => []

/-- `spqrV1InitialStateFor` instantiated at `spqrDeps F K`. -/
def spqrV1Init (F : ShaCompress) (K : MlKem) (dir : SpqrDirection) (k : BitVec 256) :
    List (BitVec 8) :=
  spqrV1InitialStateFor (spqrDeps F K) dir k

/-- `SpqrModel.spqr S` with `init` overriding the default V0 empty state. -/
def _root_.CryptoVerification.LibsignalTripleRatchet.SpqrModel.spqrWith (S : SpqrModel)
    (init : SpqrDirection → BitVec 256 → List (BitVec 8)) :
    Spqr (List (BitVec 8)) (List (BitVec 8)) :=
  ⟨init, S.send, S.recv, S.sendPanics, S.recvPanics⟩

/-- SPQR V1 `Spqr` session instance using `spqrV1Init F K`. -/
def spqrV1Session (F : ShaCompress) (K : MlKem) : Spqr (List (BitVec 8)) (List (BitVec 8)) :=
  (spqrV1 F K).spqrWith (spqrV1Init F K)

theorem spqrV1Session_init (F : ShaCompress) (K : MlKem) :
    (spqrV1Session F K).init = spqrV1Init F K := rfl

/-! ## Uniform coins: `spqrV1SessionUniformCoins` -/

/-- Little-endian 64-byte view of `r : BitVec 512` (`toLEBytes 64 r`). -/
abbrev coinBytes (r : BitVec 512) : List (BitVec 8) :=
  CryptoVerification.LibsignalAesCbc.toLEBytes 64 r

/-- SPQR V1 `Spqr` session instance parameterized by uniform 512-bit coins (`coinBytes r`),
which suffice for every `States.send` branch (`generate` reads 64 bytes, `encaps1` reads 32). -/
def spqrV1SessionUniformCoins (F : ShaCompress) (K : MlKem) : Spqr (List (BitVec 8)) (BitVec 512) :=
  ⟨spqrV1Init F K, fun st r => (spqrV1 F K).send st (coinBytes r), (spqrV1 F K).recv,
    fun st r => (spqrV1 F K).sendPanics st (coinBytes r), (spqrV1 F K).recvPanics⟩

theorem spqrV1SessionB_init (F : ShaCompress) (K : MlKem) :
    (spqrV1SessionUniformCoins F K).init = spqrV1Init F K := rfl

theorem spqrV1SessionB_send (F : ShaCompress) (K : MlKem) (st : List (BitVec 8))
    (r : BitVec 512) : (spqrV1SessionUniformCoins F K).send st r = (spqrV1Session F K).send st (coinBytes r) :=
  rfl

theorem spqrV1SessionB_recv (F : ShaCompress) (K : MlKem) :
    (spqrV1SessionUniformCoins F K).recv = (spqrV1Session F K).recv := rfl

theorem coinBytes_length (r : BitVec 512) : (coinBytes r).length = 64 := by
  simp [coinBytes, CryptoVerification.LibsignalAesCbc.toLEBytes]

end CryptoVerification.LibsignalSpqrV1
