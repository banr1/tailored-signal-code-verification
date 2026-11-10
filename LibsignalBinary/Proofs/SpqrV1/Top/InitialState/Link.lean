/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Defs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init

/-!
# `spqr::initial_state`: Equivalence with `spqrV1Init` on Libsignal Parameters

Shows that `initialStateValue F (libsignalSpqrParams false dir k)` equals `spqrV1Init F K dir k`
(the `Spqr.init` state of `spqrV1Session F K`) for every `K`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.InitialState

open CryptoGames.LibsignalSession (ShaCompress SpqrDirection)
open CryptoVerification.LibsignalSpqrV1

/-- On `libsignalSpqrParams false dir k`, `initialStateValue F` equals `spqrV1Init F K dir k`. -/
theorem initialStateValue_libsignal (F : ShaCompress) (K : MlKem) (dir : SpqrDirection)
    (k : BitVec 256) :
    initialStateValue F (libsignalSpqrParams false dir k) = spqrV1Init F K dir k := by
  simp only [spqrV1Init, spqrV1InitialStateFor, initialState_spqrDeps_eq_ok F K]

/-- `initialStateValue_libsignal` with the `Params` record written out
(`chain_params = ChainParams.default`, `libsignalChainParams_false`). -/
theorem initialStateValue_libsignal' (F : ShaCompress) (K : MlKem) (dir : SpqrDirection)
    (k : BitVec 256) :
    initialStateValue F
        { direction := Direction.ofSpqrDirection dir, version := .v1, minVersion := .v1,
          authKey := CryptoGames.HMAC.keyToBytes32 k, chainParams := ChainParams.default } =
      spqrV1Init F K dir k :=
  initialStateValue_libsignal F K dir k

end CryptoVerification.SpqrV1.Top.InitialState
