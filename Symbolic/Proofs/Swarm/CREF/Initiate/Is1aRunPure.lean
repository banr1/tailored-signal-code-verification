/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ProofHubsPure
import Symbolic.Proofs.Swarm.SHARED.StateSizePure

/-!
# Initial SPQR State Model and Encoded Size Bounds

Defines `initHdrDecoder`, `initV1State`, and `is1StateRaw` for `spqr::initial_state` and bounds
the encoded byte length of `is1StateRaw`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1

/-- Initial 96-byte header+MAC `PolyDecoder` constructed by `States.init_b`. -/
def initHdrDecoder : PolyDecoder :=
  { ptsNeeded := 48
    isComplete := false
    pts := List.replicate 16 (SortedSetPt.withCapacity 0) }

/-- Initial V1 `States` constructed by `States.init_a` (`.a2b`) or `States.init_b` (`.b2a`). -/
def initV1State (F : ShaCompress) (d : Direction) (authKey : List (BitVec 8)) :
    States spqrPolyApi (spqrAuthApi F) :=
  match d with
  | .a2b =>
    .keysUnsampled { uc := { epoch := 1#64, auth := Authenticator.new F authKey 1#64 } }
  | .b2a =>
    .noHeaderReceived
      { uc := { epoch := 1#64, auth := Authenticator.new F authKey 1#64 }
        receiving_hdr := initHdrDecoder }

@[simp]
theorem states_init_a_eq_ok (F : ShaCompress) (authKey : List (BitVec 8)) :
    States.init_a spqrPolyApi (spqrAuthApi F) authKey =
      .ok (initV1State F .a2b authKey) := rfl

@[simp]
theorem states_init_b_eq_ok (F : ShaCompress) (authKey : List (BitVec 8)) :
    States.init_b spqrPolyApi (spqrAuthApi F) authKey =
      .ok (initV1State F .b2a authKey) := rfl

/-- `PqRatchetState` built by `spqr::initial_state` on V1 direction `d` and `auth_key = k`. -/
def is1StateRaw (F : ShaCompress) (d : Direction) (k : List (BitVec 8)) : PqRatchetState :=
  { versionNegotiation := some
      { authKey := k
        direction := d.toI32
        minVersion := 1#32
        chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } }
    chain := none
    inner := some (.v1 (initV1State F d k).into_pb) }

theorem is1StateRaw_rawPqState_le (F : ShaCompress) (d : Direction) (k : List (BitVec 8)) :
    CryptoVerification.SpqrV1.Top.StateSize.SymP3.rawPqState (is1StateRaw F d k) ≤ k.length + 424 := by
  have h : CryptoVerification.SpqrV1.Top.StateSize.SymP3.rawV1State (initV1State F d k).into_pb ≤ 424 := by
    cases d with
    | a2b =>
      have := (CryptoVerification.SpqrV1.Top.StateSize.SymP3.States.init_a_raw_le
        (states_init_a_eq_ok F k)).1
      omega
    | b2a =>
      exact (CryptoVerification.SpqrV1.Top.StateSize.SymP3.States.init_b_raw_le
        (states_init_b_eq_ok F k)).1
  simp only [CryptoVerification.SpqrV1.Top.StateSize.SymP3.rawPqState, is1StateRaw,
    CryptoVerification.SpqrV1.Top.StateSize.SymP3.optRaw_some,
    CryptoVerification.SpqrV1.Top.StateSize.SymP3.optRaw_none,
    CryptoVerification.SpqrV1.Top.StateSize.SymP3.rawVN,
    CryptoVerification.SpqrV1.Top.StateSize.SymP3.rawPqInner]
  omega

theorem is1StateRaw_encodeRaw_length_lt (F : ShaCompress) (d : Direction) (k : List (BitVec 8))
    (hk : k.length ≤ 2 ^ 32) :
    (PqRatchetState.encodeRaw (is1StateRaw F d k)).length < 2 ^ 63 := by
  have h := is1StateRaw_rawPqState_le F d k
  exact (CryptoVerification.SpqrV1.Top.StateSize.SymP3.encodeState_length_lt_of_rawPqState_le
    (st := is1StateRaw F d k) (by omega)).2.2.1

theorem is1StateRaw_encodeRaw_length_lt_2_32 (F : ShaCompress) (d : Direction) (k : List (BitVec 8))
    (hk : 1176 + k.length < 2 ^ 32) :
    (PqRatchetState.encodeRaw (is1StateRaw F d k)).length < 2 ^ 32 := by
  have h1 := CryptoVerification.SpqrV1.Top.StateSize.SymP3.encodeState_length_le_rawPqState
    (is1StateRaw F d k)
  have h2 := is1StateRaw_rawPqState_le F d k
  change (PqRatchetState.encodeRaw _).length ≤ _ at h1
  omega

end Symbolic.Swarm.CREF
