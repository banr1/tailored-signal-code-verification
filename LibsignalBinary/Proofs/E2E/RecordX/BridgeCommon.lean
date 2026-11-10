/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.StateXModel
public import LibsignalBinary.Proofs.E2E.Record.Support.Phi
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.StateXModelProofDefs

/-!
# Bridge from `encodeRecordUnderExtras` to `Record.encodeRecord` and `encodeRecord`

**Checked by Lean.** Relates the generalized encoder `encodeRecordUnderExtras` to the proof-side
encoder `Record.encodeRecord ∘ Record.toRecord` for arbitrary `E : Party → RecordExtras`, and to
`encodeRecord` at `E = seedRecordExtras`.
-/

@[expose] public section

namespace CryptoVerification.E2E.RecordX

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E

abbrev _root_.CryptoVerification.E2E.EParams := Crypto
abbrev _root_.CryptoGames.LibsignalSession.Crypto.C (Z : Crypto) : Crypto := Z
abbrev _root_.CryptoGames.LibsignalSession.Crypto.params (Z : Crypto) :
    Params Bytes Unit := spqrOffSessionParams Z

/-- Converts `RecordExtras` to `Record.SessionExtras`. -/
def toSessionExtras (x : RecordExtras) : Record.SessionExtras :=
  { pending := x.pending
    kyber := x.kyber
    localRegistrationId := x.localRegistrationId
    remoteRegistrationId := x.remoteRegistrationId
    aliceBaseKey := x.aliceBaseKey }

/-- Pointwise lift of `toSessionExtras` to `Party → RecordExtras`. -/
def extrasOf (E : Party → RecordExtras) : Party → Record.SessionExtras :=
  fun P => toSessionExtras (E P)

/-- `encodeRecordUnderExtras E` agrees with `Record.encodeRecord` on `Record.toRecord (extrasOf E)`. -/
theorem encodeRecordX_eq_toRecord (E : Party → RecordExtras) (g : GhostState Bytes) :
    encodeRecordUnderExtras E g = Record.encodeRecord (Record.toRecord (extrasOf E) g) := by
  unfold encodeRecordUnderExtras encStateUnderExtras Record.encodeRecord Record.toRecord Record.encSession
  dsimp only [Option.map_some]
  cases g.session.pendingPreKey <;> rfl

theorem extrasOf_extrasSeed : extrasOf seedRecordExtras = Record.extrasM := rfl

/-- `encodeRecordUnderExtras seedRecordExtras` specializes to `encodeRecord`. -/
theorem encodeRecordX_extrasSeed (g : GhostState Bytes) :
    encodeRecordUnderExtras seedRecordExtras g = encodeRecord g := by
  rw [encodeRecordX_eq_toRecord, extrasOf_extrasSeed, Reach.encodeRecord_eq_toRecord]

theorem encodeRecordX_extrasSeed_fun : encodeRecordUnderExtras seedRecordExtras = encodeRecord :=
  funext encodeRecordX_extrasSeed

end CryptoVerification.E2E.RecordX
