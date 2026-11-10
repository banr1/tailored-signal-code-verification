/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Spec

/-!
# Canonical `PreKeySignalMessage::try_from` Semantics on Well-Formed Wire Bytes

Defines `PksmCanonical S`—stating that `S.pksmParse` agrees with `pksmCanon` on well-formed
`PreKeySignalMessage` protobuf encodings—and derives `PksmParseAgrees S` together with the exact
`pksmParse_bytes_iff` characterization on typed `PreKeyMessageFields`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunRefine

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.E2E.Pqxdh.ResponderWire

/-- Canonical `PreKeySignalMessage::try_from` result on well-formed wire bytes `x.bytes`:
`some (x.toModel i)` if `x.inner` parses to `i : SignalMessage`, and `none` otherwise. -/
def pksmCanon (x : PreKeyTryFromArgs) : Option PreKeySignalMessage :=
  match SignalMessage.tryFrom protoSignalCodec x.inner with
  | .ok i => some (x.toModel i)
  | .error _ => none

/-- `S.pksmParse` agrees with `pksmCanon` on every well-formed `PreKeyTryFromArgs` with
`x.inner.length + 2048 < 2^32`. -/
def PksmCanonical (S : RunSem) : Prop :=
  ∀ x : PreKeyTryFromArgs, x.inner.length + 2048 < 2 ^ 32 → S.pksmParse x.bytes = pksmCanon x

def argsOf (m : PreKeyMessageFields) : PreKeyTryFromArgs :=
  { ptr := 0, sret := 0, regId := m.regId, opkId := m.opkId, spkId := m.spkId, kpkId := m.kpkId,
    kyberCt := m.kyberCt, baseKey := m.baseKey, idPub := m.idPub, inner := m.inner }

theorem argsOf_bytes (m : PreKeyMessageFields) : (argsOf m).bytes = m.bytes := by
  rfl

theorem pksmParseAgrees_of_canonical {S : RunSem} (h : PksmCanonical S) : PksmParseAgrees S := by
  intro m hm hnone inner hok
  have hinner : (argsOf m).inner = m.inner := rfl
  rw [← argsOf_bytes m, h (argsOf m) hm] at hnone
  unfold pksmCanon at hnone
  rw [hinner, hok] at hnone
  nomatch hnone

/-- Characterizes `S.pksmParse m.bytes = some pm` on typed `PreKeyMessageFields` under `PksmCanonical S`. -/
theorem pksmParse_bytes_iff {S : RunSem} (h : PksmCanonical S) (m : PreKeyMessageFields)
    (hm : m.inner.length + 2048 < 2 ^ 32) (pm : PreKeySignalMessage) :
    S.pksmParse m.bytes = some pm ↔
      ∃ i : SignalMessage, SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
        pm = (argsOf m).toModel i := by
  have hinner : (argsOf m).inner = m.inner := rfl
  rw [← argsOf_bytes m, h (argsOf m) hm]
  unfold pksmCanon
  rw [hinner]
  cases SignalMessage.tryFrom protoSignalCodec m.inner with
  | ok i =>
    constructor
    · intro hsome
      exact ⟨i, rfl, (Option.some.inj hsome).symm⟩
    · rintro ⟨i', hi', rfl⟩
      cases hi'
      rfl
  | error _ =>
    constructor
    · intro hsome
      nomatch hsome
    · rintro ⟨_, hi, _⟩
      nomatch hi

end CryptoVerification.SignalSession.Cli.RunRefine
