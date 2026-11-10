/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.Proofs.SpecLemmas.LeakableSecretProofDefs

/-!
# Shadow-Turn Record Projection and Typed Bundle Predicates

Defines the responder-quarantine projection `CliTurn.leakRecords`, the shadow-turn leak predicate
`KeyInDirsV1`, and compatibility predicates for typed `PublicBundle` directories and canonical
pre-key wire messages.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open DY (Participant)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup HonestBundle LeakableSecret preKeyWire ecKey PqFromHonest parsePreKeyWire)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.SignalSession (PublicBundle)

/-- Suppresses Bob's session record when `t.bobOff = true` and agrees with `t.records r`
otherwise. -/
def CliTurn.leakRecords (t : CliTurn) (r : ProtocolSetup) (p : Participant) : Option HwBytes :=
  if t.bobOff = true ∧ p = r.bob then none else t.records r p

/-- Shadow-turn leak predicate over `t.leakRecords r` and `t.opkUsed r`. -/
def KeyInDirsV1 (r : ProtocolSetup) (t : CliTurn) (k : HwBytes) : Prop :=
  LeakableSecret r (t.leakRecords r) (t.opkUsed r) k

theorem CliTurn.leakRecords_eq_records_of_bobOff_false {t : CliTurn} {r : ProtocolSetup}
    (h : t.bobOff = false) : t.leakRecords r = t.records r := by
  funext p
  simp [CliTurn.leakRecords, h]

/-- Field-length and type-byte well-formedness predicate characterizing the image of
`publicBundleOf`. -/
def BundleTyped (b : PublicBundle) : Prop :=
  b.identityKey.length = 33 ∧ b.identityKey.head? = some 5#8 ∧
  b.signedKey.length = 33 ∧ b.signedKey.head? = some 5#8 ∧ b.signedSig.length = 64 ∧
  b.kyberKey.length = 1569 ∧ b.kyberKey.head? = some 8#8 ∧ b.kyberSig.length = 64 ∧
  ∀ id key, b.oneTime = some (id, key) → key.length = 33 ∧ key.head? = some 5#8

/-- Typed `PublicBundle` whose serialized `bundleBlob` satisfies `HonestBundle`. -/
def HonestBundleDir (interp : ExternInterpretation) (r : ProtocolSetup) (b : PublicBundle) : Prop :=
  BundleTyped b ∧ HonestBundle interp r (bundleBlob b)

/-- Canonical pre-key wire encoding built from 32-byte EC keys and a 1568-byte Kyber ciphertext. -/
def CanonicalPreKey (b : HwBytes) : Prop :=
  ∃ (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes),
    ik.length = 32 ∧ ek.length = 32 ∧ ct.length = 1568 ∧
    b = preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg

theorem canonicalPreKey_head_ne_whisper {b : HwBytes} (h : CanonicalPreKey b) :
    b.head? ≠ some wireWhisperTag := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
  unfold preKeyWire
  simp only [List.head?_cons, ne_eq, Option.some.injEq]
  decide

end DY.Libsignal.Composed.Refinement.Cli
