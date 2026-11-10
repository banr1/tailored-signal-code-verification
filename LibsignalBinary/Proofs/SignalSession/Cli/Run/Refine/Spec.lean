/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunRel
public import LibsignalBinary.Specifications.SignalSession.PqDir
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.SmDirProofDefs

/-!
# Per-Slot Model-Agreement Predicates for `RunSem`

Defines the `Outcome`-level agreement predicates (`RunSemOkPq` and `RunSemOkSm`) relating each
callee slot of `S : RunSem` (`initiate`, `encrypt`, `decryptSignal`, `pksmParse`, `decryptPrekey`)
to the PQXDH (`CliSpecPqxdh`) and Signal-Message (`CliSpecE`) protocol models on domain inputs.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunRefine

open Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose

/-- Session-API `AddrVal` of party `P` (UUID bytes and device ID `1`). -/
def addrValE (P : Party) : AddrVal := ⟨utf8 (partyAddressName P), 1#8⟩

/-! ## PQXDH directories (`CliSpecPqxdh`) -/

/-- Agreement between `S.initiate` and `pqInitModel` on PQXDH `init` inputs. -/
def PqInitiateAgrees (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams) : Prop :=
  ∀ (st : PqParty) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) (bv : BundleV),
    PqxdhPartyInSpecDomain W st → st.session = none →
    readBundleV (runFiles (pqInitInputs W st b t)) (bytesOfString bundleDir) 1#8 = some bv →
    observe (pqInitInputs W st b t).files
        (finish (S.initiate (runFiles (pqInitInputs W st b t)) (addrValE st.party.other)
          (addrValE st.party) bv t.toList) (fun _ => [])) =
      pqxdhExpectedOutcome W (pqInitInputs W st b t) (pqInitModel X W st b t)

/-- Agreement between `S.encrypt` and `pqSendModel` on PQXDH `send` inputs. -/
def PqEncryptAgrees (S : RunSem) (W : PEParams) : Prop :=
  ∀ (st : PqParty) (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64),
    PqxdhPartyInSpecDomain W st → m.length < 2 ^ 32 →
    observe (pqSendInputs W st m r).files
        (finish (S.encrypt (runFiles (pqSendInputs W st m r)) (addrValE st.party.other)
          (addrValE st.party) m r.toList) ctWire) =
      pqxdhExpectedOutcome W (pqSendInputs W st m r) (pqSendModel W st m r.toList)

/-- Agreement between `S.decryptSignal` and `pqRecvWhisperModel` on PQXDH `2 ‖ c` inputs. -/
def PqDecryptSignalAgrees (S : RunSem) (W : PEParams) : Prop :=
  ∀ (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) (msg : SignalMessage),
    PqxdhPartyInSpecDomain W st → c.length < 2 ^ 32 → SignalMessage.tryFrom protoSignalCodec c = .ok msg →
    observe (pqRecvInputs W st (wireWhisper :: c) rc).files
        (finish (S.decryptSignal (runFiles (pqRecvInputs W st (wireWhisper :: c) rc))
          (addrValE st.party.other) (addrValE st.party) msg (HMAC.keyToBytes32 rc)) id) =
      pqxdhExpectedOutcome W (pqRecvInputs W st (wireWhisper :: c) rc) (pqRecvWhisperModel W st c rc)

/-- `S.pksmParse` on typed `PreKeyMessageFields` returns `none` only when `m.inner` fails
`SignalMessage.tryFrom`. -/
def PksmParseAgrees (S : RunSem) : Prop :=
  ∀ m : PreKeyMessageFields, m.inner.length + 2048 < 2 ^ 32 → S.pksmParse m.bytes = none →
    ∀ inner : SignalMessage, SignalMessage.tryFrom protoSignalCodec m.inner ≠ .ok inner

/-- Agreement between `S.decryptPrekey` and `pqRecvPrekeyModel` on PQXDH `3 ‖ m.bytes` inputs. -/
def PqDecryptPrekeyAgrees (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams) : Prop :=
  ∀ (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256) (pm : PreKeySignalMessage),
    PqxdhPartyInSpecDomain W st → m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    S.pksmParse m.bytes = some pm →
    observe (pqRecvInputs W st (wirePrekey :: m.bytes) rc).files
        (finish (S.decryptPrekey (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
          (addrValE st.party.other) (addrValE st.party) pm (HMAC.keyToBytes32 rc)) id) =
      pqxdhExpectedOutcome W (pqRecvInputs W st (wirePrekey :: m.bytes) rc) (pqRecvPrekeyModel X W st m rc)

/-- Bundled PQXDH slot-agreement predicates for `S : RunSem`. -/
structure RunSemOkPq (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams) : Prop where
  initiate : PqInitiateAgrees S X W
  encrypt : PqEncryptAgrees S W
  decryptSignal : PqDecryptSignalAgrees S W
  pksmParse : PksmParseAgrees S
  decryptPrekey : PqDecryptPrekeyAgrees S X W

/-! ## Signal-Message directories (`CliSpecE`) -/

/-- Agreement between `S.encrypt` and `smSendModel` on reachable Signal-Message states. -/
def SmEncryptAgrees (S : RunSem) (C : Crypto) : Prop :=
  ∀ (g : GhostState (List (BitVec 8))) (m : List (BitVec 8)),
    Reach (spqrOffSessionParams C) g → m.length < 2 ^ 32 →
    observe (smSendInputs g m).files
        (finish (S.encrypt (runFiles (smSendInputs g m)) (addrValE g.party.other)
          (addrValE g.party) m []) ctWire) =
      observe (smSendInputs g m).files (smSendModel C g m)

/-- Agreement between `S.decryptSignal` and `smRecvModel` on reachable Signal-Message `2 ‖ c` inputs. -/
def SmDecryptSignalAgrees (S : RunSem) (C : Crypto) : Prop :=
  ∀ (g : GhostState (List (BitVec 8))) (c : List (BitVec 8)) (rc : BitVec 256) (msg : SignalMessage),
    Reach (spqrOffSessionParams C) g → c.length < 2 ^ 32 → SignalMessage.tryFrom protoSignalCodec c = .ok msg →
    observe (smRecvInputs g c rc).files
        (finish (S.decryptSignal (runFiles (smRecvInputs g c rc)) (addrValE g.party.other)
          (addrValE g.party) msg (HMAC.keyToBytes32 rc)) id) =
      observe (smRecvInputs g c rc).files (smRecvModel C g c rc)

/-- Bundled Signal-Message slot-agreement predicates for `S : RunSem`. -/
structure RunSemOkSm (S : RunSem) (C : Crypto) : Prop where
  encrypt : SmEncryptAgrees S C
  decryptSignal : SmDecryptSignalAgrees S C

end CryptoVerification.SignalSession.Cli.RunRefine
