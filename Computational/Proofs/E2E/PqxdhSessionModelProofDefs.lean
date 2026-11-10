/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhCorrectModel
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs

/-!
# PQXDH Session Model Proof Definitions

Proof-side send helpers (`sendWireAcknowledged`, `sendWireModel`) and the `PqxdhFirstMessageRoundtrip`
predicate over `PqxdhSessionModel`.
-/

@[expose] public section

set_option autoImplicit false
namespace CryptoVerification.E2E
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec

/-- Encrypts `m` on an acknowledged session using V1 SPQR (`pqxdhSpqrSession W`) and coins `r`,
returning the updated encoded record and `2 ‖ SignalMessage`. -/
def sendWireAcknowledged (W : PEParams) (x : RecordExtras) (g : GhostState Bytes) (m : Bytes)
    (r : Bytes) : Option (Option (Bytes × Bytes)) :=
  match SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).sendAddrs g.party) m r g.session with
  | (.ok msg, s) => some (some (encodeRecordUnderExtras (fun _ => x) { g with session := s },
      wireWhisper :: msg.serialized))
  | (.error .panic, _) => none
  | (.error _, _) => some none

/-- Model outcome of `send` on session `g` with extras `x` and coins `r`. -/
def sendWireModel (W : PEParams) (x : RecordExtras) (g : GhostState Bytes) (m : Bytes)
    (r : Bytes) : Option (Option (Bytes × Bytes)) :=
  if g.session.pendingPreKey then sendWirePending W x g m r else sendWireAcknowledged W x g m r

/-- First-message roundtrip for honest Alice and Bob under X25519, Kyber, and AES-256 laws and input
length bound `pt.length + 2304 < 2 ^ 32` (`DEV-PQ10`, `DEV-M1`): Alice's `init` and first `send`
produce `3 ‖ m.bytes` with `m.inner.length + 2048 < 2 ^ 32`, which Bob's pre-key receive model
decodes to `preKeyStoreEventsBytes m ++ pt`. -/
def PqxdhFirstMessageRoundtrip (X : UnreachedPqxdhPrimitives) (W : PEParams) : Prop :=
  ∀ (meA meB : LocalIdentity) (k : ResponderPreKeySecrets) (spkSig kpkSig : List.Vector (BitVec 8) 64)
    (t : List.Vector (BitVec 8) initiateTapeLen) (rs : List.Vector (BitVec 8) 64)
    (rc : BitVec 256) (pt : Bytes)
    (x : RecordExtras) (g : GhostState Bytes) (r w : Bytes),
    (∀ a b, W.C.X (Ratchet.clampScalar a) (W.C.pubKey (Ratchet.clampScalar b)) =
      W.C.X (Ratchet.clampScalar b) (W.C.pubKey (Ratchet.clampScalar a))) →
    (∀ a b, W.C.X (Ratchet.clampScalar a) (W.C.pubKey (Ratchet.clampScalar b)) ≠
      List.Vector.replicate 32 0#8) →
    (∀ coins, W.Q.decaps k.kpkSec (W.Q.encaps k.kpkPub coins).1 = (W.Q.encaps k.kpkPub coins).2) →
    (∀ a, SignalPqxdh.isCanonicalRef (modelPrims X W)
      (vecU8 (W.C.pubKey (Ratchet.clampScalar a))) = true) →
    (∀ key blk, W.C.D key (W.C.E key blk) = blk) →
    pt.length + 2304 < 2 ^ 32 →
    (honestBundle W.C meB k spkSig kpkSig).signaturesVerify X W = true →
    initiateState X W .A meA (honestBundle W.C meB k spkSig kpkSig) t = some (x, g) →
    sendWireModel W x g pt rs.toList = some (some (r, w)) →
    ∃ m : PreKeyMessageFields, w = wirePrekey :: m.bytes ∧ m.inner.length + 2048 < 2 ^ 32 ∧
      (recvPrekeyModel X W .B meB k m rc).map (Option.map Prod.snd) =
        some (some (preKeyStoreEventsBytes m ++ pt))

end CryptoVerification.E2E
