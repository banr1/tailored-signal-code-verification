/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bundle

/-!
# Outcome Refinement of `runAns` Against `CliSpecPqxdh` and `CliSpecE`

Proves that on every domain input of `CliSpecPqxdh` (`init`, `send`, whisper `recv`, pre-key
`recv`) and `CliSpecE` (`send`, `recv`), `observe i.files (RunCompose.runAns S i)` matches the
protocol model whenever `S` satisfies the per-slot agreement predicates (`Refine/Spec.lean`).
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

/-! ## PQXDH directory transitions (`CliSpecPqxdh`) -/

/-- PQXDH `init` refinement on a party with no session, typed bundle `b`, and randomness tape `t`. -/
theorem runAns_pqInit (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams) (hS : PqInitiateAgrees S X W)
    (st : PqParty) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen)
    (hst : PqxdhPartyInSpecDomain W st) (hnone : st.session = none) :
    observe (pqInitInputs W st b t).files (runAns S (pqInitInputs W st b t)) =
      pqxdhExpectedOutcome W (pqInitInputs W st b t) (pqInitModel X W st b t) := by
  rw [runAns_pqInit_eq, readBundleV_pqInit]
  exact hS st b t (bundleVE b) hst hnone (readBundleV_pqInit W st b t)

/-- PQXDH `send` refinement for plaintext below `2^32` bytes and 64-byte randomness `r`. -/
theorem runAns_pqSend (S : RunSem) (W : PEParams) (hS : PqEncryptAgrees S W)
    (st : PqParty) (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64)
    (hst : PqxdhPartyInSpecDomain W st) (hm : m.length < 2 ^ 32) :
    observe (pqSendInputs W st m r).files (runAns S (pqSendInputs W st m r)) =
      pqxdhExpectedOutcome W (pqSendInputs W st m r) (pqSendModel W st m r.toList) := by
  rw [runAns_pqSend_eq]
  exact hS st m r hst hm

/-- PQXDH `recv` refinement on whisper wire input `2 ‖ c` (`c.length < 2^32`). -/
theorem runAns_pqRecvWhisper (S : RunSem) (W : PEParams) (hS : PqDecryptSignalAgrees S W)
    (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256)
    (hst : PqxdhPartyInSpecDomain W st) (hc : c.length < 2 ^ 32) :
    observe (pqRecvInputs W st (wireWhisper :: c) rc).files
        (runAns S (pqRecvInputs W st (wireWhisper :: c) rc)) =
      pqxdhExpectedOutcome W (pqRecvInputs W st (wireWhisper :: c) rc) (pqRecvWhisperModel W st c rc) := by
  rw [runAns_pqRecvWhisper_eq]
  cases h : SignalMessage.tryFrom protoSignalCodec c with
  | ok msg => exact hS st c rc msg hst hc h
  | error _ =>
    unfold pqRecvWhisperModel pqxdhExpectedOutcome
    rcases st.session with _ | ⟨_, _⟩
    · rfl
    · rw [h]; rfl

/-- PQXDH `recv` refinement on pre-key wire input `3 ‖ m.bytes` when no session or a matching session is stored. -/
theorem runAns_pqRecvPrekey (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hP : PksmParseAgrees S) (hS : PqDecryptPrekeyAgrees S X W)
    (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
    (hst : PqxdhPartyInSpecDomain W st) (hm : m.inner.length + 2048 < 2 ^ 32)
    (hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m) :
    observe (pqRecvInputs W st (wirePrekey :: m.bytes) rc).files
        (runAns S (pqRecvInputs W st (wirePrekey :: m.bytes) rc)) =
      pqxdhExpectedOutcome W (pqRecvInputs W st (wirePrekey :: m.bytes) rc) (pqRecvPrekeyModel X W st m rc) := by
  rw [runAns_pqRecvPrekey_eq]
  cases hp : S.pksmParse m.bytes with
  | some pm => exact hS st m rc pm hst hm hmatch hp
  | none =>
    unfold pqRecvPrekeyModel pqxdhExpectedOutcome
    cases hi : SignalMessage.tryFrom protoSignalCodec m.inner with
    | error _ => rfl
    | ok inner => exact absurd hi (hP m hm hp inner)

/-! ## Signal-Message directory transitions (`CliSpecE`) -/

/-- Signal-Message `send` refinement on a reachable state and plaintext below `2^32` bytes. -/
theorem runAns_smSend (S : RunSem) (C : Crypto) (hS : SmEncryptAgrees S C)
    (g : GhostState (List (BitVec 8))) (m : List (BitVec 8))
    (hg : Reach (spqrOffSessionParams C) g) (hm : m.length < 2 ^ 32) :
    observe (smSendInputs g m).files (runAns S (smSendInputs g m)) =
      observe (smSendInputs g m).files (smSendModel C g m) := by
  rw [runAns_smSend_eq]
  exact hS g m hg hm

/-- Signal-Message `recv` refinement on a reachable state and whisper wire input `2 ‖ c` (`c.length < 2^32`). -/
theorem runAns_smRecv (S : RunSem) (C : Crypto) (hS : SmDecryptSignalAgrees S C)
    (g : GhostState (List (BitVec 8))) (c : List (BitVec 8)) (rc : BitVec 256)
    (hg : Reach (spqrOffSessionParams C) g) (hc : c.length < 2 ^ 32) :
    observe (smRecvInputs g c rc).files (runAns S (smRecvInputs g c rc)) =
      observe (smRecvInputs g c rc).files (smRecvModel C g c rc) := by
  rw [runAns_smRecv_eq]
  cases h : SignalMessage.tryFrom protoSignalCodec c with
  | ok msg => exact hS g c rc msg hg hc h
  | error e =>
    have h' : SignalMessage.tryFrom (spqrOffSessionParams C).codec c = .error e := h
    unfold smRecvModel recvModelSpqrOff
    rw [h']
    rfl

end CryptoVerification.SignalSession.Cli.RunRefine
