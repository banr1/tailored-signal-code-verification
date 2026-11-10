/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Spec
public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Identity

/-!
# Specification Model and Domain Preconditions for `signal_session_handshake::initiate`

Defines the model function `initDef` and file-system domain invariant `InitOk₀` for
`signal_session_handshake::initiate` (`poll_once(process_prekey_bundle(...))`, frame size
`cliInitiateFrame = 7408` bytes):
1. Checks `is_trusted_identity(remote, bundle.identity_key)` (`IdGhost.trusted`), signed/Kyber
   pre-key XEdDSA signatures, and `load_session(remote)`.
2. Draws 192 coin bytes (`padCoins`), loads `get_identity_key_pair`, checks
   `!is_same_account(local, ik, remote)`, and runs `PqxdhCorrectModel.initiateState`.
3. Saves `remote`'s identity (`saveUpd`), promotes the new state, and writes `encodeRecordUnderExtras`
   via `store_session(remote, record)`.

`InitOk₀` restricts the file state to the modeled domain:
- `noSession`: the peer's session file is empty or missing so `promote_state` keeps `previous_sessions` empty.
- `distinctAcct`: peer and local names do not parse to the same `ServiceId` (`DEV-PQ11`: the model fixes
  `self_session = false`).
- `idPairDerived` and `keyPairLt`: `identity-key-pair` has length `< 2 ^ 32` (preventing prost
  `capacity_overflow` panics) and carries the public key derived from its private key.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose

/-! ## Symbol names and frame size -/

abbrev cliInitiateName : String := "libsignal_cli_handshake::initiate"

/-- Stack frame size of `signal_session_handshake::initiate` (`0x60 + 0x1000 + 0xc90 = 7408` bytes). -/
abbrev cliInitiateFrame : Nat := 0x60 + 0x1000 + 0xc90

/-! ## File-system domain invariant (`InitOk₀`) -/

/-- `peer` and `me` parse via `serviceIdParse uuidTryParse` to the same `ServiceId`. -/
def SameServiceId (peer me : AddrVal) : Prop :=
  ∃ sid, serviceIdParse uuidTryParse peer.name = some sid ∧
    serviceIdParse uuidTryParse me.name = some sid

/-- File-system preconditions for `initDef`:
- `nameLt`..`idPathLt`: `u32` length bounds and `cliIo.pathOk` guards on `sessions/<peer>` and `identities/<peer>`;
- `idGet`: peer identity file reads cleanly as empty or one serialized key (`IdFileWf`);
- `noSession`: peer session file is missing or empty;
- `distinctAcct`: `peer` and `me` do not share a parsed `ServiceId`;
- `keyPairLt` and `idPairDerived`: `identity-key-pair` has length `< 2 ^ 32` and matches its derived public key. -/
structure InitOk₀ (W : PEParams) (F : FsFiles) (peer me : AddrVal) : Prop where
  nameLt : peer.name.length < 2 ^ 32
  textLt : (addressText peer).length < 2 ^ 32
  sessPathOk : cliIo.pathOk (pathOf (utf8 "sessions") (addressText peer))
  idPathOk : cliIo.pathOk (pathOf (utf8 "identities") peer.name)
  sessPathLt : (pathOf (utf8 "sessions") (addressText peer)).length < 2 ^ 32
  idPathLt : (pathOf (utf8 "identities") peer.name).length < 2 ^ 32
  keyPairLt : ∀ bs,
    StoresGhost.opened.identity.own.get cliIo.rd F (utf8 "identity-key-pair") = .ok bs →
    bs.length < 2 ^ 32
  idGet : ∃ bs, StoresGhost.opened.identity.peers.get cliIo.rd F peer.name = .ok bs ∧ IdFileWf bs
  noSession : StoresGhost.opened.sessions.get cliIo.rd F (addressText peer) = .ok []
  distinctAcct : ¬ SameServiceId peer me
  idPairDerived : ∀ kp, StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp →
    kp.identityKey.publicKey = (keyPairOf W.C kp.privateKey.bytes).publicKey

/-! ## Model of `initiate` (`initDef`) -/

/-- Extracts `PreKeyBundleFields` when `spkSig` and `kpkSig` are 64 bytes and `kpk` is 1568 bytes. -/
def bundleEOf? (b : BundleV) : Option PreKeyBundleFields :=
  if h1 : b.spkSig.length = 64 then
    if h2 : b.kpkSig.length = 64 then
      if h3 : b.kpk.length = 1568 then
        some { regId := b.regId, opk := b.opk.map fun (i, k) => (i, k.bytes),
               spkId := b.spkId, spkPub := b.spk.bytes, spkSig := ⟨b.spkSig, h1⟩,
               kpkId := b.kpkId, kpkPub := ⟨b.kpk, h3⟩, kpkSig := ⟨b.kpkSig, h2⟩,
               idPub := b.idKey.publicKey.bytes }
      else none
    else none
  else none

/-- Takes 192 bytes (`initiateTapeLen`) from `c`, zero-padding past `c.length`. -/
def padCoins (c : List (BitVec 8)) : List.Vector (BitVec 8) initiateTapeLen :=
  ⟨c.take initiateTapeLen ++ List.replicate (initiateTapeLen - c.length) 0#8, by
    simp only [List.length_append, List.length_take, List.length_replicate]; omega⟩

/-- Selects the initiator `Party` opposite `peer` (`B` when `peer` is `A`'s address, else `A`). -/
def initParty (peer : AddrVal) : Party :=
  if peer = RunRefine.addrValE .A then .B else .A

/-- Functional model of `signal_session_handshake::initiate` over `FsFiles`: validates bundle lengths,
trust, signatures, empty session slot, and identity key pair, then updates `identities/<peer>` via
`saveUpd` and `sessions/<peer>` via `encodeRecordUnderExtras`. -/
def initDef (X : UnreachedPqxdhPrimitives) (W : PEParams) (F : FsFiles) (peer _me : AddrVal) (b : BundleV)
    (coins : List (BitVec 8)) : SlotAns Unit :=
  let g := StoresGhost.opened
  match bundleEOf? b with
  | none => some none
  | some be =>
    match g.identity.trusted cliIo.rd F peer b.idKey with
    | .error _ => some none
    | .ok false => some none
    | .ok true =>
      match g.identity.keyPair cliIo.rd F, g.identity.regId cliIo.rd F with
      | .ok kp, .ok reg =>
        match initiateState X W (initParty peer) ⟨kp.privateKey.bytes, reg⟩ be (padCoins coins)
        with
        | none => some none
        | some (x, gs) =>
          some (some ({ g with
            identity := g.identity.saveUpd cliIo.rd F peer b.idKey
            sessions := g.sessions.put (addressText peer) (encodeRecordUnderExtras (fun _ => x) gs) }, ()))
      | _, _ => some none

/-! ## Symbol check -/

example : libsignalSessionCode.fnOff cliInitiateName =
    num% (ls_off% "libsignal_cli_handshake::initiate") :=
  ls_lemma% fnOff "libsignal_cli_handshake::initiate"

/-! ## Stack budget -/

/-- Stack budget for `signal_session_handshake::initiate` (`max 524288 (cliInitiateFrame + 848 + B.dirGetNeed)`). -/
abbrev cliInitiateNeed (B : RunBudgets) : Nat :=
  max 524288 (cliInitiateFrame + 848 + B.dirGetNeed)

end CryptoVerification.SignalSession.Cli.RunProofs
