/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains

/-!
# Abstract Semantics and Input Relation for `signal_session::run` (`runAns`, `runRel`)

Defines `runAns S i` case-by-case along `cli/src/lib.rs::run`:
- **Own-address check**: reads `"address"`, validates ASCII (`from_utf8`), and parses `address`;
  read errors reject immediately and unparseable addresses reject after command unpacking.
- **Init** (`tag = 1`): reads and parses the five pre-key bundle files (`readBundleV`), then calls
  `S.initiate` with empty stdout output.
- **Send** (`tag = 2`): calls `S.encrypt` and prepends wire type byte `2` (`SignalMessage`) or `3`
  (`PreKeySignalMessage`).
- **Recv** (`tag = 3`): parses `SignalMessage` (wire byte `2`) or `PreKeySignalMessage` (wire byte
  `3`), calls `S.decryptSignal` or `S.decryptPrekey`, and rejects empty or unrecognized prefixes.
- **Finish**: commits store writes and outputs bytes on `Ok`, or exits with rejection on `None`/`Err`.

`runRel S` pairs `runAns S` with `DomainArgv`, input size/path bounds (`RunBounds`), and the
wrapper-slot domain preconditions (`RunFilesOk S`, `RunEncOk S`, `RunHsOk S`).
-/

@[expose] public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalProtoCodec

def exceptOpt {ε α : Type} : Except ε α → Option α
  | .ok a => some a
  | .error _ => none

/-- A little-endian `u32` of exactly 4 bytes (`registration-id`). -/
def readU32LE : Bytes → Option (BitVec 32)
  | [b0, b1, b2, b3] => some (ofLe32 b0 b1 b2 b3)
  | _ => none

/-- The run-entry file system of input `i`. -/
def runFiles (i : Inputs) : FsFiles := (initFsState (cliInputs i)).files

/-- The path `read_bundle` reads for `name` in the bundle directory `dir` (`bundleReadSpec`'s
`dir ++ "/" ++ name`). -/
def bundlePath (dir : Bytes) (name : String) : Bytes := dir ++ [0x2f#8] ++ utf8 name

/-- The five bundle files `read_bundle` reads. -/
def bundleNames : List String :=
  ["identity-key", "registration-id", "signed-pre-key", "kyber-pre-key", "one-time-pre-key"]

/-- A bundle file's bytes (`read_file`; a read error is `none`). -/
def bundleFile (F : FsFiles) (dir : Bytes) (name : String) : Option Bytes :=
  exceptOpt (cliIo.rd F (bundlePath dir name))

/-- Parses `read_bundle(dir, device)` (`public.rs:93`): decodes `identity-key` (`IdentityKey::decode`),
the 4-byte little-endian `registration-id`, the signed and Kyber pre-keys (`split_signed` followed
by `PublicKey::deserialize` / `RunProofs.kemPkDeserialize`), and the optional `pre-key` (empty file
→ `none`, else `split_id` and `PublicKey::deserialize`). Any read or decode error returns `none`. -/
def readBundleV (F : FsFiles) (dir : Bytes) (device : BitVec 8) : Option BundleV := do
  let ikB ← bundleFile F dir "identity-key"
  let idKey ← exceptOpt (decodeIdentityKey ikB)
  let regB ← bundleFile F dir "registration-id"
  let regId ← readU32LE regB
  let spkB ← bundleFile F dir "signed-pre-key"
  let (spkId, spkKey, spkSig) ← splitSigned spkB
  let kpkB ← bundleFile F dir "kyber-pre-key"
  let (kpkId, kpkKey, kpkSig) ← splitSigned kpkB
  let opkB ← bundleFile F dir "one-time-pre-key"
  let opk ← (if opkB.isEmpty then some none else do
      let (opkId, opkKey) ← splitId opkB
      let k ← exceptOpt (PublicKey.deserialize opkKey)
      some (some (opkId, k)) : Option (Option (BitVec 32 × PublicKey)))
  let spk ← exceptOpt (PublicKey.deserialize spkKey)
  let kpk ← (match RunProofs.kemPkDeserialize kpkKey with
    | .ok key => some key
    | _ => none : Option Bytes)
  some { idKey, regId, device, spkId, spk, spkSig, kpkId, kpk, kpkSig, opk }

/-- The bytes `send` prints: the wire type byte (`2` Whisper, `3` PreKey) and `serialize()`. -/
def ctWire : CiphertextMessage → Bytes
  | .signalMessage m => 2#8 :: m.serialized
  | .preKeySignalMessage m => 3#8 :: m.serialized

/-- `accepted(_)` and the `Ok((stores, output))` of `run`: panic stays panic, reject stays reject,
accept commits the stores' writes and prints `out v`. -/
def finish {α : Type} (ans : SlotAns α) (out : α → Bytes) : RunAnswer :=
  match ans with
  | none => none
  | some none => some none
  | some (some (g', v)) => some (some (namedWrites g'.writes, out v))

/-- An `AddrV` (the parser's) as an `AddrVal` (the session API's). -/
def addrValOf (a : AddrV) : AddrVal := ⟨a.name, a.device⟩

/-- Abstract answer of `signal_session::run` on input `i` under callee semantics `S`. -/
def runAns (S : RunSem) (i : Inputs) : RunAnswer :=
  match parseArgs uuidTryParse (i.argv.map bytesOfString) with
  | none => none
  | some c =>
    let F := runFiles i
    let coins := MainHops.coinsOf i
    match StoresGhost.opened.identity.own.get cliIo.rd F (utf8 "address") with
    | .error _ => some none
    | .ok ownB =>
      match addrParse uuidTryParse ownB with
      | none => some none
      | some meV =>
        let me := addrValOf meV
        match c with
        | .keygen .. => none
        | .init peerV dir =>
          match readBundleV F dir peerV.device with
          | none => some none
          | some b => finish (S.initiate F (addrValOf peerV) me b coins) (fun _ => [])
        | .send peerV => finish (S.encrypt F (addrValOf peerV) me i.stdin coins) ctWire
        | .recv peerV =>
          match i.stdin with
          | [] => some none
          | t :: rest =>
            if t = 2#8 then
              match SignalMessage.tryFrom protoSignalCodec rest with
              | .ok m => finish (S.decryptSignal F (addrValOf peerV) me m coins) id
              | .error _ => some none
            else if t = 3#8 then
              match S.pksmParse rest with
              | some m => finish (S.decryptPrekey F (addrValOf peerV) me m coins) id
              | none => some none
            else some none

/-- Input size and path bounds required by `run_ok'` beyond `DomainArgv`: `send` plaintext length
`< 2 ^ 32` (`encSlotSpec`), `recv` payload length after the wire tag byte `< 2 ^ 32`
(`tryFromSpec` / `pksmSlotSpec`), ASCII own-address file bytes (`fromUtf8AsciiSpec`), `cliWrOk`
bundle file paths on `init` (`bundleReadSpec`), and `coins.length < 2 ^ 63` (`slotFrame`). -/
def RunBounds (i : Inputs) : Prop :=
  (MainHops.coinsOf i).length < 2 ^ 63 ∧
  (∀ peer, parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer) →
      i.stdin.length < 2 ^ 32) ∧
    (∀ peer, parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer) →
      i.stdin.tail.length < 2 ^ 32) ∧
    (∀ bs, StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") = .ok bs →
      ∀ b ∈ bs, b.toNat < 128) ∧
    (∀ peer dir, parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.init peer dir) →
      ∀ name ∈ bundleNames, cliWrOk (bundlePath dir name))

/-- The peer of a wrapper command (`init` / `send` / `recv`); `none` for `keygen`. -/
def callPeer : CallV → Option AddrV
  | .keygen .. => none
  | .init p _ => some p
  | .send p => some p
  | .recv p => some p

/-- Store-file well-formedness precondition `S.filesOk` at run-entry files, the command's peer,
and the own address whenever the own-address check succeeds. -/
def RunFilesOk (S : RunSem) (i : Inputs) : Prop :=
  ∀ c peer ownB meV, parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
    callPeer c = some peer →
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") = .ok ownB →
    addrParse uuidTryParse ownB = some meV →
    S.filesOk (runFiles i) (addrValOf peer) (addrValOf meV)

/-- Encrypt-slot domain precondition `S.encOk` at run-entry files, the `send` peer, and installed
coins whenever the own-address check succeeds. -/
def RunEncOk (S : RunSem) (i : Inputs) : Prop :=
  ∀ peer ownB meV, parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer) →
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") = .ok ownB →
    addrParse uuidTryParse ownB = some meV →
    S.encOk (runFiles i) (addrValOf peer) (MainHops.coinsOf i)

/-- Handshake-slot domain preconditions (`S.initOk` on `init`; `S.decPkOk` on `recv` with wire tag
`3` that parses) whenever the own-address check succeeds. -/
def RunHsOk (S : RunSem) (i : Inputs) : Prop :=
  (∀ peer dir ownB meV,
    parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.init peer dir) →
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") = .ok ownB →
    addrParse uuidTryParse ownB = some meV →
    S.initOk (runFiles i) (addrValOf peer) (addrValOf meV)) ∧
  (∀ peer ownB meV rest pm,
    parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer) →
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") = .ok ownB →
    addrParse uuidTryParse ownB = some meV →
    i.stdin = 3#8 :: rest → S.pksmParse rest = some pm →
    S.decPkOk (runFiles i) (addrValOf peer) (addrValOf meV) pm)

/-- Top-level input-output relation for `run_ok'`: conjoins `DomainArgv`, `RunBounds`,
`RunFilesOk S`, `RunEncOk S`, `RunHsOk S`, and `ans = runAns S i`. -/
def runRel (S : RunSem) (i : Inputs) (a : RunAnswer) : Prop :=
  DomainArgv i ∧ RunBounds i ∧ RunFilesOk S i ∧ RunEncOk S i ∧ RunHsOk S i ∧ a = runAns S i

/-- `runRel` is contained in the domains (the trusted chain's `hdom`). -/
theorem runRel_dom {S : RunSem} {i : Inputs} {a : RunAnswer} (h : runRel S i a) : DomainArgv i :=
  h.1

end CryptoVerification.SignalSession.Cli.RunCompose
