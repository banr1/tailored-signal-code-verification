/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.Loader

/-!
# The `signal-session` CLI: commands, runs, outcomes, and directory layout

**Trusted: the statement.** Shared CLI run interface (`Inputs`, `Outcome`, `CliRun`), canonical
file-system projections (`fsView`, `filesOf`), command-line syntax (`Address`, `Cmd`), party and
bundle directory layout (`partyDirs`, `PublicBundle`), wire type bytes, and size caps (see
`Computational/docs/TRUSTED_BASE.md`).

Each CLI invocation runs in one party's directory with relative paths, reading `argv`, `stdin`,
`coins`, and (for `init`) a bundle directory, and exiting with `0` (accepted, stores and stdout
written), `1` (protocol rejection, files unchanged and stdout empty), `2` (usage or I/O error), or
`Outcome.aborted` (`panic = "abort"`). This module imports only `Arm64.Trusted.Process.Loader` so
both computational and symbolic statements can depend on it.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

/-! ## Runs -/

/-- **The inputs of one run.** Paths are relative to the party's directory, the process's working
directory, as the CLI opens them. The engine looks a path up by its canonical form
(`Arm64.normalizePath` drops empty and `.` segments, so `a`, `./a` and `a//` name one file), and
its loader refuses a path with a leading `/` or a `..` segment.
* `argv`: the arguments after `argv[0]` (the program name, `"signal-session"`);
* `dirs`: the directories that exist (the CLI never creates one);
* `files`: the regular files that exist, `(path, bytes)`, entered in order: a later entry for a path
  wins, and a later entry below a path makes that path a directory;
* `stdin`: the bytes on file descriptor 0. -/
structure Inputs where
  /-- The arguments after `argv[0]`. -/
  argv : List String
  /-- The directories that exist. -/
  dirs : List String
  /-- The regular files, `(path, bytes)`, entered in order: a later entry for a path wins, and a
  later entry below a path makes that path a directory. -/
  files : List (String × List (BitVec 8))
  /-- The bytes on standard input. -/
  stdin : List (BitVec 8)

/-- The names of the standard streams in the engine's file system, which are never files of the
party's directory. Some engine versions' loaders (`Arm64.Process.initFsState`) write stdin's bytes
at `"<stdin>"` and empty files at `"<stdout>"` and `"<stderr>"`; others keep the streams out of the
file system. `fsView` hides these names either way. -/
def stdioPaths : List String := ["<stdin>", "<stdout>", "<stderr>"]

/-- **The regular files of an engine file system, as a lookup**: the bytes at each path that holds
a regular file (`FsState.files`, by the path's canonical form); `none` at a directory, at a missing
path, and at the standard streams' names (`stdioPaths`, compared in canonical form). The model side
(`observe`, through `filesOf`) and the binary side (`toOutcome`, `CliRun.lean`) both read files
through it. -/
def fsView (fs : Arm64.FsState) (p : String) : Option (List (BitVec 8)) :=
  if Arm64.normalizePath p ∈ stdioPaths.map Arm64.normalizePath then none
  else
    match fs.files p with
    | some (.file bs) => some bs
    | _ => none

/-- **The files of a list of `(path, bytes)` entries, as a lookup**: `fsView` of the file system
the engine's loader builds from them (`Arm64.Process.initFsState`, with no directories and an
empty stdin). So a later entry for a path wins (paths compared in canonical form), a path that a
later entry makes a directory is `none`, and so are the stdio names. Directories are `none` in
`fsView`, so the directories a run starts with do not change this lookup. A missing file and an
empty file differ here; the CLI reads both as empty (`stores.rs`, `read_file`). -/
def filesOf (files : List (String × List (BitVec 8))) (p : String) : Option (List (BitVec 8)) :=
  fsView (Arm64.Process.initFsState { files := files }) p

/-- **The outcome of one run**:
* `exited code stdout files`: the process exited with `code`, having written `stdout`, and left
  the regular files `files` (a lookup by path; `none` at missing paths, directories and the
  stdio paths);
* `aborted`: libsignal panicked (`panic = "abort"`).
The exit code is a `Nat`. The engine's process result carries it as a machine word (the
`exit_group` argument): the bridge from the engine (`SignalSession/Process.lean`, `outcomeOf`)
maps it with `.toNat`. The specs use the codes `0`, `1` and `2`. -/
inductive Outcome where
  | exited (code : Nat) (stdout : List (BitVec 8)) (files : String → Option (List (BitVec 8)))
  | aborted

/-- **Any implementation of the CLI**: the outcome of the run on `Inputs`, `none` if there is no
outcome (the run faults, gets stuck, or never ends). The statements are proved for every
`run : CliRun` that meets a domain spec. -/
abbrev CliRun := Inputs → Option Outcome

/-! ## The command line -/

/-- **A protocol address** `<service id>.<device id>` (`lib.rs`, `address`): a service id
string and a device id. The specs use the two parties' fixed addresses (`SmDir.lean`). -/
structure Address where
  /-- The service id string (e.g. a hyphenated lowercase UUID). -/
  name : String
  /-- The device id (1 to 127 for a valid `DeviceId`). -/
  device : Nat

/-- The address as text: `name ++ "." ++ device` (`ProtocolAddress`'s `Display`). This is the
argument the CLI parses and the name of its session file. -/
def Address.text (a : Address) : String := a.name ++ "." ++ toString a.device

/-- **The commands the specs cover** (`lib.rs`, `Call`): `init <peer> <bundle dir>` starts a
session with `peer` from the bundle directory; `send <peer>` encrypts stdin to `peer`; `recv
<peer>` decrypts stdin from `peer`. -/
inductive Cmd where
  | init (peer : Address) (bundle : String)
  | send (peer : Address)
  | recv (peer : Address)

/-- The arguments of a command (after `argv[0]`). -/
def Cmd.argv : Cmd → List String
  | .init peer bundle => ["init", peer.text, bundle]
  | .send peer => ["send", peer.text]
  | .recv peer => ["recv", peer.text]

/-! ## The party's directory (`stores.rs`, `public.rs`) -/

/-- The party's own address, as text. -/
def addressFile : String := "address"
/-- The party's `IdentityKeyPair`. -/
def identityKeyPairFile : String := "identity-key-pair"
/-- The party's registration id, `u32` little-endian. -/
def registrationIdFile : String := "registration-id"
/-- The randomness of the next call, written by the caller. -/
def coinsFile : String := "coins"
/-- The pinned identity key of the account `name` (one per account). -/
def identityFile (name : String) : String := "identities/" ++ name
/-- The `SessionRecord` with the device `a`. -/
def sessionFile (a : Address) : String := "sessions/" ++ a.text
/-- A `SignedPreKeyRecord`, by id (decimal). -/
def signedPreKeyFile (id : BitVec 32) : String := "signed-pre-keys/" ++ toString id.toNat
/-- A one-time `PreKeyRecord`, by id; emptied when used. -/
def oneTimePreKeyFile (id : BitVec 32) : String := "one-time-pre-keys/" ++ toString id.toNat
/-- A one-time `KyberPreKeyRecord`, by id; emptied when used. -/
def oneTimeKyberPreKeyFile (id : BitVec 32) : String :=
  "one-time-kyber-pre-keys/" ++ toString id.toNat
/-- A last-resort `KyberPreKeyRecord`, by id; kept. -/
def lastResortKyberPreKeyFile (id : BitVec 32) : String :=
  "last-resort-kyber-pre-keys/" ++ toString id.toNat
/-- The handshakes a last-resort Kyber pre-key has accepted: `(signed pre-key id:u32 ‖ base
key[33])*`. -/
def baseKeysFile (id : BitVec 32) : String :=
  "last-resort-kyber-pre-keys/" ++ toString id.toNat ++ ".base-keys"

/-- **The directories of a party** that the caller creates (the CLI never creates a directory):
the six private ones and `public/` with its four. Root-level files (`address`, `coins`, …) need
no directory. -/
def partyDirs : List String :=
  ["identities", "sessions", "signed-pre-keys", "one-time-pre-keys", "one-time-kyber-pre-keys",
   "last-resort-kyber-pre-keys", "public", "public/signed-pre-keys", "public/one-time-pre-keys",
   "public/one-time-kyber-pre-keys", "public/last-resort-kyber-pre-keys"]

/-! ## Bundle directories (`public.rs`) -/

/-- The 4 little-endian bytes of a `u32` (`u32::to_le_bytes`). -/
def le32 (v : BitVec 32) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8]

/-- **What a bundle directory holds**, as the bytes the peer published (`public.rs`): its
identity key (serialized), its registration id, a signed pre-key (id, serialized public key,
signature), a Kyber pre-key (id, serialized public key, signature) and possibly a one-time pre-key
(id, serialized public key). -/
structure PublicBundle where
  /-- The serialized `IdentityKey` (`0x05 ‖ 32 bytes`). -/
  identityKey : List (BitVec 8)
  /-- The registration id. -/
  registrationId : BitVec 32
  /-- The signed pre-key's id. -/
  signedId : BitVec 32
  /-- The signed pre-key, serialized (`0x05 ‖ 32 bytes`). -/
  signedKey : List (BitVec 8)
  /-- Its signature (64 bytes). -/
  signedSig : List (BitVec 8)
  /-- The Kyber pre-key's id. -/
  kyberId : BitVec 32
  /-- The Kyber pre-key, serialized (`0x08 ‖ 1568 bytes`). -/
  kyberKey : List (BitVec 8)
  /-- Its signature (64 bytes). -/
  kyberSig : List (BitVec 8)
  /-- The one-time pre-key (id, serialized public key), if any. -/
  oneTime : Option (BitVec 32 × List (BitVec 8))

/-- **The files of bundle directory `dir`** (`public.rs`, `read_bundle`): `identity-key`,
`registration-id`, `signed-pre-key` and `kyber-pre-key` (each `id:u32 ‖ key ‖ signature`), and
`one-time-pre-key` (`id:u32 ‖ key`) if the bundle has one. A missing `one-time-pre-key` reads as
empty, i.e. none. -/
def PublicBundle.files (dir : String) (b : PublicBundle) : List (String × List (BitVec 8)) :=
  [(dir ++ "/identity-key", b.identityKey),
   (dir ++ "/registration-id", le32 b.registrationId),
   (dir ++ "/signed-pre-key", le32 b.signedId ++ b.signedKey ++ b.signedSig),
   (dir ++ "/kyber-pre-key", le32 b.kyberId ++ b.kyberKey ++ b.kyberSig)] ++
  match b.oneTime with
  | some (id, key) => [(dir ++ "/one-time-pre-key", le32 id ++ key)]
  | none => []

/-- The bundle directory the specs pass to `init`. -/
def bundleDir : String := "bundle"

/-! ## Messages on stdin and stdout (`lib.rs`, `run` / `decode_wire`) -/

/-- The first byte of a message `send` prints and `recv` reads for a bare `SignalMessage`
(`CiphertextMessageType::Whisper`). -/
def msgTypeWhisper : BitVec 8 := 2#8

/-- The first byte for a `PreKeySignalMessage` (`CiphertextMessageType::PreKey`). Any other first
byte, and an empty message, are rejected by `recv`. -/
def msgTypePreKey : BitVec 8 := 3#8

/-! ## Observing a model's outcome -/

/-- **The outcome a run must have when the model of the call says `r`**, for a call on the files
`files` (`none` = libsignal panics; `some none` = libsignal rejects; `some (some (writes, out))` =
libsignal accepts, the stores write `writes`, and stdout is `out`):
* a panic is `aborted`;
* a rejection exits `1` with an empty stdout and every file as it was;
* an acceptance exits `0` with stdout `out` and the files `files` overwritten by `writes`. -/
def observe (files : List (String × List (BitVec 8)))
    (r : Option (Option (List (String × List (BitVec 8)) × List (BitVec 8)))) : Outcome :=
  match r with
  | none => .aborted
  | some none => .exited 1 [] (filesOf files)
  | some (some (writes, out)) => .exited 0 out (filesOf (files ++ writes))

/-! ## Input and file-size caps -/

/-- Maximum bytes `signal_session_io::read_stdin` accepts (`1 MiB = 2^20 = 1,048,576`).
Reused across both `send` (before the `10^6`-byte plaintext check) and `recv`. -/
def stdinCapBytes : Nat := 1 <<< 20

/-- Maximum bytes `signal_session_io::read_file` accepts (`2 MiB = 2^21 = 2,097,152`). -/
def fileCapBytes : Nat := 2 ^ 21

/-- `PATH_MAX = 4096`: paths of `4096` bytes or more, or with an interior NUL, are rejected
(longest accepted: `4095`). -/
abbrev cliPathMaxBytes : Nat := 4096

/-- Maximum plaintext byte length accepted by `send` (`10^6 = 1,000,000`). -/
def maxPlaintextBytes : Nat := 1_000_000

end CryptoVerification.SignalSession
