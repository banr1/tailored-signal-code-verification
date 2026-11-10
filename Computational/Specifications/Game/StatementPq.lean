/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.GenericGame
public import Computational.Specifications.Game.StatementPqOomFlag
public import LibsignalBinary.Specifications.SignalSession.PqDir

/-!
# The CLI security game on PQXDH directories with SPQR

**Trusted: the statement.** Read with `PqDir.lean` (`CliSpecPqxdh`, `encodeDir`, `pqInputs`) and
`Run.lean` (in `LibsignalBinary/Specifications/SignalSession/`), and
`Computational/Specifications/Game/StatementBinaryHarnessCore.lean`. See
`Computational/docs/TRUSTED_BASE.md`.

Multi-session security game `cliPqExp` and distinguishing advantage `CliPqxdhAdvantage` for a
libsignal command-line client `run : CliRun` executing PQXDH handshakes followed by SPQR-augmented
Double Ratchet sessions. It instantiates the generic composed game `G(Σ)`
(`Computational/Specifications/Game/GenericGame.lean`) at the CLI interface `cliIface` (`Σ_bin`),
where each ACD19 secure-messaging (SM) step (`init`, `send`, `recv`) is one invocation of `run` on
a party directory; the headline theorems instantiate `run` with the placed ARM64 semantics
`Placed.cliRunPlacedSig` (`LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean`).

At `startDR`, Alice's `init <Bob> bundle` runs on her initial `encodeDir` directory (`pqInitInputs`)
and Bob's initial directory is encoded once from the `KeyInd` metadata (`cliPartyStateB0`). Across
`exit 0` invocations, `Dir.cliPqAfter` reads back all present party files along `cliPqPartyPathsOf`
(`cliPqReadBack`) as the retained directory `CliPartyState.dir` passed to the next `send` or `recv`
(`cliPqDirInputs`), recording `sessions/<peer>` in `CliPartyState.bin.bytes`; on `corr-P`,
`cliOracleImplR` projects leaked state to `CliPartyState.bin : BinState`.

**DEV-CLI13 (formalization): Alice refuses every input whose first byte is 3.** `CliSpecPqxdh`
covers a pre-key message only when the session matches it or there is none, whereas Alice always
holds the session she started; `Dir.cliPqReceive` refuses every byte-`3`-prefixed input to Alice
before calling `run`. Effect: no claim about Alice receiving a pre-key message; honest Bob never
sends one.

**DEV-CLI14 (formalization): explicit length gate; restricts the adversary.** `Dir.cliPqReceive`
refuses inputs of `2^32` bytes or more and canonical pre-key messages whose inner message has
`2^32 - 2048` bytes or more (`cliPqLenOk`) before calling `run`, matching the injection filter
`bhInjOK`. For plaintext length bound `l < 10^6`, no honest ciphertext reaches this threshold.

**DEV-CLI18 (formalization): `exit 0` directory retention, non-zero exit rollback, and `BinState`
leakage projection.** Across `exit 0` calls, `CliPartyState.dir` retains the full party directory
snapshot (`cliPqReadBack` over `cliPqPartyPathsOf`), while `corr-P` leaks only
`CliPartyState.bin : BinState` (matching `modelIface`'s `GhostState Bytes` corruption surface rather
than long-term identity or pre-key secret files). On any non-zero exit (`exited c` with `c ≠ 0`,
`aborted`, or `none`), `Dir.cliPqAfter` returns `none` and leaves `CliPartyState` unchanged: under
`CliSpecPqxdh` rejected calls leave party files untouched, allocation-failure aborts (`DEV-CLI15`)
are accounted for separately in the CLI security bound, and mid-commit OS/I/O failures during
sequential multi-file writes (`EMFILE`, `ENOSPC`, `EIO`, power loss) are out of scope (`DEV-CLI4`).
Effect: out of scope (partial-write crash recovery on non-zero exit).
-/

@[expose] public section

set_option autoImplicit false
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

/-! ## Party directories and call inputs -/

/-- Candidate relative file paths of a party directory, in the order emitted by `encodeDir`. -/
def cliPqPartyPaths (party : Party)
    (spkIds opkIds otkIds lrkIds : List (BitVec 32)) : List String :=
  [addressFile, identityKeyPairFile, registrationIdFile,
   identityFile (partyAddressName party.other),
   sessionFile (partyAddress party.other)] ++
  spkIds.map signedPreKeyFile ++
  opkIds.map oneTimePreKeyFile ++
  otkIds.map oneTimeKyberPreKeyFile ++
  (lrkIds.map fun i => [lastResortKyberPreKeyFile i, baseKeysFile i]).flatten

def cliPqPartyPathsOf (st : PqParty) : List String :=
  cliPqPartyPaths st.party
    (st.signed.map (·.1))
    (st.oneTime.map (·.1))
    (st.kyberOneTime.map (·.1))
    (st.kyberLastResort.map (·.1))

/-- Read back present party files along `paths` from `fs`, omitting missing paths (`fs p = none`)
while keeping empty files (`fs p = some []`). -/
def cliPqReadBack (paths : List String) (fs : String → Option (List (BitVec 8))) :
    List (String × List (BitVec 8)) :=
  paths.filterMap fun p => (fs p).map fun bs => (p, bs)

/-- Build CLI `Inputs` for `cmd` from a retained party directory `dir`, extra files, coin bytes,
and `stdin`. -/
def cliPqDirInputs (dir : List (String × List (BitVec 8))) (cmd : Cmd)
    (extra : List (String × List (BitVec 8))) (coins stdin : List (BitVec 8)) : Inputs :=
  { argv := cmd.argv
    dirs := partyDirs ++ (match cmd with | .init _ dir => [dir] | _ => [])
    files := dir ++ extra ++ [(coinsFile, coins)]
    stdin := stdin }

/-- Coerce `bs` to a 64-byte signature vector, defaulting to zeros when `bs.length ≠ 64`. -/
def cliPqSig64 (bs : SignalPqxdh.Bytes) : List.Vector (BitVec 8) 64 :=
  (fitU8VecStrict 64 bs).getD (List.Vector.replicate 64 0#8)

/-- Bob's initial `PqParty` directory before his first accept in instance `bi`, pinning Alice's
identity key and installing the responder slot's signed pre-key, last-resort Kyber pre-key (with no
seen base keys), and optional one-time pre-key, with no session. -/
def cliPqxdhDirBobBeforeAccept {S : SignalPqxdh.Setup} {l : Nat} (bi : ModelDriverInstance S l)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64) : PqParty :=
  let spk : PqSignedKey := { priv := bi.keysB.spkPriv, sig := sigs.1, timestamp := 0#64 }
  let kpk : PqKyberKey :=
    { pub := bi.keysB.kpkPub, sec := bi.keysB.kpkSec, sig := sigs.2, timestamp := 0#64 }
  { party := .B, me := bi.meB, peerId := some (bhIdKeyOf bi.hdr.ikAPk), session := none,
    signed := [(bi.keysB.spkId, spk)]
    oneTime := match bi.keysB.opk with | some (i, sk) => [(i, some sk)] | none => []
    kyberOneTime := []
    kyberLastResort := [(bi.keysB.kpkId, kpk, [])] }

/-- Per-party state in a promoted CLI instance (`DEV-CLI18`): leaked `BinState` session record
`bin`, fixed candidate directory paths `paths`, and retained directory snapshot `dir`. -/
structure CliPartyState where
  bin : BinState
  paths : List String
  dir : List (String × List (BitVec 8))
  deriving DecidableEq

/-- Bob's initial `CliPartyState` before his first accept in instance `bi`. -/
def cliPartyStateB0 {S : SignalPqxdh.Setup} {l : Nat} (W : PEParams)
    (bi : ModelDriverInstance S l)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64) : CliPartyState :=
  let d0 := cliPqxdhDirBobBeforeAccept bi sigs
  { bin := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
    paths := cliPqPartyPathsOf d0
    dir := encodeDir W d0 }

/-- Ciphertext length gate (`DEV-CLI14`): requires `shortCiphertext c` (`< 2 ^ 32` bytes) and inner
payload length `< 2 ^ 32 - 2048` on canonical tag-3 wires. -/
def cliPqLenOk (c : List (BitVec 8)) : Bool :=
  shortCiphertext c &&
  match bhDecodePreKeyMsgE c with
  | some m => decide (m.inner.length + 2048 < 2 ^ 32)
  | none => true

/-- Responder slot's `(spkSig, pqspkSig)` read from `st.spkBundles` (zero-filled if absent). -/
def cliPqSigsOf {S : SignalPqxdh.Setup} {l : Nat} (st : SignalPqxdh.KeyIndState S)
    (bi : ModelDriverInstance S l) : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64 :=
  match st.spkBundles.find? (fun (idx, _) => idx == (bi.respSlot.1.val, bi.respSlot.2.val)) with
  | some (_, e) => (cliPqSig64 e.spkSig, cliPqSig64 e.pqspkSig)
  | none => (cliPqSig64 [], cliPqSig64 [])

/-- Map `f : St' → St` over the per-party states of an `SM.GameState`, keeping all metadata
unchanged. -/
def cliMapGameState {St' St Msg C : Type} (f : St' → St)
    (gs : SM.GameState St' Msg C) : SM.GameState St Msg C :=
  { st := fun P => f (gs.st P)
    epoch := gs.epoch
    idx := gs.idx
    tL := gs.tL
    trans := gs.trans
    chall := gs.chall
    comp := gs.comp
    maxAcc := gs.maxAcc
    b := gs.b
    win := gs.win
    leaks := gs.leaks }

/-- Lift `bhConfigSpkS` (`SM.ConfigR BinState Msg Bytes`) to an arbitrary party-state type `St`. -/
def cliConfigSpkS {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {St Msg : Type} : SM.ConfigR St Msg Bytes :=
  let c := bhConfigSpkS (Msg := Msg) decT encT
  let toBin : SM.GameState St Msg Bytes → SM.GameState BinState Msg Bytes :=
    cliMapGameState (fun _ => ⟨.A, [], ⟨0, []⟩⟩)
  { base := c.base
    r1 := c.r1
    must := fun gs => c.must (toBin gs)
    sendOK := fun gs => c.sendOK (toBin gs)
    corrOK := fun gs => c.corrOK (toBin gs)
    injOK := c.injOK }

/-- R-game SM oracles running over internal party state `St'` and projecting `corr-P` leakage along
`proj : St' → St` (`DEV-CLI18`). -/
def cliOracleImplR {Key St' St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (proj : St' → St) (sm : SMSchemeR Key St' Msg Coins RCoins C)
    (Δ qep : Nat) (cfg : SM.ConfigR St' Msg C) :
    QueryImpl (SM.spec St Msg Coins C) (StateT (SM.GameState St' Msg C) ProbComp) :=
  SM.transmitR sm Δ qep cfg + SM.challR sm Δ qep cfg + SM.deliverR sm cfg +
    SM.injectR sm Δ qep cfg +
    (fun P => Option.map proj <$> SM.corrR cfg P :
      QueryImpl (Party →ₒ Option St) (StateT (SM.GameState St' Msg C) ProbComp))

/-- Driver state of the CLI game, pairing `ModelDriverState` with per-instance `CliPartyState` SM
states `instGs` (`bi.gs` caches the `CliPartyState.bin` projection). -/
structure CliDriverState (S : SignalPqxdh.Setup) (l : Nat) extends ModelDriverState S l where
  instGs : List (Option (SM.GameState CliPartyState (Plain l) Bytes)) := []

/-- Monad transformer of the retained-directory CLI driver over `M`. -/
abbrev CliDrvMT (S : SignalPqxdh.Setup) (l : Nat) (M : Type → Type) :=
  StateT (CliDriverState S l) (StateT (SignalPqxdh.KeyIndState S) M)

abbrev CliDrvM (S : SignalPqxdh.Setup) (l : Nat) :=
  CliDrvMT S l ProbComp

/-- Lift a `BHDrvM` computation into `CliDrvMT`, leaving `instGs` unchanged. -/
def bhLiftCliM {S : SignalPqxdh.Setup} {l : Nat} {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    {α : Type} (m : BHDrvM S l α) : CliDrvMT S l M α := do
  let cds ← get
  let (a, ds') ← StateT.lift (liftStateT (m.run cds.toModelDriverState))
  set { cds with toModelDriverState := ds' }
  return a

def bhLiftCli {S : SignalPqxdh.Setup} {l : Nat} {α : Type}
    (m : BHDrvM S l α) : CliDrvM S l α := do
  let cds ← get
  let (a, ds') ← StateT.lift (m.run cds.toModelDriverState)
  set { cds with toModelDriverState := ds' }
  return a

def cliRunPure (run : CliRun) (i : Inputs) : ProbComp (Option Outcome) :=
  pure (run i)

abbrev cliPqSendInp (s : CliPartyState) (m : List (BitVec 8)) (rs : BitVec 512) : Inputs :=
  cliPqDirInputs s.dir (.send (partyAddress s.bin.party.other)) [] (LibsignalSpqrV1.coinBytes rs) m

abbrev cliPqRecvInp (s : CliPartyState) (c : List (BitVec 8)) (rc : BitVec 256) : Inputs :=
  cliPqDirInputs s.dir (.recv (partyAddress s.bin.party.other)) [] (HMAC.keyToBytes32 rc) c

namespace Dir

/-! ## Single-call CLI scheme steps -/

/-- Extract `(cliPqReadBack paths fs, sessions/<peer>, stdout)` on `exited 0`, or `none` on any
other outcome (`DEV-CLI18`). -/
def cliPqAfter (P : Party) (paths : List String) :
    Option Outcome → Option (List (String × List (BitVec 8)) × List (BitVec 8) × List (BitVec 8))
  | some (.exited 0 out fs) =>
    some (cliPqReadBack paths fs, (fs (sessionFile (partyAddress P.other))).getD [], out)
  | _ => none

/-- Run Alice's `init <Bob> bundle` call with 192-byte tape `t`, returning her initial
`CliPartyState` on `exited 0`. -/
def cliPqInit (run : CliRun) (W : PEParams) (dA : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : Option CliPartyState :=
  let pathsA := cliPqPartyPathsOf dA
  (cliPqAfter .A pathsA (run (pqInitInputs W dA b t))).map fun (dirA, recA, _) =>
    { bin := { party := .A, bytes := recA, epochs := { epoch := 0, chains := [(⟨b.spkPub⟩, 0)] } }
      paths := pathsA
      dir := dirA }

/-- Run `send <peer>` on `s.dir` with 64-byte send coins `rs`, updating `s` and returning stdout on
`exited 0`, or `(s, [])` otherwise. -/
def cliPqSend (run : CliRun) (s : CliPartyState)
    (m : List (BitVec 8)) (rs : BitVec 512) : CliPartyState × List (BitVec 8) :=
  match cliPqAfter s.bin.party s.paths (run (cliPqSendInp s m rs)) with
  | some (dir', recB, wire) =>
    ({ bin := { party := s.bin.party, bytes := recB, epochs := s.bin.epochs.send s.bin.party }
       paths := s.paths
       dir := dir' }, wire)
  | none => (s, [])

/-- Run `recv <peer>` on `s.dir` with 32-byte receive coins `rc`, updating `s` and parsing the inner
`SignalMessage` header for `(epoch, index)` on `exited 0`. -/
def cliPqRecv (run : CliRun) (s : CliPartyState)
    (c : List (BitVec 8)) (rc : BitVec 256) :
    Option (CliPartyState × Nat × Nat × List (BitVec 8)) :=
  (cliPqAfter s.bin.party s.paths (run (cliPqRecvInp s c rc))).map
    fun (dir', recB, pt) =>
      match (bhWireInnerBytes c).map (SignalMessage.tryFrom protoSignalCodec) with
      | some (.ok msg) =>
        let (t, ep') := s.bin.epochs.recv msg.senderRatchetKey
        ({ bin := { party := s.bin.party, bytes := recB, epochs := ep' }
           paths := s.paths, dir := dir' }, t, msg.counter.toNat + 1, pt)
      | _ =>
        ({ bin := { party := s.bin.party, bytes := recB, epochs := s.bin.epochs }
           paths := s.paths, dir := dir' }, s.bin.epochs.epoch, 0, pt)

/-- Receive step of instance `bi` (`DEV-CLI13`, `DEV-CLI14`): enforces `cliPqLenOk`, refuses any
`wirePrekey`-prefixed input to Alice, and checks partnered pre-key or whisper framing for Bob
before invoking `cliPqRecv`. -/
def cliPqReceive (run : CliRun) (l : Nat) {S : SignalPqxdh.Setup}
    {l' : Nat} (bi : ModelDriverInstance S l')
    (s : CliPartyState) (c : List (BitVec 8)) (rc : BitVec 256) :
    Option (CliPartyState × Nat × Nat × Plain l) :=
  let call := fun _ : Unit =>
    (cliPqRecv run s c rc).map fun x =>
      (x.1, x.2.1, x.2.2.1, padOrTruncatePlain l x.2.2.2)
  if !cliPqLenOk c then none
  else
    match s.bin.party with
    | .A => if c.head? == some wirePrekey then none else call ()
    | .B =>
      match bhDecodePreKeyMsgE c with
      | some m =>
        if s.bin.bytes.isEmpty || s.bin.epochs.epoch == 0 then
          if c == wirePrekey :: (bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner).bytes then call ()
          else none
        else if bhHdrOfPreKeyMsg m == bi.hdr then call ()
        else none
      | none =>
        if s.bin.bytes.isEmpty || s.bin.epochs.epoch == 0 then none
        else if c.head? == some wireWhisper then call ()
        else none

/-- `SMSchemeR` of promoted instance `bi` over retained `CliPartyState` directories. -/
def cliPqScheme (run : CliRun) (l : Nat) {S : SignalPqxdh.Setup}
    {l' : Nat} (bi : ModelDriverInstance S l') (stA0 stB0 : CliPartyState) :
    SMSchemeR Unit CliPartyState (Plain l) (BitVec 512) (BitVec 256) Bytes where
  initA _ := stA0
  initB _ := stB0
  send s m rs := cliPqSend run s m.toList rs
  receive s c rc := cliPqReceive run l bi s c rc

def cliPqInitM {M : Type → Type} [Monad M] (runM : Inputs → M (Option Outcome))
    (W : PEParams) (dA : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : M (Option CliPartyState) :=
  (fun out => cliPqInit (fun _ => out) W dA b t) <$> runM (pqInitInputs W dA b t)

def cliPqSendM {M : Type → Type} [Monad M] (runM : Inputs → M (Option Outcome))
    (s : CliPartyState) (m : List (BitVec 8)) (rs : BitVec 512) :
    M (CliPartyState × List (BitVec 8)) :=
  (fun out => cliPqSend (fun _ => out) s m rs) <$> runM (cliPqSendInp s m rs)

def cliPqRecvM {M : Type → Type} [Monad M] (runM : Inputs → M (Option Outcome))
    (s : CliPartyState) (c : List (BitVec 8)) (rc : BitVec 256) :
    M (Option (CliPartyState × Nat × Nat × List (BitVec 8))) :=
  (fun out => cliPqRecv (fun _ => out) s c rc) <$> runM (cliPqRecvInp s c rc)

def cliPqReceiveM {M : Type → Type} [Monad M] (runM : Inputs → M (Option Outcome))
    (l : Nat) {S : SignalPqxdh.Setup} {l' : Nat} (bi : ModelDriverInstance S l')
    (s : CliPartyState) (c : List (BitVec 8)) (rc : BitVec 256) :
    M (Option (CliPartyState × Nat × Nat × Plain l)) :=
  let call := fun _ : Unit =>
    (fun r => r.map fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain l x.2.2.2)) <$>
      cliPqRecvM runM s c rc
  if !cliPqLenOk c then pure none
  else
    match s.bin.party with
    | .A => if c.head? == some wirePrekey then pure none else call ()
    | .B =>
      match bhDecodePreKeyMsgE c with
      | some m =>
        if s.bin.bytes.isEmpty || s.bin.epochs.epoch == 0 then
          if c == wirePrekey :: (bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner).bytes then call ()
          else pure none
        else if bhHdrOfPreKeyMsg m == bi.hdr then call ()
        else pure none
      | none =>
        if s.bin.bytes.isEmpty || s.bin.epochs.epoch == 0 then pure none
        else if c.head? == some wireWhisper then call ()
        else pure none

/-- Monadic `SMSchemeRM` of promoted instance `bi` for an effectful runner `runM`. -/
def cliPqSchemeM {M : Type → Type} [Monad M] (runM : Inputs → M (Option Outcome))
    (l : Nat) {S : SignalPqxdh.Setup} {l' : Nat} (bi : ModelDriverInstance S l')
    (stA0 stB0 : CliPartyState) :
    SMSchemeRM M Unit CliPartyState (Plain l) (BitVec 512) (BitVec 256) Bytes where
  initA _ := stA0
  initB _ := stB0
  send s m rs := cliPqSendM runM s m.toList rs
  receive s c rc := cliPqReceiveM runM l bi s c rc

/-! ## CLI game driver and security experiment -/

/-- Promote initiator session `sid` to a Double Ratchet instance: checks `bhDrvGuard`, evaluates
`testSession` and `revealSpkSk`, runs Alice's `init` call via `cliPqInitM`, and commits the updated
`KeyIndState` and new instance only if `cliPqInitM` succeeds. -/
def cliDrvStartM {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (S : SignalPqxdh.Setup) (l : Nat) (P : SignalPqxdh.Primitives)
    (runM : Inputs → M (Option Outcome)) (W : PEParams) (mode : BHDrvMode S)
    (sid : SignalPqxdh.SessionId S) : CliDrvMT S l M (Option Nat) := do
  let ds ← get
  let some (hdr, bnd, (u_resp, j_resp)) := bhDrvGuard ds.toModelDriverState sid | return none
  let st0 ← StateT.lift get
  let (.drKeyResp _, st1) ←
    StateT.lift (liftM ((SignalPqxdh.pqxdhKeyIndImpl false S P (.testSession sid)).run st0))
    | return none
  let (.spkSkResp spkSk, st) ←
    StateT.lift (liftM ((SignalPqxdh.pqxdhKeyIndImpl false S P (.revealSpkSk u_resp j_resp)).run st1))
    | return none
  let t_dr ← StateT.lift (liftM ($ᵗ List.Vector (BitVec 8) 32))
  let some (_, u_init, _, t_init) := ds.initTapes.find? (fun (s, _, _, _) => s == sid) | return none
  let some (_, initPrinEntry) := st.principals.find? (fun (idx, _) => idx == u_init.val)
    | return none
  let some (_, respPrinEntry) := st.principals.find? (fun (idx, _) => idx == u_resp.val)
    | return none
  let some (_, respSpkEntry) :=
    st.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) | return none
  let opkSk? ← match hdr.opkId? with
    | none => pure (some none)
    | some opkId =>
      match st.opkEntries.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val, opkId.toNat)) with
      | some (_, oe) => pure (some (some (opkId.toNat, oe.opkSk)))
      | none => pure none
  let some opkOpt := opkSk? | return none
  let some meA := mkMeEStrict u_init.val initPrinEntry.secIKA0 | return none
  let some meB := mkMeEStrict u_resp.val respPrinEntry.secIKA0 | return none
  let some keysB := mkKeysEStrict j_resp.val respSpkEntry opkOpt | return none
  let some bundleE := mkBundleEStrict u_resp.val bnd | return none
  let dA : PqParty :=
    { party := .A, me := meA, peerId := some (bhIdKeyOf bnd.ikB), session := none,
      signed := [], oneTime := [], kyberOneTime := [], kyberLastResort := [] }
  let some stA0 ←
    StateT.lift (StateT.lift (cliPqInitM runM W dA bundleE (appendInitiateTape t_init t_dr)))
    | return none
  let stB0Bin : BinState := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
  let bi0 : ModelDriverInstance S l :=
    { sid := sid, hdr := hdr, idBBytes := bnd.ikB, respSlot := (u_resp, j_resp),
      meA := meA, meB := meB, keysB := keysB, stA0 := stA0.bin, stB0 := stB0Bin, gs := none }
  let stB0 := cliPartyStateB0 W bi0 (cliPqSigsOf st bi0)
  let scheme := cliPqSchemeM runM l bi0 stA0 stB0
  let gsDir : Option (SM.GameState CliPartyState (Plain l) Bytes) :=
    (mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB spkSk).map
      (fun b => scheme.initState () b)
  let gs : Option (SM.GameState BinState (Plain l) Bytes) :=
    gsDir.map (cliMapGameState CliPartyState.bin)
  let bi : ModelDriverInstance S l := { bi0 with gs := gs }
  let im0 : ModelDriverInstanceMeta S :=
    { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := bnd.opkB?.map Prod.fst }
  StateT.lift (set st)
  set { ds with bhInsts := ds.bhInsts ++ [bi], instMeta := ds.instMeta ++ [im0],
                instGs := ds.instGs ++ [gsDir] }
  return some ds.bhInsts.length

def cliDrvStart (S : SignalPqxdh.Setup) (l : Nat) (P : SignalPqxdh.Primitives)
    (run : CliRun) (W : PEParams) (mode : BHDrvMode S) (sid : SignalPqxdh.SessionId S) :
    CliDrvM S l (Option Nat) :=
  cliDrvStartM S l P (cliRunPure run) W mode sid

/-- Execute an admissible SM query `q` on promoted instance `i` via `cliOracleImplRM`, aligning
`gs.trans` on post-accept Bob deliveries and projecting `corr-P` leakage to `BinState`. -/
def cliRunStdSMM {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (runM : Inputs → M (Option Outcome)) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : CliDriverState S l) (i : Nat) (bi : ModelDriverInstance S l) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState CliPartyState (Plain l) Bytes)
    (q : (cliGameSmSpec l (BitVec 512)).Domain) :
    CliDrvMT S l M ((cliGameSmSpec l (BitVec 512)).Range q) := do
  let scheme := cliPqSchemeM runM l bi (gs.st .A) (gs.st .B)
  let cfg := cliConfigSpkS (St := CliPartyState) (Msg := Plain l) decT encT
  let gsIn : SM.GameState CliPartyState (Plain l) Bytes := match q with
    | .inl (.inl (.inr (.B, c))) => bhAlignTransForBob im.bobAccepted bi.meA.regId bi.hdr c gs
    | _ => gs
  let (r, gsOut) ←
    StateT.lift (StateT.lift ((cliOracleImplRM CliPartyState.bin scheme (2 + 1) qep cfg q).run gsIn))
  let gs' : SM.GameState CliPartyState (Plain l) Bytes := match q, r with
    | .inl (.inl (.inr (.B, c))), some (.accepted _ _ _) =>
      match gsIn.inTransit .A c with
      | some rMatched =>
        { gsOut with trans := gs.trans.filter (fun rec => rec.pos != rMatched.pos) }
      | none => { gsOut with trans := gs.trans }
    | .inl (.inl (.inr (.B, _))), _ => { gsOut with trans := gs.trans }
    | _, _ => gsOut
  let im' := bhMetaAfterSM ds.toModelDriverState bi im q r
  set { ds with bhInsts := ds.bhInsts.set i { bi with gs := some (cliMapGameState CliPartyState.bin gs') },
                instMeta := ds.instMeta.set i im',
                instGs := ds.instGs.set i (some gs') }
  return r

def cliRunStdSM (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (run : CliRun) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : CliDriverState S l) (i : Nat) (bi : ModelDriverInstance S l) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState CliPartyState (Plain l) Bytes)
    (q : (cliGameSmSpec l (BitVec 512)).Domain) :
    CliDrvM S l ((cliGameSmSpec l (BitVec 512)).Range q) :=
  cliRunStdSMM S l (cliRunPure run) qep decT encT ds i bi im gs q

/-- Pre-filter canonical pre-key wires to Alice and unpartnered or duplicate-in-transit wires to Bob
before calling `cliRunStdSMM`. -/
def cliStepLocalSMM {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (runM : Inputs → M (Option Outcome)) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : CliDriverState S l) (i : Nat) (bi : ModelDriverInstance S l) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState CliPartyState (Plain l) Bytes) :
    (q : (cliGameSmSpec l (BitVec 512)).Domain) →
      CliDrvMT S l M ((cliGameSmSpec l (BitVec 512)).Range q)
  | .inl (.inl (.inr (.A, c))) => do
    if (bhDecodePreKeyMsgE c).isSome then return none
    else cliRunStdSMM S l runM qep decT encT ds i bi im gs (.inl (.inl (.inr (.A, c))))
  | .inl (.inr (.A, c)) => do
    if (bhDecodePreKeyMsgE c).isSome then return none
    else cliRunStdSMM S l runM qep decT encT ds i bi im gs (.inl (.inr (.A, c)))
  | .inl (.inl (.inr (.B, c))) => do
    if (bhPartneredInnerBytes im.bobAccepted bi.meA.regId bi.hdr c).isNone then return none
    else cliRunStdSMM S l runM qep decT encT ds i bi im gs (.inl (.inl (.inr (.B, c))))
  | .inl (.inr (.B, c)) => do
    if !im.bobAccepted then return none
    else if (bhPartneredInnerBytes true bi.meA.regId bi.hdr c).isNone ||
        bhPartneredInTransitA true bi.meA.regId bi.hdr c gs then return none
    else cliRunStdSMM S l runM qep decT encT ds i bi im gs (.inl (.inr (.B, c)))
  | q => cliRunStdSMM S l runM qep decT encT ds i bi im gs q

def cliStepLocalSM (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (run : CliRun) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : CliDriverState S l) (i : Nat) (bi : ModelDriverInstance S l) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState CliPartyState (Plain l) Bytes) :
    (q : (cliGameSmSpec l (BitVec 512)).Domain) →
      CliDrvM S l ((cliGameSmSpec l (BitVec 512)).Range q) :=
  cliStepLocalSMM S l (cliRunPure run) qep decT encT ds i bi im gs

/-- Per-instance SM oracle handler checking `bhDrvInstClean` and pre-accept `ikA` corruption before
dispatching to `cliStepLocalSMM` (or `ext` for external instances). -/
abbrev cliDrvSMM {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (runM : Inputs → M (Option Outcome)) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec l (BitVec 512)) (CliDrvMT S l M)) :
    QueryImpl (cliGameDrSpec l (BitVec 512)) (CliDrvMT S l M) := fun ⟨i, q⟩ => do
  let ds ← get
  if !bhDrvInstClean ds.toModelDriverState i then return bhSmDefaultWithSpqr q
  else
    match ds.bhInsts[i]?, ds.instMeta[i]? with
    | some bi, some im =>
      if !im.bobAccepted && bhIsBobRecvSMQuery q && bhInstIkACorrupted ds.toModelDriverState bi then
        let imCorr : ModelDriverInstanceMeta S := { im with bobAccepted := true, ikACorrAtAccept := true }
        set { ds with instMeta := ds.instMeta.set i imCorr }; return bhSmDefaultWithSpqr q
      else
        match ds.instGs[i]? with
        | some (some gs) => cliStepLocalSMM S l runM qep decT encT ds i bi im gs q
        | _ =>
          let r ← ext q
          set { ds with instMeta := ds.instMeta.set i (bhMetaAfterSM ds.toModelDriverState bi im q r) }; return r
    | _, _ => return bhSmDefaultWithSpqr q

def cliDrvSM (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (run : CliRun) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec l (BitVec 512)) (CliDrvM S l)) :
    QueryImpl (cliGameDrSpec l (BitVec 512)) (CliDrvM S l) :=
  cliDrvSMM S l (cliRunPure run) qep decT encT ext

abbrev cliDrvCtlM {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (S : SignalPqxdh.Setup) (l : Nat) (P : SignalPqxdh.Primitives)
    (runM : Inputs → M (Option Outcome)) (W : PEParams) (mode : BHDrvMode S) :
    QueryImpl (bhDrCtlSpec S) (CliDrvMT S l M)
  | .startDR sid => cliDrvStartM S l P runM W mode sid

/-- Control oracle handler dispatching `startDR` to `cliDrvStart`. -/
def cliDrvCtl (S : SignalPqxdh.Setup) (l : Nat) (P : SignalPqxdh.Primitives)
    (run : CliRun) (W : PEParams) (mode : BHDrvMode S) : QueryImpl (bhDrCtlSpec S) (CliDrvM S l)
  | .startDR sid => cliDrvStart S l P run W mode sid

/-- Full composed-game oracle handler combining uniform coins, one-key real-HKDF `bhDrvKeyInd`,
`cliDrvCtlM`, and `cliDrvSMM`. -/
abbrev cliDrvImplM {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (P : SignalPqxdh.Primitives) (runM : Inputs → M (Option Outcome)) (W : PEParams) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec l (BitVec 512)) (CliDrvMT S l M)) (mode : BHDrvMode S) :
    QueryImpl (cliGameSpec S l (BitVec 512)) (CliDrvMT S l M) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (CliDrvMT S l M) +
    (fun q => bhLiftCliM (M := M) (bhDrvKeyInd S l P false q)) +
    cliDrvCtlM S l P runM W mode + cliDrvSMM S l runM qep decT encT ext

def cliDrvImpl (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec l (BitVec 512)) (CliDrvM S l)) (mode : BHDrvMode S) :
    QueryImpl (cliGameSpec S l (BitVec 512)) (CliDrvM S l) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (CliDrvM S l) +
    (fun q => bhLiftCli (bhDrvKeyInd S l P false q)) +
    cliDrvCtl S l P run W mode + cliDrvSM S l run qep decT encT ext

end Dir

/-- CLI protocol interface `Σ_bin` of `G(Σ)` for runner `run`, model primitives `modelPrims X W`,
plaintext byte length `l`, and epoch cap `qep`, with `BinState` corruption leakage and win predicate
`driverSomeInstanceWon`. -/
def cliIface (S : SignalPqxdh.Setup) (run : CliRun) (X : UnreachedPqxdhPrimitives)
    (W : PEParams) (l qep : Nat) {Pt : Type} (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) : ComposedIface S l where
  St := BinState
  prims := modelPrims X W
  Drv := CliDriverState S l
  init _ := {}
  impl b := Dir.cliDrvImpl S l (modelPrims X W) run W qep decT encT bhNoExtWithSpqr
    (fun _ _ _ _ _ => some b)
  won ds b := driverSomeInstanceWon ds.toModelDriverState b

/-- Multi-session CLI security experiment `G(Σ_bin)` on PQXDH + SPQR party directories: runs `A`
against `cliIface`, returning a uniform bit if `allTestedSessionsFresh (modelPrims X W)` fails at
game end and `(b' == b || driverSomeInstanceWon ds.toModelDriverState b)` otherwise. -/
def cliPqExp (S : SignalPqxdh.Setup) (run : CliRun) (X : UnreachedPqxdhPrimitives)
    (W : PEParams) (l qep : Nat) {Pt : Type} (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) (A : CliGameAdversary S l (BitVec 512)) : ProbComp Bool :=
  composedExp (cliIface S run X W l qep decT encT) A.run

/-- Distinguishing advantage `2 |Pr[cliPqExp … = true] - 1/2|` (`boolBias`) of `A` in `cliPqExp`. -/
noncomputable def CliPqxdhAdvantage (S : SignalPqxdh.Setup) (run : CliRun) (X : UnreachedPqxdhPrimitives)
    (W : PEParams) (l qep : Nat) {Pt : Type} (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) (A : CliGameAdversary S l (BitVec 512)) : ℝ≥0∞ :=
  𝒟[cliPqExp S run X W l qep decT encT A].boolBias

end CryptoVerification.E2E
