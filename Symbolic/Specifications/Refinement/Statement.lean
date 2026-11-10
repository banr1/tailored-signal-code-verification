/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation

/-!
# Whole-Protocol Refinement Statement over `signal-session` CLI Runs

Defines the `signal-session` CLI execution environment (`CliCall`, `CliTurn`, `ValidCall`,
`CliTraces`, `CliReachable`), break/invert history guards (`InvertsGuarded`), CSPRNG coin-freshness
premise (`CoinsFresh`), prefix-plus-collision excuse (`CollisionAfterExplainedPrefix`), and the
generic trace-refinement statements (`CompRefinesCliR`, `CompRefinesCli`).
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH.Refinement (bundleBlob bundleU32 bundleSplitId bundleSplitSigned
  parseEcKey parseKyberKey parseBundleFiles)
export DY.Libsignal.PQXDH.Refinement (bundleBlob bundleU32 bundleSplitId bundleSplitSigned
  parseEcKey parseKyberKey parseBundleFiles)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.SignalSession (Inputs Outcome CliRun Cmd PublicBundle filesOf stdioPaths partyDirs
  bundleDir coinsFile oneTimePreKeyFile)

/-- Parameters of a single `signal-session` CLI invocation. -/
structure CliCall where
  party : Participant
  cmd : Cmd
  bundle : List (String × HwBytes)
  stdin : HwBytes
  coins : HwBytes

def CliCall.extra (c : CliCall) : List (String × HwBytes) :=
  c.bundle ++ [(coinsFile, c.coins)]

/-- Loader-admissibility and `filesOf` visibility for input file entries: excludes `.`, standard
stream names, leading `/`, `..` segments, and files exceeding `Arm64.MAX_LFS_FILESIZE`. -/
def FilesVisible (files : List (String × HwBytes)) : Prop :=
  ∀ f ∈ files, Arm64.normalizePath f.1 ≠ [] ∧
    Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath ∧
    Arm64.hasLeadingSlash f.1 = false ∧ Arm64.hasDotDot f.1 = false ∧
    f.2.length ≤ Arm64.MAX_LFS_FILESIZE

/-- Process `Inputs` `i` corresponding to CLI call `c` over directory snapshot `d`. -/
def InputsFor (c : CliCall) (d : DirectorySnapshot) (i : Inputs) : Prop :=
  i.argv = c.cmd.argv ∧
  i.dirs = partyDirs ++ (match c.cmd with | .init _ dir => [dir] | _ => []) ∧
  i.stdin = c.stdin ∧
  (∀ p, p ∉ stdioPaths → filesOf i.files p = (filesOf c.extra p).or (d p)) ∧
  FilesVisible i.files

/-- Inter-call environment state: per-party directory snapshots, `SignalMessage` bodies emitted by
earlier exit-0 `send` calls, and whether Bob is disabled (`bobOff`) after accepting an unmatched
pre-key message alongside an existing session. -/
structure CliTurn where
  dirs : Participant → DirectorySnapshot
  sent : List HwBytes
  bobOff : Bool

def CliTurn.init (d : Participant → DirectorySnapshot) : CliTurn := ⟨d, [], false⟩

/-- Non-empty session record of `p` with its peer, if present. -/
def CliTurn.records (t : CliTurn) (r : ProtocolSetup) (p : Participant) : Option HwBytes :=
  match t.dirs p (sessionPathOf r p) with
  | some rec_ => if rec_ = [] then none else some rec_
  | none => none

/-- Whether Bob's one-time pre-key file has been emptied or removed. -/
def CliTurn.opkUsed (t : CliTurn) (r : ProtocolSetup) : Bool :=
  r.withOpk && ((t.dirs r.bob (oneTimePreKeyFile r.opkId)).getD []).isEmpty

/-- Path equivalence up to `Arm64.normalizePath`. -/
def SamePath (p q : String) : Bool := Arm64.normalizePath p == Arm64.normalizePath q

/-- Remove `coins` and `bundle/` entries (under any equivalent normalized path) after a run. -/
def scrub (d : DirectorySnapshot) : DirectorySnapshot := fun p =>
  if SamePath p coinsFile || (Arm64.normalizePath p).head? == some bundleDir then none else d p

/-- Every bundle entry is a flat `bundle/<name>` path smaller than `2^31` bytes. -/
def BundleFilesFlat (files : List (String × HwBytes)) : Prop :=
  ∀ f ∈ files, (∃ name, Arm64.normalizePath f.1 = [bundleDir, name]) ∧ f.2.length < 2 ^ 31

/-- Any bundle parsed from `files` by `parseBundleFiles` satisfies `HonestBundle`. -/
def HonestBundleFiles (interp : ExternInterpretation) (r : ProtocolSetup)
    (files : List (String × HwBytes)) : Prop :=
  ∀ b, parseBundleFiles (filesOf files) = some b → HonestBundle interp r (bundleBlob b)

/-- Bob `recv` of a non-whisper message while holding an existing session that is not eligible for
promotion (`¬ EligibleForSessionPromotion`). -/
def PreKeyNoMatch (r : ProtocolSetup) (t : CliTurn) (c : CliCall) : Prop :=
  c.party = r.bob ∧ (∃ peer, c.cmd = .recv peer) ∧ c.stdin.head? ≠ some wireWhisperTag ∧
    ∃ rec_, t.records r r.bob = some rec_ ∧ ¬ EligibleForSessionPromotion rec_ c.stdin

open Classical in
/-- Updated `CliTurn` after call `c` exits with `code`, `out`, and `files`. -/
noncomputable def CliTurn.after (t : CliTurn) (r : ProtocolSetup) (c : CliCall) (code : Nat)
    (out : HwBytes) (files : DirectorySnapshot) : CliTurn :=
  { dirs := fun q => if q = c.party then scrub files else t.dirs q
    sent := t.sent ++ (match code, c.cmd with
      | 0, .send _ => (sentBody out).toList
      | _, _ => [])
    bobOff := t.bobOff || decide (code = 0 ∧ PreKeyNoMatch r t c) }

/-- Delete `p`'s session file (re-enabling Bob when `p = r.bob`). -/
def CliTurn.clearSession (t : CliTurn) (r : ProtocolSetup) (p : Participant) : CliTurn :=
  { dirs := fun q => if q = p then
      (fun path => if SamePath path (sessionPathOf r p) then none else t.dirs q path)
      else t.dirs q
    sent := t.sent
    bobOff := t.bobOff && !decide (p = r.bob) }

def BobCallAllowed (r : ProtocolSetup) (t : CliTurn) (c : CliCall) : Prop :=
  t.bobOff = true → c.party ≠ r.bob

abbrev BobSetupDHSecret (r : ProtocolSetup) (opkOk : Prop) (k : HwBytes) : Prop :=
  k = r.ikBSecBytes ∨ k = r.spkSecBytes ∨ (r.withOpk = true ∧ opkOk ∧ k = r.opkSecBytes)

abbrev SetupDHSecret (r : ProtocolSetup) (opkOk : Prop) (k : HwBytes) : Prop :=
  k = r.ikASecBytes ∨ BobSetupDHSecret r opkOk k

/-- Secrets currently present in `p`'s directory at turn `t` (long-term/prekey files and keys in
`p`'s active session record). -/
def KeyInDir (r : ProtocolSetup) (t : CliTurn) (p : Participant) (k : HwBytes) : Prop :=
  (p = r.alice ∧ k = r.ikASecBytes) ∨
  (p = r.bob ∧ (k = r.kyberSecB ∨ BobSetupDHSecret r (t.opkUsed r = false) k)) ∨
  ∃ rec, t.records r p = some (recordBytes rec) ∧ KeyInRecord rec k

def LeaksFrom (r : ProtocolSetup) (t : CliTurn) (leaks : List CliEvent) : Prop :=
  ∀ e ∈ leaks, ∃ p k, KeyInDir r t p k ∧ e = .env (.leak p k)

def runInput (c : CliCall) : HwBytes :=
  match c.cmd with
  | .init _ _ => ((parseBundleFiles (filesOf c.bundle)).map bundleBlob).getD []
  | _ => c.stdin

def runEventOf (c : CliCall) (exit : Option (Nat × HwBytes)) : RunEvent :=
  { party := c.party, cmd := c.cmd, input := runInput c, coins := c.coins, exit }

/-- Expected `coins` byte length for each CLI subcommand (`192` for `init`, `64` for `send`, `32`
for `recv`). -/
def coinsLen : Cmd → Nat
  | .init _ _ => 192
  | .send _ => 64
  | .recv _ => 32

/-- Size bounds on `c.stdin` matching the binary specifications' input domains. -/
def StdinBounded (c : CliCall) : Prop :=
  match c.cmd with
  | .init _ _ => True
  | .send _ => c.stdin.length < 2 ^ 32
  | .recv _ =>
    (∀ body, c.stdin = wireWhisperTag :: body → body.length < 2 ^ 32) ∧
    (c.stdin.head? ≠ some wireWhisperTag → c.stdin.length < 2 ^ 32) ∧
    (∀ q, parsePreKeyWire c.stdin = some q → q.message.length + 2048 < 2 ^ 32) ∧
    (∀ (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes),
      ik.length = 32 → ek.length = 32 → ct.length = 1568 →
      c.stdin = preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg →
      msg.length + 2048 < 2 ^ 32)

def FilesBounded (d : DirectorySnapshot) : Prop :=
  ∀ path b, d path = some b → b.length < 2 ^ 31

/-- Preconditions for a guarded CLI call `c` at turn `t`: coin and file bounds, `BobCallAllowed`,
role/session state discipline, `HonestBundleFiles` on `init`, send-counter bound `< 2^32 - 1` on
`send`, and `PqFromHonest` on `recv`. -/
def ValidCall (interp : ExternInterpretation) (r : ProtocolSetup) (t : CliTurn) (c : CliCall) :
    Prop :=
  c.coins.length = coinsLen c.cmd ∧ StdinBounded c ∧ FilesBounded (t.dirs c.party) ∧
  BobCallAllowed r t c ∧
  match c.cmd with
  | .init peer dir =>
    c.party = r.alice ∧ peer = peerOf r r.alice ∧ dir = bundleDir ∧ c.stdin = [] ∧
      t.records r r.alice = none ∧ BundleFilesFlat c.bundle ∧ HonestBundleFiles interp r c.bundle
  | .send peer =>
    (c.party = r.alice ∨ c.party = r.bob) ∧ peer = peerOf r c.party ∧ c.bundle = [] ∧
      t.sent.length < 2 ^ 32 - 1 ∧ t.records r c.party ≠ none
  | .recv peer =>
    (c.party = r.alice ∨ c.party = r.bob) ∧ peer = peerOf r c.party ∧ c.bundle = [] ∧
      ((t.records r c.party ≠ none ∧
          ∃ body, c.stdin = wireWhisperTag :: body ∧ PqFromHonest t.sent body) ∨
        (c.party = r.bob ∧ (c.stdin.head? ≠ some wireWhisperTag ∨ t.records r r.bob = none) ∧
          ∀ q, parsePreKeyWire c.stdin = some q → PqFromHonest t.sent q.message))

/-- Guarded CLI event traces generated by `Rel` from turn `t`: session deletions (`clear`),
primitive break/invert events (`breakInvert`), exited CLI calls preceded by directory leaks
(`step`), and aborted CLI calls terminating the trace (`stop`). -/
inductive CliTraces (Rel : Inputs → Option Outcome → Prop) (interp : ExternInterpretation)
    (r : ProtocolSetup) : CliTurn → List CliEvent → Prop
  | done (t : CliTurn) : CliTraces Rel interp r t []
  | clear {t : CliTurn} {evs : List CliEvent} (p : Participant) :
      CliTraces Rel interp r (t.clearSession r p) evs → CliTraces Rel interp r t evs
  | breakInvert {t : CliTurn} {e : EnvEvent} {evs : List CliEvent} :
      e.IsBreakInvert → CliTraces Rel interp r t evs → CliTraces Rel interp r t (.env e :: evs)
  | step {t : CliTurn} {leaks : List CliEvent} {c : CliCall} {i : Inputs} {code : Nat}
      {out : HwBytes} {files : DirectorySnapshot} {evs : List CliEvent} :
      LeaksFrom r t leaks →
      ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
      Rel i (some (.exited code out files)) →
      CliTraces Rel interp r (t.after r c code out files) evs →
      CliTraces Rel interp r t (leaks ++ .run (runEventOf c (some (code, out))) :: evs)
  | stop {t : CliTurn} {leaks : List CliEvent} {c : CliCall} {i : Inputs}
      {o : Option Outcome} :
      LeaksFrom r t leaks →
      ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
      Rel i o → o = some .aborted →
      CliTraces Rel interp r t (leaks ++ [.run (runEventOf c none)])

/-- Inter-call turns reachable from `t₀` via exited guarded calls and session deletions. -/
inductive CliReachable (Rel : Inputs → Option Outcome → Prop) (interp : ExternInterpretation)
    (r : ProtocolSetup) (t₀ : CliTurn) : CliTurn → Prop
  | init : CliReachable Rel interp r t₀ t₀
  | clear {t : CliTurn} (p : Participant) :
      CliReachable Rel interp r t₀ t → CliReachable Rel interp r t₀ (t.clearSession r p)
  | step {t : CliTurn} {c : CliCall} {i : Inputs} {code : Nat} {out : HwBytes}
      {files : DirectorySnapshot} :
      CliReachable Rel interp r t₀ t →
      ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
      Rel i (some (.exited code out files)) →
      CliReachable Rel interp r t₀ (t.after r c code out files)

/-- 32-byte X25519 private-key slices read from `ev.coins` (`0..32` and `160..192` for `init`;
`0..32` for `recv`; none for `send`). -/
def dhCoinSecrets (ev : RunEvent) : List HwBytes :=
  match ev.cmd with
  | .init _ _ => [slice ev.coins 0 32, slice ev.coins 160 32]
  | .recv _ => [slice ev.coins 0 32]
  | .send _ => []

/-- Whether `sk` is a setup X25519 secret or a `dhCoinSecrets` slice of an exit-0 run in `evs`. -/
def HonestDHSecret (r : ProtocolSetup) (evs : List CliEvent) (sk : HwBytes) : Prop :=
  SetupDHSecret r True sk ∨
    ∃ ev out, .run ev ∈ evs ∧ ev.exit = some (0, out) ∧ sk ∈ dhCoinSecrets ev

/-- History guard on `invertDH` and `invertKEM` events: each follows its corresponding `breakDH` /
`breakKEM` event and inverts an honest setup or coin-drawn public key. -/
def InvertsGuarded (interp : ExternInterpretation) (r : ProtocolSetup) (evs : List CliEvent) : Prop :=
  ∀ (pre post : List CliEvent) (e : EnvEvent), evs = pre ++ .env e :: post →
    match e with
    | .invertDH pk sk =>
      .env .breakDH ∈ pre ∧ HonestDHSecret r pre sk ∧ pk = pubBytes interp sk
    | .invertKEM pk sk =>
      .env .breakKEM ∈ pre ∧ sk = r.kyberSecB ∧ pk = r.opaqueBytes r.pqpkPubTerm
    | _ => True

/-- 32-byte Kyber encapsulation entropy extracted from the first byte of each 4-byte CSPRNG fill at
offsets `32 + 4 * j` (`j < 32`) of an `init` call's `coins`. -/
def kyberCoinEntropy (coins : HwBytes) : HwBytes :=
  (List.range 32).map fun j => (coins[32 + 4 * j]?).getD 0#8

/-- Clamped 32-byte secret draws consumed by `ev` (`dhCoinSecrets` plus `kyberCoinEntropy` on
`init`; `dhCoinSecrets` on `recv`; none on `send`). -/
def coinDraws (ev : RunEvent) : List HwBytes :=
  match ev.cmd with
  | .init _ _ => (dhCoinSecrets ev ++ [kyberCoinEntropy ev.coins]).map clamp
  | .recv _ => (dhCoinSecrets ev).map clamp
  | .send _ => []

def exitedZeroDraws (ev : RunEvent) : List HwBytes :=
  match ev.exit with
  | some (0, _) => coinDraws ev
  | _ => []

/-- Clamped setup X25519 secrets of `r` (`ikA`, `ikB`, `spkB`, and `opkB` when `r.withOpk` holds). -/
def setupDHSecrets (r : ProtocolSetup) : List HwBytes :=
  [clamp (secretBytes r 0), clamp (secretBytes r 1), clamp (secretBytes r 2)] ++
    if r.withOpk then [clamp (secretBytes r 6)] else []

/-- CSPRNG coin-freshness premise for security theorems: all clamped setup X25519 secrets and
clamped secret coin draws of exit-0 runs in `evs` are pairwise distinct (`List.Nodup`). Refinement
theorems (`CompRefinesCli*`) do not assume `CoinsFresh`. -/
def CoinsFresh (r : ProtocolSetup) (evs : List CliEvent) : Prop :=
  (setupDHSecrets r ++ evs.flatMap fun
    | .run ev => exitedZeroDraws ev
    | .env _ => []).Nodup

instance instDecidableCoinsFresh (r : ProtocolSetup) (evs : List CliEvent) :
    Decidable (CoinsFresh r evs) :=
  inferInstanceAs (Decidable (List.Nodup _))

/-- Inner `SignalMessage` body `b` of a received whisper or pre-key wire frame `input`. -/
def RecvBody (input b : HwBytes) : Prop :=
  match input with
  | tag :: body =>
    (tag = wireWhisperTag ∧ b = body) ∨ ∃ p, parsePreKeyWire (tag :: body) = some p ∧ b = p.message
  | [] => False

/-- Whether `ss` already read a colliding network term on an earlier exit-0 `recv` event in `evs`. -/
def ReadCollisionCli (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (evs : List CliEvent) : Prop :=
  ∃ (evs₁ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent) (ss₁ ss₂ : List Step) (m : Step)
    (vis₁ : List VisEntry) (msgIdx : Nat) (out b : HwBytes) (t : DY.Bytes),
    evs = evs₁ ++ .run ev :: evs₂ ∧ ss = ss₁ ++ m :: ss₂ ∧
    (∃ peer, ev.cmd = .recv peer) ∧ ev.exit = some (0, out) ∧ RecvBody ev.input b ∧
    MatchesEvents interp r S g (setupTrace r) ss₁ evs₁ vis₁ ∧
    m.decryptMsgIdx? = some msgIdx ∧
    (runTrace r ss₁).getMessageSentAt msgIdx = some t ∧
    RecvCollisionOn interp r S g (runTrace r ss₁) vis₁ (honestSaltsOf r ss₁) t

/-- Whether extending `(g, ss)` by attacker-known `network` steps and one decrypt step reading `t`
explains `evs₁ ++ [.run ev]`. -/
def ModelAcceptsTermAfterAttackerSends (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (evs₁ : List CliEvent) (ev : RunEvent) (t : DY.Bytes) : Prop :=
  ∃ (ext : List DY.Bytes) (m : Step) (msgIdx : Nat) (g₁ : Ghost) (vis₁ : List VisEntry),
    (∀ x ∈ ext, x.AttackerKnows (runTrace r ss)) ∧
    m.decryptMsgIdx? = some msgIdx ∧
    g₁.addr = g.addr ∧ (∀ i, i < (runTrace r ss).length → g₁.σ i = g.σ i) ∧
    (runTrace r (ss ++ ext.map .network)).getMessageSentAt msgIdx = some t ∧
    Explains interp r S g₁ (ss ++ ext.map .network ++ [m]) vis₁ (evs₁ ++ [.run ev])

/-- Under explanation `(g', ss', vis')` of `evs₁`, either every representation of `b` hits
`RecvCollisionOn ∨ ReselectCollisionOn`, or at least one representation is accepted for `ev` and
every accepted representation hits `RecvCollisionOn`. -/
def RepresentationsCollideOrAcceptedCollide (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (evs₁ : List CliEvent) (g' : Ghost) (ss' : List Step)
    (vis' : List VisEntry) (ev : RunEvent) (b : HwBytes) : Prop :=
  let tr := runTrace r ss'
  let salts := honestSaltsOf r ss'
  let reps := recvRepresentationsOn interp S g' tr b
  let accepts := ModelAcceptsTermAfterAttackerSends interp r S g' ss' evs₁ ev
  (∀ t ∈ reps, RecvCollisionOn interp r S g' tr vis' salts t ∨
      ReselectCollisionOn interp r S g' tr vis' salts t) ∨
    ((∃ t ∈ reps, accepts t) ∧
      ∀ t ∈ reps, accepts t → RecvCollisionOn interp r S g' tr vis' salts t)

/-- `SignalMessage` body `b` in `ev` has a symbolic representation under `(g, ss)` and hits
`RepresentationsCollideOrAcceptedCollide` under every collision-free explanation of `evs₁`. -/
def SignalMsgAcceptedOnlyViaCollision (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ss : List Step) (evs₁ : List CliEvent) (ev : RunEvent)
    (b : HwBytes) : Prop :=
  (∃ t, t ∈ recvRepresentationsOn interp S g (runTrace r ss) b) ∧
    ∀ g' ss' vis', Explains interp r S g' ss' vis' evs₁ →
      ¬ ReadCollisionCli interp r S g' ss' evs₁ →
      RepresentationsCollideOrAcceptedCollide interp r S evs₁ g' ss' vis' ev b

/-- Pre-key message `p` (wire bytes `b`) starts a Bob session only via `KyberMismatch` or
`BobSessionStartCollidesOrImplicitRejectsOn` across all collision-free explanations of `evs₁`. -/
def PreKeyStartCollidesOrRejects (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (evs₁ : List CliEvent) (b : HwBytes) (p : PreKeyFields) : Prop :=
  (∃ x, x ∈ preKeyRepresentationsOn interp r S g (runTrace r ss) b) ∧
    (KyberMismatch interp r p ∨
      ∀ g' ss' vis', Explains interp r S g' ss' vis' evs₁ →
        ¬ ReadCollisionCli interp r S g' ss' evs₁ →
        ∀ x ∈ preKeyRepresentationsOn interp r S g' (runTrace r ss') b,
          BobSessionStartCollidesOrImplicitRejectsOn interp r S g' (runTrace r ss') vis' (honestSaltsOf r ss') p x)

/-- Ghosts sharing `g.σ` that explain `evs₁` via the same step sequence `ss`. -/
def PrefixExplainingGhosts (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (evs₁ : List CliEvent) : Set Ghost :=
  {g' | g'.σ = g.σ ∧ ∃ vis', Explains interp r S g' ss vis' evs₁}

/-- Next run event `ev` after explained prefix `evs₁` forces a cryptographic collision on either an
exit-0 `recv` or the plaintext of a `send`. -/
def NextEventCollides (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ss : List Step) (vis : List VisEntry)
    (evs₁ : List CliEvent) (ev : RunEvent) : Prop :=
  let tr := runTrace r ss
  match ev.cmd with
  | .recv _ =>
    (∃ out, ev.exit = some (0, out)) ∧
    match ev.input with
    | tag :: body =>
      (tag = wireWhisperTag ∧ SignalMsgAcceptedOnlyViaCollision interp r S g ss evs₁ ev body) ∨
      (∃ p, parsePreKeyWire (tag :: body) = some p ∧
        ((KnownBaseKeyOn interp S g tr p ∧ p.version = 4 ∧
            p.identityKey.take 33 = ecKey (pubBytes interp (secretBytes r 0)) ∧
            SignalMsgAcceptedOnlyViaCollision interp r S g ss evs₁ ev p.message) ∨
         (¬ KnownBaseKeyOn interp S g tr p ∧
            PreKeyStartCollidesOrRejects interp r S g ss evs₁ (tag :: body) p)))
    | [] => False
  | .send _ =>
    let v := ptEntryAt tr
    BytesMatchEntry interp r S g .pt ev.input v ∧
      ∀ g' ∈ PrefixExplainingGhosts interp r S g ss evs₁,
        MemoCollisionOn interp r S g' (fun u => u.AttackerKnows tr) tr vis v.terms v.terms
  | .init _ _ => False

/-- Some prefix `evs₁` of `evs` is explained by `(g, ss, vis)`, and the immediately following run
event forces `NextEventCollides`. -/
def CollisionAfterExplainedPrefix (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (evs : List CliEvent) : Prop :=
  ∃ (evs₁ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent) (g : Ghost) (ss : List Step)
    (vis : List VisEntry),
    evs = evs₁ ++ .run ev :: evs₂ ∧
    Explains interp r S g ss vis evs₁ ∧
    NextEventCollides interp r S g ss vis evs₁ ev

/-- Machine-independent external crypto contracts: `ExternCryptoLawsHold`, canonical X25519 public
keys, and rejection of X25519 torsion shifts. -/
def ExternContractsHoldCli (interp : ExternInterpretation) : Prop :=
  DY.Libsignal.Refinement.ExternCryptoLawsHold interp ∧ X25519PubCanonical interp ∧
    DY.Libsignal.PQXDH.Refinement.X25519TorsionShiftsRejected interp

/-- Whole-protocol CLI trace refinement starting from initial directory family `dirs`: for every
valid `interp`, agreeing `W`, and well-formed `r`, there exist opaque semantics `S` such that every
guarded trace `evs` is either explained (`Explains`) or hits `CollisionAfterExplainedPrefix`. -/
def CompRefinesCliR {ω : Type} (Agree : ExternInterpretation → ω → Prop)
    (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop)
    (dirs : ExternInterpretation → ProtocolSetup → Participant → DirectorySnapshot) : Prop :=
  ∀ interp : ExternInterpretation, ExternContractsHoldCli interp →
  ∀ W : ω, Agree interp W →
  ∀ r : ProtocolSetup, ProtocolSetupWF r →
  ∃ S : OpaqueSymbolSemantics, ∀ evs : List CliEvent,
    CliTraces (R interp W) interp r (CliTurn.init (dirs interp r)) evs →
    InvertsGuarded interp r evs →
      (∃ g ss vis, Explains interp r S g ss vis evs) ∨ CollisionAfterExplainedPrefix interp r S evs

/-- Whole-protocol CLI trace refinement starting from `initDirs`. -/
def CompRefinesCli {ω : Type} (Agree : ExternInterpretation → ω → Prop)
    (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop) : Prop :=
  CompRefinesCliR Agree R initDirs

def runFnToRelation (run : CliRun) : Inputs → Option Outcome → Prop := fun i o => run i = o

end DY.Libsignal.Composed.Refinement.Cli
