/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
public import LibsignalBinary.Specifications.SignalSession.Run

/-!
# Core definitions of the composed CLI game: wire parsers, driver, `KeyInd` handler, cost budgets

**Trusted: definitions used by the statement.** Every declaration in this file lies in the closure
of `Computational/Theorems/Main.lean` (via `Computational/Specifications/Game/StatementPq.lean`,
`Computational/Specifications/LibsignalCli/StatementPqElf.lean`, and
`Computational/Specifications/Reductions/Pqxdh/StatementPqReds.lean`). See
`Computational/docs/DEVIATIONS.md`.

Non-ELF building blocks of the composed PQXDH + Double Ratchet security game played against the
libsignal CLI binary (`StatementPq.lean`). The `bh` / `BH` ("binary harness") prefix denotes the
game in which sessions carry wire-byte state (`BinState`) rather than abstract model state
(`GhostState Bytes`). The adversary interacts with four oracle families: uniform coins, the PQXDH
key-indistinguishability game `KeyInd`, the session-promotion control oracle `startDR sid`, and
per-instance ACD19 secure-messaging (SM) oracles; the driver mirrors the public `KeyInd`
transcript, guards promotion, and runs each promoted instance as an SM game.

This file also connects the composed game specifications (`bhGameSpec`, `bhTargetGameSpec`) to the
`ReductionDsl` operation tables and codecs of `AtomicOps.lean` and `TargetCodecs.lean`, and defines
the closed-form step-cost budgets `bhAdapterCostBudget` (for the wire-to-model adapter) and
`bhE2ECostBudget` (for the multi-session composition reductions in `StatementPqReds.lean`), along
with their online/offline per-kind counterparts `bhAdapterCostBudgetByKind` and
`bhE2ECostBudgetByKind`.
-/

@[expose] public section

set_option autoImplicit false
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession (stdinCapBytes)

/-! ## Canonical tag-3 `PreKeySignalMessage` wire parser (`DEV-C18`) -/

/-- Decode one LEB128 varint, returning `(value, remainingBytes)`. -/
def bhReadProstVarint : List (BitVec 8) → Option (ℕ × List (BitVec 8))
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else (bhReadProstVarint rest).map (fun (hi, rest') => (b.toNat - 128 + 128 * hi, rest'))

/-- Parse optional protobuf field 1 (`preKeyId`, tag `0x08#8`). -/
def bhParseOptPreKeyId : List (BitVec 8) → Option (Option UInt32 × List (BitVec 8))
  | [] => some (none, [])
  | b :: rest =>
    if b == 0x08#8 then (bhReadProstVarint rest).map (fun (n, r) => (some (UInt32.ofNat n), r))
    else some (none, b :: rest)

/-- Parse a required `uint32` varint field with tag byte `keyByte`. -/
def bhParseUint32Field (keyByte : BitVec 8) : List (BitVec 8) → Option (UInt32 × List (BitVec 8))
  | k :: rest =>
    if k == keyByte then (bhReadProstVarint rest).map (fun (n, r) => (UInt32.ofNat n, r)) else none
  | [] => none

/-- Parse a 33-byte DJB Curve25519 public-key field (type byte `0x05#8`) with tag `keyByte`. -/
def bhParseDjbKeyField (keyByte : BitVec 8) :
    List (BitVec 8) → Option (List (BitVec 8) × List (BitVec 8))
  | k :: 0x21#8 :: 0x05#8 :: rest =>
    if k == keyByte && decide (32 ≤ rest.length) then some (rest.take 32, rest.drop 32) else none
  | _ => none

/-- Parse length-delimited field 4 (`message`, tag `0x22#8`), returning `(inner, rest)`. -/
def bhParseInnerMsgFieldWithRest : List (BitVec 8) → Option (List (BitVec 8) × List (BitVec 8))
  | 0x22#8 :: rest =>
    (bhReadProstVarint rest).bind (fun (len, afterLen) =>
      if decide (len ≤ afterLen.length) then some (afterLen.take len, afterLen.drop len) else none)
  | _ => none

/-- Parse field 8 (`kyberCiphertext`, tag `0x42#8`, length `1569`, type byte `0x08#8`). -/
def bhParseKyberCtField : List (BitVec 8) → Option (List (BitVec 8))
  | 0x42#8 :: 0xa1#8 :: 0x0c#8 :: 0x08#8 :: rest =>
    if decide (1568 ≤ rest.length) then some (rest.take 1568) else none
  | _ => none

/-- Extract the PQXDH `HandshakeHdr` from `PreKeyMessageFields`. -/
def bhHdrOfPreKeyMsg (m : PreKeyMessageFields) : SignalPqxdh.HandshakeHdr :=
  { ikAPk := vecU8 m.idPub, ekAPk := vecU8 m.baseKey, spkId := u32 m.spkId,
    opkId? := m.opkId.map u32, pqspkId := u32 m.kpkId, kemCt := vecU8 m.kyberCt }

/-- Parse a tag-3 `PreKeySignalMessage` wire buffer without checking canonical re-encoding. -/
def bhDecodePreKeyMsgERaw : Bytes → Option PreKeyMessageFields
  | t :: v :: proto =>
    if t == wirePrekey && v == versionByte currentVersion then
      (bhParseOptPreKeyId proto).bind fun (opkId?, after1) =>
      (bhParseDjbKeyField 0x12#8 after1).bind fun (bkBytes, after2) =>
      (bhParseDjbKeyField 0x1a#8 after2).bind fun (idBytes, after3) =>
      (bhParseInnerMsgFieldWithRest after3).bind fun (inner, after4) =>
      (bhParseUint32Field 0x28#8 after4).bind fun (regId, after5) =>
      (bhParseUint32Field 0x30#8 after5).bind fun (spkId, after6) =>
      (bhParseUint32Field 0x38#8 after6).bind fun (pqspkId, after7) =>
      (bhParseKyberCtField after7).bind fun kemCtBytes =>
      if hbk : bkBytes.length = 32 then if hid : idBytes.length = 32 then
        if hct : kemCtBytes.length = 1568 then
          some { regId := regId.toBitVec, opkId := opkId?.map UInt32.toBitVec,
                 spkId := spkId.toBitVec, kpkId := pqspkId.toBitVec, kyberCt := ⟨kemCtBytes, hct⟩,
                 baseKey := ⟨bkBytes, hbk⟩, idPub := ⟨idBytes, hid⟩, inner := inner }
        else none
      else none else none
    else none
  | _ => none

/-- Parse a canonical tag-3 `PreKeySignalMessage` wire buffer (`wirePrekey :: m.bytes`). -/
def bhDecodePreKeyMsgE (c : Bytes) : Option PreKeyMessageFields :=
  match bhDecodePreKeyMsgERaw c with
  | some m => if c == wirePrekey :: m.bytes then some m else none | none => none

/-- Wrap a 32-byte PQXDH public key as a session `IdentityKey`. -/
def bhIdKeyOf (bs : SignalPqxdh.Bytes) : IdentityKey := ⟨⟨u8Vec 32 bs⟩⟩

/-! ## Initiator random tape and strict input builders (`DEV-PQ6`) -/

/-- Ephemeral X25519 secret scalar `ekASk` (bytes `0..32`) from a 160-byte initiator tape. -/
def tapeEkASk (t_init : List.Vector (BitVec 8) 160) : SignalPqxdh.Bytes :=
  toU8 (t_init.toList.take 32)

/-- 32-byte ML-KEM encapsulation seed (`t_init[32 + 4*i]` for `i < 32`) from a 160-byte initiator
tape. -/
def tapeKemCoins (t_init : List.Vector (BitVec 8) 160) : SignalPqxdh.Bytes :=
  vecU8 (List.Vector.ofFn fun i : Fin 32 => t_init.get ⟨32 + 4 * i.val, by omega⟩)

/-- Concatenate a 160-byte handshake tape and a 32-byte Double Ratchet tape (`DEV-PQ6`). -/
def appendInitiateTape (t_init : List.Vector (BitVec 8) 160)
    (t_dr : List.Vector (BitVec 8) 32) : List.Vector (BitVec 8) initiateTapeLen :=
  ⟨t_init.toList ++ t_dr.toList, by simp [initiateTapeLen]⟩

/-- Convert `bs` to an `n`-byte vector, returning `none` if `bs.length ≠ n`. -/
def fitU8VecStrict (n : ℕ) (bs : SignalPqxdh.Bytes) : Option (List.Vector (BitVec 8) n) :=
  let l := ofU8 bs; if h : l.length = n then some ⟨l, h⟩ else none

/-- Build `LocalIdentity` for principal `u`, failing unless `secIKA0` has 32 bytes. -/
def mkMeEStrict (u : ℕ) (secIKA0 : SignalPqxdh.Bytes) : Option LocalIdentity := do
  let idPriv ← fitU8VecStrict 32 secIKA0
  some { regId := BitVec.ofNat 32 u, idPriv := idPriv }

/-- Build `ResponderPreKeySecrets` for slot index `j`, failing on any key-length mismatch. -/
def mkKeysEStrict (j : ℕ) (bEntry : SignalPqxdh.SpkBundleEntry)
    (opk? : Option (ℕ × SignalPqxdh.Bytes)) : Option ResponderPreKeySecrets := do
  let spkPriv ← fitU8VecStrict 32 bEntry.spkSk
  let kpkPub ← fitU8VecStrict 1568 bEntry.pqspkPk
  let kpkSec ← fitU8VecStrict 3168 bEntry.pqspkSk
  let opkV ← match opk? with
    | none => some none
    | some (o, sk) => do let v ← fitU8VecStrict 32 sk; some (some (BitVec.ofNat 32 o, v))
  some { spkId := BitVec.ofNat 32 j, spkPriv := spkPriv, opk := opkV,
         kpkId := BitVec.ofNat 32 j, kpkPub := kpkPub, kpkSec := kpkSec }

/-- Build `PreKeyBundleFields` for registration ID `u`, failing on any key- or signature-length
mismatch. -/
def mkBundleEStrict (u : ℕ) (bnd : SignalPqxdh.PreKeyBundleInput) : Option PreKeyBundleFields := do
  let spkPub ← fitU8VecStrict 32 bnd.spkB
  let spkSig ← fitU8VecStrict 64 bnd.spkSig
  let kpkPub ← fitU8VecStrict 1568 bnd.pqspkB
  let kpkSig ← fitU8VecStrict 64 bnd.pqspkSig
  let idPub ← fitU8VecStrict 32 bnd.ikB
  let opkV ← match bnd.opkB? with
    | none => some none
    | some (id, pk) => do let v ← fitU8VecStrict 32 pk; some (some (BitVec.ofNat 32 id.toNat, v))
  some { regId := BitVec.ofNat 32 u, opk := opkV, spkId := BitVec.ofNat 32 bnd.spkId.toNat,
         spkPub := spkPub, spkSig := spkSig, kpkId := BitVec.ofNat 32 bnd.pqspkId.toNat,
         kpkPub := kpkPub, kpkSig := kpkSig, idPub := idPub }

/-! ## Tag-3 routing, in-transit alignment, and injection filter
(`DEV-C11`, `DEV-C18`, `DEV-C19`) -/

/-- Canonical `PreKeyMessageFields` expected from initiator `regIdA` with header `hdr` and payload
`inner` (`DEV-C11`). -/
def bhExpectedPreKeyMsg (regIdA : BitVec 32) (hdr : SignalPqxdh.HandshakeHdr) (inner : Bytes) :
    PreKeyMessageFields :=
  { regId := regIdA, opkId := hdr.opkId?.map (fun id => BitVec.ofNat 32 id.toNat),
    spkId := BitVec.ofNat 32 hdr.spkId.toNat, kpkId := BitVec.ofNat 32 hdr.pqspkId.toNat,
    kyberCt := u8Vec SignalPqxdh.kyberCtLen hdr.kemCt, baseKey := u8Vec 32 hdr.ekAPk,
    idPub := u8Vec 32 hdr.ikAPk, inner := inner }

/-- Extract the inner `SignalMessage` bytes from a canonical tag-3 or tag-2 wire message. -/
def bhWireInnerBytes (c : Bytes) : Option Bytes :=
  match bhDecodePreKeyMsgE c with
  | some m => some m.inner
  | none => match c with | t :: body => if t == wireWhisper then some body else none | [] => none

/-- Extract the inner `SignalMessage` bytes of a wire `c` partnered with `(regIdA, sessionHdr)`
(`DEV-C11`, `DEV-C18`, `DEV-C19`): requires a byte-exact canonical `PreKeySignalMessage` before
Bob's first accept, and either a header-matching `PreKeySignalMessage` or a tag-2 `SignalMessage`
thereafter. -/
def bhPartneredInnerBytes (bobAccepted : Bool) (regIdA : BitVec 32)
    (sessionHdr : SignalPqxdh.HandshakeHdr) (c : Bytes) : Option Bytes :=
  if !bobAccepted then
    match bhDecodePreKeyMsgE c with
    | some m =>
      if c == wirePrekey :: (bhExpectedPreKeyMsg regIdA sessionHdr m.inner).bytes then
        some m.inner
      else none
    | none => none
  else
    match bhDecodePreKeyMsgE c with
    | some m => if bhHdrOfPreKeyMsg m == sessionHdr then some m.inner else none
    | none => match c with | t :: body => if t == wireWhisper then some body else none | [] => none

/-- Rewrite the first Alice in-transit record with inner `SignalMessage` `inner` to outer wire
`c`. -/
def bhAlignTransList {Msg : Type} (inner c : Bytes) :
    List (SM.Record Msg Bytes) → List (SM.Record Msg Bytes)
  | [] => []
  | r :: rest =>
    if r.pos.sender == .A && bhWireInnerBytes r.ct == some inner then { r with ct := c } :: rest
    else r :: bhAlignTransList inner c rest

/-- Align `gs.trans` on post-accept `deliver-B(c)` so a re-wrapped pre-key wire matches Alice's
in-transit inner `SignalMessage` (`DEV-C11`, `DEV-C18`); pre-accept deliveries require byte-exact
outer-wire matching. -/
def bhAlignTransForBob {St Msg : Type} (bobAccepted : Bool) (regIdA : BitVec 32)
    (sessionHdr : SignalPqxdh.HandshakeHdr) (c : Bytes)
    (gs : SM.GameState St Msg Bytes) : SM.GameState St Msg Bytes :=
  if !bobAccepted then gs
  else
    match bhPartneredInnerBytes true regIdA sessionHdr c with
    | some inner => { gs with trans := bhAlignTransList inner c gs.trans }
    | none => gs

/-- Whether `c` is partnered with `(regIdA, sessionHdr)` and carries inner `SignalMessage` bytes
currently in transit from Alice. -/
def bhPartneredInTransitA {St Msg : Type} (bobAccepted : Bool) (regIdA : BitVec 32)
    (sessionHdr : SignalPqxdh.HandshakeHdr) (c : Bytes) (gs : SM.GameState St Msg Bytes) : Bool :=
  match bhPartneredInnerBytes bobAccepted regIdA sessionHdr c with
  | some inner =>
    gs.trans.any (fun r => r.pos.sender == .A && bhWireInnerBytes r.ct == some inner)
  | none => false

/-- Ciphertext injection filter for the binary-harness SM game (`DEV-PQ10`, `DEV-CLI14`,
`DEV-CLI21`, `DEV-LS5`): requires `c.length ≤ stdinCapBytes`, `shortCiphertext c`, inner payload
length `< 2 ^ 32 - 2048` on canonical tag-3 wires, and `ratchetKeyAdmissible` on the inner
`SignalMessage`. -/
def bhInjOK {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (c : Bytes) : Bool :=
  decide (c.length ≤ stdinCapBytes) &&
  shortCiphertext c &&
  match bhDecodePreKeyMsgE c with
  | some m =>
    decide (m.inner.length + 2048 < 2 ^ 32) && ratchetKeyAdmissible protoSignalCodec decT encT m.inner
  | none =>
    match c with
    | t :: body => t == wireWhisper && ratchetKeyAdmissible protoSignalCodec decT encT body
    | [] => false

/-- `SM.ConfigR` of a binary-harness instance: `configRefuseEarlyBobCorr` with injection filter
`bhInjOK`. -/
def bhConfigSpkS {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {Msg : Type} : SM.ConfigR BinState Msg Bytes :=
  { configRefuseEarlyBobCorr decT encT with injOK := bhInjOK decT encT }

/-! ## Oracle signatures, driver state, and `KeyInd` handler -/

/-- Session-promotion control query `startDR sid` (`DEV-C9`). -/
inductive BHDRCtlQuery (S : SignalPqxdh.Setup) where
  | startDR (sid : SignalPqxdh.SessionId S)
  deriving DecidableEq, Repr

/-- Control oracle returning the new instance index on promotion, or `none` if refused. -/
@[reducible] def bhDrCtlSpec (S : SignalPqxdh.Setup) : OracleSpec (BHDRCtlQuery S) :=
  fun _ => Option ℕ

abbrev cliGameSmSpec (ℓ : ℕ) (PQC : Type) := SM.spec BinState (Plain ℓ) PQC Bytes

@[reducible] def cliGameDrSpec (ℓ : ℕ) (PQC : Type) :
    OracleSpec (ℕ × (cliGameSmSpec ℓ PQC).Domain) :=
  fun x => (cliGameSmSpec ℓ PQC).Range x.2

/-- Full oracle interface of the composed adversary: coins, `KeyInd`, `startDR`, and indexed SM
oracles. -/
abbrev cliGameSpec (S : SignalPqxdh.Setup) (ℓ : ℕ) (PQC : Type) :=
  unifSpec + SignalPqxdh.keyIndSpec S + bhDrCtlSpec S + cliGameDrSpec ℓ PQC

/-- Adversary in the composed PQXDH + Double Ratchet game. -/
structure CliGameAdversary (S : SignalPqxdh.Setup) (ℓ : ℕ) (PQC : Type) where
  run : OracleComp (cliGameSpec S ℓ PQC) Bool

/-- Default `none` response for a missing or unclean SM instance. -/
def bhSmDefaultWithSpqr {ℓ : ℕ} {PQC : Type} :
    (x : (cliGameSmSpec ℓ PQC).Domain) → (cliGameSmSpec ℓ PQC).Range x
  | .inl (.inl (.inl (.inl _))) | .inl (.inl (.inl (.inr _))) | .inl (.inl (.inr _))
  | .inl (.inr _) | .inr _ => none

def bhNoExtWithSpqr {ℓ : ℕ} {PQC : Type} {M : Type → Type} [Monad M] :
    QueryImpl (cliGameSmSpec ℓ PQC) M := fun q => pure (bhSmDefaultWithSpqr q)

def bhBytesWord (bs : SignalPqxdh.Bytes) : BitVec 256 := HKDF.bytesToKey32 (ofU8 bs)

/-- Pack a 96-byte PQXDH `DRKey` and Alice's 32-byte ratchet seed into a `SampledSessionKey`. -/
def bhKeySOf (dk : SignalPqxdh.DRKey) (aliceCoins : BitVec 256) : SampledSessionKey :=
  ((bhBytesWord dk.rootKey, bhBytesWord dk.chainKey), (aliceCoins, bhBytesWord dk.pqrKey))

def bhDrvSessionInitPrin? {S : SignalPqxdh.Setup} : SignalPqxdh.SessionId S → Option (Fin S.N_id)
  | .sendOPK u _ | .sendNoOPK u _ => some u
  | _ => none

/-- Registration ID `BitVec.ofNat 32 u.val` of an initiator session (`0#32` for responder IDs). -/
def bhInitRegId {S : SignalPqxdh.Setup} (sid : SignalPqxdh.SessionId S) : BitVec 32 :=
  match bhDrvSessionInitPrin? sid with | some u => BitVec.ofNat 32 u.val | none => 0#32

/-- Per-instance freshness and responder-slot metadata.

**DEV-C17 (formalization): initiator-identity freshness at Bob's first accept, and no adversary
`revealSpkSk`.** In `KeyInd`, initiator freshness (`isKeyIndInitStillFresh`) inspects only the
responder's keys, whereas Bob's handshake binds `ikA` only via `DH(spkB_sk, ikA)`. Corrupting `ikA`
or revealing `spkB_sk` before Bob's first accept would let an adversary forge a pre-key message
under `ikA` while Alice's session remains `KeyInd`-fresh (`DEV-PQ24`). Each promoted instance
records whether Bob has accepted (`bobAccepted`), whether `ikA` was corrupted at that first accept
(`ikACorrAtAccept`), and its responder slot `(respPrin, respSpkIdx)`, while `revealedSpks` logs
adversarial `revealSpkSk` queries (excluding the driver's own reveal at `startDR`, `DEV-C10`).
Once `bhDrvInstClean` (or `bhE2EDrvInstClean`) fails for instance `i`, SM queries on `i` return
`none` without affecting other instances. Effect: restricts the adversary. -/
structure ModelDriverInstanceMeta (S : SignalPqxdh.Setup) where
  bobAccepted : Bool := false
  ikACorrAtAccept : Bool := false
  respPrin : Option (Fin S.N_id) := none
  respSpkIdx : Option (Fin S.N_recv) := none
  instOpkId? : Option UInt32 := none
  deriving DecidableEq, Repr

/-- Per-instance keys, initial `BinState`s, and optional SM game state in `ModelDriverState`. -/
structure ModelDriverInstance (S : SignalPqxdh.Setup) (ℓ : ℕ) where
  sid : SignalPqxdh.SessionId S
  hdr : SignalPqxdh.HandshakeHdr
  idBBytes : SignalPqxdh.Bytes
  respSlot : Fin S.N_id × Fin S.N_recv
  meA : LocalIdentity
  meB : LocalIdentity
  keysB : ResponderPreKeySecrets
  stA0 : BinState
  stB0 : BinState
  gs : Option (SM.GameState BinState (Plain ℓ) Bytes)

/-- Mirrored public `KeyInd` transcript (`prins`, `bundles`, `opks`, `sends`). -/
structure ModelDriverBase (S : SignalPqxdh.Setup) where
  prins : List (Fin S.N_id × SignalPqxdh.Bytes) := []
  bundles : List ((Fin S.N_id × Fin S.N_recv) × (SignalPqxdh.Bytes × SignalPqxdh.Bytes)) := []
  opks : List ((Fin S.N_id × Fin S.N_recv × Fin S.N_opk) × SignalPqxdh.Bytes) := []
  sends : List (SignalPqxdh.SessionId S × SignalPqxdh.PreKeyBundleInput ×
    SignalPqxdh.HandshakeHdr) := []

/-- Driver state of the wire-byte composed game, extending `ModelDriverBase` with promoted
instances, initiator tapes, corrupted principals, and adversarially revealed SPK slots. -/
structure ModelDriverState (S : SignalPqxdh.Setup) (ℓ : ℕ) extends ModelDriverBase S where
  bhInsts : List (ModelDriverInstance S ℓ) := []
  instMeta : List (ModelDriverInstanceMeta S) := []
  initTapes : List (SignalPqxdh.SessionId S × Fin S.N_id × SignalPqxdh.PreKeyBundleInput ×
    List.Vector (BitVec 8) 160) := []
  corrPrins : List (Fin S.N_id) := []
  revealedSpks : List (Fin S.N_id × Fin S.N_recv) := []

/-- Byte-exact `ikA` pin on responder accepts.

**DEV-C15 (formalization): byte-exact identity pins on `KeyInd` handshake queries, and no
`revealDhSecrets`.** `KeyInd` matches identity keys modulo the cofactor projection `P.pow8`, so an
8-torsion twin `ikA + T` of a mirrored honest principal's key passes `acceptOPK` / `acceptNoOPK`
and consumes the responder's pre-key slot and Kyber replay tuple. The driver forwards a responder
accept only if `hdr.ikAPk` is byte-equal to a mirrored principal key (`bhDrvAcceptIkOk`), and an
`initiateOPK` / `initiateNoOPK` only if no mirrored principal key is a distinct `pow8`-twin of
`bnd.ikB` (`bhDrvInitiateIkOk`); the signed pre-key is checked byte-for-byte at `startDR`
(`DEV-C9`). `bhDrvKiQueryOk` also refuses `revealDhSecrets` (`DEV-PQ19`, `DEV-PQ23`) and
`testSession` (`DEV-C12`). Effect: restricts the adversary. -/
def bhDrvAcceptIkOk {S : SignalPqxdh.Setup} (ds : ModelDriverBase S)
    (hdr : SignalPqxdh.HandshakeHdr) : Bool :=
  ds.prins.any (fun e => e.2 == hdr.ikAPk)

/-- Reject bundles whose `ikB` is a distinct `pow8`-twin of a mirrored honest principal key
(`DEV-C19`). -/
def bhDrvInitiateIkOk {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives) (ds : ModelDriverBase S)
    (bnd : SignalPqxdh.PreKeyBundleInput) : Bool :=
  !ds.prins.any (fun (_, pk) => P.pow8 pk == P.pow8 bnd.ikB && pk != bnd.ikB)

/-- Admissibility filter on `KeyIndQuery` in the composed game (`DEV-C12`, `DEV-C15`, `DEV-C19`). -/
def bhDrvKiQueryOk {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives) (ds : ModelDriverBase S) :
    SignalPqxdh.KeyIndQuery S → Bool
  | .testSession _ | .revealDhSecrets => false
  | .initiateOPK _ _ bnd => bnd.opkB?.isSome && bhDrvInitiateIkOk P ds bnd
  | .initiateNoOPK _ _ bnd => bnd.opkB?.isNone && bhDrvInitiateIkOk P ds bnd
  | .acceptOPK _ _ _ hdr | .acceptNoOPK _ _ _ hdr => bhDrvAcceptIkOk ds hdr
  | _ => true

/-- Whether `u` is the responder of a promoted no-OPK instance (`respPrin = some u` and
`instOpkId? = none`). Because `startDR` reveals the responder's signed pre-key (`DEV-C10`), a
subsequent `corruptIK u` on a no-OPK session would violate `isKeyIndInitStillFresh` and void the
entire run via `allTestedSessionsFresh`; the composed drivers therefore refuse `corruptIK u` once
this holds, complementing the `!corrPrins.contains u` check in `bhDrvGuard`. -/
def bhNoOpkRespPromoted {S : SignalPqxdh.Setup} (instMeta : List (ModelDriverInstanceMeta S))
    (u : Fin S.N_id) : Bool :=
  instMeta.any (fun im => im.respPrin == some u && im.instOpkId?.isNone)

/-- Whether the initiator identity key `ikA` of `bi` belongs to a corrupted principal
(`DEV-C17`). -/
def bhInstIkACorrupted {S : SignalPqxdh.Setup} {ℓ : ℕ} (ds : ModelDriverState S ℓ)
    (bi : ModelDriverInstance S ℓ) : Bool :=
  (match bhDrvSessionInitPrin? bi.sid with | some u => ds.corrPrins.contains u | none => true) ||
  ds.prins.any (fun (u, pk) => pk == bi.hdr.ikAPk && ds.corrPrins.contains u)

/-- Per-instance cleanliness check on `ModelDriverState` (`DEV-C17`): requires an initiator
principal, uncorrupted `ikA` at Bob's first accept, and no adversarial `revealSpkSk` on
`bi.respSlot`. -/
def bhDrvInstClean {S : SignalPqxdh.Setup} {ℓ : ℕ} (ds : ModelDriverState S ℓ) (i : ℕ) : Bool :=
  match ds.bhInsts[i]?, ds.instMeta[i]? with
  | some bi, some im =>
    (bhDrvSessionInitPrin? bi.sid).isSome && !im.ikACorrAtAccept &&
      !ds.revealedSpks.contains bi.respSlot
  | _, _ => true

/-- End-of-game freshness predicate requiring every tested initiator and responder session in `st`
to remain fresh (`DEV-C10`). -/
def allTestedSessionsFresh {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (st : SignalPqxdh.KeyIndState S) : Bool :=
  st.sessions.all (fun s =>
      !s.tested ||
        SignalPqxdh.isKeyIndInitStillFresh P true st.principals st.spkBundles st.respSessions s) &&
    st.respSessions.all (fun r =>
      !r.tested ||
        SignalPqxdh.isKeyIndRespStillFresh P true st.principals st.spkBundles st.sessions r)

/-- Whether some promoted instance in `ds` with challenge bit `b` has `gs.win = true`. -/
def driverSomeInstanceWon {S : SignalPqxdh.Setup} {ℓ : ℕ} (ds : ModelDriverState S ℓ) (b : Bool) : Bool :=
  ds.bhInsts.any (fun bi => match bi.gs with | some gs => gs.b == b && gs.win | none => false)

/-- Record public keys, bundles, OPKs, and initiator headers from a `KeyInd` step in
`ModelDriverBase`. -/
def bhBaseMirror {S : SignalPqxdh.Setup} (ds : ModelDriverBase S)
    (q : SignalPqxdh.KeyIndQuery S) (r : SignalPqxdh.KeyIndResponse) : ModelDriverBase S :=
  match q, r with
  | .initPrin u, .initPrinResp ikPk _ => { ds with prins := (u, ikPk) :: ds.prins }
  | .genSPK u j, .bundleResp bnd =>
    { ds with bundles := ((u, j), (bnd.spkB, bnd.pqspkB)) :: ds.bundles }
  | .genOPK u j o, .pkResp opkPk =>
    { ds with opks := ((u, j, o), opkPk) :: ds.opks }
  | .initiateOPK u i bnd, .hdrResp hdr =>
    { ds with sends := (.sendOPK u i, bnd, hdr) :: ds.sends }
  | .initiateNoOPK u i bnd, .hdrResp hdr =>
    { ds with sends := (.sendNoOPK u i, bnd, hdr) :: ds.sends }
  | _, _ => ds

/-- Extend `bhBaseMirror` on `ModelDriverState` with corrupted principals and adversarially revealed
SPK slots. -/
def bhDrvMirror {S : SignalPqxdh.Setup} {ℓ : ℕ} (ds : ModelDriverState S ℓ)
    (q : SignalPqxdh.KeyIndQuery S) (r : SignalPqxdh.KeyIndResponse) : ModelDriverState S ℓ :=
  let dsBase := bhBaseMirror ds.toModelDriverBase q r
  let corrPrins' :=
    match q, r with | .corruptIK u, .corrResp _ _ => u :: ds.corrPrins | _, _ => ds.corrPrins
  let revSpks' := match q, r with
    | .revealSpkSk u j, .spkSkResp _ => (u, j) :: ds.revealedSpks
    | _, _ => ds.revealedSpks
  { ds with toModelDriverBase := dsBase, corrPrins := corrPrins', revealedSpks := revSpks' }

/-- Whether `bnd.opkB?` matches a mirrored OPK of responder slot `(u, j)` (`DEV-C20`). -/
def bhBaseOpkOk {S : SignalPqxdh.Setup} (ds : ModelDriverBase S)
    (u : Fin S.N_id) (j : Fin S.N_recv)
    (bnd : SignalPqxdh.PreKeyBundleInput) : Bool :=
  match bnd.opkB? with
  | none => true
  | some (opkId, opkPk) =>
    ds.opks.any (fun ((u', j', o), pk) =>
      u' == u && j' == j && UInt32.ofNat o.val == opkId &&
      o.val == opkId.toNat && pk == opkPk)

/-- Session-promotion guard for `startDR sid` (`DEV-C9`, `DEV-C10`, `DEV-C20`): checks uniqueness of
`sid` and `ekAPk`, matches the bundle and optional OPK against mirrored honest keys of some slot
`(u, j)`, and for no-OPK handshakes requires `!ds.corrPrins.contains u`. -/
def bhDrvGuard {S : SignalPqxdh.Setup} {ℓ : ℕ} (ds : ModelDriverState S ℓ)
    (sid : SignalPqxdh.SessionId S) :
    Option (SignalPqxdh.HandshakeHdr × SignalPqxdh.PreKeyBundleInput ×
      (Fin S.N_id × Fin S.N_recv)) :=
  if ds.bhInsts.any (fun bi => bi.sid == sid) then none
  else
    match ds.sends.find? (fun (s, _, _) => s == sid) with
    | none => none
    | some (_, bnd, hdr) =>
      if ds.bhInsts.any (fun bi => bi.hdr.ekAPk == hdr.ekAPk) then none
      else
        match ds.bundles.find? (fun ((_, j), (spkB, pqspkB)) =>
            spkB == bnd.spkB && pqspkB == bnd.pqspkB &&
            hdr.spkId == UInt32.ofNat j.val &&
            hdr.pqspkId == UInt32.ofNat j.val) with
        | none => none
        | some ((u, j), _) =>
          if ds.prins.any (fun (u', pk) => u' == u && pk == bnd.ikB) &&
             bhBaseOpkOk ds.toModelDriverBase u j bnd &&
             (bnd.opkB?.isSome || !ds.corrPrins.contains u) then
            some (hdr, bnd, (u, j))
          else none

/-- Instance challenge-bit selector (`none` for an external SM instance, `some b` for bit `b`).
-/ abbrev BHDrvMode (S : SignalPqxdh.Setup) :=
  SignalPqxdh.SessionId S → (Fin S.N_id × Fin S.N_recv) →
    SignalPqxdh.Bytes → SignalPqxdh.Bytes → SignalPqxdh.Bytes → Option Bool

abbrev BHDrvM (S : SignalPqxdh.Setup) (ℓ : ℕ) :=
  StateT (ModelDriverState S ℓ) (StateT (SignalPqxdh.KeyIndState S) ProbComp)

/-- Execute a `KeyInd` initiator handshake from a uniform 160-byte tape `t_init` (using a lazy
random oracle when `useRo = true` and concrete HKDF when `useRo = false`), recording `t_init` in
`ds.initTapes`. -/
def bhRunInitiate (S : SignalPqxdh.Setup) {ℓ : ℕ} (P : SignalPqxdh.Primitives)
    (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id) (bundle : SignalPqxdh.PreKeyBundleInput)
    (useRo : Bool := false) : BHDrvM S ℓ SignalPqxdh.KeyIndResponse := do
  let st ← StateT.lift get
  if st.sessions.any (fun e => e.sid == sid) then return .noneResp
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val) | return .noneResp
  if !(match SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with
       | some (_, e) => e.ikAPk == bundle.ikB | none => true) then
    return .noneResp
  if !SignalPqxdh.koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
    return .noneResp
  let t_init ← StateT.lift (liftM ($ᵗ List.Vector (BitVec 8) 160))
  let ekASk := tapeEkASk t_init; let kemCoins := tapeKemCoins t_init
  let sigPkB := SignalPqxdh.resolveSigPk P st.principals bundle.ikB
  if !(P.sigVerify sigPkB (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return .noneResp
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins | return .noneResp
  let ekAPk := P.x25519Base ekASk
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB; let dh2 := P.x25519 ekASk bundle.ikB
  let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := SignalPqxdh.buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKeyReal, roCache') ←
    StateT.lift (liftM (SignalPqxdh.evalHkdfOrRo useRo P st.roCache secrets))
  let hdr : SignalPqxdh.HandshakeHdr :=
    { ikAPk := uEntry.ikAPk, ekAPk := ekAPk, spkId := bundle.spkId,
      opkId? := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }
  let honestPeer := SignalPqxdh.isHonestUncorruptedPeer P st.principals bundle.ikB
  let (spkHon, opkHon, pqspkHon) :=
    SignalPqxdh.checkBundleProvenance P st.principals st.spkBundles st.opkEntries bundle
  let sessEntry : SignalPqxdh.KeyIndInitiatorEntry S :=
    { sid := sid, honestPeer := honestPeer, peerIkPk := bundle.ikB, peerSpkPk := bundle.spkB,
      peerOpkPk? := bundle.opkB?.map Prod.snd, peerPqspkPk := bundle.pqspkB, spkHonest := spkHon,
      opkHonest := opkHon, pqspkHonest := pqspkHon, ekASk := ekASk, fresh := honestPeer.isSome,
      drKeyReal := drKeyReal, drKeyRand := drKeyReal, hdr := hdr, tested := false }
  let drKeyRand ← match SignalPqxdh.keyIndPartnerRandKey? P st.respSessions sessEntry with
    | some dk => pure dk | none => StateT.lift (liftM SignalPqxdh.sampleDRKey96)
  let entry := { sessEntry with drKeyRand := drKeyRand }
  StateT.lift (set { st with sessions := entry :: st.sessions, roCache := roCache' })
  modify fun ds => { ds with initTapes := (sid, u, bundle, t_init) :: ds.initTapes }
  match SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with
  | some _ => return .hdrResp hdr | none => return .initUnfreshResp drKeyReal hdr

/-- `KeyInd` oracle handler for the composed driver (`DEV-C12`, `DEV-C15`, `DEV-C19`, `DEV-PQ6`,
`DEV-PQ13`): at `useRo = false`, `.initPrin u` samples a single scalar shared by X25519 and XEdDSA
(`secIKAsign := secIKA0`, matching libsignal's one-key identities, `DEV-PQ13`), and `.corruptIK u`
is refused while `bhNoOpkRespPromoted ds.instMeta u` holds. -/
def bhDrvKeyInd (S : SignalPqxdh.Setup) (ℓ : ℕ) (P : SignalPqxdh.Primitives)
    (useRo : Bool := false) : QueryImpl (SignalPqxdh.keyIndSpec S) (BHDrvM S ℓ) := fun q =>
  match q with
  | .testSession _ | .revealDhSecrets => return .noneResp
  | .initPrin u => do
    let r ← if !useRo then
        StateT.lift (do
          let st ← get
          if st.principals.any (fun (idx, _) => idx == u.val) then
            return .noneResp
          let secIKA0 ← liftM SignalPqxdh.sampleScalar32
          let ikAPk := P.x25519Base secIKA0
          let entry : SignalPqxdh.PrincipalEntry :=
            { secIKA0 := secIKA0, ikAPk := ikAPk,
              secIKAsign := secIKA0, ikSignPk := ikAPk, corrupted := false }
          set { st with principals := (u.val, entry) :: st.principals }
          return .initPrinResp ikAPk ikAPk)
      else StateT.lift (SignalPqxdh.pqxdhKeyIndImpl useRo S P (.initPrin u))
    modify (fun ds => bhDrvMirror ds (.initPrin u) r); return r
  | .initiateOPK u i bnd => do
    let ds ← get
    if bnd.opkB?.isNone || !bhDrvInitiateIkOk P ds.toModelDriverBase bnd then return .noneResp
    let r ← bhRunInitiate S P (.sendOPK u i) u bnd useRo
    modify (fun ds => bhDrvMirror ds (.initiateOPK u i bnd) r); return r
  | .initiateNoOPK u i bnd => do
    let ds ← get
    if bnd.opkB?.isSome || !bhDrvInitiateIkOk P ds.toModelDriverBase bnd then return .noneResp
    let r ← bhRunInitiate S P (.sendNoOPK u i) u bnd useRo
    modify (fun ds => bhDrvMirror ds (.initiateNoOPK u i bnd) r); return r
  | .acceptOPK k j o hdr => do
    let ds ← get
    if !bhDrvAcceptIkOk ds.toModelDriverBase hdr then return .noneResp
    let r ← StateT.lift (SignalPqxdh.pqxdhKeyIndImpl useRo S P (.acceptOPK k j o hdr))
    modify (fun ds => bhDrvMirror ds (.acceptOPK k j o hdr) r); return r
  | .acceptNoOPK k j l hdr => do
    let ds ← get
    if !bhDrvAcceptIkOk ds.toModelDriverBase hdr then return .noneResp
    let r ← StateT.lift (SignalPqxdh.pqxdhKeyIndImpl useRo S P (.acceptNoOPK k j l hdr))
    modify (fun ds => bhDrvMirror ds (.acceptNoOPK k j l hdr) r); return r
  | .roQuery secrets => do
    let st ← StateT.lift get
    let (dk, roCache') ←
      StateT.lift (liftM (SignalPqxdh.evalHkdfOrRo useRo P st.roCache secrets))
    StateT.lift (set { st with roCache := roCache' })
    return .drKeyResp dk
  | .corruptIK u => do
    let ds ← get
    if bhNoOpkRespPromoted ds.instMeta u then return .noneResp
    let r ← StateT.lift (SignalPqxdh.pqxdhKeyIndImpl useRo S P (.corruptIK u))
    modify (fun ds => bhDrvMirror ds (.corruptIK u) r); return r
  | q => do
    let r ← StateT.lift (SignalPqxdh.pqxdhKeyIndImpl useRo S P q)
    modify (fun ds => bhDrvMirror ds q r); return r

/-- Whether an SM query is `deliver-B` or `inject-B`. -/
def bhIsBobRecvSMQuery {ℓ : ℕ} {PQC : Type} : (cliGameSmSpec ℓ PQC).Domain → Bool
  | .inl (.inl (.inr (.B, _))) | .inl (.inr (.B, _)) => true
  | _ => false

/-- Whether a `deliver-B` or `inject-B` query returned `some (.accepted ..)`. -/
def bhIsBobAcceptSMResp {St : Type} {ℓ : ℕ} {PQC : Type} :
    (q : (SM.spec St (Plain ℓ) PQC Bytes).Domain) → (SM.spec St (Plain ℓ) PQC Bytes).Range q → Bool
  | .inl (.inl (.inr (.B, _))), some (.accepted _ _ _) => true
  | .inl (.inr (.B, _)), some (.accepted _ _ _) => true
  | _, _ => false

/-- Record `bobAccepted` and `ikACorrAtAccept` on Bob's first accepted message (`DEV-C17`). -/
def bhMetaAfterSM {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC : Type}
    (ds : ModelDriverState S ℓ) (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S)
    (q : (cliGameSmSpec ℓ PQC).Domain) (r : (cliGameSmSpec ℓ PQC).Range q) : ModelDriverInstanceMeta S :=
  if !im.bobAccepted && bhIsBobAcceptSMResp q r then
    { im with bobAccepted := true, ikACorrAtAccept := bhInstIkACorrupted ds bi }
  else im

/-! ## Wire-to-model adapter interfaces and cost budgets -/

/-- Non-coin game oracle interface over wire-byte party state `BinState`. -/
@[reducible] def bhGameSpec (S : SignalPqxdh.Setup) (ℓ : ℕ) (PQC : Type) :=
  SignalPqxdh.keyIndSpec S + bhDrCtlSpec S + cliGameDrSpec ℓ PQC

@[reducible] def bhModelDrSpecWithSpqr (ℓ : ℕ) (PQC : Type) :
    OracleSpec (ℕ × (SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Domain) :=
  fun x => (SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Range x.2

/-- Non-coin game oracle interface over model party state `GhostState Bytes`. -/
@[reducible] def bhTargetGameSpec (S : SignalPqxdh.Setup) (ℓ : ℕ) (PQC : Type) :=
  SignalPqxdh.keyIndSpec S + bhDrCtlSpec S + bhModelDrSpecWithSpqr ℓ PQC

def bhCtlUnStart {S : SignalPqxdh.Setup} : BHDRCtlQuery S → SignalPqxdh.SessionId S
  | .startDR sid => sid

@[reducible] def e2eTargetGameCodec (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type := Empty) :
    ReductionDsl.GameCodec (ReductionDsl.atomicSig ℓ Pt) (bhTargetGameSpec S ℓ (BitVec 512)) :=
  ReductionDsl.e2eGameCodec S ℓ Pt bhCtlUnStart

@[reducible] def e2eBhAdapterIface (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type := Empty) :
    ReductionDsl.Iface (ReductionDsl.atomicSig ℓ Pt) (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) :=
  ReductionDsl.e2eAdapterIface S ℓ Pt BHDRCtlQuery.startDR

@[reducible] def e2eBhAdapterCodec (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type := Empty) :
    ReductionDsl.GameCodec (ReductionDsl.atomicSig ℓ Pt) (bhGameSpec S ℓ (BitVec 512)) :=
  ReductionDsl.e2eAdapterCodec S ℓ Pt bhCtlUnStart

/-- `ReductionDsl.CostedReduction` program type for the wire-to-model (`BinState` to
`GhostState Bytes`) game adapter. -/
abbrev CliToModelAdapterProg (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :=
  ReductionDsl.CostedReduction (ReductionDsl.atomicAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ Pt)
    (bhGameSpec S ℓ (BitVec 512)) (e2eBhAdapterCodec S ℓ Pt) .unit .unit .bool .bool

/-- Query-kind classifier shared by `bhGameSpec` and `bhTargetGameSpec`: offline `KeyInd`
random-oracle queries (`.roQuery`) have kind `1`, and all online queries (non-RO `KeyInd`,
`startDR`, and per-instance SM) have kind `0`. -/
def bhQueryKind {S : SignalPqxdh.Setup} {ι : Type} :
    (SignalPqxdh.KeyIndQuery S ⊕ BHDRCtlQuery S) ⊕ ι → Fin 2
  | .inl (.inl (.roQuery _)) => 1
  | _ => 0

/-- Per-kind query budgets under `bhQueryKind`: kind `0` bounds online queries
(`min b.q_on b.q_total` non-RO `KeyInd` queries plus `qStart` promotions and `qDR` SM queries), and
kind `1` bounds offline `.roQuery` calls (`min b.q_ro b.q_total`). -/
def bhKindCounts (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) : Fin 2 → ℕ
  | 0 => min b.q_on b.q_total + qStart + qDR
  | 1 => min b.q_ro b.q_total

/-- Step-cost budget for a `CliToModelAdapterProg`, clamping mirrored `KeyInd` table sizes at
`min b.q_total S.N_*`. -/
def bhAdapterCostBudget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) : ℕ :=
  let M_id := min b.q_total S.N_id
  let M_spk := min b.q_total S.N_spk_tot
  let M_opk := min b.q_total S.N_opk_tot
  let M_send := min b.q_total S.N_send_tot
  2 ^ 6 * (b.q_total + qStart + qDR + 1) *
    (2 * M_id + 56 * M_spk + 3 * M_opk + 2 * M_send +
      2 * Nat.log 2 S.N_id + 8 * Nat.log 2 S.N_spk_tot +
      2 * Nat.log 2 S.N_opk_tot + 2 * Nat.log 2 S.N_send_tot +
      4 * qStart + 4 * ℓ + 2 ^ 12)

/-- Per-kind step-cost budget for a `CliToModelAdapterProg` under `bhQueryKind`: clamps mirrored
`KeyInd` table sizes at the online count `M_on = min b.q_on b.q_total` and charges a constant
`2 ^ 12` per offline `.roQuery` call (`M_ro = min b.q_ro b.q_total`), since offline hash queries
are forwarded without mutating adapter tables. The proofs meet this with
`cliToModelAdapterProgTblRo`, whose `.ki` arm sends `.roQuery` around the base-state mirror update;
`cliToModelAdapterProgTblRo_eval_eq` proves it has the same `eval` as `cliToModelAdapterProgTbl`
(`Proofs/E2E/Dsl/CliAdapterTblByKind.lean`). -/
def bhAdapterCostBudgetByKind (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) : ℕ :=
  let M_on := min b.q_on b.q_total
  let M_ro := min b.q_ro b.q_total
  let M_id := min M_on S.N_id
  let M_spk := min M_on S.N_spk_tot
  let M_opk := min M_on S.N_opk_tot
  let M_send := min M_on S.N_send_tot
  2 ^ 6 * (M_on + qStart + qDR + 1) *
      (2 * M_id + 56 * M_spk + 3 * M_opk + 2 * M_send +
        2 * Nat.log 2 S.N_id + 8 * Nat.log 2 S.N_spk_tot +
        2 * Nat.log 2 S.N_opk_tot + 2 * Nat.log 2 S.N_send_tot +
        4 * qStart + 4 * ℓ + 2 ^ 12) +
    2 ^ 12 * M_ro

/-- Kind-preservation predicate on a wire-to-model adapter `L`: if the source adversary makes at
most `qKind i` queries of kind `i` under `bhQueryKind` for every `i`, so does `L.eval A ()`. -/
def CliAdapterForwardsKinds {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (L : CliToModelAdapterProg S ℓ decT encT) (qKind : Fin 2 → ℕ) : Prop :=
  ∀ (A : Unit → OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) Bool),
    (∀ a i, (A a).IsQueryBoundP
      (fun t => SignalPqxdh.isGameQueryOfKind bhQueryKind i t = true) (qKind i)) →
    ∀ i, (L.eval A ()).IsQueryBoundP
      (fun t => SignalPqxdh.isGameQueryOfKind bhQueryKind i t = true) (qKind i)

/-- Total and per-kind step-cost, query-count, size-honesty, and kind-preservation bounds on a
wire-to-model adapter `L`, combining `GRedBounded` at `bhAdapterCostBudget`, `GRedCostByKind` at
`bhAdapterCostBudgetByKind`, and `CliAdapterForwardsKinds` under `bhKindCounts b qStart qDR`. -/
def CliAdapterCostBounded {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ)
    (L : CliToModelAdapterProg S ℓ decT encT) : Prop :=
  let qTot := b.q_total + qStart + qDR
  let qKind := bhKindCounts b qStart qDR
  GRedBounded L (fun _ => 1) (fun _ => 0) qTot qTot (bhAdapterCostBudget S b qStart qDR ℓ) ∧
  GRedCostByKind L (fun _ => 1) (fun _ => 0) bhQueryKind qKind (List.ofFn qKind).sum
    (bhAdapterCostBudgetByKind S b qStart qDR ℓ) ∧
  CliAdapterForwardsKinds L qKind

/-! ## ML-KEM totality hypothesis -/

/-- `K.encaps1` succeeds on all 64-byte SPQR headers (`Encaps1Total K`) and on all `K.fromSeed`
PQXDH public keys (`DEV-KFF1`). -/
def MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds (K : LibsignalSpqrV1.MlKem) : Prop :=
  Encaps1Total K ∧
  ∀ (s : List.Vector (BitVec 8) 64) (r : List.Vector (BitVec 8) 32),
    (K.encaps1 (K.fromSeed s).1.toList r).isSome = true

/-! ## Query budgets, model-state driver, and composition cost budgets -/

def bhIsInstQueryWithSpqr {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC : Type} (k : ℕ) :
    (cliGameSpec S ℓ PQC).Domain → Bool
  | .inr ⟨i, _⟩ => i == k
  | _ => false

/-- Global query-count bounds on `A` across random-oracle, handshake, `startDR`, and SM queries
(`DEV-PQ14`). -/
def CliGameAdversaryQueryBounded {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC : Type}
    (A : CliGameAdversary S ℓ PQC) (b : SignalPqxdh.QueryBudget) (qDR : ℕ) : Prop :=
  OracleComp.IsQueryBoundP A.run
    (fun q => q matches .inl (.inl (.inr (.roQuery _)))) b.q_ro ∧
  OracleComp.IsQueryBoundP A.run
    (fun q => q matches .inl (.inl (.inr (.initiateOPK ..)))
      || q matches .inl (.inl (.inr (.initiateNoOPK ..)))) S.N_send_tot ∧
  OracleComp.IsQueryBoundP A.run
    (fun q => q matches .inl (.inl (.inr (.acceptOPK ..)))
      || q matches .inl (.inl (.inr (.acceptNoOPK ..)))) S.N_recv_tot ∧
  OracleComp.IsQueryBoundP A.run (fun q => q matches .inl (.inl (.inr _))) b.q_total ∧
  -- Online (non-RO) `KeyInd` query bound
  OracleComp.IsQueryBoundP A.run
    (fun q => q matches .inl (.inl (.inr _))
      && !(q matches .inl (.inl (.inr (.roQuery _))))) b.q_on ∧
  OracleComp.IsQueryBoundP A.run (fun q => q matches .inl (.inr _)) S.N_send_tot ∧
  OracleComp.IsQueryBoundP A.run (fun q => q matches .inr _) qDR

/-- Global and per-instance query-count bounds on `A` for at most `qStart` promoted instances
(`DEV-C13`). -/
def CliGameAdversaryPerInstanceBounded {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC : Type}
    (A : CliGameAdversary S ℓ PQC)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) : Prop :=
  CliGameAdversaryQueryBounded A b (∑ k ∈ Finset.range qStart, qs k) ∧
  OracleComp.IsQueryBoundP A.run (fun q => q matches .inl (.inr _)) qStart ∧
  ∀ k < qStart, OracleComp.IsQueryBoundP A.run (fun q => bhIsInstQueryWithSpqr k q) (qs k)

/-- `KeyInd` query budget of the composed reduction, adding up to `2 * min qStart S.N_send_tot`
queries for the `testSession` and `revealSpkSk` issued by each `startDR` (`DEV-C9`). -/
def keyIndReductionBudget (S : SignalPqxdh.Setup) (qStart : ℕ) (b : SignalPqxdh.QueryBudget) :
    SignalPqxdh.QueryBudget :=
  { b with
    q_total := b.q_total + 2 * min qStart S.N_send_tot
    q_on    := b.q_on + 2 * min qStart S.N_send_tot }

/-- Reassociate `A.run` into `unifSpec + bhGameSpec S ℓ PQC`. -/
def cliGameAdversaryReassoc {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC : Type}
    (A : CliGameAdversary S ℓ PQC) :
    OracleComp (unifSpec + bhGameSpec S ℓ PQC) Bool :=
  simulateQ
    (fun q => match q with
      | .inl (.inl (.inl n)) =>
        query (spec := unifSpec + bhGameSpec S ℓ PQC) (.inl n)
      | .inl (.inl (.inr kq)) =>
        query (spec := unifSpec + bhGameSpec S ℓ PQC) (.inr (.inl (.inl kq)))
      | .inl (.inr cq) =>
        query (spec := unifSpec + bhGameSpec S ℓ PQC) (.inr (.inl (.inr cq)))
      | .inr dq =>
        query (spec := unifSpec + bhGameSpec S ℓ PQC) (.inr (.inr dq)))
    A.run

/-- Promoted Double Ratchet instance over `GhostState Bytes` in `BHE2EDrvState`. -/
structure BHModelInst (S : SignalPqxdh.Setup) (ℓ : ℕ) where
  sid : SignalPqxdh.SessionId S
  hdr : SignalPqxdh.HandshakeHdr
  idA : IdentityKey
  idB : IdentityKey
  spkCoins : BitVec 256
  gs : Option (SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)

/-- State of the model-state E2E driver and composition reductions. -/
structure BHE2EDrvState (S : SignalPqxdh.Setup) (ℓ : ℕ) extends ModelDriverBase S where
  corrPrins : List (Fin S.N_id) := []
  revealedSpks : List (Fin S.N_id × Fin S.N_recv) := []
  insts : List (BHModelInst S ℓ) := []
  instMeta : List (ModelDriverInstanceMeta S) := []
  st : SignalPqxdh.KeyIndState S := SignalPqxdh.KeyIndState.empty S false
  b : Bool := false
  paused : Bool := false

def bhModelSmDefault {ℓ : ℕ} {PQC : Type} :
    (x : (SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Domain) →
    (SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Range x
  | .inl (.inl (.inl (.inl _))) | .inl (.inl (.inl (.inr _))) | .inl (.inl (.inr _))
  | .inl (.inr _) | .inr _ => none

/-- Sum-flattened response of a single-instance `GhostState Bytes` SM query. -/
abbrev BHE2ESmResp (ℓ : ℕ) :=
  Option Bytes × Option (SM.RecvResult (Plain ℓ)) × Option (GhostState Bytes)

def bhPackSmResp {ℓ : ℕ} {PQC : Type} :
    (q : (SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Domain) →
    (SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Range q → BHE2ESmResp ℓ
  | .inl (.inl (.inl (.inl _))), r => (r, none, none)
  | .inl (.inl (.inl (.inr _))), r => (r, none, none)
  | .inl (.inl (.inr _)), r => (none, r, none)
  | .inl (.inr _), r => (none, r, none)
  | .inr _, r => (none, none, r)

def bhUnpackSmResp {ℓ : ℕ} {PQC : Type} :
    (q : (SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Domain) →
    BHE2ESmResp ℓ → (SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Range q
  | .inl (.inl (.inl (.inl _))), (r, _, _) => r
  | .inl (.inl (.inl (.inr _))), (r, _, _) => r
  | .inl (.inl (.inr _)), (_, r, _) => r
  | .inl (.inr _), (_, r, _) => r
  | .inr _, (_, _, r) => r

/-- Mirror a `KeyInd` query/response pair into `BHE2EDrvState`. -/
def bhE2EMirror {S : SignalPqxdh.Setup} {ℓ : ℕ} (σ : BHE2EDrvState S ℓ)
    (q : SignalPqxdh.KeyIndQuery S) (r : SignalPqxdh.KeyIndResponse) : BHE2EDrvState S ℓ :=
  let base' := bhBaseMirror σ.toModelDriverBase q r
  let corr' :=
    match q, r with | .corruptIK u, .corrResp _ _ => u :: σ.corrPrins | _, _ => σ.corrPrins
  let revSpks' := match q, r with
    | .revealSpkSk u j, .spkSkResp _ => (u, j) :: σ.revealedSpks
    | _, _ => σ.revealedSpks
  { σ with toModelDriverBase := base', corrPrins := corr', revealedSpks := revSpks' }

/-- Per-instance cleanliness check on `BHE2EDrvState` (`DEV-C17`). -/
def bhE2EDrvInstClean {S : SignalPqxdh.Setup} {ℓ : ℕ} (σ : BHE2EDrvState S ℓ) (i : ℕ) : Bool :=
  match σ.insts[i]?, σ.instMeta[i]? with
  | some d, some im =>
    (bhDrvSessionInitPrin? d.sid).isSome && !im.ikACorrAtAccept &&
      (match im.respPrin, im.respSpkIdx with
       | some u, some j => !σ.revealedSpks.contains (u, j)
       | _, _ => false)
  | _, _ => true

/-- Whether some promoted instance in `σ` with challenge bit `b` has `gs.win = true`. -/
def bhE2EDrvWon {S : SignalPqxdh.Setup} {ℓ : ℕ} (σ : BHE2EDrvState S ℓ) (b : Bool) : Bool :=
  σ.insts.any (fun d => match d.gs with | some gs => gs.b == b && gs.win | none => false)

/-- Session-promotion guard on `BHE2EDrvState` (`DEV-C9`, `DEV-C10`, `DEV-C20`), mirroring
`bhDrvGuard`. -/
def bhE2EGuard {S : SignalPqxdh.Setup} {ℓ : ℕ} (σ : BHE2EDrvState S ℓ)
    (sid : SignalPqxdh.SessionId S) :
    Option (SignalPqxdh.HandshakeHdr × SignalPqxdh.PreKeyBundleInput ×
      (Fin S.N_id × Fin S.N_recv)) :=
  if σ.insts.any (fun d => d.sid == sid) then none
  else
    match σ.sends.find? (fun (s, _, _) => s == sid) with
    | none => none
    | some (_, bnd, hdr) =>
      if σ.insts.any (fun d => d.hdr.ekAPk == hdr.ekAPk) then none
      else
        match σ.bundles.find? (fun ((_, j), (spkB, pqspkB)) =>
            spkB == bnd.spkB && pqspkB == bnd.pqspkB &&
            hdr.spkId == UInt32.ofNat j.val &&
            hdr.pqspkId == UInt32.ofNat j.val) with
        | none => none
        | some ((u, j), _) =>
          if σ.prins.any (fun (u', pk) => u' == u && pk == bnd.ikB) &&
             bhBaseOpkOk σ.toModelDriverBase u j bnd &&
             (bnd.opkB?.isSome || !σ.corrPrins.contains u) then
            some (hdr, bnd, (u, j))
          else none

/-- Whether the initiator identity key of `d` belongs to a corrupted principal in `σ`. -/
def bhE2EInstIkACorr {S : SignalPqxdh.Setup} {ℓ : ℕ} (σ : BHE2EDrvState S ℓ)
    (d : BHModelInst S ℓ) : Bool :=
  (match bhDrvSessionInitPrin? d.sid with | some u => σ.corrPrins.contains u | none => true) ||
  σ.prins.any (fun (u, pk) => pk == d.hdr.ikAPk && σ.corrPrins.contains u)

/-- Execute one model-state SM query on promoted instance `i` of `BHE2EDrvState` (`DEV-C11`,
`DEV-C19`). -/
def bhE2EStepLocalSm {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (q : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    ProbComp (BHE2ESmResp ℓ × BHE2EDrvState S ℓ) := do
  if !bhE2EDrvInstClean σ i then return ((none, none, none), σ)
  else
    match σ.insts[i]?, σ.instMeta[i]? with
    | some d, some im =>
      if !im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d then
        let imCorr := { im with bobAccepted := true, ikACorrAtAccept := true }
        let σ' := { σ with instMeta := σ.instMeta.set i imCorr }
        return ((none, none, none), σ')
      else
        match d.gs with
        | none => return ((none, none, none), σ)
        | some gs =>
          let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
          let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
          let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
          let runStd (q' : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
              (σ0 : BHE2EDrvState S ℓ) : ProbComp (BHE2ESmResp ℓ × BHE2EDrvState S ℓ) := do
            let (r, gs') ← (SM.oracleImplR sch (2 + 1) qep cfg q').run gs
            let accepted := bhIsBobAcceptSMResp q' r
            let im' := if !im.bobAccepted && accepted then
                { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ0 d }
              else im
            let σ1 := { σ0 with insts := σ0.insts.set i { d with gs := some gs' },
                                instMeta := σ0.instMeta.set i im' }
            return (bhPackSmResp q' r, σ1)
          match q with
          | .inl (.inl (.inr (.A, c))) =>
            if (bhDecodePreKeyMsgE c).isSome then return ((none, none, none), σ)
            else runStd q σ
          | .inl (.inr (.A, c)) =>
            if (bhDecodePreKeyMsgE c).isSome then return ((none, none, none), σ)
            else runStd q σ
          | .inl (.inl (.inr (.B, c))) =>
            if !im.bobAccepted then
              match bhDecodePreKeyMsgE c with
              | some m =>
                if c == wirePrekey ::
                    (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes then
                  runStd (.inl (.inl (.inr (.B, m.inner)))) σ
                else return ((none, none, none), σ)
              | none => return ((none, none, none), σ)
            else
              match bhDecodePreKeyMsgE c with
              | some m =>
                if bhHdrOfPreKeyMsg m == d.hdr then
                  runStd (.inl (.inl (.inr (.B, m.inner)))) σ
                else return ((none, none, none), σ)
              | none => runStd (.inl (.inl (.inr (.B, c)))) σ
          | .inl (.inr (.B, c)) =>
            if !im.bobAccepted then return ((none, none, none), σ)
            else
              match bhDecodePreKeyMsgE c with
              | some m =>
                if bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
                   decide (m.inner.length + 2048 < 2 ^ 32) then
                  runStd (.inl (.inr (.B, m.inner))) σ
                else return ((none, none, none), σ)
              | none => runStd (.inl (.inr (.B, c))) σ
          | _ => runStd q σ
    | _, _ => return ((none, none, none), σ)

/-- Complete `startDR sid` on `BHE2EDrvState` from `KeyInd` responses `(kr1, kr2)` and Alice's
ratchet seed `aliceCoins`. -/
def bhE2EFinishStartSpk {S : SignalPqxdh.Setup} {ℓ : ℕ} (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (bMode? : Option Bool) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (aliceCoins : BitVec 256) :
    Option ℕ × BHE2EDrvState S ℓ :=
  match bhE2EGuard σ sid, kr1, kr2 with
  | some (hdr, bnd, (u, j)), .drKeyResp dk, .spkSkResp spkSk =>
    if dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
       dk.pqrKey.length == 32 && spkSk.length == 32 then
      let idA := bhIdKeyOf hdr.ikAPk; let idB := bhIdKeyOf bnd.ikB
      let spkCoins := bhBytesWord spkSk
      let kS : SampledSessionKey := bhKeySOf dk aliceCoins
      let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
      let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr idA idB) ℓ spkCoins
      let gs := bMode?.map (fun b => SM.initState sch.sendPart kS b)
      let inst : BHModelInst S ℓ := { sid, hdr, idA, idB, spkCoins, gs }
      let im : ModelDriverInstanceMeta S :=
        { respPrin := some u, respSpkIdx := some j, instOpkId? := hdr.opkId? }
      (some σ.insts.length,
       { σ with insts := σ.insts ++ [inst], instMeta := σ.instMeta ++ [im] })
    else (none, σ)
  | _, _, _ => (none, σ)

/-- Step-cost budget for the model-state composition reductions, bounding per-query dispatch and
clamped table scans (`min b.q_total S.N_*`, `min qStart nSend`) together with the post-game
`allTestedSessionsFresh` pass. -/
def bhE2ECostBudget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qInst qep ℓ : ℕ) : ℕ :=
  let nId := min b.q_total S.N_id
  let nSpk := min b.q_total S.N_spk_tot
  let nOpk := min b.q_total S.N_opk_tot
  let nSend := min b.q_total S.N_send_tot
  let nRecv := min b.q_total S.N_recv_tot
  let nInst := min qStart nSend
  2 ^ 10 * (b.q_total + qStart + qDR + 1) *
      (b.q_total + nOpk + nInst + qInst + Nat.log 2 qep +
        10 * (nId + nSpk + nSend + nRecv) + maxForwardJumps + ℓ + 1) +
    2 ^ 13 * nInst * (nId + nSpk + nRecv + 1)

/-- Per-kind step-cost budget for the model-state composition reductions under `bhQueryKind`:
clamps session and key table scans at the online count `M_on = min b.q_on b.q_total`
(`Q_on = M_on + qStart + qDR`), adds logarithmic random-oracle table lookup/insert cost across at
most `M_ro + 2 * Q_on + 1` entries (`M_ro = min b.q_ro b.q_total`), and retains the post-game
`allTestedSessionsFresh` pass. The table term can pay for a balanced lookup-tree walk of
`O(bits K)` steps per offline query, `K = M_ro + 2 * Q_on + 1`; the current E2E proofs forward
each `.roQuery` to the target game in `O(bits M_on)` steps, which `roStep_mul_le_roTableTerm`
(`Proofs/E2E/Dsl/PrefixRedHaltedByKind.lean`) bounds by the table term. -/
def bhE2ECostBudgetByKind (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qInst qep ℓ : ℕ) : ℕ :=
  let M_on := min b.q_on b.q_total
  let M_ro := min b.q_ro b.q_total
  let Q_on := M_on + qStart + qDR
  let nId := min M_on S.N_id
  let nSpk := min M_on S.N_spk_tot
  let nOpk := min M_on S.N_opk_tot
  let nSend := min M_on S.N_send_tot
  let nRecv := min M_on S.N_recv_tot
  let nInst := min qStart nSend
  2 ^ 10 * (Q_on + 1) *
      (M_on + nOpk + nInst + qInst + Nat.log 2 qep +
        10 * (nId + nSpk + nSend + nRecv) + maxForwardJumps + ℓ + 1) +
    2 ^ 13 * (M_ro + Q_on) * (ReductionDsl.bits (M_ro + 2 * Q_on + 1) + 4) +
    2 ^ 13 * nInst * (nId + nSpk + nRecv + 1)

/-- Step-cost, program-size, query-count, size-honesty, and run-local block-width bound on a
`ReductionDsl.TwoStageCostedReduction`: whenever every adversary game query and every target
oracle answer on a run fits width `B`, the stage-1 checkpoint and stage-2 output fit
`2 * (costBudget + q + 1) * (B + 1)`. -/
def GRed2Bounded {S : ReductionDsl.Sig}
    {O : ReductionDsl.Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : ReductionDsl.Iface S T} {G : OracleSpec κ}
    {C : ReductionDsl.GameCodec S G} {rIn aIn aOut ch rIn2 out : ReductionDsl.Ty S}
    (R : ReductionDsl.TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ) (dflt : aOut.denote) : Prop :=
  R.totalCost q ≤ costBudget ∧
  R.size ≤ ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget ∧
  R.init.queries wTag wSamp + R.handlePre.queries wTag wSamp + R.chDone.queries wTag wSamp = 0 ∧
  R.totalQueries wTag wSamp q ≤ qOut ∧
  CostedOpsSizeHonest O ∧
  CostedSampSizeHonest I.smp ∧
  ∀ (B : ℕ),
    (∀ v : aOut.denote, CostedFits B aOut v) →
    ∀ (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote),
      (∀ a, ReductionDsl.AllGameQueriesFit B C (A a)) →
      ∀ (x : rIn.denote), CostedFits B rIn x →
      let widthB := 2 * (costBudget + q + 1) * (B + 1)
      ∀ cm ∈ ReductionDsl.supportWhen (I.AnswerFits B) (R.eval1 A x q dflt),
        CostedFits widthB ch cm.1 ∧
        ∀ (y : rIn2.denote), CostedFits B rIn2 y →
          ∀ z ∈ ReductionDsl.supportWhen (I.AnswerFits B) (R.eval2 cm.2 y q dflt),
            CostedFits widthB out z

/-- Evaluate a coin-only stage-1 computation in `ProbComp` by answering unused SM queries with
`bhModelSmDefault`. -/
def stageOneAsProbComp {ℓ : ℕ} {PQC α : Type}
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes) α) :
    ProbComp α :=
  simulateQ
    (QueryImpl.ofLift unifSpec ProbComp +
      (fun q => pure (bhModelSmDefault q) :
        QueryImpl (SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes) ProbComp))
    oa

end CryptoVerification.E2E
