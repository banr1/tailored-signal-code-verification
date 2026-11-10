/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Samplers
public import Computational.Specifications.Pqxdh.Game
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance

/-!
# Shared atomic sorts, samplers, and operations for `ReductionDsl`

**Trusted: definitions used by the statement.** This file defines the sort signature `atomicSig`,
coin-only uniform sampler tables (`atomicBaseSamplers`, `atomicSamplers`), and layered pure and
cryptographic operation tables (`atomicPureOps` through `atomicE2EOps`) shared across PQXDH
handshake, Double Ratchet and SPQR V1 session, multi-session composition, binary-harness adapter,
and leaf-primitive reductions. See `Computational/docs/TRUSTED_BASE.md`.

Each sort in `AtomicSort` carries an explicit 32-byte block measure `AtomicSort.blocks ℓ Pt`: byte
slices `pbytes w` and `bytes w` count `⌈len / w⌉` blocks, fixed words up to 256 bits and group
points count `1` block, 512-bit words and serialized public/identity keys count `2` blocks,
plaintexts count `ℓ / 32 + 1` blocks, and composite party states (`ghostSt`, `binSt`) take the
leaf-maximum block count matching `Ty.Fits`.

Multi-step Double Ratchet chain skips and SPQR symmetric-chain jumps are excluded from `AtomicOps`
and expressed as bounded `ReductionDsl` loops over single-step operations (`chainStep`,
`spqrChainNextKey`). Variable-length wire and state encoders clamp outputs to explicit bounds
strictly above protocol-reachable sizes so `OpsSizeHonest` holds uniformly. The little-endian word
helpers, five-part ML-KEM-768 split, and block-level HMAC/AES operations are adapted from earlier
definitions by Charles Sutton.
-/

@[expose] public section

set_option autoImplicit false

namespace ReductionDsl

open OracleSpec OracleComp
open CryptoVerification CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoGames
open Ratchet LibsignalInst LibsignalSession LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM CKA

/-! ## Base sorts and block measures -/

/-- Base sorts of `atomicSig ℓ Pt`. -/
inductive AtomicSort where
  | pbytes (w : ℕ+) | pu32 | bytes (w : ℕ+)
  | u8 | u32 | u64 | bv128 | bv256 | bv512 | fin (n : ℕ)
  | pk | idKey | plain | pt | ghostSt | binSt
  deriving DecidableEq

/-- Carrier type of each `AtomicSort` at plaintext byte length `ℓ` and group carrier `Pt`. -/
@[reducible] def AtomicSort.den (ℓ : ℕ) (Pt : Type) : AtomicSort → Type
  | .pbytes _ => SignalPqxdh.Bytes
  | .pu32 => UInt32
  | .bytes _ => Bytes
  | .u8 => BitVec 8
  | .u32 => BitVec 32
  | .u64 => BitVec 64
  | .bv128 => BitVec 128
  | .bv256 => BitVec 256
  | .bv512 => BitVec 512
  | .fin n => Fin n
  | .pk => PublicKey
  | .idKey => IdentityKey
  | .plain => Plain ℓ
  | .pt => Pt
  | .ghostSt => GhostState Bytes
  | .binSt => BinState

/-- Leaf-maximum 32-byte block measure of a model party state `GhostState Bytes`. -/
def ghostStBlocks (g : GhostState Bytes) : ℕ :=
  let pqBlk := (g.session.pqRatchetState.length + 31) / 32
  let rcBlk := g.session.receiverChains.foldr
    (fun rc acc => max acc (rc.messageKeys.foldr
      (fun mk m => max m ((mk.seed.length + 31) / 32)) rc.messageKeys.length))
    g.session.receiverChains.length
  let ceBlk := g.chainEpochs.foldr (fun e acc => max acc (bits e)) g.chainEpochs.length
  max 1 (max pqBlk (max rcBlk (max ceBlk (bits g.epoch))))

/-- Leaf-maximum 32-byte block measure of a binary party state `BinState`. -/
def binStBlocks (bs : BinState) : ℕ :=
  let bBlk := (bs.bytes.length + 31) / 32
  let chBlk := bs.epochs.chains.foldr (fun p acc => max acc (bits p.2)) bs.epochs.chains.length
  max 1 (max bBlk (max chBlk (bits bs.epochs.epoch)))

/-- Block measure of an `AtomicSort` value. -/
def AtomicSort.blocks (ℓ : ℕ) (Pt : Type) : (s : AtomicSort) → s.den ℓ Pt → ℕ
  | .pbytes w, x => (x.length + w - 1) / w
  | .bytes w, x => (x.length + w - 1) / w
  | .pu32, _ | .u8, _ | .u32, _ | .u64, _ | .bv128, _ | .bv256, _ | .pt, _ => 1
  | .plain, _ => ℓ / 32 + 1
  | .bv512, _ | .pk, _ | .idKey, _ => 2
  | .fin _, k => max 1 (bits k.val)
  | .ghostSt, g => ghostStBlocks g
  | .binSt, bs => binStBlocks bs

/-- Shared `ReductionDsl` signature at plaintext length `ℓ` and group carrier `Pt`. -/
@[reducible] def atomicSig (ℓ : ℕ) (Pt : Type := Empty) : Sig :=
  ⟨AtomicSort, AtomicSort.den ℓ Pt, AtomicSort.blocks ℓ Pt⟩

section TyAbbrevs

variable {ℓ : ℕ} {Pt : Type}

@[reducible] def PB (w : ℕ+) : Ty (atomicSig ℓ Pt) := .base (.pbytes w)
@[reducible] def PU32 : Ty (atomicSig ℓ Pt) := .base .pu32
@[reducible] def B (w : ℕ+) : Ty (atomicSig ℓ Pt) := .base (.bytes w)
@[reducible] def U8 : Ty (atomicSig ℓ Pt) := .base .u8
@[reducible] def U32 : Ty (atomicSig ℓ Pt) := .base .u32
@[reducible] def U64 : Ty (atomicSig ℓ Pt) := .base .u64
@[reducible] def BV128 : Ty (atomicSig ℓ Pt) := .base .bv128
@[reducible] def BV256 : Ty (atomicSig ℓ Pt) := .base .bv256
@[reducible] def BV512 : Ty (atomicSig ℓ Pt) := .base .bv512
@[reducible] def FinT (n : ℕ) : Ty (atomicSig ℓ Pt) := .base (.fin n)
@[reducible] def PK : Ty (atomicSig ℓ Pt) := .base .pk
@[reducible] def IdKey : Ty (atomicSig ℓ Pt) := .base .idKey
@[reducible] def PlainT : Ty (atomicSig ℓ Pt) := .base .plain
@[reducible] def PtT : Ty (atomicSig ℓ Pt) := .base .pt
@[reducible] def GhostStT : Ty (atomicSig ℓ Pt) := .base .ghostSt
@[reducible] def BinStT : Ty (atomicSig ℓ Pt) := .base .binSt

/-- `ReductionDsl` product type for the 96-byte PQXDH output `(rootKey, chainKey, pqrKey)`. -/
@[reducible] def drKeyT : Ty (atomicSig ℓ Pt) := .prod (PB 32) (.prod (PB 32) (PB 32))
def drKeyV (k : SignalPqxdh.DRKey) : (drKeyT (ℓ := ℓ) (Pt := Pt)).denote :=
  (k.rootKey, (k.chainKey, k.pqrKey))
def drKeyOfV (v : (drKeyT (ℓ := ℓ) (Pt := Pt)).denote) : SignalPqxdh.DRKey :=
  ⟨v.1, v.2.1, v.2.2⟩

/-- `ReductionDsl` product type for `SignalPqxdh.HandshakeHdr`. -/
@[reducible] def hdrT : Ty (atomicSig ℓ Pt) :=
  .prod (PB 32) (.prod (PB 32) (.prod PU32 (.prod (.opt PU32) (.prod PU32 (PB 1568)))))
def hdrV (h : SignalPqxdh.HandshakeHdr) : (hdrT (ℓ := ℓ) (Pt := Pt)).denote :=
  (h.ikAPk, (h.ekAPk, (h.spkId, (h.opkId?, (h.pqspkId, h.kemCt)))))
def hdrOfV (v : (hdrT (ℓ := ℓ) (Pt := Pt)).denote) : SignalPqxdh.HandshakeHdr :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩

-- Structured value types for decomposed SPQR V1, Double Ratchet, GhostState, and SignalMessage.
@[reducible] def spqrParamsT : Ty (atomicSig ℓ Pt) := .prod U32 U32
@[reducible] def spqrVnT : Ty (atomicSig ℓ Pt) := .prod (B 32) (.prod U32 (.prod U32 (.opt spqrParamsT)))
@[reducible] def spqrPrevEntryT : Ty (atomicSig ℓ Pt) := .prod U32 BV256
@[reducible] def spqrDirT : Ty (atomicSig ℓ Pt) :=
  .prod U32 (.prod (B 32) (.prod (.list spqrPrevEntryT) (B 35)))
@[reducible] def spqrEpochLinkT : Ty (atomicSig ℓ Pt) := .prod (.opt spqrDirT) (.opt spqrDirT)
@[reducible] def spqrChainT : Ty (atomicSig ℓ Pt) :=
  .prod U32 (.prod U64 (.prod (.list spqrEpochLinkT) (.prod (B 32) (.prod U64 (.opt spqrParamsT)))))
@[reducible] def spqrStatePartsT : Ty (atomicSig ℓ Pt) :=
  .prod (.opt (B 32)) (.prod (.opt spqrVnT) (.opt spqrChainT))
@[reducible] def drSenderChainT : Ty (atomicSig ℓ Pt) := .prod (.prod PK BV256) (.prod BV256 U32)
@[reducible] def drRecvChainT : Ty (atomicSig ℓ Pt) :=
  .prod PK (.prod (.opt (.prod BV256 U32)) (.list (.prod BV256 U32)))
@[reducible] def ghostPartsT : Ty (atomicSig ℓ Pt) :=
  .prod .bool (.prod U32 (.prod IdKey (.prod (.opt IdKey) (.prod BV256 (.prod U32
    (.prod .bool (.prod .nat (.prod (.list .nat)
      (.prod (.opt drSenderChainT) (.prod (.list drRecvChainT) (B 32)))))))))))
@[reducible] def signalHdrT : Ty (atomicSig ℓ Pt) := .prod U8 (.prod PK (.prod U32 U32))
@[reducible] def signalParsedT : Ty (atomicSig ℓ Pt) :=
  .prod signalHdrT (.prod (B 32) (.prod (B 32) (.opt (B 32))))

def partyToBool : Party → Bool | .A => false | .B => true
def boolToParty : Bool → Party | false => .A | true => .B

end TyAbbrevs

/-! ## Coin-only uniform samplers -/

/-- Fixed-width bitvector sorts sampled uniformly without `[SampleableType Pt]`. -/
inductive AtomicBaseUnif where
  | bv128 | bv256 | bv512
  deriving DecidableEq, Repr

def AtomicBaseUnif.sort : AtomicBaseUnif → AtomicSort
  | .bv128 => .bv128 | .bv256 => .bv256 | .bv512 => .bv512

def AtomicBaseUnif.cost : AtomicBaseUnif → ℕ
  | .bv128 | .bv256 => 1 | .bv512 => 2

instance (ℓ : ℕ) (Pt : Type) (b : AtomicBaseUnif) :
    SampleableType ((atomicSig ℓ Pt).den b.sort) := by
  cases b <;> dsimp [atomicSig, AtomicBaseUnif.sort] <;> exact inferInstance

/-- Coin-only uniform sampler table usable without `[SampleableType Pt]`. -/
@[reducible] def atomicBaseSamplers (ℓ : ℕ) (Pt : Type := Empty) : Samplers (atomicSig ℓ Pt) :=
  ReductionDsl.unifSamplers (S := atomicSig ℓ Pt) AtomicBaseUnif.sort AtomicBaseUnif.cost

/-- Uniformly sampleable base sorts, including group elements `Pt`. -/
inductive AtomicUnifBase where
  | bv128 | bv256 | bv512 | pt
  deriving DecidableEq, Repr

def AtomicUnifBase.sort : AtomicUnifBase → AtomicSort
  | .bv128 => .bv128 | .bv256 => .bv256 | .bv512 => .bv512 | .pt => .pt

def AtomicUnifBase.cost : AtomicUnifBase → ℕ
  | .bv128 | .bv256 | .pt => 1 | .bv512 => 2

instance (ℓ : ℕ) (Pt : Type) [SampleableType Pt] (b : AtomicUnifBase) :
    SampleableType ((atomicSig ℓ Pt).den b.sort) := by
  cases b <;> dsimp [atomicSig, AtomicUnifBase.sort] <;> exact inferInstance

/-- Uniform sampler table over bitvectors and group elements `Pt`. -/
@[reducible] def atomicSamplers (ℓ : ℕ) (Pt : Type) [SampleableType Pt] :
    Samplers (atomicSig ℓ Pt) :=
  ReductionDsl.unifSamplers (S := atomicSig ℓ Pt) AtomicUnifBase.sort AtomicUnifBase.cost

/-! ## Pure wire and state-decomposition helpers -/

section PureHelpers

def toLEBytes (n : Nat) {w : Nat} (x : BitVec w) : Bytes :=
  List.ofFn fun j : Fin n => x.extractLsb' (8 * j.val) 8

def bytesToWordLE (w : Nat) (bs : Bytes) : BitVec w :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend w) 0

def fitBytesN (n : Nat) (bs : Bytes) : List.Vector (BitVec 8) n :=
  ⟨(bs ++ List.replicate n 0#8).take n, by simp⟩

-- Canonical `PreKeySignalMessage` (tag-3) and `SignalMessage` (tag-2) protobuf wire parsers.
def e2eReadProstVarint : List (BitVec 8) → Option (ℕ × List (BitVec 8))
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else (e2eReadProstVarint rest).map (fun (hi, rest') => (b.toNat - 128 + 128 * hi, rest'))

def e2eParseOptPreKeyId : List (BitVec 8) → Option (Option UInt32 × List (BitVec 8))
  | [] => some (none, [])
  | b :: rest =>
    if b == 0x08#8 then (e2eReadProstVarint rest).map (fun (n, r) => (some (UInt32.ofNat n), r))
    else some (none, b :: rest)

def e2eParseUint32Field (keyByte : BitVec 8) :
    List (BitVec 8) → Option (UInt32 × List (BitVec 8))
  | k :: rest =>
    if k == keyByte then (e2eReadProstVarint rest).map (fun (n, r) => (UInt32.ofNat n, r)) else none
  | [] => none

def e2eParseDjbKeyField (keyByte : BitVec 8) :
    List (BitVec 8) → Option (List (BitVec 8) × List (BitVec 8))
  | k :: 0x21#8 :: 0x05#8 :: rest =>
    if k == keyByte && decide (32 ≤ rest.length) then some (rest.take 32, rest.drop 32) else none
  | _ => none

def e2eParseInnerMsgField : List (BitVec 8) → Option (List (BitVec 8) × List (BitVec 8))
  | 0x22#8 :: rest =>
    (e2eReadProstVarint rest).bind (fun (len, afterLen) =>
      if decide (len ≤ afterLen.length) then some (afterLen.take len, afterLen.drop len) else none)
  | _ => none

def e2eParseKyberCtField : List (BitVec 8) → Option (List (BitVec 8))
  | 0x42#8 :: 0xa1#8 :: 0x0c#8 :: 0x08#8 :: rest =>
    if decide (1568 ≤ rest.length) then some (rest.take 1568) else none
  | _ => none

def e2eDecodePreKeyRaw : Bytes → Option PreKeyMessageFields
  | t :: v :: proto =>
    if t == wirePrekey && v == versionByte currentVersion then
      (e2eParseOptPreKeyId proto).bind fun (opkId?, after1) =>
      (e2eParseDjbKeyField 0x12#8 after1).bind fun (bkBytes, after2) =>
      (e2eParseDjbKeyField 0x1a#8 after2).bind fun (idBytes, after3) =>
      (e2eParseInnerMsgField after3).bind fun (inner, after4) =>
      (e2eParseUint32Field 0x28#8 after4).bind fun (regId, after5) =>
      (e2eParseUint32Field 0x30#8 after5).bind fun (spkId, after6) =>
      (e2eParseUint32Field 0x38#8 after6).bind fun (pqspkId, after7) =>
      (e2eParseKyberCtField after7).bind fun kemCtBytes =>
      if hbk : bkBytes.length = 32 then if hid : idBytes.length = 32 then
        if hct : kemCtBytes.length = 1568 then
          some { regId := regId.toBitVec, opkId := opkId?.map UInt32.toBitVec,
                 spkId := spkId.toBitVec, kpkId := pqspkId.toBitVec, kyberCt := ⟨kemCtBytes, hct⟩,
                 baseKey := ⟨bkBytes, hbk⟩, idPub := ⟨idBytes, hid⟩, inner := inner }
        else none
      else none else none
    else none
  | _ => none

def e2eDecodePreKeyMsg (c : Bytes) : Option PreKeyMessageFields :=
  match e2eDecodePreKeyRaw c with
  | some m => if c == wirePrekey :: m.bytes then some m else none
  | none => none

def e2eHdrOfPreKeyMsg (m : PreKeyMessageFields) : SignalPqxdh.HandshakeHdr :=
  { ikAPk := vecU8 m.idPub, ekAPk := vecU8 m.baseKey, spkId := u32 m.spkId,
    opkId? := m.opkId.map u32, pqspkId := u32 m.kpkId, kemCt := vecU8 m.kyberCt }

def e2eExpectedPreKeyMsg (regIdA : BitVec 32) (hdr : SignalPqxdh.HandshakeHdr)
    (inner : Bytes) : PreKeyMessageFields :=
  { regId := regIdA, opkId := hdr.opkId?.map (fun id => BitVec.ofNat 32 id.toNat),
    spkId := BitVec.ofNat 32 hdr.spkId.toNat, kpkId := BitVec.ofNat 32 hdr.pqspkId.toNat,
    kyberCt := u8Vec 1568 hdr.kemCt, baseKey := u8Vec 32 hdr.ekAPk,
    idPub := u8Vec 32 hdr.ikAPk, inner := inner }

def e2eWireInnerBytes (c : Bytes) : Option Bytes :=
  match e2eDecodePreKeyMsg c with
  | some m => some (m.inner.take c.length)
  | none =>
    match c with
    | t :: body => if t == wireWhisper then some body else none
    | [] => none

def e2ePartneredInnerBytes (bobAccepted : Bool) (regIdA : BitVec 32)
    (sessionHdr : SignalPqxdh.HandshakeHdr) (c : Bytes) : Option Bytes :=
  if !bobAccepted then
    match e2eDecodePreKeyMsg c with
    | some m =>
      if c == wirePrekey :: (e2eExpectedPreKeyMsg regIdA sessionHdr m.inner).bytes then
        some (m.inner.take c.length)
      else none
    | none => none
  else
    match e2eDecodePreKeyMsg c with
    | some m =>
      if e2eHdrOfPreKeyMsg m == sessionHdr then some (m.inner.take c.length) else none
    | none =>
      match c with
      | t :: body => if t == wireWhisper then some body else none
      | [] => none

-- SPQR V1 `PqRatchetState`, `GhostState`, and `SessionRecord` pure decomposition helpers.
def e2eReadU32BE : Bytes → BitVec 32
  | b0 :: b1 :: b2 :: b3 :: _ =>
    (b0.zeroExtend 32 <<< 24) ||| (b1.zeroExtend 32 <<< 16) |||
      (b2.zeroExtend 32 <<< 8) ||| b3.zeroExtend 32
  | _ => 0#32

def splitSpqrPrev : ℕ → Bytes → List (BitVec 32 × BitVec 256) × Bytes
  | 0, bs => ([], bs.take 35)
  | fuel + 1, bs =>
    if bs.length < 36 then ([], bs)
    else
      let (rest, tail) := splitSpqrPrev fuel (bs.drop 36)
      ((e2eReadU32BE (bs.take 4), HKDF.bytesToKey32 ((bs.drop 4).take 32)) :: rest, tail)

def joinSpqrPrev (entries : List (BitVec 32 × BitVec 256)) (tail : Bytes) : Bytes :=
  (entries.flatMap fun (idx, key) => HMAC.toBEBytes 4 idx ++ HMAC.keyToBytes32 key) ++ tail.take 35

def spqrParamsToV {ℓ : ℕ} {Pt : Type} (p : LibsignalSpqrV1.ChainParamsPB) :
    (spqrParamsT (ℓ := ℓ) (Pt := Pt)).denote := (p.maxJump, p.maxOooKeys)

def spqrParamsOfV {ℓ : ℕ} {Pt : Type} (v : (spqrParamsT (ℓ := ℓ) (Pt := Pt)).denote) :
    LibsignalSpqrV1.ChainParamsPB := { maxJump := v.1, maxOooKeys := v.2 }

def spqrVnToV {ℓ : ℕ} {Pt : Type} (vn : LibsignalSpqrV1.VersionNegotiationPB) :
    (spqrVnT (ℓ := ℓ) (Pt := Pt)).denote :=
  (vn.authKey.take 64, (vn.direction, (vn.minVersion, vn.chainParams.map spqrParamsToV)))

def spqrVnOfV {ℓ : ℕ} {Pt : Type} (v : (spqrVnT (ℓ := ℓ) (Pt := Pt)).denote) :
    LibsignalSpqrV1.VersionNegotiationPB :=
  { authKey := v.1, direction := v.2.1, minVersion := v.2.2.1,
    chainParams := v.2.2.2.map spqrParamsOfV }

def spqrDirToV {ℓ : ℕ} {Pt : Type} (d : LibsignalSpqrV1.EpochDirectionPB) :
    (spqrDirT (ℓ := ℓ) (Pt := Pt)).denote :=
  let (entries, tail) := splitSpqrPrev 2201 d.prev
  (d.ctr, (d.next.take 64, (entries, tail)))

def spqrDirOfV {ℓ : ℕ} {Pt : Type} (v : (spqrDirT (ℓ := ℓ) (Pt := Pt)).denote) :
    LibsignalSpqrV1.EpochDirectionPB :=
  { ctr := v.1, next := v.2.1, prev := joinSpqrPrev v.2.2.1 v.2.2.2 }

def spqrChainToV {ℓ : ℕ} {Pt : Type} (c : LibsignalSpqrV1.ChainPB) :
    (spqrChainT (ℓ := ℓ) (Pt := Pt)).denote :=
  let links := (c.links.take 4).map fun lk => (lk.send.map spqrDirToV, lk.recv.map spqrDirToV)
  (c.direction, (c.currentEpoch, (links, (c.nextRoot.take 64, (c.sendEpoch,
    c.params.map spqrParamsToV)))))

def spqrChainOfV {ℓ : ℕ} {Pt : Type} (v : (spqrChainT (ℓ := ℓ) (Pt := Pt)).denote) :
    LibsignalSpqrV1.ChainPB :=
  let links := v.2.2.1.map fun (s?, r?) =>
    ({ send := s?.map spqrDirOfV, recv := r?.map spqrDirOfV } : LibsignalSpqrV1.ChainEpochPB)
  { direction := v.1, currentEpoch := v.2.1, links := links,
    nextRoot := v.2.2.2.1, sendEpoch := v.2.2.2.2.1, params := v.2.2.2.2.2.map spqrParamsOfV }

def spqrSplitEval {ℓ : ℕ} {Pt : Type} (bs : Bytes) :
    Option (spqrStatePartsT (ℓ := ℓ) (Pt := Pt)).denote :=
  match LibsignalSpqrV1.Proto.spqrDecodeState bs with
  | .error _ => none
  | .ok st =>
    let v1? := st.inner.map fun (.v1 v) => (LibsignalSpqrV1.V1State.encodeRaw v).take 64000
    some (v1?, (st.versionNegotiation.map spqrVnToV, st.chain.map spqrChainToV))

def spqrJoinEval {ℓ : ℕ} {Pt : Type} (parts : (spqrStatePartsT (ℓ := ℓ) (Pt := Pt)).denote) :
    Bytes :=
  let (v1?, (vn?, ch?)) := parts
  let raw :=
    LibsignalSpqrV1.Proto.encodeOptMessage
      LibsignalSpqrV1.VersionNegotiationPB.encodeRaw 1#32 (vn?.map spqrVnOfV) ++
    LibsignalSpqrV1.Proto.encodeOptMessage
      LibsignalSpqrV1.ChainPB.encodeRaw 2#32 (ch?.map spqrChainOfV) ++
    match v1? with
    | none => []
    | some v1Raw => LibsignalSpqrV1.Proto.encodeMessage id 3#32 v1Raw
  raw.take (32 * 11000)

def ghostSplitEval {ℓ : ℕ} {Pt : Type} (g : GhostState Bytes) :
    (ghostPartsT (ℓ := ℓ) (Pt := Pt)).denote :=
  let st := g.session
  let sc? := st.senderChain.map fun sc =>
    ((sc.ratchetKey.publicKey, HKDF.bytesToKey32 sc.ratchetKey.privateKey.bytes.toList),
     (sc.chainKey.key, sc.chainKey.index))
  let rcs := (st.receiverChains.take 5).map fun rc =>
    (rc.senderRatchetKey,
     (rc.chainKey.map (fun ck => (ck.key, ck.index)),
      rc.messageKeys.map (fun mk => (HKDF.bytesToKey32 mk.seed, mk.counter))))
  (partyToBool g.party, (st.sessionVersion, (st.localIdentity, (st.remoteIdentity,
    (st.rootKey, (st.previousCounter, (st.pendingPreKey, (g.epoch,
      (g.chainEpochs, (sc?, (rcs, st.pqRatchetState)))))))))))

def ghostJoinEval {ℓ : ℕ} {Pt : Type} (p : (ghostPartsT (ℓ := ℓ) (Pt := Pt)).denote) :
    GhostState Bytes :=
  let (isB, (ver, (locId, (remId?, (rk, (prevCtr, (pend, (ep, (cEps, (sc?, (rcs, pqSt))))))))))) := p
  let sc := sc?.map fun ((pub, priv), (ck, idx)) =>
    ({ ratchetKey := { publicKey := pub, privateKey := ⟨Ratchet.keyToBytesVec32 priv⟩ },
       chainKey := { key := ck, index := idx } } : SenderChain)
  let rcList := (rcs.take 5).map fun (srk, (ck?, mks)) =>
    ({ senderRatchetKey := srk,
       chainKey := ck?.map fun (ck, idx) =>
         ({ key := ck, index := idx } : LibsignalSession.ChainKey),
       messageKeys := mks.map fun (sd, ctr) =>
         ({ seed := HMAC.keyToBytes32 sd, counter := ctr } : MessageKeyGenerator) } : ReceiverChain)
  { party := boolToParty isB, epoch := ep, chainEpochs := cEps
    session := { sessionVersion := ver, localIdentity := locId, remoteIdentity := remId?,
                 rootKey := rk, previousCounter := prevCtr, senderChain := sc,
                 receiverChains := rcList, pendingPreKey := pend, pqRatchetState := pqSt } }

def e2eRecordExtras (regIdA regIdB bobRemoteRegId : BitVec 32)
    (hdr : SignalPqxdh.HandshakeHdr) : Party → RecordExtras
  | .A =>
    let base : PublicKey := ⟨u8Vec 32 hdr.ekAPk⟩
    { pending := { preKeyId := hdr.opkId?.map (fun id => BitVec.ofNat 32 id.toNat)
                   signedPreKeyId := BitVec.ofNat 32 hdr.spkId.toNat
                   baseKey := base, timestamp := 0#64 }
      kyber := some { preKeyId := BitVec.ofNat 32 hdr.pqspkId.toNat
                      ciphertext := kyberKey (u8Vec 1568 hdr.kemCt) }
      remoteRegistrationId := regIdB, localRegistrationId := regIdA, aliceBaseKey := base.serialize }
  | .B =>
    let base : PublicKey := ⟨u8Vec 32 hdr.ekAPk⟩
    { pending := { preKeyId := none, signedPreKeyId := 0#32, baseKey := base, timestamp := 0#64 }
      kyber := none
      remoteRegistrationId := bobRemoteRegId, localRegistrationId := regIdB
      aliceBaseKey := base.serialize }

def e2eEncodeSessionRecord {ℓ : ℕ} {Pt : Type}
    (inp : ((U32 (ℓ := ℓ) (Pt := Pt)).denote × (U32 (ℓ := ℓ) (Pt := Pt)).denote ×
      (U32 (ℓ := ℓ) (Pt := Pt)).denote × (hdrT (ℓ := ℓ) (Pt := Pt)).denote) × GhostState Bytes) :
    BinState :=
  let ((regIdA, (regIdB, (bobRemoteRegId, hdrV0))), g) := inp
  let bs := binStateOfUnderExtras (e2eRecordExtras regIdA regIdB bobRemoteRegId (hdrOfV hdrV0)) g
  { bs with bytes := bs.bytes.take (32 * 24000) }

end PureHelpers

/-! ## Pure operations -/

/-- Pure byte, word, key, wire, and state-codec operations independent of cryptographic primitives. -/
inductive AtomicPureOp where
  -- `SignalPqxdh.Bytes` (`List UInt8`) slices and protobuf varint
  | pbytesLit (w : ℕ+) (v : SignalPqxdh.Bytes) | pbytesCat (m n : ℕ+)
  | pbytesCons (b : UInt8) (w : ℕ+) | pbytesWiden (w d : ℕ+) | pbytesTakeK (w k : ℕ+)
  | pbytesTake (w : ℕ+) | pbytesDrop (w : ℕ+) | pbytesLen (w : ℕ+) | pbytesEq (m n : ℕ+)
  | pbVarint
  -- `Bytes` (`List (BitVec 8)`) slices and `PB` / `B` conversions
  | bytesLit (w : ℕ+) (v : Bytes) | bytesCat (m n : ℕ+)
  | bytesAppend8 | bytesAppend16
  | bytesCons (b : BitVec 8) (w : ℕ+) | bytesWiden (w d : ℕ+) | bytesTakeK (w k : ℕ+)
  | bytesTake (w : ℕ+) | bytesDrop (w : ℕ+) | bytesLen (w : ℕ+) | bytesEq (m n : ℕ+)
  | bytesLtOp (m n : ℕ+) | pbytesToBytes (w : ℕ+) | bytesToPbytes (w : ℕ+)
  -- Fixed-width word arithmetic and codecs
  | pu32Lit (k : UInt32) | pu32OfNat | pu32ToNat | pu32Eq | pu32ToU32 | u32ToPu32
  | u8Lit (v : BitVec 8) | u8OfNat | u8ToNat | u8Eq | u8Lt
  | u32Lit (v : BitVec 32) | u32OfNat | u32ToNat | u32Eq | u32Lt | u32Add | u32Sub | u32BeBytes
  | u64Lit (v : BitVec 64) | u64OfNat | u64ToNat | u64Eq | u64Lt | u64Add | u64Sub | u64Trunc8
  | u64LeBytes | bytesToU64Le
  | finVal (n : ℕ) | finEq (n : ℕ)
  | bv128Lit (v : BitVec 128) | bv128Eq | bv128Xor | bv128ToBytes16 | bytesToBv128
  | bv256Lit (v : BitVec 256) | bv256Eq
  | bv256ToPbytes32 | pbytesToBv256 | bv256ToBytes32 | bytesToBv256
  | bv512Lit (v : BitVec 512) | bv512ToBytes64 | bv512ToPbytes64
  -- Serialized key and `Plain ℓ` codecs
  | idKeyOfPbytes | idKeySerialize | idKeyEq
  | pkOfPbytes | pkDeserialize | pkSerialize | pkEq
  | plainDefault | plainToBytes | bytesToPlain | fitPlain | plainEq
  -- Wire message and session-state codecs
  | checkShortCiphertext | parsePreKeyWire | partneredInnerBytes | wireInnerBytes | splitWhisperWire
  | isValidSignalWire | signalMsgParse | wrapWhisperWire | wrapPreKeyWire
  | spqrParsePreamble | spqrAssembleMsg | spqrStateSplit | spqrStateJoin
  | ghostStateSplit | ghostStateJoin | encodeSessionRecord

@[reducible] def AtomicPureOp.dom (ℓ : ℕ) (Pt : Type) : AtomicPureOp → Ty (atomicSig ℓ Pt)
  | .pbytesLit _ _ | .bytesLit _ _ | .pu32Lit _ | .u8Lit _ | .u32Lit _ | .u64Lit _
  | .bv128Lit _ | .bv256Lit _ | .bv512Lit _ | .plainDefault => .unit
  | .pbytesCat m n | .pbytesEq m n => .prod (PB m) (PB n)
  | .pbytesCons _ w | .pbytesWiden w _ | .pbytesTakeK w _ | .pbytesLen w | .pbytesToBytes w => PB w
  | .pbytesTake w | .pbytesDrop w => .prod .nat (PB w)
  | .pbVarint | .pu32OfNat | .u8OfNat | .u32OfNat | .u64OfNat => .nat
  | .bytesCat m n | .bytesEq m n | .bytesLtOp m n => .prod (B m) (B n)
  | .bytesAppend8 => .prod (B 32) (B 8)
  | .bytesAppend16 => .prod (B 32) (B 16)
  | .bytesCons _ w | .bytesWiden w _ | .bytesTakeK w _ | .bytesLen w | .bytesToPbytes w => B w
  | .bytesTake w | .bytesDrop w => .prod .nat (B w)
  | .pu32ToNat | .pu32ToU32 => PU32
  | .pu32Eq => .prod PU32 PU32
  | .u32ToPu32 | .u32ToNat | .u32BeBytes => U32
  | .u8ToNat => U8
  | .u8Eq | .u8Lt => .prod U8 U8
  | .u32Eq | .u32Lt | .u32Add | .u32Sub => .prod U32 U32
  | .u64ToNat | .u64Trunc8 | .u64LeBytes => U64
  | .bytesToU64Le => B 8
  | .u64Eq | .u64Lt | .u64Add | .u64Sub => .prod U64 U64
  | .finVal n => FinT n
  | .finEq n => .prod (FinT n) (FinT n)
  | .bv128Eq | .bv128Xor => .prod BV128 BV128
  | .bv128ToBytes16 => BV128
  | .bytesToBv128 => B 16
  | .bv256Eq => .prod BV256 BV256
  | .bv256ToPbytes32 | .bv256ToBytes32 => BV256
  | .pbytesToBv256 | .idKeyOfPbytes | .pkOfPbytes => PB 32
  | .bytesToBv256 | .bytesToPlain | .fitPlain | .parsePreKeyWire | .wireInnerBytes
  | .splitWhisperWire | .isValidSignalWire | .signalMsgParse | .wrapWhisperWire
  | .spqrParsePreamble | .spqrStateSplit => B 32
  | .bv512ToBytes64 | .bv512ToPbytes64 => BV512
  | .idKeySerialize => IdKey
  | .idKeyEq => .prod IdKey IdKey
  | .pkDeserialize => B 33
  | .pkSerialize => PK
  | .pkEq => .prod PK PK
  | .plainToBytes => PlainT
  | .plainEq => .prod PlainT PlainT
  | .checkShortCiphertext => .prod (B 32) (.opt (B 32))
  | .partneredInnerBytes => .prod .bool (.prod U32 (.prod hdrT (B 32)))
  | .wrapPreKeyWire => .prod U32 (.prod hdrT (B 32))
  | .spqrAssembleMsg => .prod U64 (.prod U32 (B 64))
  | .spqrStateJoin => spqrStatePartsT
  | .ghostStateSplit => GhostStT
  | .ghostStateJoin => ghostPartsT
  | .encodeSessionRecord => .prod (.prod U32 (.prod U32 (.prod U32 hdrT))) GhostStT

@[reducible] def AtomicPureOp.cod (ℓ : ℕ) (Pt : Type) : AtomicPureOp → Ty (atomicSig ℓ Pt)
  | .pbytesLit w _ | .pbytesTake w | .pbytesDrop w | .bytesToPbytes w => PB w
  | .pbytesCat m n => PB (m + n)
  | .pbytesCons _ w => PB (w + 1)
  | .pbytesWiden w d => PB (w + d)
  | .pbytesTakeK _ k => PB k
  | .pbVarint => PB 10
  | .pbytesLen _ | .bytesLen _ | .pu32ToNat | .u8ToNat | .u32ToNat | .u64ToNat | .finVal _ => .nat
  | .pbytesEq _ _ | .bytesEq _ _ | .bytesLtOp _ _ | .pu32Eq | .u8Eq | .u8Lt | .u32Eq | .u32Lt
  | .u64Eq | .u64Lt | .finEq _ | .bv128Eq | .bv256Eq | .idKeyEq | .pkEq | .plainEq
  | .checkShortCiphertext | .isValidSignalWire => .bool
  | .bytesLit w _ | .bytesTake w | .bytesDrop w | .pbytesToBytes w => B w
  | .bytesCat m n => B (m + n)
  | .bytesCons _ w => B (w + 1)
  | .bytesWiden w d => B (w + d)
  | .bytesTakeK _ k => B k
  | .pu32Lit _ | .pu32OfNat | .u32ToPu32 => PU32
  | .u8Lit _ | .u8OfNat | .u64Trunc8 => U8
  | .u32Lit _ | .u32OfNat | .pu32ToU32 | .u32Add | .u32Sub => U32
  | .u32BeBytes => B 4
  | .u64Lit _ | .u64OfNat | .u64Add | .u64Sub | .bytesToU64Le => U64
  | .u64LeBytes => B 8
  | .bv128Lit _ | .bv128Xor | .bytesToBv128 => BV128
  | .bv128ToBytes16 => B 16
  | .bv256Lit _ | .pbytesToBv256 | .bytesToBv256 => BV256
  | .bv256ToPbytes32 => PB 32
  | .bv256ToBytes32 | .bytesAppend8 | .bytesAppend16
  | .plainToBytes | .wrapWhisperWire | .wrapPreKeyWire
  | .spqrAssembleMsg | .spqrStateJoin => B 32
  | .bv512Lit _ => BV512
  | .bv512ToBytes64 => B 64
  | .bv512ToPbytes64 => PB 64
  | .idKeyOfPbytes => IdKey
  | .idKeySerialize | .pkSerialize => B 33
  | .pkOfPbytes => PK
  | .pkDeserialize => .opt PK
  | .plainDefault | .fitPlain => PlainT
  | .bytesToPlain => .opt PlainT
  | .parsePreKeyWire => .opt (.prod U32 (.prod hdrT (B 32)))
  | .partneredInnerBytes | .wireInnerBytes | .splitWhisperWire => .opt (B 32)
  | .signalMsgParse => .opt signalParsedT
  | .spqrParsePreamble => .opt (.prod U8 (.prod U64 (.prod U32 (B 32))))
  | .spqrStateSplit => .opt spqrStatePartsT
  | .ghostStateSplit => ghostPartsT
  | .ghostStateJoin => GhostStT
  | .encodeSessionRecord => BinStT

def AtomicPureOp.eval (ℓ : ℕ) (Pt : Type) :
    (o : AtomicPureOp) → (o.dom ℓ Pt).denote → (o.cod ℓ Pt).denote
  | .pbytesLit _ v, _ => v
  | .pbytesCat _ _, (x, y) => x ++ y
  | .pbytesCons b _, x => b :: x
  | .pbytesWiden _ _, x => x
  | .pbytesTakeK _ k, x => x.take k
  | .pbytesTake _, (n, x) => x.take n
  | .pbytesDrop _, (n, x) => x.drop n
  | .pbytesLen _, x => x.length
  | .pbytesEq _ _, (x, y) => x == y
  | .pbVarint, n => SignalPqxdh.pbVarint n
  | .bytesLit _ v, _ => v
  | .bytesCat _ _, (x, y) => x ++ y
  | .bytesAppend8, (x, y) => x ++ y.take 8
  | .bytesAppend16, (x, y) => x ++ y.take 16
  | .bytesCons b _, x => b :: x
  | .bytesWiden _ _, x => x
  | .bytesTakeK _ k, x => x.take k
  | .bytesTake _, (n, x) => x.take n
  | .bytesDrop _, (n, x) => x.drop n
  | .bytesLen _, x => x.length
  | .bytesEq _ _, (x, y) => x == y
  | .bytesLtOp _ _, (x, y) => LibsignalSpqrV1.bytesLt x y
  | .pbytesToBytes _, x => ofU8 x
  | .bytesToPbytes _, x => toU8 x
  | .pu32Lit k, _ => k
  | .pu32OfNat, n => UInt32.ofNat n
  | .pu32ToNat, k => k.toNat
  | .pu32Eq, (a, b) => a == b
  | .pu32ToU32, k => k.toBitVec
  | .u32ToPu32, v => UInt32.ofBitVec v
  | .u8Lit v, _ => v
  | .u8OfNat, n => BitVec.ofNat 8 n
  | .u8ToNat, v => v.toNat
  | .u8Eq, (a, b) => a == b
  | .u8Lt, (a, b) => decide (a < b)
  | .u32Lit v, _ => v
  | .u32OfNat, n => BitVec.ofNat 32 n
  | .u32ToNat, v => v.toNat
  | .u32Eq, (a, b) => a == b
  | .u32Lt, (a, b) => decide (a < b)
  | .u32Add, (a, b) => a + b
  | .u32Sub, (a, b) => a - b
  | .u32BeBytes, v => HMAC.toBEBytes 4 v
  | .u64Lit v, _ => v
  | .u64OfNat, n => BitVec.ofNat 64 n
  | .u64ToNat, v => v.toNat
  | .u64Eq, (a, b) => a == b
  | .u64Lt, (a, b) => decide (a < b)
  | .u64Add, (a, b) => a + b
  | .u64Sub, (a, b) => a - b
  | .u64Trunc8, v => v.truncate 8
  | .u64LeBytes, v => toLEBytes 8 v
  | .bytesToU64Le, bs => bytesToWordLE 64 bs
  | .finVal _, k => k.val
  | .finEq _, (a, b) => a == b
  | .bv128Lit v, _ => v
  | .bv128Eq, (a, b) => a == b
  | .bv128Xor, (a, b) => a ^^^ b
  | .bv128ToBytes16, v => toLEBytes 16 v
  | .bytesToBv128, bs => bytesToWordLE 128 bs
  | .bv256Lit v, _ => v
  | .bv256Eq, (a, b) => a == b
  | .bv256ToPbytes32, v => SignalPqxdh.word256ToBytes v
  | .pbytesToBv256, bs => HKDF.bytesToKey32 (ofU8 bs)
  | .bv256ToBytes32, v => HMAC.keyToBytes32 v
  | .bytesToBv256, bs => HKDF.bytesToKey32 bs
  | .bv512Lit v, _ => v
  | .bv512ToBytes64, v => LibsignalSpqrV1.coinBytes v
  | .bv512ToPbytes64, v => toU8 (LibsignalSpqrV1.coinBytes v)
  | .idKeyOfPbytes, bs => ⟨⟨u8Vec 32 bs⟩⟩
  | .idKeySerialize, k => k.serialize
  | .idKeyEq, (a, b) => a == b
  | .pkOfPbytes, bs => ⟨u8Vec 32 bs⟩
  | .pkDeserialize, bs => (PublicKey.deserialize bs).toOption
  | .pkSerialize, k => k.serialize
  | .pkEq, (a, b) => a == b
  | .plainDefault, _ => List.Vector.replicate ℓ 0#8
  | .plainToBytes, m => m.toList
  | .bytesToPlain, bs => if h : bs.length = ℓ then some ⟨bs, h⟩ else none
  | .fitPlain, bs => Ratchet.padOrTruncatePlain ℓ bs
  | .plainEq, (a, b) => decide (a = b)
  | .checkShortCiphertext, (c, inner?) =>
    shortCiphertext c &&
      match inner? with | some i => decide (i.length + 2048 < 2 ^ 32) | none => true
  | .parsePreKeyWire, c =>
    (e2eDecodePreKeyMsg c).map fun m => (m.regId, (hdrV (e2eHdrOfPreKeyMsg m), m.inner.take c.length))
  | .partneredInnerBytes, (bobAcc, (regIdA, (hdr, c))) =>
    e2ePartneredInnerBytes bobAcc regIdA (hdrOfV hdr) c
  | .wireInnerBytes, c => e2eWireInnerBytes c
  | .splitWhisperWire, c =>
    match c with | t :: body => if t == wireWhisper then some body else none | [] => none
  | .isValidSignalWire, body => (SignalMessage.tryFrom protoSignalCodec body).isOk
  | .signalMsgParse, body =>
    match SignalMessage.tryFrom protoSignalCodec body with
    | .ok m =>
      some ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
            (m.ciphertext.take body.length,
             (m.pqRatchet.take body.length, m.addresses.map (·.take body.length))))
    | .error _ => none
  | .wrapWhisperWire, ct =>
    if ct.isEmpty then [] else (wireWhisper :: ct).take (32 * (2 * (ℓ / 32) + 26))
  | .wrapPreKeyWire, (regIdA, (hdr, inner)) =>
    if inner.isEmpty then []
    else (wirePrekey :: (e2eExpectedPreKeyMsg regIdA (hdrOfV hdr) inner).bytes).take
      (32 * (2 * (ℓ / 32) + 84))
  | .spqrParsePreamble, msg =>
    match LibsignalSpqrV1.msgPreamble msg with
    | .ok p => some (p.version, (p.epoch, (p.index, p.remaining.take msg.length)))
    | .error _ => none
  | .spqrAssembleMsg, (ep, (idx, sfx)) =>
    (LibsignalSpqrV1.encode_varint (idx.zeroExtend 64)
      (LibsignalSpqrV1.encode_varint ep [1#8]) ++ sfx.take 64).take 96
  | .spqrStateSplit, bs => spqrSplitEval bs
  | .spqrStateJoin, parts => spqrJoinEval parts
  | .ghostStateSplit, g => ghostSplitEval g
  | .ghostStateJoin, parts => ghostJoinEval parts
  | .encodeSessionRecord, inp => e2eEncodeSessionRecord inp

def AtomicPureOp.cost (ℓ : ℕ) : AtomicPureOp → ℕ
  | .pbytesLit w v => w + v.length
  | .bytesLit w v => w + v.length
  | .pbytesCat m n | .pbytesEq m n | .bytesCat m n | .bytesEq m n | .bytesLtOp m n => m + n
  | .pbytesCons _ w | .pbytesTake w | .pbytesDrop w
  | .bytesCons _ w | .bytesTake w | .bytesDrop w => w + 1
  | .pbytesWiden w d | .bytesWiden w d => w + d
  | .pbytesTakeK w k | .bytesTakeK w k => w + k
  | .pbytesLen w | .bytesLen w => bits w + 1
  | .pbytesToBytes w | .bytesToPbytes w => w
  | .pu32Lit _ | .pu32OfNat | .pu32Eq | .pu32ToU32 | .u32ToPu32
  | .u8Lit _ | .u8OfNat | .u8Eq | .u8Lt | .u64Trunc8
  | .u32Lit _ | .u32OfNat | .u32Eq | .u32Lt | .u32Add | .u32Sub | .finVal _ => 1
  | .u64Lit _ | .u64OfNat | .u64Eq | .u64Lt | .u64Add | .u64Sub | .finEq _
  | .bv128Lit _ | .bv128Eq | .bv128Xor | .bv256Lit _ | .bv256Eq
  | .bytesAppend8 | .bytesAppend16
  | .idKeyEq | .pkEq | .splitWhisperWire => 2
  | .bv512Lit _ => 3
  | .u32BeBytes | .checkShortCiphertext | .spqrParsePreamble => 4
  | .spqrAssembleMsg => 6
  | .u8ToNat | .u64LeBytes | .bytesToU64Le => 8
  | .pbVarint => 10
  | .bv128ToBytes16 | .bytesToBv128 | .ghostStateSplit | .ghostStateJoin => 16
  | .pu32ToNat | .u32ToNat | .bv256ToPbytes32 | .pbytesToBv256
  | .bv256ToBytes32 | .bytesToBv256 => 32
  | .idKeyOfPbytes | .idKeySerialize | .pkOfPbytes | .pkDeserialize | .pkSerialize => 33
  | .u64ToNat | .bv512ToBytes64 | .bv512ToPbytes64 => 64
  | .parsePreKeyWire | .wireInnerBytes => 96
  | .partneredInnerBytes => 128
  | .plainDefault | .plainToBytes | .bytesToPlain | .fitPlain | .plainEq => ℓ / 32 + 2
  | .isValidSignalWire | .signalMsgParse => ℓ / 32 + 18
  | .wrapWhisperWire => 2 * (ℓ / 32) + 28
  | .wrapPreKeyWire => 2 * (ℓ / 32) + 88
  | .spqrStateSplit | .spqrStateJoin => 11200
  | .encodeSessionRecord => 24576

/-- Literal payload byte length carried by an `AtomicPureOp` (`0` for non-literal operations). -/
def AtomicPureOp.opSize : AtomicPureOp → ℕ
  | .pbytesLit _ v | .bytesLit _ v => v.length
  | .u8Lit _ | .pbytesCons _ _ | .bytesCons _ _ => 1
  | .pu32Lit _ | .u32Lit _ => 4
  | .u64Lit _ => 8
  | .bv128Lit _ => 16
  | .bv256Lit _ => 32
  | .bv512Lit _ => 64
  | _ => 0

@[reducible] def atomicPureOps (ℓ : ℕ) (Pt : Type := Empty) : Ops (atomicSig ℓ Pt) :=
  ⟨AtomicPureOp, AtomicPureOp.dom ℓ Pt, AtomicPureOp.cod ℓ Pt,
   AtomicPureOp.eval ℓ Pt, AtomicPureOp.cost ℓ, AtomicPureOp.opSize⟩

/-! ## Curve admissibility and point codecs -/

/-- Curve25519 point canonicality checks on `PublicKey` values and serialized `SignalMessage` headers. -/
inductive AtomicCurveCheckOp where
  | decEncCheck | checkRatchetKeyOnCurve
  deriving DecidableEq, Repr

@[reducible] def atomicCurveCheckOps (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) : Ops (atomicSig ℓ Pt) where
  Op := AtomicCurveCheckOp
  dom := fun | .decEncCheck => PK | .checkRatchetKeyOnCurve => B 32
  cod := fun | .decEncCheck | .checkRatchetKeyOnCurve => .bool
  eval := fun
    | .decEncCheck, pk => match decT pk with | some T => decide (encT T = pk) | none => false
    | .checkRatchetKeyOnCurve, body => ratchetKeyAdmissible protoSignalCodec decT encT body
  cost := fun | .decEncCheck => 8 | .checkRatchetKeyOnCurve => ℓ / 32 + 24

/-- Point serialization operation `encT : Pt → PublicKey`. -/
inductive AtomicPtEncOp where | ptEncPk deriving DecidableEq, Repr

@[reducible] def atomicPtEncOps (ℓ : ℕ) {Pt : Type} (encT : Pt → PublicKey) :
    Ops (atomicSig ℓ Pt) where
  Op := AtomicPtEncOp
  dom := fun | .ptEncPk => PtT
  cod := fun | .ptEncPk => PK
  eval := fun | .ptEncPk, Q => encT Q
  cost := fun | .ptEncPk => 4

/-- Point deserialization operation `decT : PublicKey → Option Pt`. -/
inductive AtomicPtDecOp where | ptDecPk deriving DecidableEq, Repr

@[reducible] def atomicPtDecOps (ℓ : ℕ) {Pt : Type} (decT : PublicKey → Option Pt) :
    Ops (atomicSig ℓ Pt) where
  Op := AtomicPtDecOp
  dom := fun | .ptDecPk => PK
  cod := fun | .ptDecPk => .opt PtT
  eval := fun | .ptDecPk, pk => decT pk
  cost := fun | .ptDecPk => 8

/-! ## Cryptographic operations -/

section CryptoHelpers

def spqrMsgPayloadSuffix {P : LibsignalSpqrV1.PolyApi}
    (m : LibsignalSpqrV1.Message P) : Bytes :=
  let tByte := [(LibsignalSpqrV1.MessageType.from_payload m.payload).toU8]
  let body :=
    match m.payload with
    | .hdr c | .ek c | .ekCt1Ack c | .ct1 c | .ct2 c => LibsignalSpqrV1.encode_chunk c []
    | .none | .ct1Ack _ => []
  (tByte ++ body).take 64

def spqrBraidSendEval {ℓ : ℕ} {Pt : Type} (F : ShaCompress) (K : LibsignalSpqrV1.MlKem)
    (v1Raw : Bytes) (coins : BitVec 512) :
    Bool × Option ((B (ℓ := ℓ) (Pt := Pt) 32).denote × BitVec 64 ×
      Option (BitVec 64 × BitVec 256) × (B (ℓ := ℓ) (Pt := Pt) 64).denote) :=
  match LibsignalSpqrV1.V1State.decode v1Raw with
  | .error _ => (false, none)
  | .ok pb =>
    match LibsignalSpqrV1.States.from_pb LibsignalSpqrV1.spqrPolyApi
        (LibsignalSpqrV1.spqrAuthApi F) pb with
    | .error (.panic _) => (true, none)
    | .error (.err _) => (false, none)
    | .ok st0 =>
      match st0.send K (LibsignalSpqrV1.coinBytes coins) with
      | .error (.panic _) => (true, none)
      | .error (.err _) => (false, none)
      | .ok (sOut, _) =>
        let newV1 := (LibsignalSpqrV1.V1State.encodeRaw sOut.state.into_pb).take 64000
        let epSec? := sOut.key.map fun es => (es.epoch, HKDF.bytesToKey32 es.secret)
        (false, some (newV1, (sOut.msg.epoch, (epSec?, spqrMsgPayloadSuffix sOut.msg))))

def spqrBraidRecvEval {ℓ : ℕ} {Pt : Type} (F : ShaCompress) (K : LibsignalSpqrV1.MlKem)
    (v1Raw : Bytes) (msgEpoch : BitVec 64) (remaining : Bytes) :
    Bool × Bool × Option (Option (BitVec 64 × BitVec 256) × (B (ℓ := ℓ) (Pt := Pt) 32).denote) :=
  match LibsignalSpqrV1.Message.deserialize LibsignalSpqrV1.spqrPolyApi msgEpoch remaining with
  | .error e => (false, e.isStateDecode, none)
  | .ok sckaMsg =>
    match LibsignalSpqrV1.V1State.decode v1Raw with
    | .error _ => (false, true, none)
    | .ok pb =>
      match LibsignalSpqrV1.States.from_pb LibsignalSpqrV1.spqrPolyApi
          (LibsignalSpqrV1.spqrAuthApi F) pb with
      | .error (.panic _) => (true, false, none)
      | .error (.err e) => (false, e.isStateDecode, none)
      | .ok st0 =>
        match st0.recv K sckaMsg with
        | .error (.panic _) => (true, false, none)
        | .error (.err e) => (false, e.isStateDecode, none)
        | .ok rOut =>
          let newV1 := (LibsignalSpqrV1.V1State.encodeRaw rOut.state.into_pb).take 64000
          let epSec? := rOut.key.map fun es => (es.epoch, HKDF.bytesToKey32 es.secret)
          (false, false, some (epSec?, newV1))

def spqrNegotiateInitEval {ℓ : ℕ} {Pt : Type} (F : ShaCompress) (K : LibsignalSpqrV1.MlKem)
    (verByte : BitVec 8) (dirI32 : BitVec 32) (authKey : Bytes) :
    Bool × Option (Option (B (ℓ := ℓ) (Pt := Pt) 32).denote) :=
  match LibsignalSpqrV1.Version.fromU8? verByte with
  | none => (true, none)
  | some v =>
    match LibsignalSpqrV1.Direction.fromI32? dirI32 with
    | none => (false, none)
    | some dir =>
      match LibsignalSpqrV1.initInner (LibsignalSpqrV1.spqrDeps F K) v dir authKey with
      | .error _ => (true, none)
      | .ok pb? =>
        (false, some (pb?.map fun pb => (LibsignalSpqrV1.V1State.encodeRaw pb).take 48000))

def spqrChainFromVnEval {ℓ : ℕ} {Pt : Type} (F : ShaCompress)
    (vn : (spqrVnT (ℓ := ℓ) (Pt := Pt)).denote) :
    Option (spqrChainT (ℓ := ℓ) (Pt := Pt)).denote :=
  match LibsignalSpqrV1.chainFromVersionNegotiation
      (LibsignalSpqrV1.spqrHkdfWith F) (spqrVnOfV vn) with
  | .ok c => some (spqrChainToV c.intoPb)
  | .error _ => none

def spqrChainAddEpochEval {ℓ : ℕ} {Pt : Type} (F : ShaCompress)
    (ch : (spqrChainT (ℓ := ℓ) (Pt := Pt)).denote) (ep : BitVec 64) (sec : BitVec 256) :
    Bool × Option (spqrChainT (ℓ := ℓ) (Pt := Pt)).denote :=
  match LibsignalSpqrV1.Chain.fromPb (spqrChainOfV ch) with
  | .error _ => (false, none)
  | .ok c0 =>
    match c0.addEpoch (LibsignalSpqrV1.spqrHkdfWith F) ⟨ep, HMAC.keyToBytes32 sec⟩ with
    | .error _ => (true, none)
    | .ok c1 => (false, some (spqrChainToV c1.intoPb))

def spqrChainNextKeyEval {ℓ : ℕ} {Pt : Type} (F : ShaCompress) (next : Bytes) (ctr : BitVec 32) :
    Bool × Option ((B (ℓ := ℓ) (Pt := Pt) 32).denote × BitVec 32 × BitVec 256) :=
  match LibsignalSpqrV1.ChainEpochDirection.nextKeyInternal
      (LibsignalSpqrV1.spqrHkdfWith F) next ctr with
  | .error _ => (true, none)
  | .ok (next', _, (idx, mkBytes)) =>
    (false, some (next'.take 32, (idx, HKDF.bytesToKey32 mkBytes)))

end CryptoHelpers

/-- Session symmetric, HMAC-SHA256, AES-256, and Curve25519 operations over `C : Crypto`. -/
inductive AtomicSymOp where
  | sessionKeyPairGen | sessionRootCreateChain | chainStep | deriveMsgKeys
  | aes256CbcEnc | aes256CbcDec | signalMsgEncode | signalMsgVerifyMac
  | hmacSha256Op (w : ℕ+) | aes256EncBlock | aes256DecBlock
  deriving DecidableEq, Repr

@[reducible] def AtomicSymOp.dom (ℓ : ℕ) (Pt : Type) : AtomicSymOp → Ty (atomicSig ℓ Pt)
  | .sessionKeyPairGen => BV256
  | .sessionRootCreateChain => .prod BV256 (.prod PK BV256)
  | .chainStep => .prod BV256 U32
  | .deriveMsgKeys => .prod BV256 (.prod U32 (.opt BV256))
  | .aes256CbcEnc => .prod BV256 (.prod BV128 PlainT)
  | .aes256CbcDec => .prod BV256 (.prod BV128 (B 32))
  | .signalMsgEncode =>
    .prod signalHdrT (.prod (B 32) (.prod (B 32)
      (.prod (.opt (B 32)) (.prod IdKey (.prod IdKey BV256)))))
  | .signalMsgVerifyMac => .prod (B 32) (.prod (.opt (B 32)) (.prod IdKey (.prod IdKey BV256)))
  | .hmacSha256Op w => .prod BV256 (B w)
  | .aes256EncBlock | .aes256DecBlock => .prod BV256 BV128

@[reducible] def AtomicSymOp.cod (ℓ : ℕ) (Pt : Type) : AtomicSymOp → Ty (atomicSig ℓ Pt)
  | .sessionKeyPairGen => .prod PK BV256
  | .sessionRootCreateChain => .opt (.prod BV256 BV256)
  | .chainStep => .opt (.prod (.prod BV256 U32) BV256)
  | .deriveMsgKeys => .prod BV256 (.prod BV256 (.prod BV128 U32))
  | .aes256CbcEnc | .signalMsgEncode => B 32
  | .aes256CbcDec => .opt PlainT
  | .signalMsgVerifyMac => .bool
  | .hmacSha256Op _ => BV256
  | .aes256EncBlock | .aes256DecBlock => BV128

def AtomicSymOp.eval (ℓ : ℕ) (Pt : Type) (C : Crypto) :
    (o : AtomicSymOp) → (o.dom ℓ Pt).denote → (o.cod ℓ Pt).denote
  | .sessionKeyPairGen, coins =>
    let kp := KeyPair.generate C coins
    (kp.publicKey, HKDF.bytesToKey32 kp.privateKey.bytes.toList)
  | .sessionRootCreateChain, (rk, (theirPk, ourPriv)) =>
    match LibsignalSession.rootCreateChain C rk theirPk ⟨Ratchet.keyToBytesVec32 ourPriv⟩ with
    | .ok (rk', ck) => some (rk', ck.key)
    | .error _ => none
  | .chainStep, (ck, idx) =>
    let ckObj : LibsignalSession.ChainKey := { key := ck, index := idx }
    match LibsignalSession.ChainKey.nextChainKey C.F ckObj with
    | .ok ckNext =>
      let mkGen := LibsignalSession.ChainKey.messageKeys C.F ckObj
      some ((ckNext.key, ckNext.index), HKDF.bytesToKey32 mkGen.seed)
    | .error _ => none
  | .deriveMsgKeys, (seed, (ctr, salt?)) =>
    let saltVec? : HKDF.Salt := salt?.map Ratchet.keyToBytesVec32
    let mks := MessageKeyGenerator.generateKeys C.F ⟨HMAC.keyToBytes32 seed, ctr⟩ saltVec?
    (mks.cipherKey, (mks.macKey, (mks.iv, mks.counter)))
  | .aes256CbcEnc, (k, (iv, pt)) => (aesCbcEncrypt C.E k iv pt.toList).take (32 * (ℓ / 32 + 2))
  | .aes256CbcDec, (k, (iv, ct)) => (aesCbcDecrypt C.D k iv ct).map (Ratchet.padOrTruncatePlain ℓ)
  | .signalMsgEncode,
      ((msgVer, (senderRk, (ctr, prevCtr))), (ct, (pqMsg, (addr?, (idS, (idR, macKey)))))) =>
    (SignalMessage.new C.F protoSignalCodec msgVer macKey addr? senderRk ctr prevCtr ct
      idS idR pqMsg).serialized.take (32 * (2 * (ℓ / 32) + 24))
  | .signalMsgVerifyMac, (body, (expectedAddr?, (idS, (idR, macKey)))) =>
    match SignalMessage.tryFrom protoSignalCodec body with
    | .ok m => m.verifyMacWithAddresses C.F expectedAddr? idS idR macKey
    | .error _ => false
  | .hmacSha256Op _, (k, msg) => HKDF.bytesToKey32 (HMAC.hmacWith C.F (HMAC.keyToBytes32 k) msg)
  | .aes256EncBlock, (k, blk) => C.E k blk
  | .aes256DecBlock, (k, blk) => C.D k blk

def AtomicSymOp.cost (ℓ : ℕ) : AtomicSymOp → ℕ
  | .sessionKeyPairGen | .chainStep => 8
  | .sessionRootCreateChain => 16
  | .deriveMsgKeys => 12
  | .aes256CbcEnc => 2 * (ℓ / 16 + 2) + 4
  | .aes256CbcDec => 2 * (ℓ / 16 + 2) + (ℓ / 32 + 6)
  | .signalMsgEncode => 4 * (ℓ / 32 + 12) + 204
  | .signalMsgVerifyMac => 2 * (ℓ / 32 + 12) + 8
  | .hmacSha256Op w => 2 * (((w : ℕ) + 63) / 64) + 8
  | .aes256EncBlock | .aes256DecBlock => 2

@[reducible] def atomicSymOps (ℓ : ℕ) (Pt : Type) (C : Crypto) : Ops (atomicSig ℓ Pt) :=
  ⟨AtomicSymOp, AtomicSymOp.dom ℓ Pt, AtomicSymOp.cod ℓ Pt,
   AtomicSymOp.eval ℓ Pt C, AtomicSymOp.cost ℓ, fun _ => 0⟩

/-- Abstract group and root-chain KDF operations over `Dh : DHFun (BitVec 256) Pt`. -/
inductive AtomicGroupOp where
  | ptBase | ptLam | ptDh | ptIsZero | ptEq | ptEncBytes | extractPrfTag | rootExpandPrg
  deriving DecidableEq, Repr

@[reducible] def AtomicGroupOp.dom (ℓ : ℕ) (Pt : Type) : AtomicGroupOp → Ty (atomicSig ℓ Pt)
  | .ptBase | .ptLam => .unit
  | .ptDh | .extractPrfTag => .prod BV256 PtT
  | .ptIsZero | .ptEncBytes => PtT
  | .ptEq => .prod PtT PtT
  | .rootExpandPrg => BV256

@[reducible] def AtomicGroupOp.cod (ℓ : ℕ) (Pt : Type) : AtomicGroupOp → Ty (atomicSig ℓ Pt)
  | .ptBase | .ptLam | .ptDh => PtT
  | .ptIsZero | .ptEq => .bool
  | .ptEncBytes => B 32
  | .extractPrfTag => BV256
  | .rootExpandPrg => .prod BV256 BV256

def AtomicGroupOp.eval (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (lam : Pt) :
    (o : AtomicGroupOp) → (o.dom ℓ Pt).denote → (o.cod ℓ Pt).denote
  | .ptBase, _ => Dh.base
  | .ptLam, _ => lam
  | .ptDh, (x, Q) => Dh.dh x Q
  | .ptIsZero, Q => decide (Q = 0)
  | .ptEq, (Q₁, Q₂) => decide (Q₁ = Q₂)
  | .ptEncBytes, Q => (encPt Q).take 32
  | .extractPrfTag, (rk, Q) => (Ratchet.extractPRF C.F encPt).tag rk Q
  | .rootExpandPrg, prk => (Ratchet.expandPRG C.F).gen prk

def AtomicGroupOp.cost : AtomicGroupOp → ℕ
  | .ptBase | .ptLam | .ptIsZero => 1
  | .ptEq => 2
  | .ptEncBytes => 4
  | .ptDh | .extractPrfTag => 8
  | .rootExpandPrg => 12

@[reducible] def atomicGroupOps (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (lam : Pt := 0) :
    Ops (atomicSig ℓ Pt) :=
  ⟨AtomicGroupOp, AtomicGroupOp.dom ℓ Pt, AtomicGroupOp.cod ℓ Pt,
   AtomicGroupOp.eval ℓ Pt C Dh encPt lam, AtomicGroupOp.cost, fun _ => 0⟩

/-- Single-step SPQR V1 transition and five-part ML-KEM-768 operations over `(C, K)`. -/
inductive AtomicSpqrKemOp where
  | spqrV1InitOp | spqrNegotiateInit | spqrBraidSend | spqrBraidRecv
  | spqrChainFromVn | spqrChainAddEpoch | spqrChainNextKey
  | kem768FromSeed | kem768Encaps1 | kem768Encaps2 | kem768Decaps | kem768ValidPk
  deriving DecidableEq, Repr

@[reducible] def AtomicSpqrKemOp.dom (ℓ : ℕ) (Pt : Type) : AtomicSpqrKemOp → Ty (atomicSig ℓ Pt)
  | .spqrV1InitOp => .prod .bool BV256
  | .spqrNegotiateInit => .prod U8 (.prod U32 (B 32))
  | .spqrBraidSend => .prod (B 32) BV512
  | .spqrBraidRecv => .prod (B 32) (.prod U64 (B 32))
  | .spqrChainFromVn => spqrVnT
  | .spqrChainAddEpoch => .prod spqrChainT (.prod U64 BV256)
  | .spqrChainNextKey => .prod (B 32) U32
  | .kem768FromSeed => BV512
  | .kem768Encaps1 => .prod (B 64) BV256
  | .kem768Encaps2 => .prod (B 2080) (B 1152)
  | .kem768Decaps => .prod (B 2400) (.prod (B 960) (B 128))
  | .kem768ValidPk => .prod (B 64) (B 1152)

@[reducible] def AtomicSpqrKemOp.cod (ℓ : ℕ) (Pt : Type) : AtomicSpqrKemOp → Ty (atomicSig ℓ Pt)
  | .spqrV1InitOp => B 32
  | .spqrNegotiateInit => .prod .bool (.opt (.opt (B 32)))
  | .spqrBraidSend =>
    .prod .bool (.opt (.prod (B 32) (.prod U64 (.prod (.opt (.prod U64 BV256)) (B 64)))))
  | .spqrBraidRecv =>
    .prod .bool (.prod .bool (.opt (.prod (.opt (.prod U64 BV256)) (B 32))))
  | .spqrChainFromVn => .opt spqrChainT
  | .spqrChainAddEpoch => .prod .bool (.opt spqrChainT)
  | .spqrChainNextKey => .prod .bool (.opt (.prod (B 32) (.prod U32 BV256)))
  | .kem768FromSeed => .prod (B 64) (.prod (B 1152) (B 2400))
  | .kem768Encaps1 => .opt (.prod (B 960) (.prod (B 2080) BV256))
  | .kem768Encaps2 => .opt (B 128)
  | .kem768Decaps => .opt BV256
  | .kem768ValidPk => .bool

def AtomicSpqrKemOp.eval (ℓ : ℕ) (Pt : Type) (C : Crypto) (K : LibsignalSpqrV1.MlKem) :
    (o : AtomicSpqrKemOp) → (o.dom ℓ Pt).denote → (o.cod ℓ Pt).denote
  | .spqrV1InitOp, (isAlice, pqrKey) =>
    (LibsignalSpqrV1.spqrV1Init C.F K (if isAlice then .a2b else .b2a) pqrKey).take 512
  | .spqrNegotiateInit, (verByte, (dirI32, authKey)) =>
    spqrNegotiateInitEval C.F K verByte dirI32 authKey
  | .spqrBraidSend, (v1Raw, coins) => spqrBraidSendEval C.F K v1Raw coins
  | .spqrBraidRecv, (v1Raw, (msgEpoch, rem)) => spqrBraidRecvEval C.F K v1Raw msgEpoch rem
  | .spqrChainFromVn, vn => spqrChainFromVnEval C.F vn
  | .spqrChainAddEpoch, (ch, (ep, sec)) => spqrChainAddEpochEval C.F ch ep sec
  | .spqrChainNextKey, (next, ctr) => spqrChainNextKeyEval C.F next ctr
  | .kem768FromSeed, seed =>
    let (hdr, ek, dk) := K.fromSeed ⟨LibsignalSpqrV1.coinBytes seed, LibsignalSpqrV1.coinBytes_length seed⟩
    (hdr.toList, (ek.toList, dk.toList))
  | .kem768Encaps1, (hdr, rand) =>
    (K.encaps1 hdr (Ratchet.keyToBytesVec32 rand)).map fun (ct1, es, ss) =>
      (ct1.toList, (es.toList, HKDF.bytesToKey32 ss.toList))
  | .kem768Encaps2, (es, ek) =>
    if hes : es.length = 2080 then
      if hek : ek.length = 1152 then some (K.encaps2 ⟨es, hes⟩ ⟨ek, hek⟩).toList else none
    else none
  | .kem768Decaps, (dk, (ct1, ct2)) =>
    if hdk : dk.length = 2400 then
      if h1 : ct1.length = 960 then
        if h2 : ct2.length = 128 then
          some (HKDF.bytesToKey32 (K.decaps ⟨dk, hdk⟩ ⟨ct1, h1⟩ ⟨ct2, h2⟩).toList)
        else none
      else none
    else none
  | .kem768ValidPk, (hdr, ek) => K.validPkBytes hdr ek

def AtomicSpqrKemOp.cost : AtomicSpqrKemOp → ℕ
  | .spqrV1InitOp => 210
  | .spqrNegotiateInit => 1600
  | .spqrBraidSend | .spqrBraidRecv => 3072
  | .spqrChainFromVn => 16
  | .spqrChainAddEpoch => 24
  | .spqrChainNextKey => 12
  | .kem768FromSeed | .kem768Encaps1 | .kem768Decaps => 160
  | .kem768Encaps2 => 80
  | .kem768ValidPk => 40

@[reducible] def atomicSpqrKemOps (ℓ : ℕ) (Pt : Type) (C : Crypto) (K : LibsignalSpqrV1.MlKem) :
    Ops (atomicSig ℓ Pt) :=
  ⟨AtomicSpqrKemOp, AtomicSpqrKemOp.dom ℓ Pt, AtomicSpqrKemOp.cod ℓ Pt,
   AtomicSpqrKemOp.eval ℓ Pt C K, AtomicSpqrKemOp.cost, fun _ => 0⟩

/-- PQXDH handshake primitive operations over `P : SignalPqxdh.Primitives`. -/
inductive AtomicPqxdhOp where
  | x25519 | x25519Base | pow8 | isCanonical
  | sigPkGen | sigSign | sigVerify
  | kemKeyGen | kemEncaps | kemDecaps | hkdfDerive96
  deriving DecidableEq, Repr

@[reducible] def AtomicPqxdhOp.dom (ℓ : ℕ) (Pt : Type) : AtomicPqxdhOp → Ty (atomicSig ℓ Pt)
  | .x25519 => .prod (PB 32) (PB 32)
  | .x25519Base | .pow8 | .isCanonical | .sigPkGen => PB 32
  | .sigSign | .sigVerify => .prod (PB 32) (.prod (PB 1569) (PB 64))
  | .kemKeyGen => PB 64
  | .kemEncaps => .prod (PB 1568) (PB 32)
  | .kemDecaps => .prod (PB 3168) (PB 1568)
  | .hkdfDerive96 => PB 192

@[reducible] def AtomicPqxdhOp.cod (ℓ : ℕ) (Pt : Type) : AtomicPqxdhOp → Ty (atomicSig ℓ Pt)
  | .x25519 | .x25519Base | .pow8 | .sigPkGen => PB 32
  | .isCanonical | .sigVerify => .bool
  | .sigSign => PB 64
  | .kemKeyGen => .prod (PB 1568) (PB 3168)
  | .kemEncaps => .opt (.prod (PB 32) (PB 1568))
  | .kemDecaps => .opt (PB 32)
  | .hkdfDerive96 => drKeyT

def AtomicPqxdhOp.eval (ℓ : ℕ) (Pt : Type) (P : SignalPqxdh.Primitives) :
    (o : AtomicPqxdhOp) → (o.dom ℓ Pt).denote → (o.cod ℓ Pt).denote
  | .x25519, (sk, pk) => (P.x25519 sk pk).take 32
  | .x25519Base, sk => (P.x25519Base sk).take 32
  | .pow8, pk => (P.pow8 pk).take 32
  | .isCanonical, pk => P.isCanonical pk
  | .sigPkGen, sk => (P.sigPkGen sk).take 32
  | .sigSign, (sk, (msg, rnd)) => (P.sigSign sk msg rnd).take 64
  | .sigVerify, (pk, (msg, sig)) => P.sigVerify pk msg sig
  | .kemKeyGen, seed => let (pk, sk) := P.kemKeyGen seed; (pk.take 1568, sk.take 3168)
  | .kemEncaps, (pk, coins) =>
    (P.kemEncaps pk coins).map fun (ss, ct) => (ss.take 32, ct.take 1568)
  | .kemDecaps, (sk, ct) => (P.kemDecaps sk ct).map (·.take 32)
  | .hkdfDerive96, ikm =>
    let dk := P.hkdfDerive96 ikm
    (dk.rootKey.take 32, (dk.chainKey.take 32, dk.pqrKey.take 32))

def AtomicPqxdhOp.cost : AtomicPqxdhOp → ℕ
  | .x25519 | .x25519Base | .pow8 | .sigPkGen => 8
  | .isCanonical => 2
  | .sigSign | .sigVerify => 60
  | .kemKeyGen | .kemEncaps | .kemDecaps => 160
  | .hkdfDerive96 => 16

@[reducible] def atomicPqxdhOps (ℓ : ℕ) (Pt : Type) (P : SignalPqxdh.Primitives) :
    Ops (atomicSig ℓ Pt) :=
  ⟨AtomicPqxdhOp, AtomicPqxdhOp.dom ℓ Pt, AtomicPqxdhOp.cod ℓ Pt,
   AtomicPqxdhOp.eval ℓ Pt P, AtomicPqxdhOp.cost, fun _ => 0⟩

/-! ## Composed operation tables -/

/-- Wire and state adapter operation table: pure operations plus curve canonicality checks. -/
@[reducible] def atomicAdapterOps (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) : Ops (atomicSig ℓ Pt) :=
  Ops.sum (atomicPureOps ℓ Pt) (atomicCurveCheckOps ℓ decT encT)

/-- Operation table for FS-AEAD and symmetric chain-slot reductions. -/
@[reducible] def atomicFsOps (ℓ : ℕ) (Pt : Type) (C : Crypto) (encT : Pt → PublicKey) :
    Ops (atomicSig ℓ Pt) :=
  Ops.sum (atomicPureOps ℓ Pt) (Ops.sum (atomicPtEncOps ℓ encT) (atomicSymOps ℓ Pt C))

/-- Operation table for ACD19 continuous-key-agreement and Double Ratchet reductions. -/
@[reducible] def atomicFig8Ops (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt := 0) : Ops (atomicSig ℓ Pt) :=
  Ops.sum (atomicFsOps ℓ Pt C encT) (atomicGroupOps ℓ Pt C Dh encPt lam)

/-- Single-session operation table with point deserialization, curve checks, and SPQR/ML-KEM-768
operations. -/
@[reducible] def atomicSessionOps (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt := 0) : Ops (atomicSig ℓ Pt) :=
  Ops.sum (Ops.sum (atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (Ops.sum (atomicPtDecOps ℓ decT) (atomicCurveCheckOps ℓ decT encT)))
    (atomicSpqrKemOps ℓ Pt C K)

/-- Multi-session end-to-end composition operation table with PQXDH handshake primitives. -/
@[reducible] def atomicE2EOps (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : LibsignalSpqrV1.MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Ops (atomicSig ℓ Pt) :=
  Ops.sum (atomicAdapterOps ℓ decT encT)
    (Ops.sum (Ops.sum (atomicPtEncOps ℓ encT) (atomicPtDecOps ℓ decT))
      (Ops.sum (atomicSymOps ℓ Pt C)
        (Ops.sum (atomicSpqrKemOps ℓ Pt C K) (atomicPqxdhOps ℓ Pt P))))

end ReductionDsl
