/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Witness
import all Init.Data.Repr
import all Init.Data.String.Defs

/-!
# Concrete 3-Call CLI Model Steps for Handshake Non-Vacuity

Evaluates the 3-call CLI execution (`init` on Alice, `send` on Alice, `recv` on Bob) against
`CliSpecPqxdh` for every `X : UnreachedPqxdhPrimitives` and both `withOpk = false` and
`withOpk = true`, together with `PqxdhPartyInSpecDomain` well-formedness witnesses.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.HandshakeModel

set_option maxRecDepth 200000

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (setupPublic pubBytes)
open CryptoGames.LibsignalSession (GhostState SignalMessage)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.RecordCodecs
  (IdentityKeyPairStructure SignedPreKeyRecordStructure PreKeyRecordStructure)
open CryptoVerification.E2E
  (UnreachedPqxdhPrimitives PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras
   initiateTapeLen initiateState recvPrekeyState ReachablePqxdhSession
   keyPairOf djbKey wirePrekey wireWhisper encodeRecordUnderExtras pqxdhSessionParams
   modelPrims blockLevelPrims)
open CryptoVerification.SignalSession
  (PqParty pqInitModel pqSendModel pqRecvPrekeyModel
   preKeysNamedBy markKyberUsed removeOpk encodeDir PqxdhPartyInSpecDomain
   signedRecordBytes kyberRecordBytes oneTimeRecordBytes baseKeysBytes
   sessionFile partyAddress le32)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myParams myInterp freshBytes pt0 myKyberPubBytes myKyberSecField
   mkRecords mkRecords_wf)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers (nvX)
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)

def tsEk (withOpk : Bool) : Nat := if withOpk then 26 else 22

def tsEnt (withOpk : Bool) : Nat := if withOpk then 27 else 23

def tsDhsA (withOpk : Bool) : Nat := if withOpk then 28 else 24

def tsM0 (withOpk : Bool) : Nat := if withOpk then 35 else 31

def tsC0 (withOpk : Bool) : Nat := if withOpk then 36 else 32

def tsDhsB (withOpk : Bool) : Nat := if withOpk then 42 else 38

def entByte (withOpk : Bool) : BitVec 8 := BitVec.ofNat 8 (tsEnt withOpk + 1)

/-- 192-byte `init` random tape: `ek (32B) ++ replicate 128 entByte ++ dhsA (32B)`. -/
def tapeInitBytes (withOpk : Bool) : HwBytes :=
  freshBytes (tsEk withOpk) 32 ++
  List.replicate 128 (entByte withOpk) ++
  freshBytes (tsDhsA withOpk) 32

def tapeInit (withOpk : Bool) : List.Vector (BitVec 8) initiateTapeLen :=
  if withOpk then ⟨tapeInitBytes true, rfl⟩ else ⟨tapeInitBytes false, rfl⟩

/-- 64-byte `send` coins (`0x31 = 49 ≤ 96`, disjoint from `'m' = 109`). -/
def cSend0 : HwBytes := List.replicate 64 0x31#8
def cSend0Vec : List.Vector (BitVec 8) 64 := ⟨cSend0, rfl⟩

def rcBytes (withOpk : Bool) : HwBytes := freshBytes (tsDhsB withOpk) 32
def rcVal (withOpk : Bool) : BitVec 256 := CryptoGames.HKDF.bytesToKey32 (rcBytes withOpk)

theorem keyToBytes32_rcVal (withOpk : Bool) :
    CryptoGames.HMAC.keyToBytes32 (rcVal withOpk) = rcBytes withOpk := by
  cases withOpk <;> decide

/-! ## Universal `UnreachedPqxdhPrimitives` Independence -/

theorem pqInitModel_congr_extras (X Y : UnreachedPqxdhPrimitives) (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    pqInitModel X W st b t = pqInitModel Y W st b t := by
  unfold pqInitModel initiateState SignalPqxdh.Model.initiateKeys modelPrims
    SignalPqxdh.xeddsaVerifyRef SignalPqxdh.isCanonicalRef SignalPqxdh.hkdfDerive96Ref
    SignalPqxdh.sha512Ref blockLevelPrims
  rfl

theorem pqRecvPrekeyModel_congr_extras (X Y : UnreachedPqxdhPrimitives) (W : PEParams) (st : PqParty)
    (m : PreKeyMessageFields) (rc : BitVec 256) :
    pqRecvPrekeyModel X W st m rc = pqRecvPrekeyModel Y W st m rc := by
  unfold pqRecvPrekeyModel recvPrekeyState SignalPqxdh.Model.acceptKeys modelPrims
    SignalPqxdh.isCanonicalRef SignalPqxdh.hkdfDerive96Ref blockLevelPrims
  rfl

/-! ## Computable Initial States and Bundle (`stA0_cli`, `stB0_cli`, `bE_cli`) -/

def idPubA_vec : List.Vector (BitVec 8) 32 :=
  ⟨[11#8] ++ List.replicate 24 1#8 ++ List.replicate 7 0#8, rfl⟩

def idPubB_vec : List.Vector (BitVec 8) 32 :=
  ⟨[11#8] ++ List.replicate 24 6#8 ++ List.replicate 7 0#8, rfl⟩

def spkPubB_vec : List.Vector (BitVec 8) 32 :=
  ⟨[19#8] ++ List.replicate 24 11#8 ++ List.replicate 7 0#8, rfl⟩

def opkPubB_vec : List.Vector (BitVec 8) 32 :=
  ⟨[27#8] ++ List.replicate 24 23#8 ++ List.replicate 7 0#8, rfl⟩

def basePubA_vec (withOpk : Bool) : List.Vector (BitVec 8) 32 :=
  if withOpk then ⟨[35#8] ++ List.replicate 24 27#8 ++ List.replicate 7 0#8, rfl⟩
  else ⟨[27#8] ++ List.replicate 24 23#8 ++ List.replicate 7 0#8, rfl⟩

def ephPubA_vec (withOpk : Bool) : List.Vector (BitVec 8) 32 :=
  if withOpk then ⟨[35#8] ++ List.replicate 24 29#8 ++ List.replicate 7 0#8, rfl⟩
  else ⟨[35#8] ++ List.replicate 24 25#8 ++ List.replicate 7 0#8, rfl⟩

def ephPrivA_vec (withOpk : Bool) : List.Vector (BitVec 8) 32 :=
  if withOpk then ⟨[24#8] ++ List.replicate 30 29#8 ++ [93#8], rfl⟩
  else ⟨[24#8] ++ List.replicate 30 25#8 ++ [89#8], rfl⟩

def ephPubB_vec (withOpk : Bool) : List.Vector (BitVec 8) 32 :=
  if withOpk then ⟨[51#8] ++ List.replicate 24 43#8 ++ List.replicate 7 0#8, rfl⟩
  else ⟨[43#8] ++ List.replicate 24 39#8 ++ List.replicate 7 0#8, rfl⟩

def ephPrivB_vec (withOpk : Bool) : List.Vector (BitVec 8) 32 :=
  if withOpk then ⟨[40#8] ++ List.replicate 30 43#8 ++ [107#8], rfl⟩
  else ⟨[32#8] ++ List.replicate 30 39#8 ++ [103#8], rfl⟩

def myKyberPub1568 : List.Vector (BitVec 8) 1568 :=
  bytesToVec 1568 myKyberPubBytes

def myKyberSec3168 : List.Vector (BitVec 8) 3168 :=
  bytesToVec 3168 (myKyberSecField.drop 1)

def stA0_cli (_withOpk : Bool) : PqParty where
  party := .A
  me := ⟨bytesToVec 32 (List.replicate 32 1#8), 10#32⟩
  peerId := some ⟨⟨idPubB_vec⟩⟩
  session := none
  signed := []
  oneTime := []
  kyberOneTime := []
  kyberLastResort := []

def stB0_cli (withOpk : Bool) : PqParty where
  party := .B
  me := ⟨bytesToVec 32 (List.replicate 32 6#8), 20#32⟩
  peerId := some ⟨⟨idPubA_vec⟩⟩
  session := none
  signed := [(1#32, ⟨bytesToVec 32 (List.replicate 32 11#8), List.Vector.replicate 64 0#8, 0⟩)]
  oneTime :=
    if withOpk then [(3#32, some (bytesToVec 32 (List.replicate 32 23#8)))]
    else []
  kyberOneTime := []
  kyberLastResort :=
    [(2#32, ⟨myKyberPub1568, myKyberSec3168, List.Vector.replicate 64 0#8, 0⟩, [])]

def bE_cli (withOpk : Bool) : PreKeyBundleFields where
  regId := 20#32
  spkId := 1#32
  spkPub := spkPubB_vec
  spkSig := List.Vector.replicate 64 0#8
  kpkId := 2#32
  kpkPub := myKyberPub1568
  kpkSig := List.Vector.replicate 64 0#8
  idPub := idPubB_vec
  opk := if withOpk then some (3#32, opkPubB_vec) else none

theorem bytesToVec_toList_of_len {n : Nat} {bs : HwBytes} (hlen : bs.length = n) :
    (bytesToVec n bs).toList = bs :=
  List.take_left' hlen

theorem mkRecords_opaque5 (withOpk : Bool) :
    (mkRecords withOpk).opaqueBytes (setupPublic (mkRecords withOpk) 5) =
      List.replicate 64 0#8 := by
  have h5 := (mkRecords_wf withOpk).2.2.2.1
  dsimp only [mkRecords, DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm] at h5 ⊢
  split_ifs at h5 ⊢
  · rw [myKyberPubBytes, List.length_replicate] at h5; cases h5
  · rfl

theorem mkRecords_opaque7 (withOpk : Bool) :
    (mkRecords withOpk).opaqueBytes (setupPublic (mkRecords withOpk) 7) =
      List.replicate 64 0#8 := by
  have h7 := (mkRecords_wf withOpk).2.2.2.2.2.1
  dsimp only [mkRecords, DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm] at h7 ⊢
  split_ifs at h7 ⊢
  · rw [myKyberPubBytes, List.length_replicate] at h7; cases h7
  · rfl

theorem keyPair_idA :
    (keyPairOf myParams.C (bytesToVec 32 (List.replicate 32 1#8))).publicKey.bytes = idPubA_vec :=
  Subtype.ext (by decide)

theorem keyPair_idB :
    (keyPairOf myParams.C (bytesToVec 32 (List.replicate 32 6#8))).publicKey.bytes = idPubB_vec :=
  Subtype.ext (by decide)

theorem keyPair_spkB :
    (keyPairOf myParams.C (bytesToVec 32 (List.replicate 32 11#8))).publicKey.bytes = spkPubB_vec :=
  Subtype.ext (by decide)

theorem keyPair_opkB :
    (keyPairOf myParams.C (bytesToVec 32 (List.replicate 32 23#8))).publicKey.bytes = opkPubB_vec :=
  Subtype.ext (by decide)

theorem pubBytes_idA :
    pubBytes myInterp (List.replicate 32 1#8) = idPubA_vec.toList := by decide

theorem pubBytes_idB :
    pubBytes myInterp (List.replicate 32 6#8) = idPubB_vec.toList := by decide

theorem pubBytes_spkB :
    pubBytes myInterp (List.replicate 32 11#8) = spkPubB_vec.toList := by decide

theorem pubBytes_opkB :
    pubBytes myInterp (List.replicate 32 23#8) = opkPubB_vec.toList := by decide

/-! ## Closed-Form Evaluation of the 3 CLI Calls -/

def kyberWithTag0 (withOpk : Bool) : HwBytes :=
  if withOpk then
    [0x08#8, 0xa1#8] ++ List.replicate 32 0x1c#8 ++ List.replicate 32 0x77#8 ++
      List.replicate 1503 0x00#8
  else
    [0x08#8, 0xa1#8] ++ List.replicate 32 0x18#8 ++ List.replicate 32 0x77#8 ++
      List.replicate 1503 0x00#8

def kyberCt0_vec (withOpk : Bool) : List.Vector (BitVec 8) 1568 :=
  bytesToVec 1568 ((kyberWithTag0 withOpk).drop 1)

def x_A (withOpk : Bool) : RecordExtras :=
  { pending := ⟨if withOpk then some 3#32 else none, 1#32, ⟨basePubA_vec withOpk⟩, 0#64⟩
    kyber := some ⟨2#32, kyberWithTag0 withOpk⟩
    remoteRegistrationId := 20#32
    localRegistrationId := 10#32
    aliceBaseKey := [5#8] ++ (basePubA_vec withOpk).1 }

def x_B (withOpk : Bool) : RecordExtras :=
  { pending := ⟨none, 0#32, ⟨basePubA_vec withOpk⟩, 0#64⟩
    kyber := none
    remoteRegistrationId := 10#32
    localRegistrationId := 20#32
    aliceBaseKey := [5#8] ++ (basePubA_vec withOpk).1 }

def pqA0 (withOpk : Bool) : HwBytes :=
  if withOpk then
    [0x0a#8, 0x26#8, 0x0a#8, 0x20#8, 0x3e#8, 0x83#8, 0x22#8, 0x05#8, 0x43#8, 0x26#8, 0xe8#8,
     0xab#8, 0x9d#8, 0x37#8, 0x0e#8, 0x9c#8, 0x70#8, 0x44#8, 0x25#8, 0x8b#8, 0x68#8, 0xad#8,
     0xec#8, 0x54#8, 0xb1#8, 0xf5#8, 0xe1#8, 0x2f#8, 0x04#8, 0xa6#8, 0x07#8, 0x79#8, 0x16#8,
     0x20#8, 0x54#8, 0x31#8, 0x18#8, 0x01#8, 0x22#8, 0x00#8, 0x1a#8, 0x4c#8, 0x0a#8, 0x4a#8,
     0x0a#8, 0x48#8, 0x08#8, 0x01#8, 0x12#8, 0x44#8, 0x0a#8, 0x20#8, 0xd2#8, 0x33#8, 0xbd#8,
     0x3a#8, 0xb1#8, 0x3b#8, 0x04#8, 0xce#8, 0x2e#8, 0x1b#8, 0xc2#8, 0x5b#8, 0x6b#8, 0x92#8,
     0x8d#8, 0x2d#8, 0xd6#8, 0x88#8, 0xfc#8, 0x7a#8, 0xd7#8, 0x0f#8, 0x8d#8, 0x98#8, 0x9b#8,
     0xaa#8, 0x5b#8, 0xf3#8, 0x73#8, 0x75#8, 0xcc#8, 0x69#8, 0x12#8, 0x20#8, 0x56#8, 0x8f#8,
     0x27#8, 0x48#8, 0x90#8, 0xf9#8, 0x9a#8, 0x65#8, 0x2a#8, 0x69#8, 0x6f#8, 0x89#8, 0x68#8,
     0x36#8, 0x44#8, 0x52#8, 0xb3#8, 0xe7#8, 0x7c#8, 0x1c#8, 0x92#8, 0x8e#8, 0x39#8, 0x13#8,
     0x95#8, 0xd7#8, 0x1a#8, 0x9e#8, 0x13#8, 0xad#8, 0x44#8, 0xfb#8]
  else
    [0x0a#8, 0x26#8, 0x0a#8, 0x20#8, 0xc8#8, 0xe2#8, 0x05#8, 0xf1#8, 0xb7#8, 0x18#8, 0xa1#8,
     0x3c#8, 0x05#8, 0x42#8, 0xaf#8, 0x92#8, 0xd0#8, 0x82#8, 0x47#8, 0x7a#8, 0x6f#8, 0xeb#8,
     0x3f#8, 0xb3#8, 0x9c#8, 0x36#8, 0xbf#8, 0xe0#8, 0xe0#8, 0x37#8, 0xaa#8, 0xd0#8, 0xda#8,
     0x49#8, 0x21#8, 0xd6#8, 0x18#8, 0x01#8, 0x22#8, 0x00#8, 0x1a#8, 0x4c#8, 0x0a#8, 0x4a#8,
     0x0a#8, 0x48#8, 0x08#8, 0x01#8, 0x12#8, 0x44#8, 0x0a#8, 0x20#8, 0x54#8, 0x17#8, 0x6c#8,
     0x1b#8, 0xed#8, 0x90#8, 0xd8#8, 0x18#8, 0x3c#8, 0x8e#8, 0xd8#8, 0x07#8, 0x52#8, 0xfa#8,
     0x07#8, 0x3f#8, 0xe0#8, 0xcf#8, 0x2b#8, 0xd1#8, 0x1d#8, 0x4e#8, 0xac#8, 0x2b#8, 0x9c#8,
     0x19#8, 0x92#8, 0x33#8, 0xaf#8, 0x5d#8, 0x0b#8, 0xdc#8, 0x12#8, 0x20#8, 0xcb#8, 0x88#8,
     0x72#8, 0x7d#8, 0x45#8, 0xaf#8, 0x8d#8, 0x32#8, 0x27#8, 0x90#8, 0xe7#8, 0xfe#8, 0x31#8,
     0x90#8, 0xb5#8, 0xcd#8, 0x2f#8, 0xf2#8, 0x49#8, 0xc2#8, 0x49#8, 0x72#8, 0x88#8, 0x15#8,
     0xcb#8, 0x66#8, 0x14#8, 0xa3#8, 0x6c#8, 0x7f#8, 0xd8#8, 0xca#8]

def pqA1 (withOpk : Bool) : HwBytes :=
  if withOpk then
    [0x0a#8, 0x26#8, 0x0a#8, 0x20#8, 0x3e#8, 0x83#8, 0x22#8, 0x05#8, 0x43#8, 0x26#8, 0xe8#8,
     0xab#8, 0x9d#8, 0x37#8, 0x0e#8, 0x9c#8, 0x70#8, 0x44#8, 0x25#8, 0x8b#8, 0x68#8, 0xad#8,
     0xec#8, 0x54#8, 0xb1#8, 0xf5#8, 0xe1#8, 0x2f#8, 0x04#8, 0xa6#8, 0x07#8, 0x79#8, 0x16#8,
     0x20#8, 0x54#8, 0x31#8, 0x18#8, 0x01#8, 0x22#8, 0x00#8, 0x12#8, 0x70#8, 0x1a#8, 0x4a#8,
     0x0a#8, 0x24#8, 0x08#8, 0x01#8, 0x12#8, 0x20#8, 0xca#8, 0xf0#8, 0x12#8, 0xf8#8, 0xc4#8,
     0x50#8, 0xf3#8, 0xcb#8, 0x38#8, 0xba#8, 0xd9#8, 0xd4#8, 0xb1#8, 0xcc#8, 0x47#8, 0x27#8,
     0x18#8, 0x1f#8, 0x4e#8, 0x49#8, 0x22#8, 0x9a#8, 0x87#8, 0x3a#8, 0xe5#8, 0x12#8, 0x74#8,
     0x91#8, 0xcb#8, 0x36#8, 0xe2#8, 0x47#8, 0x12#8, 0x22#8, 0x12#8, 0x20#8, 0x3f#8, 0xde#8,
     0x84#8, 0x74#8, 0x7b#8, 0x6d#8, 0x41#8, 0x9b#8, 0x20#8, 0x09#8, 0x8d#8, 0xe8#8, 0x6b#8,
     0xd1#8, 0x02#8, 0x1e#8, 0x70#8, 0x3a#8, 0xc2#8, 0x65#8, 0x52#8, 0xe7#8, 0x28#8, 0x0b#8,
     0xf4#8, 0x4d#8, 0xed#8, 0xf9#8, 0x10#8, 0x38#8, 0xdd#8, 0x39#8, 0x22#8, 0x20#8, 0xe2#8,
     0xd6#8, 0x55#8, 0xd3#8, 0xcc#8, 0xc1#8, 0xa1#8, 0x00#8, 0xc3#8, 0x12#8, 0x57#8, 0x55#8,
     0x3d#8, 0x96#8, 0x6f#8, 0xcd#8, 0x8e#8, 0x7a#8, 0xad#8, 0xaf#8, 0x63#8, 0x4c#8, 0x1f#8,
     0x59#8, 0x2f#8, 0x94#8, 0xc7#8, 0x79#8, 0x8d#8, 0xf5#8, 0x34#8, 0xa2#8, 0x32#8, 0x00#8,
     0x1a#8, 0xb9#8, 0x1d#8, 0x12#8, 0xb6#8, 0x1d#8, 0x0a#8, 0xae#8, 0x1c#8, 0x08#8, 0x01#8,
     0x12#8, 0x44#8, 0x0a#8, 0x20#8, 0xd2#8, 0x33#8, 0xbd#8, 0x3a#8, 0xb1#8, 0x3b#8, 0x04#8,
     0xce#8, 0x2e#8, 0x1b#8, 0xc2#8, 0x5b#8, 0x6b#8, 0x92#8, 0x8d#8, 0x2d#8, 0xd6#8, 0x88#8,
     0xfc#8, 0x7a#8, 0xd7#8, 0x0f#8, 0x8d#8, 0x98#8, 0x9b#8, 0xaa#8, 0x5b#8, 0xf3#8, 0x73#8,
     0x75#8, 0xcc#8, 0x69#8, 0x12#8, 0x20#8, 0x56#8, 0x8f#8, 0x27#8, 0x48#8, 0x90#8, 0xf9#8,
     0x9a#8, 0x65#8, 0x2a#8, 0x69#8, 0x6f#8, 0x89#8, 0x68#8, 0x36#8, 0x44#8, 0x52#8, 0xb3#8,
     0xe7#8, 0x7c#8, 0x1c#8, 0x92#8, 0x8e#8, 0x39#8, 0x13#8, 0x95#8, 0xd7#8, 0x1a#8, 0x9e#8,
     0x13#8, 0xad#8, 0x44#8, 0xfb#8, 0x1a#8, 0x80#8, 0x09#8] ++ List.replicate 1152 0x00#8 ++
    [0x22#8, 0xe0#8, 0x12#8] ++ List.replicate 2400 0x00#8 ++
    [0x12#8, 0x82#8, 0x01#8, 0x08#8, 0x01#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
     0xe8#8, 0x11#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xbd#8, 0xac#8, 0x12#8,
     0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x98#8, 0x89#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8,
     0x00#8, 0x00#8, 0xea#8, 0x46#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x99#8,
     0x31#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x34#8, 0xfe#8, 0x12#8, 0x06#8,
     0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x62#8, 0x8c#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8,
     0x00#8, 0xa6#8, 0xe4#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x1a#8, 0xcf#8,
     0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x27#8, 0xdf#8, 0x12#8, 0x06#8, 0x00#8,
     0x00#8, 0x00#8, 0x00#8, 0x8d#8, 0x1e#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
     0x5b#8, 0x32#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x64#8, 0x9c#8, 0x12#8,
     0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x13#8, 0xc6#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8,
     0x00#8, 0x00#8, 0x71#8, 0xe4#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x7a#8,
     0x3c#8]
  else
    [0x0a#8, 0x26#8, 0x0a#8, 0x20#8, 0xc8#8, 0xe2#8, 0x05#8, 0xf1#8, 0xb7#8, 0x18#8, 0xa1#8,
     0x3c#8, 0x05#8, 0x42#8, 0xaf#8, 0x92#8, 0xd0#8, 0x82#8, 0x47#8, 0x7a#8, 0x6f#8, 0xeb#8,
     0x3f#8, 0xb3#8, 0x9c#8, 0x36#8, 0xbf#8, 0xe0#8, 0xe0#8, 0x37#8, 0xaa#8, 0xd0#8, 0xda#8,
     0x49#8, 0x21#8, 0xd6#8, 0x18#8, 0x01#8, 0x22#8, 0x00#8, 0x12#8, 0x70#8, 0x1a#8, 0x4a#8,
     0x0a#8, 0x24#8, 0x08#8, 0x01#8, 0x12#8, 0x20#8, 0x97#8, 0x41#8, 0x91#8, 0xe0#8, 0x85#8,
     0xe7#8, 0xc2#8, 0xe1#8, 0x2b#8, 0x2d#8, 0x79#8, 0xd7#8, 0xf3#8, 0xa3#8, 0xe7#8, 0xa4#8,
     0x8f#8, 0xc2#8, 0x09#8, 0xf1#8, 0x5e#8, 0x8a#8, 0x14#8, 0x1c#8, 0xd9#8, 0x5f#8, 0x89#8,
     0xc1#8, 0x7f#8, 0x3b#8, 0x38#8, 0xf1#8, 0x12#8, 0x22#8, 0x12#8, 0x20#8, 0x67#8, 0xfb#8,
     0xb1#8, 0x19#8, 0x3b#8, 0x8e#8, 0xe2#8, 0x07#8, 0xc4#8, 0xf0#8, 0xed#8, 0xe1#8, 0x28#8,
     0x1c#8, 0x23#8, 0x5e#8, 0xe1#8, 0xfc#8, 0xe5#8, 0xf0#8, 0xa5#8, 0xb3#8, 0x1b#8, 0xc2#8,
     0xce#8, 0xcb#8, 0x10#8, 0xf7#8, 0x6d#8, 0x93#8, 0x22#8, 0xe8#8, 0x22#8, 0x20#8, 0xb5#8,
     0xdd#8, 0xa6#8, 0x16#8, 0xc5#8, 0xf9#8, 0x3f#8, 0x6c#8, 0x88#8, 0xcc#8, 0xe6#8, 0x27#8,
     0x26#8, 0x0b#8, 0xa0#8, 0x4b#8, 0xb8#8, 0x72#8, 0xd3#8, 0x2a#8, 0xd1#8, 0x93#8, 0x45#8,
     0x6a#8, 0x04#8, 0xff#8, 0x01#8, 0xe0#8, 0xef#8, 0xc0#8, 0x56#8, 0xeb#8, 0x32#8, 0x00#8,
     0x1a#8, 0xb9#8, 0x1d#8, 0x12#8, 0xb6#8, 0x1d#8, 0x0a#8, 0xae#8, 0x1c#8, 0x08#8, 0x01#8,
     0x12#8, 0x44#8, 0x0a#8, 0x20#8, 0x54#8, 0x17#8, 0x6c#8, 0x1b#8, 0xed#8, 0x90#8, 0xd8#8,
     0x18#8, 0x3c#8, 0x8e#8, 0xd8#8, 0x07#8, 0x52#8, 0xfa#8, 0x07#8, 0x3f#8, 0xe0#8, 0xcf#8,
     0x2b#8, 0xd1#8, 0x1d#8, 0x4e#8, 0xac#8, 0x2b#8, 0x9c#8, 0x19#8, 0x92#8, 0x33#8, 0xaf#8,
     0x5d#8, 0x0b#8, 0xdc#8, 0x12#8, 0x20#8, 0xcb#8, 0x88#8, 0x72#8, 0x7d#8, 0x45#8, 0xaf#8,
     0x8d#8, 0x32#8, 0x27#8, 0x90#8, 0xe7#8, 0xfe#8, 0x31#8, 0x90#8, 0xb5#8, 0xcd#8, 0x2f#8,
     0xf2#8, 0x49#8, 0xc2#8, 0x49#8, 0x72#8, 0x88#8, 0x15#8, 0xcb#8, 0x66#8, 0x14#8, 0xa3#8,
     0x6c#8, 0x7f#8, 0xd8#8, 0xca#8, 0x1a#8, 0x80#8, 0x09#8] ++ List.replicate 1152 0x00#8 ++
    [0x22#8, 0xe0#8, 0x12#8] ++ List.replicate 2400 0x00#8 ++
    [0x12#8, 0x82#8, 0x01#8, 0x08#8, 0x01#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
     0x5d#8, 0x82#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xcc#8, 0x01#8, 0x12#8,
     0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x10#8, 0xb7#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8,
     0x00#8, 0x00#8, 0x52#8, 0xd2#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x6a#8,
     0x44#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x8b#8, 0x66#8, 0x12#8, 0x06#8,
     0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x1e#8, 0x77#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8,
     0x00#8, 0x9e#8, 0xc5#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xbb#8, 0xd4#8,
     0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xd7#8, 0x9c#8, 0x12#8, 0x06#8, 0x00#8,
     0x00#8, 0x00#8, 0x00#8, 0x29#8, 0x8c#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
     0xfe#8, 0x11#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x8d#8, 0xe3#8, 0x12#8,
     0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x1a#8, 0x3f#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8,
     0x00#8, 0x00#8, 0x64#8, 0x4d#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xe5#8,
     0x08#8]

def rkA1 (withOpk : Bool) : BitVec 256 :=
  if withOpk then 0xf5c474fbd334ac4c298db659a773aed9585912c390b8e27af0fa1548227febfc#256
  else 0x9b7845d69807b8241a3122595a64270bf3bc0a6f17cfb0f595c469ce60e5e0d4#256

def cksA1 (withOpk : Bool) : BitVec 256 :=
  if withOpk then 0xdc8623ddce68547f3f551501a4bc3d6b7d885d076bfe45a1a6b454b1efc69249#256
  else 0x0246bb4190f60e2c3676076e2d82274dd4ed6bf9426b2ee80e8e62f66e22ca43#256

def ckrA1 (withOpk : Bool) : BitVec 256 :=
  if withOpk then 0xa774ed29e5fc2de180f99768270a65c53db9a101580b76086066006023e87090#256
  else 0xa71702ed76c97e891f3a9ae769414a4936a4119a2b6696cd600ab7789b0cd08d#256

def cksA2 (withOpk : Bool) : BitVec 256 :=
  if withOpk then 0x0b6233b3fbfbf6977892a9fa5403c558003bb09a6dbc2351ec81b877437e9989#256
  else 0xeaac70d8a9f9c96e923f532733b80ad0e302175ab0fdd431e2fcf90a5a8c7d8a#256

def g_A1 (withOpk : Bool) : GhostState HwBytes :=
  ⟨.A,
    { sessionVersion := 4#32
      localIdentity := ⟨⟨idPubA_vec⟩⟩
      remoteIdentity := some ⟨⟨idPubB_vec⟩⟩
      rootKey := rkA1 withOpk
      previousCounter := 0#32
      senderChain := some ⟨⟨⟨ephPubA_vec withOpk⟩, ⟨ephPrivA_vec withOpk⟩⟩, ⟨cksA1 withOpk, 0#32⟩⟩
      receiverChains := [⟨⟨spkPubB_vec⟩, some ⟨ckrA1 withOpk, 0#32⟩, []⟩]
      pendingPreKey := true
      pqRatchetState := pqA0 withOpk },
    0, [0]⟩

def g_A2 (withOpk : Bool) : GhostState HwBytes :=
  ⟨.A,
    { (g_A1 withOpk).session with
      senderChain := some ⟨⟨⟨ephPubA_vec withOpk⟩, ⟨ephPrivA_vec withOpk⟩⟩, ⟨cksA2 withOpk, 1#32⟩⟩
      pqRatchetState := pqA1 withOpk },
    0, [0]⟩

def stA1_cli (withOpk : Bool) : PqParty :=
  { stA0_cli withOpk with peerId := some ⟨⟨idPubB_vec⟩⟩, session := some (x_A withOpk, g_A1 withOpk) }

def stA2_cli (withOpk : Bool) : PqParty :=
  { stA0_cli withOpk with peerId := some ⟨⟨idPubB_vec⟩⟩, session := some (x_A withOpk, g_A2 withOpk) }

def pkAddrMid : HwBytes :=
  [0x32#8, 0x24#8, 0x00#8, 0x8a#8, 0x6f#8, 0x1c#8, 0x2e#8, 0x3b#8, 0x4d#8, 0x4e#8, 0x5f#8,
   0x9a#8, 0x0b#8, 0x1c#8, 0x2d#8, 0x3e#8, 0x4f#8, 0x5a#8, 0x6b#8, 0x01#8, 0x00#8, 0x5d#8,
   0x3e#8, 0x2f#8, 0x10#8, 0x7a#8, 0x8b#8, 0x4c#8, 0x9d#8, 0x8e#8, 0x0f#8, 0xa1#8, 0xb2#8,
   0xc3#8, 0xd4#8, 0xe5#8, 0xf6#8, 0x01#8]

def innerBytes0 (withOpk : Bool) : HwBytes :=
  if withOpk then
    [0x44#8, 0x0a#8, 0x21#8, 0x05#8] ++ (ephPubA_vec true).1 ++
      [0x10#8, 0x00#8, 0x18#8, 0x00#8, 0x22#8, 0x10#8,
       0xe2#8, 0x9e#8, 0x75#8, 0xf0#8, 0x29#8, 0xe9#8, 0xdf#8, 0x48#8,
       0x66#8, 0x14#8, 0xd7#8, 0x1c#8, 0x13#8, 0xb5#8, 0xef#8, 0x60#8,
       0x2a#8, 0x25#8] ++ List.replicate 4 0x01#8 ++ List.replicate 33 0x00#8 ++
      pkAddrMid ++ [0x76#8, 0xcd#8, 0x21#8, 0x83#8, 0x45#8, 0xdf#8, 0x1d#8, 0x6e#8]
  else
    [0x44#8, 0x0a#8, 0x21#8, 0x05#8] ++ (ephPubA_vec false).1 ++
      [0x10#8, 0x00#8, 0x18#8, 0x00#8, 0x22#8, 0x10#8,
       0x7e#8, 0x02#8, 0x47#8, 0xf2#8, 0xd5#8, 0x06#8, 0xe6#8, 0x6e#8,
       0x10#8, 0x68#8, 0x8c#8, 0xec#8, 0x67#8, 0x1a#8, 0x7c#8, 0x90#8,
       0x2a#8, 0x25#8] ++ List.replicate 4 0x01#8 ++ List.replicate 33 0x00#8 ++
      pkAddrMid ++ [0xe6#8, 0x64#8, 0xbe#8, 0x96#8, 0xe3#8, 0xc5#8, 0xbc#8, 0x6a#8]

def pkMsg0 (withOpk : Bool) : PreKeyMessageFields where
  regId := 10#32
  opkId := if withOpk then some 3#32 else none
  spkId := 1#32
  kpkId := 2#32
  kyberCt := kyberCt0_vec withOpk
  baseKey := basePubA_vec withOpk
  idPub := idPubA_vec
  inner := innerBytes0 withOpk

def wire0 (withOpk : Bool) : HwBytes :=
  wirePrekey :: (pkMsg0 withOpk).bytes

def pqB1 (withOpk : Bool) : HwBytes :=
  (if withOpk then
    [0x12#8, 0x72#8, 0x08#8, 0x01#8, 0x1a#8, 0x4a#8, 0x0a#8, 0x22#8, 0x12#8, 0x20#8, 0x3f#8,
     0xde#8, 0x84#8, 0x74#8, 0x7b#8, 0x6d#8, 0x41#8, 0x9b#8, 0x20#8, 0x09#8, 0x8d#8, 0xe8#8,
     0x6b#8, 0xd1#8, 0x02#8, 0x1e#8, 0x70#8, 0x3a#8, 0xc2#8, 0x65#8, 0x52#8, 0xe7#8, 0x28#8,
     0x0b#8, 0xf4#8, 0x4d#8, 0xed#8, 0xf9#8, 0x10#8, 0x38#8, 0xdd#8, 0x39#8, 0x12#8, 0x24#8,
     0x08#8, 0x01#8, 0x12#8, 0x20#8, 0xca#8, 0xf0#8, 0x12#8, 0xf8#8, 0xc4#8, 0x50#8, 0xf3#8,
     0xcb#8, 0x38#8, 0xba#8, 0xd9#8, 0xd4#8, 0xb1#8, 0xcc#8, 0x47#8, 0x27#8, 0x18#8, 0x1f#8,
     0x4e#8, 0x49#8, 0x22#8, 0x9a#8, 0x87#8, 0x3a#8, 0xe5#8, 0x12#8, 0x74#8, 0x91#8, 0xcb#8,
     0x36#8, 0xe2#8, 0x47#8, 0x22#8, 0x20#8, 0xe2#8, 0xd6#8, 0x55#8, 0xd3#8, 0xcc#8, 0xc1#8,
     0xa1#8, 0x00#8, 0xc3#8, 0x12#8, 0x57#8, 0x55#8, 0x3d#8, 0x96#8, 0x6f#8, 0xcd#8, 0x8e#8,
     0x7a#8, 0xad#8, 0xaf#8, 0x63#8, 0x4c#8, 0x1f#8, 0x59#8, 0x2f#8, 0x94#8, 0xc7#8, 0x79#8,
     0x8d#8, 0xf5#8, 0x34#8, 0xa2#8, 0x32#8, 0x00#8, 0x1a#8, 0xb3#8, 0x01#8, 0x32#8, 0xb0#8,
     0x01#8, 0x0a#8, 0x48#8, 0x08#8, 0x01#8, 0x12#8, 0x44#8, 0x0a#8, 0x20#8, 0xd2#8, 0x33#8,
     0xbd#8, 0x3a#8, 0xb1#8, 0x3b#8, 0x04#8, 0xce#8, 0x2e#8, 0x1b#8, 0xc2#8, 0x5b#8, 0x6b#8,
     0x92#8, 0x8d#8, 0x2d#8, 0xd6#8, 0x88#8, 0xfc#8, 0x7a#8, 0xd7#8, 0x0f#8, 0x8d#8, 0x98#8,
     0x9b#8, 0xaa#8, 0x5b#8, 0xf3#8, 0x73#8, 0x75#8, 0xcc#8, 0x69#8, 0x12#8, 0x20#8, 0x56#8,
     0x8f#8, 0x27#8, 0x48#8, 0x90#8, 0xf9#8, 0x9a#8, 0x65#8, 0x2a#8, 0x69#8, 0x6f#8, 0x89#8,
     0x68#8, 0x36#8, 0x44#8, 0x52#8, 0xb3#8, 0xe7#8, 0x7c#8, 0x1c#8, 0x92#8, 0x8e#8, 0x39#8,
     0x13#8, 0x95#8, 0xd7#8, 0x1a#8, 0x9e#8, 0x13#8, 0xad#8, 0x44#8, 0xfb#8, 0x12#8, 0x64#8,
     0x08#8, 0x30#8, 0x10#8, 0x10#8]
  else
    [0x12#8, 0x72#8, 0x08#8, 0x01#8, 0x1a#8, 0x4a#8, 0x0a#8, 0x22#8, 0x12#8, 0x20#8, 0x67#8,
     0xfb#8, 0xb1#8, 0x19#8, 0x3b#8, 0x8e#8, 0xe2#8, 0x07#8, 0xc4#8, 0xf0#8, 0xed#8, 0xe1#8,
     0x28#8, 0x1c#8, 0x23#8, 0x5e#8, 0xe1#8, 0xfc#8, 0xe5#8, 0xf0#8, 0xa5#8, 0xb3#8, 0x1b#8,
     0xc2#8, 0xce#8, 0xcb#8, 0x10#8, 0xf7#8, 0x6d#8, 0x93#8, 0x22#8, 0xe8#8, 0x12#8, 0x24#8,
     0x08#8, 0x01#8, 0x12#8, 0x20#8, 0x97#8, 0x41#8, 0x91#8, 0xe0#8, 0x85#8, 0xe7#8, 0xc2#8,
     0xe1#8, 0x2b#8, 0x2d#8, 0x79#8, 0xd7#8, 0xf3#8, 0xa3#8, 0xe7#8, 0xa4#8, 0x8f#8, 0xc2#8,
     0x09#8, 0xf1#8, 0x5e#8, 0x8a#8, 0x14#8, 0x1c#8, 0xd9#8, 0x5f#8, 0x89#8, 0xc1#8, 0x7f#8,
     0x3b#8, 0x38#8, 0xf1#8, 0x22#8, 0x20#8, 0xb5#8, 0xdd#8, 0xa6#8, 0x16#8, 0xc5#8, 0xf9#8,
     0x3f#8, 0x6c#8, 0x88#8, 0xcc#8, 0xe6#8, 0x27#8, 0x26#8, 0x0b#8, 0xa0#8, 0x4b#8, 0xb8#8,
     0x72#8, 0xd3#8, 0x2a#8, 0xd1#8, 0x93#8, 0x45#8, 0x6a#8, 0x04#8, 0xff#8, 0x01#8, 0xe0#8,
     0xef#8, 0xc0#8, 0x56#8, 0xeb#8, 0x32#8, 0x00#8, 0x1a#8, 0xb3#8, 0x01#8, 0x32#8, 0xb0#8,
     0x01#8, 0x0a#8, 0x48#8, 0x08#8, 0x01#8, 0x12#8, 0x44#8, 0x0a#8, 0x20#8, 0x54#8, 0x17#8,
     0x6c#8, 0x1b#8, 0xed#8, 0x90#8, 0xd8#8, 0x18#8, 0x3c#8, 0x8e#8, 0xd8#8, 0x07#8, 0x52#8,
     0xfa#8, 0x07#8, 0x3f#8, 0xe0#8, 0xcf#8, 0x2b#8, 0xd1#8, 0x1d#8, 0x4e#8, 0xac#8, 0x2b#8,
     0x9c#8, 0x19#8, 0x92#8, 0x33#8, 0xaf#8, 0x5d#8, 0x0b#8, 0xdc#8, 0x12#8, 0x20#8, 0xcb#8,
     0x88#8, 0x72#8, 0x7d#8, 0x45#8, 0xaf#8, 0x8d#8, 0x32#8, 0x27#8, 0x90#8, 0xe7#8, 0xfe#8,
     0x31#8, 0x90#8, 0xb5#8, 0xcd#8, 0x2f#8, 0xf2#8, 0x49#8, 0xc2#8, 0x49#8, 0x72#8, 0x88#8,
     0x15#8, 0xcb#8, 0x66#8, 0x14#8, 0xa3#8, 0x6c#8, 0x7f#8, 0xd8#8, 0xca#8, 0x12#8, 0x64#8,
     0x08#8, 0x30#8, 0x10#8, 0x10#8]) ++
  (List.replicate 16 ([0x1a#8, 0x04#8] ++ List.replicate 4 0x00#8)).flatten

def rkB1 (withOpk : Bool) : BitVec 256 :=
  if withOpk then 0xe623bf102398726b6879300b17918a5a44ec17742bd2da47ae364b6456bd8ba5#256
  else 0x8240ca6e67edddb629f2694daf4d13e067b8fc53142421240d95ceee943b0cb5#256

def cksB1 (withOpk : Bool) : BitVec 256 :=
  if withOpk then 0x1ed9e259ecf73a3a89af00268ec692f1570df2883d03b2b048b2c5fc0b8ab47c#256
  else 0x0213fed2792dfd3dc6e62935f6d1d3370cdc67cdde0b56e28815d0d1b73dfd6a#256

def g_B1 (withOpk : Bool) : GhostState HwBytes :=
  ⟨.B,
    { sessionVersion := 4#32
      localIdentity := ⟨⟨idPubB_vec⟩⟩
      remoteIdentity := some ⟨⟨idPubA_vec⟩⟩
      rootKey := rkB1 withOpk
      previousCounter := 0#32
      senderChain := some ⟨⟨⟨ephPubB_vec withOpk⟩, ⟨ephPrivB_vec withOpk⟩⟩, ⟨cksB1 withOpk, 0#32⟩⟩
      receiverChains := [⟨⟨ephPubA_vec withOpk⟩, some ⟨cksA2 withOpk, 1#32⟩, []⟩]
      pendingPreKey := false
      pqRatchetState := pqB1 withOpk },
    1, [1]⟩

def stB0Marked (withOpk : Bool) : PqParty :=
  { stB0_cli withOpk with
    kyberLastResort :=
      [(2#32, ⟨myKyberPub1568, myKyberSec3168, List.Vector.replicate 64 0#8, 0⟩,
        [(1#32, basePubA_vec withOpk)])] }

def stB1_cli (withOpk : Bool) : PqParty :=
  { stB0Marked withOpk with
    peerId := some ⟨⟨idPubA_vec⟩⟩
    session := some (x_B withOpk, g_B1 withOpk)
    oneTime := if withOpk then [(3#32, none)] else [] }

theorem wire0_eq (withOpk : Bool) :
    wire0 withOpk = wirePrekey :: (pkMsg0 withOpk).bytes := rfl

private def reprParty : CryptoGames.Party → Bool
  | .A => false
  | .B => true

private theorem reprParty_inj {a b : CryptoGames.Party} (h : reprParty a = reprParty b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private def reprRecordExtras (x : RecordExtras) :=
  ((x.pending.1, x.pending.2, x.pending.3.bytes.1, x.pending.4),
   x.kyber.map (fun k => (k.1, @id (List (BitVec 8)) k.2)),
   x.remoteRegistrationId, x.localRegistrationId, @id (List (BitVec 8)) x.aliceBaseKey)

private theorem reprRecordExtras_inj {a b : RecordExtras}
    (h : reprRecordExtras a = reprRecordExtras b) : a = b := by
  rcases a with ⟨⟨p1, p2, ⟨pb⟩, p4⟩, kyA, rA, lA, bkA⟩
  rcases b with ⟨⟨q1, q2, ⟨qb⟩, q4⟩, kyB, rB, lB, bkB⟩
  simp only [reprRecordExtras, id_eq, Prod.mk.injEq] at h
  rcases h with ⟨⟨rfl, rfl, hpb, rfl⟩, hky, rfl, rfl, rfl⟩
  cases Subtype.ext hpb; congr 1
  cases kyA with
  | none => cases kyB with | none => rfl | some _ => cases hky
  | some ka =>
    cases kyB with
    | none => cases hky
    | some kb =>
      rcases ka with ⟨i1, c1⟩; rcases kb with ⟨i2, c2⟩
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hky
      rcases hky with ⟨rfl, rfl⟩; rfl

private def reprKyberKey (k : CryptoVerification.SignalSession.PqKyberKey) :=
  (k.pub.1, k.sec.1, k.sig.1, k.timestamp)

private theorem reprKyberKey_inj {a b : CryptoVerification.SignalSession.PqKyberKey}
    (h : reprKyberKey a = reprKyberKey b) : a = b := by
  rcases a with ⟨p1, s1, g1, t1⟩; rcases b with ⟨p2, s2, g2, t2⟩
  simp only [reprKyberKey, Prod.mk.injEq] at h
  rcases h with ⟨hp, hs, hg, rfl⟩
  rw [Subtype.ext hp, Subtype.ext hs, Subtype.ext hg]

private def reprSession (s : CryptoGames.LibsignalSession.SessionState CryptoVerification.E2E.Bytes) :=
  (s.sessionVersion, s.localIdentity.publicKey.bytes.1,
   s.remoteIdentity.map (fun k => k.publicKey.bytes.1), s.rootKey, s.previousCounter,
   s.senderChain.map (fun sc =>
     ((sc.ratchetKey.publicKey.bytes.1, sc.ratchetKey.privateKey.bytes.1),
      (sc.chainKey.key, sc.chainKey.index))),
   s.receiverChains.map (fun rc =>
     (rc.senderRatchetKey.bytes.1, rc.chainKey.map (fun ck => (ck.key, ck.index)),
      rc.messageKeys.map (fun mk => (mk.seed, mk.counter)))),
   s.pendingPreKey, @id (List (BitVec 8)) s.pqRatchetState)

private theorem reprSession_inj {a b : CryptoGames.LibsignalSession.SessionState CryptoVerification.E2E.Bytes}
    (h : reprSession a = reprSession b) : a = b := by
  rcases a with ⟨sv1, ⟨⟨li1⟩⟩, ri1, rk1, pc1, sc1, rc1, pp1, pq1⟩
  rcases b with ⟨sv2, ⟨⟨li2⟩⟩, ri2, rk2, pc2, sc2, rc2, pp2, pq2⟩
  simp only [reprSession, id_eq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, hli, hri, rfl, rfl, hsc, hrc, rfl, hpq⟩
  cases Subtype.ext hli
  have hri' : ri1 = ri2 := Option.map_injective (by rintro ⟨⟨v1⟩⟩ ⟨⟨v2⟩⟩ hv; cases Subtype.ext hv; rfl) hri
  have hsc' : sc1 = sc2 := by
    refine Option.map_injective ?_ hsc
    rintro ⟨⟨⟨pub1⟩, ⟨prv1⟩⟩, ⟨ck1, ci1⟩⟩ ⟨⟨⟨pub2⟩, ⟨prv2⟩⟩, ⟨ck2, ci2⟩⟩ hs
    simp only [Prod.mk.injEq] at hs; rcases hs with ⟨⟨hp1, hp2⟩, rfl, rfl⟩
    rw [Subtype.ext hp1, Subtype.ext hp2]
  have hrc' : rc1 = rc2 := by
    refine List.map_injective_iff.mpr ?_ hrc
    rintro ⟨⟨srk1⟩, ck1, mks1⟩ ⟨⟨srk2⟩, ck2, mks2⟩ hr
    simp only [Prod.mk.injEq] at hr; rcases hr with ⟨hsrk, hck, hmks⟩
    have hck' : ck1 = ck2 := Option.map_injective
      (by rintro ⟨k1, i1⟩ ⟨k2, i2⟩ hc; simp only [Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩; rfl) hck
    have hmks' : mks1 = mks2 := List.map_injective_iff.mpr
      (by rintro ⟨sd1, ct1⟩ ⟨sd2, ct2⟩ hm; simp only [Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩; rfl) hmks
    rw [Subtype.ext hsrk, hck', hmks']
  have hpq' : pq1 = pq2 := hpq
  rw [hri', hsc', hrc', hpq']

private def reprPqParty (st : PqParty) :=
  (reprParty st.party, (st.me.1.1, st.me.2), st.peerId.map (fun k => k.publicKey.bytes.1),
   st.session.map (fun (x, g) =>
     (reprRecordExtras x, reprParty g.party, reprSession g.session, g.epoch, g.chainEpochs)),
   st.signed.map (fun (i, s) => (i, s.priv.1, s.sig.1, s.timestamp)),
   st.oneTime.map (fun (i, o) => (i, o.map fun v : List.Vector (BitVec 8) 32 => v.1)),
   st.kyberOneTime.map (fun (i, o) => (i, o.map reprKyberKey)),
   st.kyberLastResort.map (fun (i, k, s) =>
     (i, reprKyberKey k, s.map fun p : BitVec 32 × List.Vector (BitVec 8) 32 => (p.1, p.2.1))))

private theorem reprPqParty_inj {a b : PqParty} (h : reprPqParty a = reprPqParty b) : a = b := by
  rcases a with ⟨pa, ⟨ma1, ma2⟩, pida, sa, sga, ota, kota, klra⟩
  rcases b with ⟨pb, ⟨mb1, mb2⟩, pidb, sb, sgb, otb, kotb, klrb⟩
  simp only [reprPqParty, Prod.mk.injEq] at h
  rcases h with ⟨hp, ⟨hma, rfl⟩, hpid, hsess, hsig, hot, hkot, hklr⟩
  cases reprParty_inj hp; cases Subtype.ext hma
  have hpid' : pida = pidb := Option.map_injective (by rintro ⟨⟨v1⟩⟩ ⟨⟨v2⟩⟩ hv; cases Subtype.ext hv; rfl) hpid
  have hsess' : sa = sb := by
    refine Option.map_injective ?_ hsess
    rintro ⟨xa, ⟨gpa, gsa, gea, gca⟩⟩ ⟨xb, ⟨gpb, gsb, geb, gcb⟩⟩ heq
    simp only [Prod.mk.injEq] at heq; rcases heq with ⟨hx, hgp, hgs, rfl, rfl⟩
    rw [reprRecordExtras_inj hx, reprParty_inj hgp, reprSession_inj hgs]
  have hsig' : sga = sgb := by
    refine List.map_injective_iff.mpr ?_ hsig
    rintro ⟨i1, ⟨pr1, sg1, ts1⟩⟩ ⟨i2, ⟨pr2, sg2, ts2⟩⟩ heq
    simp only [Prod.mk.injEq] at heq; rcases heq with ⟨rfl, hpr, hsg, rfl⟩
    rw [Subtype.ext hpr, Subtype.ext hsg]
  have hot' : ota = otb := List.map_injective_iff.mpr
    (by rintro ⟨i1, o1⟩ ⟨i2, o2⟩ heq; simp only [Prod.mk.injEq] at heq; rcases heq with ⟨rfl, ho⟩
        rw [Option.map_injective (fun _ _ => Subtype.ext) ho]) hot
  have hkot' : kota = kotb := List.map_injective_iff.mpr
    (by rintro ⟨i1, o1⟩ ⟨i2, o2⟩ heq; simp only [Prod.mk.injEq] at heq; rcases heq with ⟨rfl, ho⟩
        rw [Option.map_injective (fun _ _ => reprKyberKey_inj) ho]) hkot
  have hklr' : klra = klrb := by
    refine List.map_injective_iff.mpr ?_ hklr
    rintro ⟨i1, k1, l1⟩ ⟨i2, k2, l2⟩ heq
    simp only [Prod.mk.injEq] at heq; rcases heq with ⟨rfl, hk, hl⟩
    have hl' : l1 = l2 := List.map_injective_iff.mpr
      (by rintro ⟨j1, v1⟩ ⟨j2, v2⟩ hjv; simp only [Prod.mk.injEq] at hjv; rcases hjv with ⟨rfl, hv⟩
          rw [Subtype.ext hv]) hl
    rw [reprKyberKey_inj hk, hl']
  rw [hpid', hsess', hsig', hot', hkot', hklr']

private def reprOut (r : Option (Option (PqParty × HwBytes))) :=
  r.map (Option.map fun (st, out) => (reprPqParty st, @id (List (BitVec 8)) out))

private theorem eq_of_reprOut {a b : Option (Option (PqParty × HwBytes))}
    (h : reprOut a = reprOut b) : a = b := by
  unfold reprOut at h
  refine Option.map_injective (fun x y hxy => Option.map_injective ?_ hxy) h
  rintro ⟨s1, o1⟩ ⟨s2, o2⟩ hs
  simp only [Prod.mk.injEq, id_eq] at hs
  rw [reprPqParty_inj hs.1, hs.2]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 200000 in
private def decReprOut (a b : Option (Option (PqParty × HwBytes))) : Bool :=
  reprOut a == reprOut b

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem eq_of_decReprOut {a b : Option (Option (PqParty × HwBytes))}
    (h : decReprOut a b = true) : a = b := by
  unfold decReprOut at h
  exact eq_of_reprOut (eq_of_beq h)

private theorem tapeInit_eq (withOpk : Bool) :
    tapeInit withOpk = ⟨tapeInitBytes withOpk, by cases withOpk <;> rfl⟩ := by
  cases withOpk
  · exact Subtype.ext (bytesToVec_toList_of_len (n := initiateTapeLen) (bs := tapeInitBytes false) (by decide))
  · exact Subtype.ext (bytesToVec_toList_of_len (n := initiateTapeLen) (bs := tapeInitBytes true) (by decide))

theorem initStep_eq (withOpk : Bool) :
    pqInitModel nvX myParams (stA0_cli withOpk) (bE_cli withOpk) (tapeInit withOpk) =
      some (some (stA1_cli withOpk, [])) := by
  rw [tapeInit_eq]
  cases withOpk <;> exact eq_of_decReprOut (by decide +kernel)

theorem initStep_eq_any (X : UnreachedPqxdhPrimitives) (withOpk : Bool) :
    pqInitModel X myParams (stA0_cli withOpk) (bE_cli withOpk) (tapeInit withOpk) =
      some (some (stA1_cli withOpk, [])) := by
  rw [pqInitModel_congr_extras X nvX]
  exact initStep_eq withOpk

theorem sendStep_eq (withOpk : Bool) :
    pqSendModel myParams (stA1_cli withOpk) pt0 cSend0 =
      some (some (stA2_cli withOpk, wire0 withOpk)) := by
  cases withOpk <;> exact eq_of_decReprOut (by decide +kernel)

theorem markKyberUsed_stB0 (withOpk : Bool) :
    markKyberUsed (stB0_cli withOpk) (pkMsg0 withOpk) =
      some (stB0Marked withOpk) := by
  cases withOpk
  · have hko : (stB0_cli false).kyberOneTime.lookup (pkMsg0 false).kpkId = none := rfl
    have hlr : (stB0_cli false).kyberLastResort.lookup (pkMsg0 false).kpkId =
        some (⟨myKyberPub1568, myKyberSec3168, List.Vector.replicate 64 0#8, 0⟩, []) := rfl
    unfold markKyberUsed
    rw [hko, hlr]
    simp only [List.not_mem_nil]
    rfl
  · have hko : (stB0_cli true).kyberOneTime.lookup (pkMsg0 true).kpkId = none := rfl
    have hlr : (stB0_cli true).kyberLastResort.lookup (pkMsg0 true).kpkId =
        some (⟨myKyberPub1568, myKyberSec3168, List.Vector.replicate 64 0#8, 0⟩, []) := rfl
    unfold markKyberUsed
    rw [hko, hlr]
    simp only [List.not_mem_nil]
    rfl

theorem recvStep_eq (withOpk : Bool) :
    pqRecvPrekeyModel nvX myParams (stB0_cli withOpk) (pkMsg0 withOpk) (rcVal withOpk) =
      some (some (stB1_cli withOpk, pt0)) := by
  unfold pqRecvPrekeyModel
  rw [markKyberUsed_stB0]
  cases withOpk <;> exact eq_of_decReprOut (by decide +kernel)

theorem recvStep_eq_any (X : UnreachedPqxdhPrimitives) (withOpk : Bool) :
    pqRecvPrekeyModel X myParams (stB0_cli withOpk) (pkMsg0 withOpk) (rcVal withOpk) =
      some (some (stB1_cli withOpk, pt0)) := by
  rw [pqRecvPrekeyModel_congr_extras X nvX]
  exact recvStep_eq withOpk

/-! ## Domain Well-Formedness (`PqxdhPartyInSpecDomain`) -/

theorem wfPq_stA0 (withOpk : Bool) : PqxdhPartyInSpecDomain myParams (stA0_cli withOpk) := by
  have hcap : ∀ f ∈ encodeDir myParams (stA0_cli withOpk),
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
    cases withOpk <;>
      (unfold encodeDir CryptoVerification.SignalSession.fileCapBytes
       dsimp only [stA0_cli, List.map]; rw [keyPair_idA]; decide +kernel)
  have hfiles : ∀ f ∈ encodeDir myParams (stA0_cli withOpk),
      f.2.length < 2 ^ 31 ∧
        ((∀ i, f.1 ≠ CryptoVerification.SignalSession.baseKeysFile i) →
          f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes) :=
    fun f hf => ⟨by have h := hcap f hf; unfold CryptoVerification.SignalSession.fileCapBytes at h; omega,
      fun _ => hcap f hf⟩
  refine ⟨(fun _ _ hs => by cases withOpk <;> cases hs), hfiles, (by cases withOpk <;> decide),
    (by cases withOpk <;> decide), (by cases withOpk <;> decide), (by cases withOpk <;> decide)⟩

theorem wfPq_stB0 (withOpk : Bool) : PqxdhPartyInSpecDomain myParams (stB0_cli withOpk) := by
  have hcap : ∀ f ∈ encodeDir myParams (stB0_cli withOpk),
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
    cases withOpk
    · unfold encodeDir signedRecordBytes CryptoVerification.SignalSession.fileCapBytes
      dsimp only [stB0_cli, List.map]
      rw [keyPair_idB, keyPair_spkB]
      decide +kernel
    · unfold encodeDir signedRecordBytes oneTimeRecordBytes CryptoVerification.SignalSession.fileCapBytes
      dsimp only [stB0_cli]
      simp only [↓reduceIte, List.map]
      rw [keyPair_idB, keyPair_spkB, keyPair_opkB]
      decide +kernel
  have hfiles : ∀ f ∈ encodeDir myParams (stB0_cli withOpk),
      f.2.length < 2 ^ 31 ∧
        ((∀ i, f.1 ≠ CryptoVerification.SignalSession.baseKeysFile i) →
          f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes) :=
    fun f hf => ⟨by have h := hcap f hf; unfold CryptoVerification.SignalSession.fileCapBytes at h; omega,
      fun _ => hcap f hf⟩
  refine ⟨(fun _ _ hs => by cases withOpk <;> cases hs), hfiles, (by cases withOpk <;> decide),
    (by cases withOpk <;> decide), (by cases withOpk <;> decide), (by cases withOpk <;> decide)⟩

private theorem reachPq_gA1 (withOpk : Bool) :
    ReachablePqxdhSession myParams (stA0_cli withOpk).me (x_A withOpk) (g_A1 withOpk) := by
  have h1 := initStep_eq withOpk
  unfold pqInitModel at h1
  have htr : (stA0_cli withOpk).trusts ⟨⟨(bE_cli withOpk).idPub⟩⟩ = true := by
    cases withOpk <;> rfl
  have hpA : (stA0_cli withOpk).party = .A := rfl
  rw [htr, hpA] at h1
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1
  cases hi : initiateState nvX myParams .A (stA0_cli withOpk).me (bE_cli withOpk) (tapeInit withOpk) with
  | none => rw [hi] at h1; cases h1
  | some xg =>
    rcases xg with ⟨x0, g0⟩
    rw [hi] at h1
    have hst := (Prod.mk.inj (Option.some.inj (Option.some.inj h1))).1
    have hsess : some (x0, g0) = some (x_A withOpk, g_A1 withOpk) := congrArg PqParty.session hst
    rcases Prod.mk.inj (Option.some.inj hsess) with ⟨rfl, rfl⟩
    exact ReachablePqxdhSession.initiate nvX .A (stA0_cli withOpk).me (bE_cli withOpk) (tapeInit withOpk)
      (x_A withOpk) (g_A1 withOpk) hi

theorem wfPq_stA1 (withOpk : Bool) : PqxdhPartyInSpecDomain myParams (stA1_cli withOpk) := by
  have hcap : ∀ f ∈ encodeDir myParams (stA1_cli withOpk),
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
    cases withOpk <;>
      (unfold encodeDir CryptoVerification.SignalSession.fileCapBytes
       dsimp only [stA1_cli, stA0_cli, List.map]; rw [keyPair_idA]; decide +kernel)
  have hfiles : ∀ f ∈ encodeDir myParams (stA1_cli withOpk),
      f.2.length < 2 ^ 31 ∧
        ((∀ i, f.1 ≠ CryptoVerification.SignalSession.baseKeysFile i) →
          f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes) :=
    fun f hf => ⟨by have h := hcap f hf; unfold CryptoVerification.SignalSession.fileCapBytes at h; omega,
      fun _ => hcap f hf⟩
  refine ⟨?_, hfiles, by cases withOpk <;> decide, by cases withOpk <;> decide,
    by cases withOpk <;> decide, by cases withOpk <;> decide⟩
  rintro x g hs
  have hsess0 : (stA1_cli withOpk).session = some (x_A withOpk, g_A1 withOpk) := rfl
  rw [hsess0] at hs
  rcases Prod.mk.inj (Option.some.inj hs) with ⟨rfl, rfl⟩
  have hmem : (sessionFile (partyAddress (stA1_cli withOpk).party.other),
      encodeRecordUnderExtras (fun _ => x_A withOpk) (g_A1 withOpk)) ∈
      encodeDir myParams (stA1_cli withOpk) := by
    unfold encodeDir; simp [hsess0]
  exact ⟨⟨g_A1 withOpk, reachPq_gA1 withOpk, rfl, rfl⟩, rfl, (hfiles _ hmem).1⟩

private theorem send_gA1_eq (withOpk : Bool) :
    ((pqxdhSessionParams myParams).send (g_A1 withOpk) pt0 cSend0).1.party = (g_A2 withOpk).party ∧
    ((pqxdhSessionParams myParams).send (g_A1 withOpk) pt0 cSend0).1.session = (g_A2 withOpk).session := by
  cases withOpk <;> exact ⟨by decide +kernel, by decide +kernel⟩

theorem wfPq_stA2 (withOpk : Bool) : PqxdhPartyInSpecDomain myParams (stA2_cli withOpk) := by
  have hcap : ∀ f ∈ encodeDir myParams (stA2_cli withOpk),
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
    cases withOpk <;>
      (unfold encodeDir CryptoVerification.SignalSession.fileCapBytes
       dsimp only [stA2_cli, stA0_cli, List.map]; rw [keyPair_idA]; decide +kernel)
  have hfiles : ∀ f ∈ encodeDir myParams (stA2_cli withOpk),
      f.2.length < 2 ^ 31 ∧
        ((∀ i, f.1 ≠ CryptoVerification.SignalSession.baseKeysFile i) →
          f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes) :=
    fun f hf => ⟨by have h := hcap f hf; unfold CryptoVerification.SignalSession.fileCapBytes at h; omega,
      fun _ => hcap f hf⟩
  refine ⟨?_, hfiles, by cases withOpk <;> decide, by cases withOpk <;> decide,
    by cases withOpk <;> decide, by cases withOpk <;> decide⟩
  rintro x g hs
  have hsess2 : (stA2_cli withOpk).session = some (x_A withOpk, g_A2 withOpk) := rfl
  rw [hsess2] at hs
  rcases Prod.mk.inj (Option.some.inj hs) with ⟨rfl, rfl⟩
  have hrec1 : (encodeRecordUnderExtras (fun _ => x_A withOpk) (g_A1 withOpk)).length < 2 ^ 31 :=
    ((wfPq_stA1 withOpk).1 (x_A withOpk) (g_A1 withOpk) rfl).2.2
  have hR2 := ReachablePqxdhSession.send pt0 cSend0 (reachPq_gA1 withOpk) hrec1
  obtain ⟨hp0, hs0⟩ := send_gA1_eq withOpk
  have hmem : (sessionFile (partyAddress (stA2_cli withOpk).party.other),
      encodeRecordUnderExtras (fun _ => x_A withOpk) (g_A2 withOpk)) ∈
      encodeDir myParams (stA2_cli withOpk) := by
    unfold encodeDir; simp [hsess2]
  exact ⟨⟨((pqxdhSessionParams myParams).send (g_A1 withOpk) pt0 cSend0).1, hR2, hp0, hs0⟩,
    rfl, (hfiles _ hmem).1⟩

theorem wfPq_stB1 (withOpk : Bool) : PqxdhPartyInSpecDomain myParams (stB1_cli withOpk) := by
  have hcap : ∀ f ∈ encodeDir myParams (stB1_cli withOpk),
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
    cases withOpk <;>
      (unfold encodeDir signedRecordBytes CryptoVerification.SignalSession.fileCapBytes
       dsimp only [stB1_cli, stB0Marked, stB0_cli, ↓reduceIte, List.map]
       rw [keyPair_idB, keyPair_spkB]
       decide +kernel)
  have hfiles : ∀ f ∈ encodeDir myParams (stB1_cli withOpk),
      f.2.length < 2 ^ 31 ∧
        ((∀ i, f.1 ≠ CryptoVerification.SignalSession.baseKeysFile i) →
          f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes) :=
    fun f hf => ⟨by have h := hcap f hf; unfold CryptoVerification.SignalSession.fileCapBytes at h; omega,
      fun _ => hcap f hf⟩
  refine ⟨?_, hfiles, by cases withOpk <;> decide, by cases withOpk <;> decide,
    by cases withOpk <;> decide, by cases withOpk <;> decide⟩
  rintro x g hs
  have hsess1 : (stB1_cli withOpk).session = some (x_B withOpk, g_B1 withOpk) := rfl
  rw [hsess1] at hs
  rcases Prod.mk.inj (Option.some.inj hs) with ⟨rfl, rfl⟩
  have hr := recvStep_eq withOpk
  unfold pqRecvPrekeyModel at hr
  cases htry : SignalMessage.tryFrom protoSignalCodec (pkMsg0 withOpk).inner with
  | error _ => rw [htry] at hr; cases hr
  | ok _ =>
    rw [htry] at hr
    have htr : (stB0_cli withOpk).trusts ⟨⟨(pkMsg0 withOpk).idPub⟩⟩ = true := by
      cases withOpk <;> rfl
    have hs0 : (stB0_cli withOpk).session = none := rfl
    dsimp only at hr; rw [htr, hs0] at hr
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
    cases hk : preKeysNamedBy (stB0_cli withOpk) (pkMsg0 withOpk) with
    | none => rw [hk] at hr; cases hr
    | some k =>
      rw [hk] at hr; dsimp only at hr
      cases hrs : recvPrekeyState nvX myParams (stB0_cli withOpk).party (stB0_cli withOpk).me
          k (pkMsg0 withOpk) (rcVal withOpk) with
      | none => rw [hrs] at hr; cases hr
      | some o =>
        cases o with
        | none => rw [hrs] at hr; cases hr
        | some xgp =>
          rcases xgp with ⟨x0, g0, pt'⟩
          rw [hrs, markKyberUsed_stB0] at hr
          have hst := (Prod.mk.inj (Option.some.inj (Option.some.inj hr))).1
          have hpair : some (x0, g0) = some (x_B withOpk, g_B1 withOpk) :=
            congrArg PqParty.session hst
          rcases Prod.mk.inj (Option.some.inj hpair) with ⟨rfl, rfl⟩
          have hmem : (sessionFile (partyAddress (stB1_cli withOpk).party.other),
              encodeRecordUnderExtras (fun _ => x_B withOpk) (g_B1 withOpk)) ∈
              encodeDir myParams (stB1_cli withOpk) := by
            unfold encodeDir; simp [hsess1]
          exact ⟨⟨g_B1 withOpk, ReachablePqxdhSession.recvPrekey nvX (stB0_cli withOpk).party
              (stB0_cli withOpk).me k (pkMsg0 withOpk) (rcVal withOpk)
              (x_B withOpk) (g_B1 withOpk) pt' hrs,
              rfl, rfl⟩, rfl, (hfiles _ hmem).1⟩

end Symbolic.Proofs.Tests.CliNonvacuity.HandshakeModel
