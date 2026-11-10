/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ModelTraces
public import LibsignalBinary.Specifications.RecordCodecs.Proto

/-!
# Initial CLI Directories

Initial filesystem directory snapshots (`initDirs`) provisioned for Alice and Bob before any
`signal-session` CLI invocation in the refinement statement, encoding the setup keys and
registration IDs of `ProtocolSetup` with no pre-existing session files.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement
open CryptoVerification.SignalSession (Address filesOf addressFile identityKeyPairFile
  registrationIdFile identityFile sessionFile signedPreKeyFile oneTimePreKeyFile
  lastResortKyberPreKeyFile baseKeysFile le32)
open CryptoVerification.RecordCodecs (IdentityKeyPairStructure SignedPreKeyRecordStructure
  PreKeyRecordStructure)

def aliceUuid : String := "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b"

def bobUuid : String := "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6"

def nameOf (r : ProtocolSetup) (p : Participant) : String := if p = r.alice then aliceUuid else bobUuid

def peerNameOf (r : ProtocolSetup) (p : Participant) : String :=
  if p = r.alice then bobUuid else aliceUuid

def addrOf (r : ProtocolSetup) (p : Participant) : Address := ⟨nameOf r p, 1⟩

def peerOf (r : ProtocolSetup) (p : Participant) : Address := ⟨peerNameOf r p, 1⟩

def sessionPathOf (r : ProtocolSetup) (p : Participant) : String := sessionFile (peerOf r p)

/-- UTF-8 byte encoding of `s`. -/
def textBytes (s : String) : HwBytes := s.toUTF8.toList.map fun b => BitVec.ofNat 8 b.toNat

/-- Decode hexadecimal byte pairs from a hyphenated UUID string. -/
def parseUuidBytes (s : String) : HwBytes :=
  let hexVal (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
  let rec pairs : List Char → HwBytes
    | a :: b :: rest => BitVec.ofNat 8 (16 * hexVal a + hexVal b) :: pairs rest
    | _ => []
  pairs (s.toList.filter (· != '-'))

/-- Binary `ProtocolAddress` encoding (`0x00` ACI tag || 16-byte UUID || 1-byte device ID). -/
def serializeAddress (a : Address) : HwBytes :=
  0x00#8 :: parseUuidBytes a.name ++ [BitVec.ofNat 8 a.device]

/-- Concatenated `(sender, recipient)` binary addresses written into `SignalMessage` field 6. -/
def serializeAddresses (sender recipient : Address) : HwBytes :=
  serializeAddress sender ++ serializeAddress recipient

/-- Regular files in a participant's working directory (`none` when absent). -/
abbrev DirectorySnapshot := String → Option HwBytes

def idSecret (r : ProtocolSetup) (p : Participant) : HwBytes :=
  if p = r.alice then r.ikASecBytes else r.ikBSecBytes

def peerIdSecret (r : ProtocolSetup) (p : Participant) : HwBytes :=
  if p = r.alice then r.ikBSecBytes else r.ikASecBytes

def regIdOf (r : ProtocolSetup) (p : Participant) : BitVec 32 := if p = r.alice then r.regIdA else r.regIdB

/-- Files provisioned for both Alice and Bob: `address`, `identity-key-pair`, `registration-id`,
and pinned `identities/<peer>`. -/
def commonFiles (interp : ExternInterpretation) (r : ProtocolSetup) (p : Participant) :
    List (String × HwBytes) :=
  [(addressFile, textBytes (addrOf r p).text),
   (identityKeyPairFile,
     IdentityKeyPairStructure.encode ⟨ecKey (pubBytes interp (idSecret r p)), idSecret r p⟩),
   (registrationIdFile, le32 (regIdOf r p)),
   (identityFile (peerNameOf r p), ecKey (pubBytes interp (peerIdSecret r p)))]

/-- Bob's pre-key files: signed pre-key, last-resort Kyber pre-key with empty `.base-keys`, and
optional one-time pre-key when `r.withOpk` holds. -/
def bobPreKeyFiles (interp : ExternInterpretation) (r : ProtocolSetup) : List (String × HwBytes) :=
  [(signedPreKeyFile r.spkId, SignedPreKeyRecordStructure.encode
      ⟨r.spkId, ecKey (pubBytes interp r.spkSecBytes), r.spkSecBytes,
        r.opaqueBytes r.spkSigTerm, 0⟩),
   (lastResortKyberPreKeyFile r.kpkId, SignedPreKeyRecordStructure.encode
      ⟨r.kpkId, kyberKey (r.opaqueBytes r.pqpkPubTerm), kyberKey (r.kyberSecB.drop 1),
        r.opaqueBytes r.pqpkSigTerm, 0⟩),
   (baseKeysFile r.kpkId, [])] ++
  (if r.withOpk then
    [(oneTimePreKeyFile r.opkId, PreKeyRecordStructure.encode
      ⟨r.opkId, ecKey (pubBytes interp r.opkSecBytes), r.opkSecBytes⟩)]
   else [])

/-- Initial directory snapshot for each participant (`commonFiles` for Alice, `commonFiles ++
bobPreKeyFiles` for Bob, empty otherwise). -/
def initDirs (interp : ExternInterpretation) (r : ProtocolSetup) (p : Participant) : DirectorySnapshot :=
  if p = r.alice then filesOf (commonFiles interp r p)
  else if p = r.bob then filesOf (commonFiles interp r p ++ bobPreKeyFiles interp r)
  else fun _ => none

end DY.Libsignal.Composed.Refinement.Cli
