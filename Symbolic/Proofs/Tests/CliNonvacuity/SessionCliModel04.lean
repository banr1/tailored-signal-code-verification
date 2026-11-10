/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Defs

/-!
# Flat CLI Model Step Equations for Multi-Turn Sessions, Calls 0..4

Provides closed-form `PqParty` and `PreKeyMessageFields` states for Calls 0..4 (`alice init`,
`alice send m0`, `alice send m1`, `bob recv m0`, `bob recv m1 [promote]`) so each model equation
checks in isolation without nested `unwrapOut` unfolding, together with universal
`UnreachedPqxdhPrimitives` independence (`call0_model_X`, `call3_model_X`, `call4_model_X`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel04

set_option maxRecDepth 200000

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (pubBytes secretBytes setupPublic)
open DY.Libsignal.Composed.Refinement.Cli (idSecret peerIdSecret regIdOf)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.E2E
  (PreKeyBundleFields PreKeyMessageFields ResponderPreKeySecrets RecordExtras UnreachedPqxdhPrimitives initiateState recvPrekeyState
   keyPairOf wirePrekey)
open CryptoVerification.SignalSession
  (PqParty pqInitModel pqSendModel pqRecvPrekeyModel PqSessionMatches markKyberUsed)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers (nvX)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myParams myInterp myHooks_agree pt0 pt1 myKyberPubBytes mkRecords mkRecords_wf
   mkRecords_opaqueBytes_6)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
  (r0 stA_init stB_init bE tapeInitBytes tapeInit cSend0 cSend1 rc3Bytes rc4Bytes rc3 rc4)
open Symbolic.Swarm.CREF.Cli
  (initPqParty partyOf bytesToVec_toList_of_len pubBytes_eq_keyPairOf_of_modelAgree)
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)

/-! ## Key Vectors and Initial States (`stA0_cli`, `stB0_cli`, `bE_cli`) -/

def idPubA_vec : List.Vector (BitVec 8) 32 :=
  ⟨[11#8] ++ List.replicate 24 1#8 ++ List.replicate 7 0#8, rfl⟩

def idPubB_vec : List.Vector (BitVec 8) 32 :=
  ⟨[11#8] ++ List.replicate 24 6#8 ++ List.replicate 7 0#8, rfl⟩

def spkPubB_vec : List.Vector (BitVec 8) 32 :=
  ⟨[19#8] ++ List.replicate 24 11#8 ++ List.replicate 7 0#8, rfl⟩

def basePubA_vec : List.Vector (BitVec 8) 32 :=
  ⟨[27#8] ++ List.replicate 24 23#8 ++ List.replicate 7 0#8, rfl⟩

def ephPubA1_vec : List.Vector (BitVec 8) 32 :=
  ⟨[35#8] ++ List.replicate 24 25#8 ++ List.replicate 7 0#8, rfl⟩

def ephPrivA1_vec : List.Vector (BitVec 8) 32 :=
  ⟨[24#8] ++ List.replicate 30 25#8 ++ [89#8], rfl⟩

def ephPubB1_vec : List.Vector (BitVec 8) 32 :=
  ⟨[51#8] ++ List.replicate 24 46#8 ++ List.replicate 7 0#8, rfl⟩

def ephPrivB1_vec : List.Vector (BitVec 8) 32 :=
  ⟨[40#8] ++ List.replicate 30 46#8 ++ [110#8], rfl⟩

def kpkPub_vec : List.Vector (BitVec 8) 1568 :=
  List.Vector.replicate 1568 0x77#8

def kpkSec_vec : List.Vector (BitVec 8) 3168 :=
  ⟨List.replicate 1536 0#8 ++ List.replicate 1568 0x77#8 ++ List.replicate 64 0#8, rfl⟩

def kyberCt_vec : List.Vector (BitVec 8) 1568 :=
  ⟨[161#8] ++ List.replicate 32 24#8 ++ List.replicate 32 119#8 ++ List.replicate 1503 0#8, rfl⟩

def stA0_cli : PqParty where
  party := .A
  me := ⟨List.Vector.replicate 32 1#8, 10#32⟩
  peerId := some ⟨⟨idPubB_vec⟩⟩
  session := none
  signed := []
  oneTime := []
  kyberOneTime := []
  kyberLastResort := []

def stB0_cli : PqParty where
  party := .B
  me := ⟨List.Vector.replicate 32 6#8, 20#32⟩
  peerId := some ⟨⟨idPubA_vec⟩⟩
  session := none
  signed := [(1#32, ⟨List.Vector.replicate 32 11#8, List.Vector.replicate 64 0#8, 0⟩)]
  oneTime := []
  kyberOneTime := []
  kyberLastResort :=
    [(2#32, ⟨kpkPub_vec, kpkSec_vec, List.Vector.replicate 64 0#8, 0⟩, [])]

def bE_cli : PreKeyBundleFields where
  regId := 20#32
  spkId := 1#32
  spkPub := spkPubB_vec
  spkSig := List.Vector.replicate 64 0#8
  kpkId := 2#32
  kpkPub := kpkPub_vec
  kpkSig := List.Vector.replicate 64 0#8
  idPub := idPubB_vec
  opk := none

theorem keyToBytes32_rc3 : CryptoGames.HMAC.keyToBytes32 rc3 = rc3Bytes := by decide
theorem keyToBytes32_rc4 : CryptoGames.HMAC.keyToBytes32 rc4 = rc4Bytes := by decide

theorem r0_opaque5 : r0.opaqueBytes (setupPublic r0 5) = List.replicate 64 0#8 := by
  have h5 := (mkRecords_wf false).2.2.2.1
  dsimp only [r0, mkRecords, DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm] at h5 ⊢
  split_ifs at h5 ⊢
  · rw [myKyberPubBytes, List.length_replicate] at h5; cases h5
  · rfl

theorem r0_opaque6 : r0.opaqueBytes (setupPublic r0 6) = List.replicate 1568 0x77#8 :=
  mkRecords_opaqueBytes_6 false

theorem r0_opaque7 : r0.opaqueBytes (setupPublic r0 7) = List.replicate 64 0#8 := by
  have h7 := (mkRecords_wf false).2.2.2.2.2.1
  dsimp only [r0, mkRecords, DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm] at h7 ⊢
  split_ifs at h7 ⊢
  · rw [myKyberPubBytes, List.length_replicate] at h7; cases h7
  · rfl

private theorem pubBytes_myInterp_eq {bs : HwBytes} (hlen : bs.length = 32) :
    pubBytes myInterp bs =
      (keyPairOf myParams.C (bytesToVec 32 bs)).publicKey.bytes.toList := by
  have hv : (bytesToVec 32 bs).toList = bs := bytesToVec_toList_of_len hlen
  have hAg : DY.Libsignal.Composed.Refinement.Cli.ModelAgree myInterp myParams := myHooks_agree
  conv_lhs => rw [← hv]
  exact pubBytes_eq_keyPairOf_of_modelAgree hAg (bytesToVec 32 bs)

private theorem bytesToVec_pubBytes_myInterp {bs : HwBytes} (hlen : bs.length = 32) :
    bytesToVec 32 (pubBytes myInterp bs) =
      (keyPairOf myParams.C (bytesToVec 32 bs)).publicKey.bytes := by
  rw [pubBytes_myInterp_eq hlen]
  apply Subtype.ext
  change (bytesToVec 32 (keyPairOf myParams.C (bytesToVec 32 bs)).publicKey.bytes.toList).toList =
    (keyPairOf myParams.C (bytesToVec 32 bs)).publicKey.bytes.toList
  exact bytesToVec_toList_of_len (List.Vector.toList_length _)

private theorem bytesToVec_replicate (n : Nat) (x : BitVec 8) :
    bytesToVec n (List.replicate n x) = List.Vector.replicate n x := by
  apply Subtype.ext
  exact bytesToVec_toList_of_len (List.length_replicate ..)

private theorem bytesToVec_kpkSec :
    bytesToVec 3168 (r0.kyberSecB.drop 1) = kpkSec_vec := by
  apply Subtype.ext
  have hd : r0.kyberSecB.drop 1 = kpkSec_vec.toList := rfl
  rw [hd]
  exact bytesToVec_toList_of_len (List.Vector.toList_length _)

theorem kp_idA :
    (keyPairOf myParams.C (List.Vector.replicate 32 1#8)).publicKey.bytes = idPubA_vec := by
  decide +kernel

theorem kp_idB :
    (keyPairOf myParams.C (List.Vector.replicate 32 6#8)).publicKey.bytes = idPubB_vec := by
  decide +kernel

theorem kp_spkB :
    (keyPairOf myParams.C (List.Vector.replicate 32 11#8)).publicKey.bytes = spkPubB_vec := by
  decide +kernel

private theorem idPubA_eq :
    bytesToVec 32 (pubBytes myInterp (List.replicate 32 1#8)) = idPubA_vec := by
  rw [bytesToVec_pubBytes_myInterp (List.length_replicate ..), bytesToVec_replicate]
  exact kp_idA

private theorem idPubB_eq :
    bytesToVec 32 (pubBytes myInterp (List.replicate 32 6#8)) = idPubB_vec := by
  rw [bytesToVec_pubBytes_myInterp (List.length_replicate ..), bytesToVec_replicate]
  exact kp_idB

private theorem spkPubB_eq :
    bytesToVec 32 (pubBytes myInterp (List.replicate 32 11#8)) = spkPubB_vec := by
  rw [bytesToVec_pubBytes_myInterp (List.length_replicate ..), bytesToVec_replicate]
  exact kp_spkB

theorem r0_secretBytes_eq (k : Nat) :
    secretBytes r0 k =
      (([(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)][k]?).map fun p =>
        r0.fresh p.1 p.2).getD [] := by
  unfold secretBytes
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r0 (mkRecords_wf false).1,
      show r0.withOpk = false from rfl]
  simp

theorem stA_init_eq : stA_init = stA0_cli := by
  unfold stA_init initPqParty stA0_cli
  have ha : ("alice" = r0.alice) := rfl
  have hid : idSecret r0 "alice" = List.replicate 32 1#8 := by
    unfold idSecret DY.Libsignal.Composed.Refinement.ProtocolSetup.ikASecBytes
    simp only [ha, ↓reduceIte, r0_secretBytes_eq]; rfl
  have hpid : peerIdSecret r0 "alice" = List.replicate 32 6#8 := by
    unfold peerIdSecret DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecBytes
    simp only [ha, ↓reduceIte, r0_secretBytes_eq]; rfl
  have hp : partyOf r0 "alice" = .A := rfl
  have hreg : regIdOf r0 "alice" = 10#32 := rfl
  rw [hp, hid, hreg, hpid]
  simp only [ha, ↓reduceIte, idPubB_eq, bytesToVec_replicate]

theorem stB_init_eq : stB_init = stB0_cli := by
  unfold stB_init initPqParty stB0_cli kpkPub_vec
  have hne : ("bob" : String) ≠ r0.alice := by show "bob" ≠ "alice"; decide
  have hid : idSecret r0 "bob" = List.replicate 32 6#8 := by
    unfold idSecret DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecBytes
    simp only [hne, ↓reduceIte, r0_secretBytes_eq]; rfl
  have hpid : peerIdSecret r0 "bob" = List.replicate 32 1#8 := by
    unfold peerIdSecret DY.Libsignal.Composed.Refinement.ProtocolSetup.ikASecBytes
    simp only [hne, ↓reduceIte, r0_secretBytes_eq]; rfl
  have hp : partyOf r0 "bob" = .B := rfl
  have hreg : regIdOf r0 "bob" = 20#32 := rfl
  have hsec2 : secretBytes r0 2 = List.replicate 32 11#8 := by
    rw [r0_secretBytes_eq]; rfl
  rw [hp, hid, hreg, hpid]
  simp only [hne, ↓reduceIte, Bool.false_eq_true,
    (show r0.withOpk = false from rfl),
    (show r0.spkId = 1#32 from rfl),
    (show r0.kpkId = 2#32 from rfl),
    hsec2, r0_opaque5, r0_opaque6, r0_opaque7, bytesToVec_kpkSec, idPubA_eq, bytesToVec_replicate]

theorem bE_eq : bE = bE_cli := by
  unfold bE bE_cli kpkPub_vec
  have hsec1 : secretBytes r0 1 = List.replicate 32 6#8 := by
    rw [r0_secretBytes_eq]; rfl
  have hsec2 : secretBytes r0 2 = List.replicate 32 11#8 := by
    rw [r0_secretBytes_eq]; rfl
  simp only [(show r0.regIdB = 20#32 from rfl),
    (show r0.spkId = 1#32 from rfl),
    (show r0.kpkId = 2#32 from rfl),
    hsec1, hsec2, r0_opaque5, r0_opaque6, r0_opaque7,
    idPubB_eq, spkPubB_eq, bytesToVec_replicate]

/-! ## Closed-Form States and Messages for Calls 0..4 -/

def x_A : RecordExtras :=
  { pending := ⟨none, 1#32, ⟨basePubA_vec⟩, 0#64⟩
    kyber := some ⟨2#32, [8#8] ++ kyberCt_vec.1⟩
    remoteRegistrationId := 20#32
    localRegistrationId := 10#32
    aliceBaseKey := [5#8] ++ basePubA_vec.1 }

def x_B : RecordExtras :=
  { pending := ⟨none, 0#32, ⟨basePubA_vec⟩, 0#64⟩
    kyber := none
    remoteRegistrationId := 10#32
    localRegistrationId := 20#32
    aliceBaseKey := [5#8] ++ basePubA_vec.1 }

def rk_A1 : BitVec 256 :=
  0x9b7845d69807b8241a3122595a64270bf3bc0a6f17cfb0f595c469ce60e5e0d4#256
def sck_A1 : BitVec 256 :=
  0x246bb4190f60e2c3676076e2d82274dd4ed6bf9426b2ee80e8e62f66e22ca43#256
def sck_A2 : BitVec 256 :=
  0xeaac70d8a9f9c96e923f532733b80ad0e302175ab0fdd431e2fcf90a5a8c7d8a#256
def sck_A3 : BitVec 256 :=
  0xed39e2b1ed41bc153619e44220184550fc355f51c6fc4203c8abc465a4bc2856#256
def rck_A0 : BitVec 256 :=
  0xa71702ed76c97e891f3a9ae769414a4936a4119a2b6696cd600ab7789b0cd08d#256

def rk_B1 : BitVec 256 :=
  0x6d78dda759e69e46e728e19603586a1aeb368482c69902a8b5fd661bb7fc8256#256
def sck_B1 : BitVec 256 :=
  0x5af28a08d87036667f1fda19854e39c37d8972e145fa5496ce2990150eaa4b61#256

def pqA_epoch (idx : BitVec 8) : HwBytes :=
  [26#8, 185#8, 29#8, 18#8, 182#8, 29#8, 10#8, 174#8, 28#8, 8#8, 1#8, 18#8, 68#8, 10#8, 32#8,
   84#8, 23#8, 108#8, 27#8, 237#8, 144#8, 216#8, 24#8, 60#8, 142#8, 216#8, 7#8, 82#8, 250#8, 7#8,
   63#8, 224#8, 207#8, 43#8, 209#8, 29#8, 78#8, 172#8, 43#8, 156#8, 25#8, 146#8, 51#8, 175#8,
   93#8, 11#8, 220#8, 18#8, 32#8, 203#8, 136#8, 114#8, 125#8, 69#8, 175#8, 141#8, 50#8, 39#8,
   144#8, 231#8, 254#8, 49#8, 144#8, 181#8, 205#8, 47#8, 242#8, 73#8, 194#8, 73#8, 114#8, 136#8,
   21#8, 203#8, 102#8, 20#8, 163#8, 108#8, 127#8, 216#8, 202#8, 26#8, 128#8, 9#8] ++
    List.replicate 1152 0#8 ++
    [34#8, 224#8, 18#8] ++ List.replicate 2400 0#8 ++
    [18#8, 130#8, 1#8, 8#8, idx,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 93#8, 130#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 204#8, 1#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 16#8, 183#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 82#8, 210#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 106#8, 68#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 139#8, 102#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 30#8, 119#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 158#8, 197#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 187#8, 212#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 215#8, 156#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 41#8, 140#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 254#8, 17#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 141#8, 227#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 26#8, 63#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 100#8, 77#8,
     18#8, 6#8, 0#8, 0#8, 0#8, 0#8, 229#8, 8#8]

def pqA2_state : HwBytes :=
  [10#8, 38#8, 10#8, 32#8, 200#8, 226#8, 5#8, 241#8, 183#8, 24#8, 161#8, 60#8, 5#8, 66#8, 175#8,
   146#8, 208#8, 130#8, 71#8, 122#8, 111#8, 235#8, 63#8, 179#8, 156#8, 54#8, 191#8, 224#8, 224#8,
   55#8, 170#8, 208#8, 218#8, 73#8, 33#8, 214#8, 24#8, 1#8, 34#8, 0#8, 18#8, 112#8, 26#8, 74#8,
   10#8, 36#8, 8#8, 1#8, 18#8, 32#8, 151#8, 65#8, 145#8, 224#8, 133#8, 231#8, 194#8, 225#8, 43#8,
   45#8, 121#8, 215#8, 243#8, 163#8, 231#8, 164#8, 143#8, 194#8, 9#8, 241#8, 94#8, 138#8, 20#8,
   28#8, 217#8, 95#8, 137#8, 193#8, 127#8, 59#8, 56#8, 241#8, 18#8, 34#8, 18#8, 32#8, 103#8,
   251#8, 177#8, 25#8, 59#8, 142#8, 226#8, 7#8, 196#8, 240#8, 237#8, 225#8, 40#8, 28#8, 35#8,
   94#8, 225#8, 252#8, 229#8, 240#8, 165#8, 179#8, 27#8, 194#8, 206#8, 203#8, 16#8, 247#8, 109#8,
   147#8, 34#8, 232#8, 34#8, 32#8, 181#8, 221#8, 166#8, 22#8, 197#8, 249#8, 63#8, 108#8, 136#8,
   204#8, 230#8, 39#8, 38#8, 11#8, 160#8, 75#8, 184#8, 114#8, 211#8, 42#8, 209#8, 147#8, 69#8,
   106#8, 4#8, 255#8, 1#8, 224#8, 239#8, 192#8, 86#8, 235#8, 50#8, 0#8] ++ pqA_epoch 1#8

def pqA3_state : HwBytes :=
  [10#8, 38#8, 10#8, 32#8, 200#8, 226#8, 5#8, 241#8, 183#8, 24#8, 161#8, 60#8, 5#8, 66#8, 175#8,
   146#8, 208#8, 130#8, 71#8, 122#8, 111#8, 235#8, 63#8, 179#8, 156#8, 54#8, 191#8, 224#8, 224#8,
   55#8, 170#8, 208#8, 218#8, 73#8, 33#8, 214#8, 24#8, 1#8, 34#8, 0#8, 18#8, 112#8, 26#8, 74#8,
   10#8, 36#8, 8#8, 2#8, 18#8, 32#8, 231#8, 196#8, 189#8, 214#8, 120#8, 18#8, 79#8, 223#8, 65#8,
   60#8, 55#8, 86#8, 177#8, 8#8, 227#8, 107#8, 147#8, 122#8, 109#8, 53#8, 209#8, 127#8, 229#8,
   199#8, 238#8, 177#8, 196#8, 165#8, 224#8, 160#8, 125#8, 62#8, 18#8, 34#8, 18#8, 32#8, 103#8,
   251#8, 177#8, 25#8, 59#8, 142#8, 226#8, 7#8, 196#8, 240#8, 237#8, 225#8, 40#8, 28#8, 35#8,
   94#8, 225#8, 252#8, 229#8, 240#8, 165#8, 179#8, 27#8, 194#8, 206#8, 203#8, 16#8, 247#8, 109#8,
   147#8, 34#8, 232#8, 34#8, 32#8, 181#8, 221#8, 166#8, 22#8, 197#8, 249#8, 63#8, 108#8, 136#8,
   204#8, 230#8, 39#8, 38#8, 11#8, 160#8, 75#8, 184#8, 114#8, 211#8, 42#8, 209#8, 147#8, 69#8,
   106#8, 4#8, 255#8, 1#8, 224#8, 239#8, 192#8, 86#8, 235#8, 50#8, 0#8] ++ pqA_epoch 2#8

def g_A1 : GhostState HwBytes :=
  ⟨.A,
    { sessionVersion := 4#32
      localIdentity := ⟨⟨idPubA_vec⟩⟩
      remoteIdentity := some ⟨⟨idPubB_vec⟩⟩
      rootKey := rk_A1
      previousCounter := 0#32
      senderChain := some ⟨⟨⟨ephPubA1_vec⟩, ⟨ephPrivA1_vec⟩⟩, ⟨sck_A1, 0#32⟩⟩
      receiverChains := [⟨⟨spkPubB_vec⟩, some ⟨rck_A0, 0#32⟩, []⟩]
      pendingPreKey := true
      pqRatchetState :=
        [10#8, 38#8, 10#8, 32#8, 200#8, 226#8, 5#8, 241#8, 183#8, 24#8, 161#8, 60#8, 5#8, 66#8,
         175#8, 146#8, 208#8, 130#8, 71#8, 122#8, 111#8, 235#8, 63#8, 179#8, 156#8, 54#8, 191#8,
         224#8, 224#8, 55#8, 170#8, 208#8, 218#8, 73#8, 33#8, 214#8, 24#8, 1#8, 34#8, 0#8, 26#8,
         76#8, 10#8, 74#8, 10#8, 72#8, 8#8, 1#8, 18#8, 68#8, 10#8, 32#8, 84#8, 23#8, 108#8, 27#8,
         237#8, 144#8, 216#8, 24#8, 60#8, 142#8, 216#8, 7#8, 82#8, 250#8, 7#8, 63#8, 224#8, 207#8,
         43#8, 209#8, 29#8, 78#8, 172#8, 43#8, 156#8, 25#8, 146#8, 51#8, 175#8, 93#8, 11#8, 220#8,
         18#8, 32#8, 203#8, 136#8, 114#8, 125#8, 69#8, 175#8, 141#8, 50#8, 39#8, 144#8, 231#8,
         254#8, 49#8, 144#8, 181#8, 205#8, 47#8, 242#8, 73#8, 194#8, 73#8, 114#8, 136#8, 21#8,
         203#8, 102#8, 20#8, 163#8, 108#8, 127#8, 216#8, 202#8] },
    0, [0]⟩

def g_A2 : GhostState HwBytes :=
  ⟨.A,
    { g_A1.session with
      senderChain := some ⟨⟨⟨ephPubA1_vec⟩, ⟨ephPrivA1_vec⟩⟩, ⟨sck_A2, 1#32⟩⟩
      pqRatchetState := pqA2_state },
    0, [0]⟩

def g_A3 : GhostState HwBytes :=
  ⟨.A,
    { g_A1.session with
      senderChain := some ⟨⟨⟨ephPubA1_vec⟩, ⟨ephPrivA1_vec⟩⟩, ⟨sck_A3, 2#32⟩⟩
      pqRatchetState := pqA3_state },
    0, [0]⟩

def stA1_cli : PqParty := { stA0_cli with peerId := some ⟨⟨idPubB_vec⟩⟩, session := some (x_A, g_A1) }
def stA2_cli : PqParty := { stA0_cli with peerId := some ⟨⟨idPubB_vec⟩⟩, session := some (x_A, g_A2) }
def stA3_cli : PqParty := { stA0_cli with peerId := some ⟨⟨idPubB_vec⟩⟩, session := some (x_A, g_A3) }

def pkAddrField : HwBytes :=
  [50#8, 36#8, 0#8, 138#8, 111#8, 28#8, 46#8, 59#8, 77#8, 78#8, 95#8, 154#8, 11#8, 28#8, 45#8,
   62#8, 79#8, 90#8, 107#8, 1#8, 0#8, 93#8, 62#8, 47#8, 16#8, 122#8, 139#8, 76#8, 157#8, 142#8,
   15#8, 161#8, 178#8, 195#8, 212#8, 229#8, 246#8, 1#8]

def pkMsg0 : PreKeyMessageFields where
  regId := 10#32
  opkId := none
  spkId := 1#32
  kpkId := 2#32
  kyberCt := kyberCt_vec
  baseKey := basePubA_vec
  idPub := idPubA_vec
  inner :=
    [68#8, 10#8, 33#8, 5#8] ++ ephPubA1_vec.1 ++
      [16#8, 0#8, 24#8, 0#8, 34#8, 16#8, 126#8, 2#8, 71#8, 242#8, 213#8, 6#8, 230#8, 110#8,
       16#8, 104#8, 140#8, 236#8, 103#8, 26#8, 124#8, 144#8, 42#8, 37#8, 1#8, 1#8, 1#8, 1#8] ++
      List.replicate 33 0#8 ++ pkAddrField ++
      [230#8, 100#8, 190#8, 150#8, 227#8, 197#8, 188#8, 106#8]

def pkMsg1 : PreKeyMessageFields where
  regId := 10#32
  opkId := none
  spkId := 1#32
  kpkId := 2#32
  kyberCt := kyberCt_vec
  baseKey := basePubA_vec
  idPub := idPubA_vec
  inner :=
    [68#8, 10#8, 33#8, 5#8] ++ ephPubA1_vec.1 ++
      [16#8, 1#8, 24#8, 0#8, 34#8, 16#8, 185#8, 108#8, 101#8, 235#8, 153#8, 103#8, 202#8, 216#8,
       27#8, 48#8, 219#8, 47#8, 76#8, 75#8, 11#8, 50#8, 42#8, 37#8, 1#8, 1#8, 2#8, 1#8, 1#8] ++
      List.replicate 32 0#8 ++ pkAddrField ++
      [245#8, 130#8, 109#8, 233#8, 52#8, 106#8, 68#8, 0#8]

def wire0 : HwBytes := wirePrekey :: pkMsg0.bytes
def wire1 : HwBytes := wirePrekey :: pkMsg1.bytes

def pqB2_state : HwBytes :=
  [18#8, 114#8, 8#8, 1#8, 26#8, 74#8, 10#8, 34#8, 18#8, 32#8, 103#8, 251#8, 177#8, 25#8, 59#8,
   142#8, 226#8, 7#8, 196#8, 240#8, 237#8, 225#8, 40#8, 28#8, 35#8, 94#8, 225#8, 252#8, 229#8,
   240#8, 165#8, 179#8, 27#8, 194#8, 206#8, 203#8, 16#8, 247#8, 109#8, 147#8, 34#8, 232#8, 18#8,
   36#8, 8#8, 2#8, 18#8, 32#8, 231#8, 196#8, 189#8, 214#8, 120#8, 18#8, 79#8, 223#8, 65#8, 60#8,
   55#8, 86#8, 177#8, 8#8, 227#8, 107#8, 147#8, 122#8, 109#8, 53#8, 209#8, 127#8, 229#8, 199#8,
   238#8, 177#8, 196#8, 165#8, 224#8, 160#8, 125#8, 62#8, 34#8, 32#8, 181#8, 221#8, 166#8, 22#8,
   197#8, 249#8, 63#8, 108#8, 136#8, 204#8, 230#8, 39#8, 38#8, 11#8, 160#8, 75#8, 184#8, 114#8,
   211#8, 42#8, 209#8, 147#8, 69#8, 106#8, 4#8, 255#8, 1#8, 224#8, 239#8, 192#8, 86#8, 235#8,
   50#8, 0#8, 26#8, 244#8, 1#8, 50#8, 241#8, 1#8, 10#8, 72#8, 8#8, 1#8, 18#8, 68#8, 10#8, 32#8,
   84#8, 23#8, 108#8, 27#8, 237#8, 144#8, 216#8, 24#8, 60#8, 142#8, 216#8, 7#8, 82#8, 250#8, 7#8,
   63#8, 224#8, 207#8, 43#8, 209#8, 29#8, 78#8, 172#8, 43#8, 156#8, 25#8, 146#8, 51#8, 175#8,
   93#8, 11#8, 220#8, 18#8, 32#8, 203#8, 136#8, 114#8, 125#8, 69#8, 175#8, 141#8, 50#8, 39#8,
   144#8, 231#8, 254#8, 49#8, 144#8, 181#8, 205#8, 47#8, 242#8, 73#8, 194#8, 73#8, 114#8, 136#8,
   21#8, 203#8, 102#8, 20#8, 163#8, 108#8, 127#8, 216#8, 202#8, 18#8, 164#8, 1#8, 8#8, 48#8,
   16#8, 16#8] ++
    (List.replicate 16 ([26#8, 8#8] ++ List.replicate 5 0#8 ++ [1#8, 0#8, 0#8])).flatten

def g_B1 : GhostState HwBytes :=
  ⟨.B,
    { sessionVersion := 4#32
      localIdentity := ⟨⟨idPubB_vec⟩⟩
      remoteIdentity := some ⟨⟨idPubA_vec⟩⟩
      rootKey := rk_B1
      previousCounter := 0#32
      senderChain := some ⟨⟨⟨ephPubB1_vec⟩, ⟨ephPrivB1_vec⟩⟩, ⟨sck_B1, 0#32⟩⟩
      receiverChains := [⟨⟨ephPubA1_vec⟩, some ⟨sck_A2, 1#32⟩, []⟩]
      pendingPreKey := false
      pqRatchetState :=
        [18#8, 114#8, 8#8, 1#8, 26#8, 74#8, 10#8, 34#8, 18#8, 32#8, 103#8, 251#8, 177#8, 25#8,
         59#8, 142#8, 226#8, 7#8, 196#8, 240#8, 237#8, 225#8, 40#8, 28#8, 35#8, 94#8, 225#8,
         252#8, 229#8, 240#8, 165#8, 179#8, 27#8, 194#8, 206#8, 203#8, 16#8, 247#8, 109#8, 147#8,
         34#8, 232#8, 18#8, 36#8, 8#8, 1#8, 18#8, 32#8, 151#8, 65#8, 145#8, 224#8, 133#8, 231#8,
         194#8, 225#8, 43#8, 45#8, 121#8, 215#8, 243#8, 163#8, 231#8, 164#8, 143#8, 194#8, 9#8,
         241#8, 94#8, 138#8, 20#8, 28#8, 217#8, 95#8, 137#8, 193#8, 127#8, 59#8, 56#8, 241#8,
         34#8, 32#8, 181#8, 221#8, 166#8, 22#8, 197#8, 249#8, 63#8, 108#8, 136#8, 204#8, 230#8,
         39#8, 38#8, 11#8, 160#8, 75#8, 184#8, 114#8, 211#8, 42#8, 209#8, 147#8, 69#8, 106#8, 4#8,
         255#8, 1#8, 224#8, 239#8, 192#8, 86#8, 235#8, 50#8, 0#8, 26#8, 179#8, 1#8, 50#8, 176#8,
         1#8, 10#8, 72#8, 8#8, 1#8, 18#8, 68#8, 10#8, 32#8, 84#8, 23#8, 108#8, 27#8, 237#8, 144#8,
         216#8, 24#8, 60#8, 142#8, 216#8, 7#8, 82#8, 250#8, 7#8, 63#8, 224#8, 207#8, 43#8, 209#8,
         29#8, 78#8, 172#8, 43#8, 156#8, 25#8, 146#8, 51#8, 175#8, 93#8, 11#8, 220#8, 18#8, 32#8,
         203#8, 136#8, 114#8, 125#8, 69#8, 175#8, 141#8, 50#8, 39#8, 144#8, 231#8, 254#8, 49#8,
         144#8, 181#8, 205#8, 47#8, 242#8, 73#8, 194#8, 73#8, 114#8, 136#8, 21#8, 203#8, 102#8,
         20#8, 163#8, 108#8, 127#8, 216#8, 202#8, 18#8, 100#8, 8#8, 48#8, 16#8, 16#8] ++
          (List.replicate 16 ([26#8, 4#8] ++ List.replicate 4 0#8)).flatten },
    1, [1]⟩

def g_B2 : GhostState HwBytes :=
  ⟨.B,
    { g_B1.session with
      receiverChains := [⟨⟨ephPubA1_vec⟩, some ⟨sck_A3, 2#32⟩, []⟩]
      pqRatchetState := pqB2_state },
    1, [1]⟩

def stB0Marked : PqParty :=
  { stB0_cli with
    kyberLastResort :=
      [(2#32, ⟨kpkPub_vec, kpkSec_vec, List.Vector.replicate 64 0#8, 0⟩,
        [(1#32, basePubA_vec)])] }

def stB1_cli : PqParty :=
  { stB0Marked with peerId := some ⟨⟨idPubA_vec⟩⟩, session := some (x_B, g_B1) }

def stB2_cli : PqParty :=
  { stB0Marked with peerId := some ⟨⟨idPubA_vec⟩⟩, session := some (x_B, g_B2) }

/-! ## Model Step Proofs and `UnreachedPqxdhPrimitives` Independence for Calls 0..4 -/

attribute [local semireducible] CryptoVerification.LibsignalSpqrV1.MlKem.fromSeed

theorem initiateState_indep (X₁ X₂ : UnreachedPqxdhPrimitives) :
    initiateState X₁ = initiateState X₂ := by
  funext W P me b t
  rfl

theorem recvPrekeyState_indep (X₁ X₂ : UnreachedPqxdhPrimitives) :
    recvPrekeyState X₁ = recvPrekeyState X₂ := by
  funext W P me k m rc
  rfl

theorem pqInitModel_indep (X₁ X₂ : UnreachedPqxdhPrimitives) :
    pqInitModel X₁ = pqInitModel X₂ := by
  funext W st b t
  unfold pqInitModel
  rw [initiateState_indep X₁ X₂]

theorem pqRecvPrekeyModel_indep (X₁ X₂ : UnreachedPqxdhPrimitives) :
    pqRecvPrekeyModel X₁ = pqRecvPrekeyModel X₂ := by
  funext W st m rc
  unfold pqRecvPrekeyModel
  rw [recvPrekeyState_indep X₁ X₂]

def reprParty : CryptoGames.Party → Bool
  | .A => false
  | .B => true

theorem reprParty_inj {a b : CryptoGames.Party} (h : reprParty a = reprParty b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

def reprRecordExtras (x : RecordExtras) :=
  ((x.pending.1, x.pending.2, x.pending.3.bytes.1, x.pending.4),
   x.kyber.map (fun k => (k.1, @id (List (BitVec 8)) k.2)),
   x.remoteRegistrationId, x.localRegistrationId, @id (List (BitVec 8)) x.aliceBaseKey)

theorem reprRecordExtras_inj {a b : RecordExtras}
    (h : reprRecordExtras a = reprRecordExtras b) : a = b := by
  rcases a with ⟨⟨p1, p2, ⟨pb⟩, p4⟩, kyA, rA, lA, bkA⟩
  rcases b with ⟨⟨q1, q2, ⟨qb⟩, q4⟩, kyB, rB, lB, bkB⟩
  simp only [reprRecordExtras, id_eq, Prod.mk.injEq] at h
  rcases h with ⟨⟨rfl, rfl, hpb, rfl⟩, hky, rfl, rfl, rfl⟩
  cases Subtype.ext hpb
  congr 1
  cases kyA with
  | none => cases kyB with | none => rfl | some _ => cases hky
  | some ka =>
    cases kyB with
    | none => cases hky
    | some kb =>
      rcases ka with ⟨i1, c1⟩; rcases kb with ⟨i2, c2⟩
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hky
      rcases hky with ⟨rfl, rfl⟩; rfl

def reprKyberKey (k : CryptoVerification.SignalSession.PqKyberKey) :=
  (k.pub.1, k.sec.1, k.sig.1, k.timestamp)

theorem reprKyberKey_inj {a b : CryptoVerification.SignalSession.PqKyberKey}
    (h : reprKyberKey a = reprKyberKey b) : a = b := by
  rcases a with ⟨p1, s1, g1, t1⟩; rcases b with ⟨p2, s2, g2, t2⟩
  simp only [reprKyberKey, Prod.mk.injEq] at h
  rcases h with ⟨hp, hs, hg, rfl⟩
  rw [Subtype.ext hp, Subtype.ext hs, Subtype.ext hg]

def reprSession (s : CryptoGames.LibsignalSession.SessionState CryptoVerification.E2E.Bytes) :=
  (s.sessionVersion, s.localIdentity.publicKey.bytes.1,
   s.remoteIdentity.map (fun k => k.publicKey.bytes.1),
   s.rootKey, s.previousCounter,
   s.senderChain.map (fun sc =>
     ((sc.ratchetKey.publicKey.bytes.1, sc.ratchetKey.privateKey.bytes.1),
      (sc.chainKey.key, sc.chainKey.index))),
   s.receiverChains.map (fun rc =>
     (rc.senderRatchetKey.bytes.1,
      rc.chainKey.map (fun ck => (ck.key, ck.index)),
      rc.messageKeys.map (fun mk => (mk.seed, mk.counter)))),
   s.pendingPreKey, @id (List (BitVec 8)) s.pqRatchetState)

theorem reprSession_inj {a b : CryptoGames.LibsignalSession.SessionState CryptoVerification.E2E.Bytes}
    (h : reprSession a = reprSession b) : a = b := by
  rcases a with ⟨sv1, ⟨⟨li1⟩⟩, ri1, rk1, pc1, sc1, rc1, pp1, pq1⟩
  rcases b with ⟨sv2, ⟨⟨li2⟩⟩, ri2, rk2, pc2, sc2, rc2, pp2, pq2⟩
  simp only [reprSession, id_eq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, hli, hri, rfl, rfl, hsc, hrc, rfl, hpq⟩
  cases Subtype.ext hli
  have hri' : ri1 = ri2 := by
    refine Option.map_injective ?_ hri
    rintro ⟨⟨v1⟩⟩ ⟨⟨v2⟩⟩ hv; cases Subtype.ext hv; rfl
  have hsc' : sc1 = sc2 := by
    refine Option.map_injective ?_ hsc
    rintro ⟨⟨⟨pub1⟩, ⟨prv1⟩⟩, ⟨ck1, ci1⟩⟩ ⟨⟨⟨pub2⟩, ⟨prv2⟩⟩, ⟨ck2, ci2⟩⟩ hs
    simp only [Prod.mk.injEq] at hs
    rcases hs with ⟨⟨hp1, hp2⟩, rfl, rfl⟩
    rw [Subtype.ext hp1, Subtype.ext hp2]
  have hrc' : rc1 = rc2 := by
    refine List.map_injective_iff.mpr ?_ hrc
    rintro ⟨⟨srk1⟩, ck1, mks1⟩ ⟨⟨srk2⟩, ck2, mks2⟩ hr
    simp only [Prod.mk.injEq] at hr
    rcases hr with ⟨hsrk, hck, hmks⟩
    have hck' : ck1 = ck2 := by
      refine Option.map_injective ?_ hck
      rintro ⟨k1, i1⟩ ⟨k2, i2⟩ hc
      simp only [Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩; rfl
    have hmks' : mks1 = mks2 := by
      refine List.map_injective_iff.mpr ?_ hmks
      rintro ⟨sd1, ct1⟩ ⟨sd2, ct2⟩ hm
      simp only [Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩; rfl
    rw [Subtype.ext hsrk, hck', hmks']
  have hpq' : pq1 = pq2 := hpq
  rw [hri', hsc', hrc', hpq']

def reprPqParty (st : PqParty) :=
  (reprParty st.party, (st.me.1.1, st.me.2), st.peerId.map (fun k => k.publicKey.bytes.1),
   st.session.map (fun (x, g) =>
     (reprRecordExtras x, reprParty g.party, reprSession g.session, g.epoch, g.chainEpochs)),
   st.signed.map (fun (i, s) => (i, s.priv.1, s.sig.1, s.timestamp)),
   st.oneTime.map (fun (i, o) => (i, o.map fun v : List.Vector (BitVec 8) 32 => v.1)),
   st.kyberOneTime.map (fun (i, o) => (i, o.map reprKyberKey)),
   st.kyberLastResort.map (fun (i, k, s) =>
     (i, reprKyberKey k, s.map fun p : BitVec 32 × List.Vector (BitVec 8) 32 => (p.1, p.2.1))))

theorem reprPqParty_inj {a b : PqParty} (h : reprPqParty a = reprPqParty b) : a = b := by
  rcases a with ⟨pa, ⟨ma1, ma2⟩, pida, sa, sga, ota, kota, klra⟩
  rcases b with ⟨pb, ⟨mb1, mb2⟩, pidb, sb, sgb, otb, kotb, klrb⟩
  simp only [reprPqParty, Prod.mk.injEq] at h
  rcases h with ⟨hp, ⟨hma, rfl⟩, hpid, hsess, hsig, hot, hkot, hklr⟩
  cases reprParty_inj hp
  cases Subtype.ext hma
  have hpid' : pida = pidb := by
    refine Option.map_injective ?_ hpid
    rintro ⟨⟨v1⟩⟩ ⟨⟨v2⟩⟩ hv
    cases Subtype.ext hv; rfl
  have hsess' : sa = sb := by
    refine Option.map_injective ?_ hsess
    rintro ⟨xa, ⟨gpa, gsa, gea, gca⟩⟩ ⟨xb, ⟨gpb, gsb, geb, gcb⟩⟩ heq
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨hx, hgp, hgs, rfl, rfl⟩
    rw [reprRecordExtras_inj hx, reprParty_inj hgp, reprSession_inj hgs]
  have hsig' : sga = sgb := by
    refine List.map_injective_iff.mpr ?_ hsig
    rintro ⟨i1, ⟨pr1, sg1, ts1⟩⟩ ⟨i2, ⟨pr2, sg2, ts2⟩⟩ heq
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, hpr, hsg, rfl⟩
    rw [Subtype.ext hpr, Subtype.ext hsg]
  have hot' : ota = otb := by
    refine List.map_injective_iff.mpr ?_ hot
    rintro ⟨i1, o1⟩ ⟨i2, o2⟩ heq
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, ho⟩
    rw [Option.map_injective (fun _ _ => Subtype.ext) ho]
  have hkot' : kota = kotb := by
    refine List.map_injective_iff.mpr ?_ hkot
    rintro ⟨i1, o1⟩ ⟨i2, o2⟩ heq
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, ho⟩
    rw [Option.map_injective (fun _ _ => reprKyberKey_inj) ho]
  have hklr' : klra = klrb := by
    refine List.map_injective_iff.mpr ?_ hklr
    rintro ⟨i1, k1, l1⟩ ⟨i2, k2, l2⟩ heq
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, hk, hl⟩
    have hl' : l1 = l2 := by
      refine List.map_injective_iff.mpr ?_ hl
      rintro ⟨j1, v1⟩ ⟨j2, v2⟩ hjv
      simp only [Prod.mk.injEq] at hjv
      rcases hjv with ⟨rfl, hv⟩
      rw [Subtype.ext hv]
    rw [reprKyberKey_inj hk, hl']
  rw [hpid', hsess', hsig', hot', hkot', hklr']

def reprOut (r : Option (Option (PqParty × HwBytes))) :=
  r.map (Option.map fun (st, out) => (reprPqParty st, @id (List (BitVec 8)) out))

theorem eq_of_reprOut {a b : Option (Option (PqParty × HwBytes))}
    (h : reprOut a = reprOut b) : a = b := by
  unfold reprOut at h
  refine Option.map_injective ?_ h
  intro x y hxy
  refine Option.map_injective ?_ hxy
  rintro ⟨s1, o1⟩ ⟨s2, o2⟩ hs
  simp only [Prod.mk.injEq, id_eq] at hs
  rw [reprPqParty_inj hs.1, hs.2]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 200000 in
def decReprOut (a b : Option (Option (PqParty × HwBytes))) : Bool :=
  reprOut a == reprOut b

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 200000 in
theorem eq_of_decReprOut {a b : Option (Option (PqParty × HwBytes))}
    (h : decReprOut a b = true) : a = b := by
  unfold decReprOut at h
  exact eq_of_reprOut (eq_of_beq h)

theorem tapeInit_eq : tapeInit = ⟨tapeInitBytes, rfl⟩ := by
  apply List.Vector.eq
  exact bytesToVec_toList_of_len (by decide)

theorem wire0_eq : wire0 = wirePrekey :: pkMsg0.bytes := rfl

theorem wire1_eq : wire1 = wirePrekey :: pkMsg1.bytes := rfl

theorem call0_model :
    pqInitModel nvX myParams stA0_cli bE_cli tapeInit = some (some (stA1_cli, [])) := by
  rw [tapeInit_eq]
  exact eq_of_decReprOut (by decide +kernel)

theorem call0_model_X (X : UnreachedPqxdhPrimitives) :
    pqInitModel X myParams stA0_cli bE_cli tapeInit = some (some (stA1_cli, [])) := by
  rw [pqInitModel_indep X nvX]
  exact call0_model

theorem call1_model :
    pqSendModel myParams stA1_cli pt0 cSend0 = some (some (stA2_cli, wire0)) :=
  eq_of_decReprOut (by decide +kernel)

theorem call2_model :
    pqSendModel myParams stA2_cli pt1 cSend1 = some (some (stA3_cli, wire1)) :=
  eq_of_decReprOut (by decide +kernel)

theorem markKyberUsed_stB0 :
    markKyberUsed stB0_cli pkMsg0 = some stB0Marked := by
  have hko : stB0_cli.kyberOneTime.lookup pkMsg0.kpkId = none := rfl
  have hlr : stB0_cli.kyberLastResort.lookup pkMsg0.kpkId =
      some (⟨kpkPub_vec, kpkSec_vec, List.Vector.replicate 64 0#8, 0⟩, []) := rfl
  unfold markKyberUsed
  rw [hko, hlr]
  simp only [List.not_mem_nil]
  rfl

theorem call3_model :
    pqRecvPrekeyModel nvX myParams stB0_cli pkMsg0 rc3 = some (some (stB1_cli, pt0)) := by
  unfold pqRecvPrekeyModel
  rw [markKyberUsed_stB0]
  exact eq_of_decReprOut (by decide +kernel)

theorem call3_model_X (X : UnreachedPqxdhPrimitives) :
    pqRecvPrekeyModel X myParams stB0_cli pkMsg0 rc3 = some (some (stB1_cli, pt0)) := by
  rw [pqRecvPrekeyModel_indep X nvX]
  exact call3_model

theorem call4_sessionMatches :
    ∀ x g, stB1_cli.session = some (x, g) → PqSessionMatches x g pkMsg1 := by
  intro x g hs
  injection hs with hpair
  cases hpair
  exact ⟨rfl, rfl⟩

theorem call4_model :
    pqRecvPrekeyModel nvX myParams stB1_cli pkMsg1 rc4 = some (some (stB2_cli, pt1)) :=
  eq_of_decReprOut (by decide +kernel)

theorem call4_model_X (X : UnreachedPqxdhPrimitives) :
    pqRecvPrekeyModel X myParams stB1_cli pkMsg1 rc4 = some (some (stB2_cli, pt1)) := by
  rw [pqRecvPrekeyModel_indep X nvX]
  exact call4_model

end Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel04
