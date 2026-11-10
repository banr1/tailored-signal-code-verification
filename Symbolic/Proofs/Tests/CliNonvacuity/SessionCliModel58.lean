/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel04
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Repr
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.SignalSession.Closure.Promote

/-!
# Flat CLI Model Step Equations for Multi-Turn Sessions, Calls 5..8, and `PqxdhPartyInSpecDomain`

Provides closed-form `PqParty` and whisper message states for Calls 5..8 (`bob send reply0`,
`alice recv reply0`, `alice send m2`, `bob recv m2`) together with `PqxdhPartyInSpecDomain` domain
well-formedness witnesses for all party states across Calls 0..8.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel58

set_option maxRecDepth 200000

open DY.Libsignal (HwBytes)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.E2E
  (RecordExtras ReachablePqxdhSession initiateState recvPrekeyState pqxdhSessionParams wireWhisper encodeRecordUnderExtras)
open CryptoVerification.SignalSession
  (PqParty pqInitModel pqSendModel pqRecvPrekeyModel pqRecvWhisperModel PqSessionMatches preKeysNamedBy
   PqxdhPartyInSpecDomain encodeDir signedRecordBytes)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers (nvX)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myParams ptReply0 pt2)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
  (tapeInit cSendReply0 cSend2 rc3 rc4 rc6Bytes rc8Bytes rc6 rc8)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel04
  (idPubA_vec idPubB_vec spkPubB_vec ephPubA1_vec ephPubB1_vec ephPrivB1_vec
   rck_A0 sck_A3 kp_idA kp_idB kp_spkB
   stA0_cli stA1_cli stA2_cli stA3_cli stB0_cli stB0Marked stB1_cli stB2_cli bE_cli
   x_A x_B pqA_epoch g_A1 g_A2 g_A3 g_B1 g_B2 pkMsg0 pkMsg1
   eq_of_decReprOut call0_model call1_model call2_model markKyberUsed_stB0 call3_model
   call4_sessionMatches call4_model)

/-! ## Ratchet Key Vectors and Coin Key Helpers for Calls 5..8 -/

def ephPubA2_vec : List.Vector (BitVec 8) 32 :=
  ⟨[75#8] ++ List.replicate 24 66#8 ++ List.replicate 7 0#8, rfl⟩

def ephPrivA2_vec : List.Vector (BitVec 8) 32 :=
  ⟨[64#8] ++ List.replicate 31 66#8, rfl⟩

def ephPubB2_vec : List.Vector (BitVec 8) 32 :=
  ⟨[91#8] ++ List.replicate 24 84#8 ++ List.replicate 7 0#8, rfl⟩

def ephPrivB2_vec : List.Vector (BitVec 8) 32 :=
  ⟨[80#8] ++ List.replicate 31 84#8, rfl⟩

theorem keyToBytes32_rc6 : CryptoGames.HMAC.keyToBytes32 rc6 = rc6Bytes := by decide
theorem keyToBytes32_rc8 : CryptoGames.HMAC.keyToBytes32 rc8 = rc8Bytes := by decide

/-! ## Closed-Form States and Whisper Messages for Calls 5..8 -/

def sck_B3 : BitVec 256 :=
  0xaf337149e07f41923a7444ac1feac6bcb6a27c7cf0e9105eda7ea8b91f843f1#256
def rk_A4 : BitVec 256 :=
  0xc2cd24a0fbb355b6203518760cc6ce371b4052331586e9f2c4858d9646cd39#256
def sck_A4 : BitVec 256 :=
  0x871f9cac5b68d400b62331f92496252b712abf51102bebd2f581bc625b989b4a#256
def sck_A5 : BitVec 256 :=
  0xc9ace0097dbb7410736cdf98349b351517d1032f194c69255078e84964b6f739#256
def rk_B4 : BitVec 256 :=
  0x53c5b511bd0c367f303c913d406f65e6955ea0f9d518aa964af1df504ef1f28a#256
def sck_B4 : BitVec 256 :=
  0x90134e78a94a2c18e95dc14539edb9686dc817bcc7d1bfc0b47d5cd8252422ef#256

def pqB3_state : HwBytes :=
  [18#8, 116#8, 8#8, 1#8, 26#8, 76#8, 10#8, 36#8, 8#8, 1#8, 18#8, 32#8, 43#8, 215#8, 165#8, 221#8,
   123#8, 241#8, 209#8, 74#8, 174#8, 217#8, 173#8, 141#8, 20#8, 163#8, 202#8, 95#8, 111#8, 227#8,
   43#8, 109#8, 78#8, 175#8, 150#8, 230#8, 36#8, 203#8, 232#8, 139#8, 63#8, 146#8, 116#8, 143#8,
   18#8, 36#8, 8#8, 2#8, 18#8, 32#8, 231#8, 196#8, 189#8, 214#8, 120#8, 18#8, 79#8, 223#8, 65#8,
   60#8, 55#8, 86#8, 177#8, 8#8, 227#8, 107#8, 147#8, 122#8, 109#8, 53#8, 209#8, 127#8, 229#8,
   199#8, 238#8, 177#8, 196#8, 165#8, 224#8, 160#8, 125#8, 62#8, 34#8, 32#8, 181#8, 221#8, 166#8,
   22#8, 197#8, 249#8, 63#8, 108#8, 136#8, 204#8, 230#8, 39#8, 38#8, 11#8, 160#8, 75#8, 184#8,
   114#8, 211#8, 42#8, 209#8, 147#8, 69#8, 106#8, 4#8, 255#8, 1#8, 224#8, 239#8, 192#8, 86#8,
   235#8, 50#8, 0#8, 26#8, 244#8, 1#8, 50#8, 241#8, 1#8, 10#8, 72#8, 8#8, 1#8, 18#8, 68#8, 10#8,
   32#8, 84#8, 23#8, 108#8, 27#8, 237#8, 144#8, 216#8, 24#8, 60#8, 142#8, 216#8, 7#8, 82#8, 250#8,
   7#8, 63#8, 224#8, 207#8, 43#8, 209#8, 29#8, 78#8, 172#8, 43#8, 156#8, 25#8, 146#8, 51#8, 175#8,
   93#8, 11#8, 220#8, 18#8, 32#8, 203#8, 136#8, 114#8, 125#8, 69#8, 175#8, 141#8, 50#8, 39#8,
   144#8, 231#8, 254#8, 49#8, 144#8, 181#8, 205#8, 47#8, 242#8, 73#8, 194#8, 73#8, 114#8, 136#8,
   21#8, 203#8, 102#8, 20#8, 163#8, 108#8, 127#8, 216#8, 202#8, 18#8, 164#8, 1#8, 8#8, 48#8,
   16#8, 16#8] ++
    (List.replicate 16 ([26#8, 8#8] ++ List.replicate 5 0#8 ++ [1#8, 0#8, 0#8])).flatten

def g_B3 : GhostState HwBytes :=
  ⟨.B,
    { g_B2.session with
      senderChain := some ⟨⟨⟨ephPubB1_vec⟩, ⟨ephPrivB1_vec⟩⟩, ⟨sck_B3, 1#32⟩⟩
      pqRatchetState := pqB3_state },
    1, [1]⟩

def stB3_cli : PqParty :=
  { stB0Marked with peerId := some ⟨⟨idPubA_vec⟩⟩, session := some (x_B, g_B3) }

def bodyReply0 : HwBytes :=
  [68#8, 10#8, 33#8, 5#8] ++ ephPubB1_vec.1 ++
    [16#8, 0#8, 24#8, 0#8, 34#8, 16#8, 116#8, 28#8, 164#8, 90#8, 71#8, 201#8, 89#8, 2#8, 217#8,
     184#8, 186#8, 168#8, 21#8, 98#8, 182#8, 66#8, 42#8, 4#8, 1#8, 1#8, 1#8, 0#8, 156#8, 165#8,
     199#8, 240#8, 234#8, 84#8, 36#8, 191#8]

def wireReply0 : HwBytes := wireWhisper :: bodyReply0

def pqA4_state : HwBytes :=
  [18#8, 114#8, 26#8, 76#8, 10#8, 36#8, 8#8, 2#8, 18#8, 32#8, 231#8, 196#8, 189#8, 214#8, 120#8,
   18#8, 79#8, 223#8, 65#8, 60#8, 55#8, 86#8, 177#8, 8#8, 227#8, 107#8, 147#8, 122#8, 109#8, 53#8,
   209#8, 127#8, 229#8, 199#8, 238#8, 177#8, 196#8, 165#8, 224#8, 160#8, 125#8, 62#8, 18#8, 36#8,
   8#8, 1#8, 18#8, 32#8, 43#8, 215#8, 165#8, 221#8, 123#8, 241#8, 209#8, 74#8, 174#8, 217#8,
   173#8, 141#8, 20#8, 163#8, 202#8, 95#8, 111#8, 227#8, 43#8, 109#8, 78#8, 175#8, 150#8, 230#8,
   36#8, 203#8, 232#8, 139#8, 63#8, 146#8, 116#8, 143#8, 34#8, 32#8, 181#8, 221#8, 166#8, 22#8,
   197#8, 249#8, 63#8, 108#8, 136#8, 204#8, 230#8, 39#8, 38#8, 11#8, 160#8, 75#8, 184#8, 114#8,
   211#8, 42#8, 209#8, 147#8, 69#8, 106#8, 4#8, 255#8, 1#8, 224#8, 239#8, 192#8, 86#8, 235#8,
   50#8, 0#8] ++ pqA_epoch 2#8

def pqA5_state : HwBytes :=
  [18#8, 114#8, 26#8, 76#8, 10#8, 36#8, 8#8, 3#8, 18#8, 32#8, 88#8, 102#8, 155#8, 154#8, 185#8,
   43#8, 116#8, 58#8, 30#8, 238#8, 205#8, 142#8, 233#8, 117#8, 2#8, 251#8, 236#8, 233#8, 132#8,
   132#8, 123#8, 146#8, 33#8, 159#8, 242#8, 5#8, 38#8, 104#8, 99#8, 126#8, 106#8, 219#8, 18#8,
   36#8, 8#8, 1#8, 18#8, 32#8, 43#8, 215#8, 165#8, 221#8, 123#8, 241#8, 209#8, 74#8, 174#8, 217#8,
   173#8, 141#8, 20#8, 163#8, 202#8, 95#8, 111#8, 227#8, 43#8, 109#8, 78#8, 175#8, 150#8, 230#8,
   36#8, 203#8, 232#8, 139#8, 63#8, 146#8, 116#8, 143#8, 34#8, 32#8, 181#8, 221#8, 166#8, 22#8,
   197#8, 249#8, 63#8, 108#8, 136#8, 204#8, 230#8, 39#8, 38#8, 11#8, 160#8, 75#8, 184#8, 114#8,
   211#8, 42#8, 209#8, 147#8, 69#8, 106#8, 4#8, 255#8, 1#8, 224#8, 239#8, 192#8, 86#8, 235#8,
   50#8, 0#8] ++ pqA_epoch 3#8

def g_A4 : GhostState HwBytes :=
  ⟨.A,
    { g_A1.session with
      rootKey := rk_A4
      previousCounter := 1#32
      senderChain := some ⟨⟨⟨ephPubA2_vec⟩, ⟨ephPrivA2_vec⟩⟩, ⟨sck_A4, 0#32⟩⟩
      receiverChains :=
        [⟨⟨spkPubB_vec⟩, some ⟨rck_A0, 0#32⟩, []⟩,
         ⟨⟨ephPubB1_vec⟩, some ⟨sck_B3, 1#32⟩, []⟩]
      pendingPreKey := false
      pqRatchetState := pqA4_state },
    0, [0]⟩

def g_A5 : GhostState HwBytes :=
  ⟨.A,
    { g_A4.session with
      senderChain := some ⟨⟨⟨ephPubA2_vec⟩, ⟨ephPrivA2_vec⟩⟩, ⟨sck_A5, 1#32⟩⟩
      pqRatchetState := pqA5_state },
    0, [0]⟩

def stA4_cli : PqParty :=
  { stA0_cli with peerId := some ⟨⟨idPubB_vec⟩⟩, session := some (x_A, g_A4) }

def stA5_cli : PqParty :=
  { stA0_cli with peerId := some ⟨⟨idPubB_vec⟩⟩, session := some (x_A, g_A5) }

def body2 : HwBytes :=
  [68#8, 10#8, 33#8, 5#8] ++ ephPubA2_vec.1 ++
    [16#8, 0#8, 24#8, 1#8, 34#8, 16#8, 190#8, 25#8, 201#8, 163#8, 121#8, 134#8, 120#8, 153#8,
     38#8, 206#8, 1#8, 51#8, 84#8, 189#8, 108#8, 58#8, 42#8, 37#8, 1#8, 1#8, 3#8, 1#8, 2#8, 93#8,
     130#8, 204#8, 1#8, 16#8, 183#8, 82#8, 210#8, 106#8, 68#8, 139#8, 102#8, 30#8, 119#8, 158#8,
     197#8, 187#8, 212#8, 215#8, 156#8, 41#8, 140#8, 254#8, 17#8, 141#8, 227#8, 26#8, 63#8, 100#8,
     77#8, 229#8, 8#8, 13#8, 133#8, 53#8, 156#8, 98#8, 233#8, 59#8, 251#8]

def wire2 : HwBytes := wireWhisper :: body2

def pqB4_state : HwBytes :=
  [18#8, 116#8, 8#8, 1#8, 26#8, 76#8, 10#8, 36#8, 8#8, 1#8, 18#8, 32#8, 43#8, 215#8, 165#8, 221#8,
   123#8, 241#8, 209#8, 74#8, 174#8, 217#8, 173#8, 141#8, 20#8, 163#8, 202#8, 95#8, 111#8, 227#8,
   43#8, 109#8, 78#8, 175#8, 150#8, 230#8, 36#8, 203#8, 232#8, 139#8, 63#8, 146#8, 116#8, 143#8,
   18#8, 36#8, 8#8, 3#8, 18#8, 32#8, 88#8, 102#8, 155#8, 154#8, 185#8, 43#8, 116#8, 58#8, 30#8,
   238#8, 205#8, 142#8, 233#8, 117#8, 2#8, 251#8, 236#8, 233#8, 132#8, 132#8, 123#8, 146#8, 33#8,
   159#8, 242#8, 5#8, 38#8, 104#8, 99#8, 126#8, 106#8, 219#8, 34#8, 32#8, 181#8, 221#8, 166#8,
   22#8, 197#8, 249#8, 63#8, 108#8, 136#8, 204#8, 230#8, 39#8, 38#8, 11#8, 160#8, 75#8, 184#8,
   114#8, 211#8, 42#8, 209#8, 147#8, 69#8, 106#8, 4#8, 255#8, 1#8, 224#8, 239#8, 192#8, 86#8,
   235#8, 50#8, 0#8, 26#8, 183#8, 1#8, 58#8, 180#8, 1#8, 10#8, 138#8, 1#8, 8#8, 1#8, 18#8, 68#8,
   10#8, 32#8, 84#8, 23#8, 108#8, 27#8, 237#8, 144#8, 216#8, 24#8, 60#8, 142#8, 216#8, 7#8, 82#8,
   250#8, 7#8, 63#8, 224#8, 207#8, 43#8, 209#8, 29#8, 78#8, 172#8, 43#8, 156#8, 25#8, 146#8, 51#8,
   175#8, 93#8, 11#8, 220#8, 18#8, 32#8, 203#8, 136#8, 114#8, 125#8, 69#8, 175#8, 141#8, 50#8,
   39#8, 144#8, 231#8, 254#8, 49#8, 144#8, 181#8, 205#8, 47#8, 242#8, 73#8, 194#8, 73#8, 114#8,
   136#8, 21#8, 203#8, 102#8, 20#8, 163#8, 108#8, 127#8, 216#8, 202#8, 26#8, 64#8] ++
    List.replicate 64 0#8 ++
    [18#8, 37#8, 8#8, 192#8, 4#8, 16#8, 16#8] ++
    (List.replicate 16 [26#8, 0#8]).flatten

def g_B4 : GhostState HwBytes :=
  ⟨.B,
    { g_B2.session with
      rootKey := rk_B4
      senderChain := some ⟨⟨⟨ephPubB2_vec⟩, ⟨ephPrivB2_vec⟩⟩, ⟨sck_B4, 0#32⟩⟩
      receiverChains :=
        [⟨⟨ephPubA1_vec⟩, some ⟨sck_A3, 2#32⟩, []⟩,
         ⟨⟨ephPubA2_vec⟩, some ⟨sck_A5, 1#32⟩, []⟩]
      pqRatchetState := pqB4_state },
    1, [1]⟩

def stB4_cli : PqParty :=
  { stB0Marked with peerId := some ⟨⟨idPubA_vec⟩⟩, session := some (x_B, g_B4) }

/-! ## Model Step Proofs for Calls 5..8 -/

attribute [local semireducible] CryptoVerification.LibsignalSpqrV1.MlKem.fromSeed

theorem wireReply0_eq : wireReply0 = wireWhisper :: bodyReply0 := rfl

theorem wire2_eq : wire2 = wireWhisper :: body2 := rfl

theorem call5_model :
    pqSendModel myParams stB2_cli ptReply0 cSendReply0 = some (some (stB3_cli, wireReply0)) :=
  eq_of_decReprOut (by decide +kernel)

theorem call6_model :
    pqRecvWhisperModel myParams stA3_cli bodyReply0 rc6 = some (some (stA4_cli, ptReply0)) :=
  eq_of_decReprOut (by decide +kernel)

theorem call7_model :
    pqSendModel myParams stA4_cli pt2 cSend2 = some (some (stA5_cli, wire2)) :=
  eq_of_decReprOut (by decide +kernel)

theorem call8_model :
    pqRecvWhisperModel myParams stB3_cli body2 rc8 = some (some (stB4_cli, pt2)) :=
  eq_of_decReprOut (by decide +kernel)

/-! ## Domain Well-Formedness (`PqxdhPartyInSpecDomain`) for Calls 0..8 -/

private theorem wf_file_pair_of_le_cap {f : String × HwBytes}
    (h : f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes) :
    f.2.length < 2 ^ 31 ∧
      ((∀ i, f.1 ≠ CryptoVerification.SignalSession.baseKeysFile i) →
        f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes) := by
  refine ⟨?_, fun _ => h⟩
  unfold CryptoVerification.SignalSession.fileCapBytes at h
  omega

theorem encodeDir_some_of_none (st : PqParty) (x : RecordExtras) (g : GhostState HwBytes)
    (hsess : st.session = some (x, g))
    (hbase : ∀ f ∈ encodeDir myParams { st with session := none },
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes)
    (hrec : (encodeRecordUnderExtras (fun _ => x) g).length ≤
      CryptoVerification.SignalSession.fileCapBytes) :
    ∀ f ∈ encodeDir myParams st,
      f.2.length < 2 ^ 31 ∧
        ((∀ i, f.1 ≠ CryptoVerification.SignalSession.baseKeysFile i) →
          f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes) := by
  intro f hf
  apply wf_file_pair_of_le_cap
  unfold encodeDir at hf hbase
  dsimp only at hf hbase
  rw [hsess] at hf
  simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hf hbase
  by_cases h : f = (CryptoVerification.SignalSession.sessionFile
      (CryptoVerification.SignalSession.partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)
  · subst h; exact hrec
  · simp only [h, or_false] at hf
    exact hbase f hf

theorem encodeDir_stA0_files_le_cap :
    ∀ f ∈ encodeDir myParams stA0_cli,
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
  unfold encodeDir CryptoVerification.SignalSession.fileCapBytes
  dsimp only [stA0_cli]
  rw [kp_idA]
  decide +kernel

theorem encodeDir_stA0_files_lt :
    ∀ f ∈ encodeDir myParams stA0_cli, f.2.length < 2 ^ 31 :=
  fun f hf => (wf_file_pair_of_le_cap (encodeDir_stA0_files_le_cap f hf)).1

theorem encodeDir_stB0_files_le_cap :
    ∀ f ∈ encodeDir myParams stB0_cli,
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
  unfold encodeDir signedRecordBytes CryptoVerification.SignalSession.fileCapBytes
  dsimp only [stB0_cli, List.map]
  rw [kp_idB, kp_spkB]
  decide +kernel

theorem encodeDir_stB0_files_lt :
    ∀ f ∈ encodeDir myParams stB0_cli, f.2.length < 2 ^ 31 :=
  fun f hf => (wf_file_pair_of_le_cap (encodeDir_stB0_files_le_cap f hf)).1

theorem encodeDir_stB0Marked_files_le_cap :
    ∀ f ∈ encodeDir myParams
        { stB0Marked with peerId := some ⟨⟨idPubA_vec⟩⟩, session := none },
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
  unfold encodeDir signedRecordBytes CryptoVerification.SignalSession.fileCapBytes
  dsimp only [stB0Marked, stB0_cli, List.map]
  rw [kp_idB, kp_spkB]
  decide +kernel

theorem encodeDir_stB0Marked_files_lt :
    ∀ f ∈ encodeDir myParams
        { stB0Marked with peerId := some ⟨⟨idPubA_vec⟩⟩, session := none },
      f.2.length < 2 ^ 31 :=
  fun f hf => (wf_file_pair_of_le_cap (encodeDir_stB0Marked_files_le_cap f hf)).1

theorem mkWfPq_some {st : PqParty} {x₀ : RecordExtras} {g : GhostState HwBytes}
    (hsess : st.session = some (x₀, g))
    (hreach : ∃ g₀ : GhostState HwBytes,
      ReachablePqxdhSession myParams st.me x₀ g₀ ∧ g₀.party = g.party ∧ g₀.session = g.session)
    (hparty : g.party = st.party)
    (hrec : (encodeRecordUnderExtras (fun _ => x₀) g).length ≤
      CryptoVerification.SignalSession.fileCapBytes)
    (hbase : ∀ f ∈ encodeDir myParams { st with session := none },
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes)
    (hnd : (st.signed.map (·.1)).Nodup ∧ (st.oneTime.map (·.1)).Nodup ∧
      (st.kyberOneTime.map (·.1)).Nodup ∧ (st.kyberLastResort.map (·.1)).Nodup) :
    PqxdhPartyInSpecDomain myParams st := by
  refine ⟨fun x g' hs => ?_, encodeDir_some_of_none st x₀ g hsess hbase hrec,
    hnd.1, hnd.2.1, hnd.2.2.1, hnd.2.2.2⟩
  rw [hsess] at hs
  injection hs with hp
  cases hp
  have hlt : (encodeRecordUnderExtras (fun _ => x₀) g).length < 2 ^ 31 := by
    unfold CryptoVerification.SignalSession.fileCapBytes at hrec
    omega
  exact ⟨hreach, hparty, hlt⟩

theorem reachPq_of_pqSendModel {st st' : PqParty} {x : RecordExtras}
    {g g' : GhostState HwBytes} {m r wire : HwBytes}
    (hsess : st.session = some (x, g)) (hsess' : st'.session = some (x, g'))
    (hR : ∃ g₀ : GhostState HwBytes,
      ReachablePqxdhSession myParams st.me x g₀ ∧ g₀.party = g.party ∧ g₀.session = g.session)
    (hlen : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31)
    (hsend : pqSendModel myParams st m r = some (some (st', wire))) :
    ∃ g₁ : GhostState HwBytes,
      ReachablePqxdhSession myParams st'.me x g₁ ∧ g₁.party = g'.party ∧ g₁.session = g'.session := by
  rcases hR with ⟨g₀, hR₀, hgp, hgs⟩
  have hlen₀ : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
    simpa only [encodeRecordUnderExtras, hgs] using hlen
  unfold pqSendModel at hsend
  rw [hsess] at hsend
  dsimp only at hsend
  rcases henc : CryptoGames.LibsignalSession.SessionState.messageEncrypt myParams.C
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec
      (CryptoVerification.E2E.pqxdhSpqrSession myParams)
      ((pqxdhSessionParams myParams).sendAddrs g.party) m r g.session with ⟨err | msg, s⟩
  · cases err <;> simp [henc] at hsend
  · rw [henc] at hsend; dsimp only at hsend
    cases hrem : g.session.remoteIdentity with
    | none => simp [hrem] at hsend
    | some k =>
      rw [hrem] at hsend; dsimp only at hsend
      cases htr : !st.trusts k
      · rw [htr] at hsend
        simp only [Bool.false_eq_true, ↓reduceIte] at hsend
        have hst' := (Prod.mk.inj (Option.some.inj (Option.some.inj hsend))).1
        have hme : st'.me = st.me := by rw [← hst']
        have hg' : { g with session := s } = g' := by
          have h1 :
              ({ st with peerId := some k, session := some (x, { g with session := s }) } :
                PqParty).session = st'.session := congrArg PqParty.session hst'
          rw [hsess'] at h1
          exact (Prod.mk.inj (Option.some.inj h1)).2
        refine ⟨((pqxdhSessionParams myParams).send g₀ m r).1, hme ▸ ReachablePqxdhSession.send m r hR₀ hlen₀, ?_, ?_⟩
        · unfold CryptoGames.LibsignalSession.Params.send
          have hC : (pqxdhSessionParams myParams).C = myParams.C := rfl
          have hc : (pqxdhSessionParams myParams).codec =
              CryptoVerification.LibsignalProtoCodec.protoSignalCodec := rfl
          have hsp : (pqxdhSessionParams myParams).spqr = CryptoVerification.E2E.pqxdhSpqrSession myParams := rfl
          rw [hC, hc, hsp, hgp, hgs, henc, ← hg']
        · unfold CryptoGames.LibsignalSession.Params.send
          have hC : (pqxdhSessionParams myParams).C = myParams.C := rfl
          have hc : (pqxdhSessionParams myParams).codec =
              CryptoVerification.LibsignalProtoCodec.protoSignalCodec := rfl
          have hsp : (pqxdhSessionParams myParams).spqr = CryptoVerification.E2E.pqxdhSpqrSession myParams := rfl
          rw [hC, hc, hsp, hgp, hgs, henc, ← hg']
      · rw [htr] at hsend
        cases hsend

theorem reachPq_of_pqRecvWhisperModel {st st' : PqParty} {x : RecordExtras}
    {g g' : GhostState HwBytes} {c pt : HwBytes} {rc : BitVec 256}
    (hsess : st.session = some (x, g)) (hsess' : st'.session = some (x, g'))
    (hR : ∃ g₀ : GhostState HwBytes,
      ReachablePqxdhSession myParams st.me x g₀ ∧ g₀.party = g.party ∧ g₀.session = g.session)
    (hlen : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31)
    (hrecv : pqRecvWhisperModel myParams st c rc = some (some (st', pt))) :
    ∃ g₁ : GhostState HwBytes,
      ReachablePqxdhSession myParams st'.me x g₁ ∧ g₁.party = g'.party ∧ g₁.session = g'.session := by
  rcases hR with ⟨g₀, hR₀, hgp, hgs⟩
  have hlen₀ : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
    simpa only [encodeRecordUnderExtras, hgs] using hlen
  unfold pqRecvWhisperModel CryptoVerification.SignalSession.pqxdhSessionDecryptModel at hrecv
  rw [hsess] at hrecv
  dsimp only at hrecv
  rcases hc : CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec c with err | msg
  · simp [hc] at hrecv
  · rw [hc] at hrecv; dsimp only at hrecv
    rcases hd : CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord myParams.C
        (CryptoVerification.E2E.pqxdhSpqrSession myParams) ((pqxdhSessionParams myParams).expectedAddrs g.party)
        msg .whisper rc g.session with ⟨err | pt₀, s⟩
    · cases err <;> simp [hd] at hrecv
    · rw [hd] at hrecv; dsimp only at hrecv
      cases hrem : s.remoteIdentity with
      | none => simp [hrem] at hrecv
      | some k =>
        rw [hrem] at hrecv; dsimp only at hrecv
        split_ifs at hrecv with htr
        · cases hrecv
        · have hst' := (Prod.mk.inj (Option.some.inj (Option.some.inj hrecv))).1
          have hme : st'.me = st.me := by rw [← hst']
          have hg' : { g with session := s } = g' := by
            have h1 : ({ st with peerId := some k, session := some (x, { g with session := s }) } :
                PqParty).session = st'.session := congrArg PqParty.session hst'
            rw [hsess'] at h1
            exact (Prod.mk.inj (Option.some.inj h1)).2
          have hrec_eq : ∃ g₁ r, (pqxdhSessionParams myParams).receive g₀ c rc = some (g₁, r) ∧
              g₁.party = g₀.party ∧ g₁.session = s := by
            unfold CryptoGames.LibsignalSession.Params.receive
            have hC : (pqxdhSessionParams myParams).C = myParams.C := rfl
            have hcod : (pqxdhSessionParams myParams).codec =
                CryptoVerification.LibsignalProtoCodec.protoSignalCodec := rfl
            have hsp : (pqxdhSessionParams myParams).spqr = CryptoVerification.E2E.pqxdhSpqrSession myParams := rfl
            rw [hcod, hc]
            dsimp only
            rw [hC, hsp, hgp, hgs, hd]
            exact ⟨_, _, rfl, rfl, rfl⟩
          rcases hrec_eq with ⟨g₁, r, hrec, hp1, hs1⟩
          exact ⟨g₁, hme ▸ ReachablePqxdhSession.recv hR₀ hlen₀ hrec,
            by rw [hp1, hgp, ← hg'], by rw [hs1, ← hg']⟩

theorem reachPq_A1_ex :
    ∃ g₀ : GhostState HwBytes,
      ReachablePqxdhSession myParams stA1_cli.me x_A g₀ ∧ g₀.party = g_A1.party ∧ g₀.session = g_A1.session := by
  have h1 := call0_model
  unfold pqInitModel at h1
  have htr : stA0_cli.trusts ⟨⟨bE_cli.idPub⟩⟩ = true := rfl
  have hpA : stA0_cli.party = .A := rfl
  rw [htr, hpA] at h1
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1
  cases hi : initiateState nvX myParams .A stA0_cli.me bE_cli tapeInit with
  | none => rw [hi] at h1; cases h1
  | some xg =>
    rcases xg with ⟨x0, g0⟩
    rw [hi] at h1
    have hst := (Prod.mk.inj (Option.some.inj (Option.some.inj h1))).1
    have hsess : ({ stA0_cli with peerId := some ⟨⟨bE_cli.idPub⟩⟩, session := some (x0, g0) } :
        PqParty).session = stA1_cli.session := congrArg PqParty.session hst
    injection hsess with hp
    cases hp
    exact ⟨g_A1, ReachablePqxdhSession.initiate nvX .A stA0_cli.me bE_cli tapeInit x_A g_A1 hi, rfl, rfl⟩

theorem reachPq_A2_ex :
    ∃ g₀ : GhostState HwBytes,
      ReachablePqxdhSession myParams stA2_cli.me x_A g₀ ∧ g₀.party = g_A2.party ∧ g₀.session = g_A2.session :=
  reachPq_of_pqSendModel rfl rfl reachPq_A1_ex (by decide +kernel) call1_model

theorem reachPq_A3_ex :
    ∃ g₀ : GhostState HwBytes,
      ReachablePqxdhSession myParams stA3_cli.me x_A g₀ ∧ g₀.party = g_A3.party ∧ g₀.session = g_A3.session :=
  reachPq_of_pqSendModel rfl rfl reachPq_A2_ex (by decide +kernel) call2_model

theorem reachPq_B1_ex :
    ∃ g₀ : GhostState HwBytes,
      ReachablePqxdhSession myParams stB1_cli.me x_B g₀ ∧ g₀.party = g_B1.party ∧ g₀.session = g_B1.session := by
  have h3 := call3_model
  unfold pqRecvPrekeyModel at h3
  rcases hc : CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec pkMsg0.inner with err | inner
  · simp [hc] at h3
  · rw [hc] at h3
    dsimp only at h3
    have htr : (!stB0_cli.trusts ⟨⟨pkMsg0.idPub⟩⟩) = false := rfl
    have hs0 : stB0_cli.session = none := rfl
    have hpB : stB0_cli.party = .B := rfl
    rw [htr, hs0, hpB] at h3
    simp only [Bool.false_eq_true, ↓reduceIte] at h3
    cases hk : preKeysNamedBy stB0_cli pkMsg0 with
    | none => rw [hk] at h3; cases h3
    | some k =>
      rw [hk] at h3; dsimp only at h3
      cases hr : recvPrekeyState nvX myParams .B stB0_cli.me k pkMsg0 rc3 with
      | none => rw [hr] at h3; cases h3
      | some o =>
        cases o with
        | none => rw [hr] at h3; cases h3
        | some xgp =>
          rcases xgp with ⟨x0, g0, pt_out⟩
          rw [hr, markKyberUsed_stB0] at h3
          dsimp only at h3
          have hst := (Prod.mk.inj (Option.some.inj (Option.some.inj h3))).1
          have hsess : ({ CryptoVerification.SignalSession.removeOpk stB0Marked pkMsg0 with
              peerId := some ⟨⟨pkMsg0.idPub⟩⟩, session := some (x0, g0) } : PqParty).session =
              stB1_cli.session := congrArg PqParty.session hst
          injection hsess with hp
          cases hp
          exact ⟨g_B1, ReachablePqxdhSession.recvPrekey nvX .B stB0_cli.me k pkMsg0 rc3 x_B g_B1 pt_out hr,
            rfl, rfl⟩

theorem reachPq_B2_ex :
    ∃ g₀ : GhostState HwBytes,
      ReachablePqxdhSession myParams stB2_cli.me x_B g₀ ∧ g₀.party = g_B2.party ∧ g₀.session = g_B2.session := by
  rcases reachPq_B1_ex with ⟨g₀, hR₀, hgp, hgs⟩
  have hlen₀ : (encodeRecordUnderExtras (fun _ => x_B) g₀).length < 2 ^ 31 := by
    have hlen : (encodeRecordUnderExtras (fun _ => x_B) g_B1).length < 2 ^ 31 := by decide +kernel
    simpa only [encodeRecordUnderExtras, hgs] using hlen
  have h4 := call4_model
  unfold pqRecvPrekeyModel at h4
  rcases hc : CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec pkMsg1.inner with err | inner
  · simp [hc] at h4
  · rw [hc] at h4
    dsimp only at h4
    have htr : (!stB1_cli.trusts ⟨⟨pkMsg1.idPub⟩⟩) = false := rfl
    have hs1 : stB1_cli.session = some (x_B, g_B1) := rfl
    have hm : PqSessionMatches x_B g_B1 pkMsg1 := call4_sessionMatches x_B g_B1 rfl
    have hrem : ¬ (g_B1.session.remoteIdentity ≠ some ⟨⟨pkMsg1.idPub⟩⟩) := by decide
    rw [htr, hs1] at h4
    simp only [Bool.false_eq_true, hm, hrem, ↓reduceIte] at h4
    rcases hd : CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord myParams.C
        (CryptoVerification.E2E.pqxdhSpqrSession myParams) ((pqxdhSessionParams myParams).expectedAddrs g_B1.party)
        inner .preKey rc4 g_B1.session with ⟨err | pt_out, s⟩
    · cases err <;> simp [hd] at h4
    · rw [hd] at h4; dsimp only at h4
      have hst := (Prod.mk.inj (Option.some.inj (Option.some.inj h4))).1
      have hg' : { g_B1 with session := s } = g_B2 := by
        have h1 :
            ({ stB1_cli with
                peerId := some ⟨⟨pkMsg1.idPub⟩⟩,
                session := some (x_B, { g_B1 with session := s }) } : PqParty).session =
              stB2_cli.session := congrArg PqParty.session hst
        exact (Prod.mk.inj (Option.some.inj h1)).2
      have hd₀ : CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord myParams.C
          (CryptoVerification.E2E.pqxdhSpqrSession myParams) ((pqxdhSessionParams myParams).expectedAddrs g₀.party)
          inner .preKey rc4 g₀.session = (.ok pt_out, s) := by
        simpa only [hgp, hgs] using hd
      rcases CryptoVerification.SignalSession.Closure.Promote.reachPq_promote_proof
          myParams stB1_cli.me x_B g₀ pkMsg1.inner inner rc4 pt_out s hR₀ hlen₀ hc hd₀ with
        ⟨g₁, hR₁, hp₁, hs₁⟩
      exact ⟨g₁, hR₁, by rw [hp₁, hgp, ← hg'], by rw [hs₁, ← hg']⟩

theorem reachPq_B3_ex :
    ∃ g₀ : GhostState HwBytes,
      ReachablePqxdhSession myParams stB3_cli.me x_B g₀ ∧ g₀.party = g_B3.party ∧ g₀.session = g_B3.session :=
  reachPq_of_pqSendModel rfl rfl reachPq_B2_ex (by decide +kernel) call5_model

theorem reachPq_A4_ex :
    ∃ g₀ : GhostState HwBytes,
      ReachablePqxdhSession myParams stA4_cli.me x_A g₀ ∧ g₀.party = g_A4.party ∧ g₀.session = g_A4.session :=
  reachPq_of_pqRecvWhisperModel rfl rfl reachPq_A3_ex (by decide +kernel) call6_model

theorem reachPq_A5_ex :
    ∃ g₀ : GhostState HwBytes,
      ReachablePqxdhSession myParams stA5_cli.me x_A g₀ ∧ g₀.party = g_A5.party ∧ g₀.session = g_A5.session :=
  reachPq_of_pqSendModel rfl rfl reachPq_A4_ex (by decide +kernel) call7_model

theorem reachPq_B4_ex :
    ∃ g₀ : GhostState HwBytes,
      ReachablePqxdhSession myParams stB4_cli.me x_B g₀ ∧ g₀.party = g_B4.party ∧ g₀.session = g_B4.session :=
  reachPq_of_pqRecvWhisperModel rfl rfl reachPq_B3_ex (by decide +kernel) call8_model

theorem wfPq_stA0 : PqxdhPartyInSpecDomain myParams stA0_cli :=
  ⟨(fun _ _ hs => nomatch hs),
    fun f hf => wf_file_pair_of_le_cap (encodeDir_stA0_files_le_cap f hf),
    by decide, by decide, by decide, by decide⟩

theorem wfPq_stB0 : PqxdhPartyInSpecDomain myParams stB0_cli :=
  ⟨(fun _ _ hs => nomatch hs),
    fun f hf => wf_file_pair_of_le_cap (encodeDir_stB0_files_le_cap f hf),
    by decide, by decide, by decide, by decide⟩

theorem wfPq_stA1 : PqxdhPartyInSpecDomain myParams stA1_cli :=
  mkWfPq_some rfl reachPq_A1_ex rfl
    (by unfold CryptoVerification.SignalSession.fileCapBytes; decide +kernel)
    encodeDir_stA0_files_le_cap (by decide +kernel)

theorem wfPq_stA2 : PqxdhPartyInSpecDomain myParams stA2_cli :=
  mkWfPq_some rfl reachPq_A2_ex rfl
    (by unfold CryptoVerification.SignalSession.fileCapBytes; decide +kernel)
    encodeDir_stA0_files_le_cap (by decide +kernel)

theorem wfPq_stA3 : PqxdhPartyInSpecDomain myParams stA3_cli :=
  mkWfPq_some rfl reachPq_A3_ex rfl
    (by unfold CryptoVerification.SignalSession.fileCapBytes; decide +kernel)
    encodeDir_stA0_files_le_cap (by decide +kernel)

theorem wfPq_stB1 : PqxdhPartyInSpecDomain myParams stB1_cli :=
  mkWfPq_some rfl reachPq_B1_ex rfl
    (by unfold CryptoVerification.SignalSession.fileCapBytes; decide +kernel)
    encodeDir_stB0Marked_files_le_cap (by decide +kernel)

theorem wfPq_stB2 : PqxdhPartyInSpecDomain myParams stB2_cli :=
  mkWfPq_some rfl reachPq_B2_ex rfl
    (by unfold CryptoVerification.SignalSession.fileCapBytes; decide +kernel)
    encodeDir_stB0Marked_files_le_cap (by decide +kernel)

theorem wfPq_stB3 : PqxdhPartyInSpecDomain myParams stB3_cli :=
  mkWfPq_some rfl reachPq_B3_ex rfl
    (by unfold CryptoVerification.SignalSession.fileCapBytes; decide +kernel)
    encodeDir_stB0Marked_files_le_cap (by decide +kernel)

theorem wfPq_stA4 : PqxdhPartyInSpecDomain myParams stA4_cli :=
  mkWfPq_some rfl reachPq_A4_ex rfl
    (by unfold CryptoVerification.SignalSession.fileCapBytes; decide +kernel)
    encodeDir_stA0_files_le_cap (by decide +kernel)

theorem wfPq_stA5 : PqxdhPartyInSpecDomain myParams stA5_cli :=
  mkWfPq_some rfl reachPq_A5_ex rfl
    (by unfold CryptoVerification.SignalSession.fileCapBytes; decide +kernel)
    encodeDir_stA0_files_le_cap (by decide +kernel)

theorem wfPq_stB4 : PqxdhPartyInSpecDomain myParams stB4_cli :=
  mkWfPq_some rfl reachPq_B4_ex rfl
    (by unfold CryptoVerification.SignalSession.fileCapBytes; decide +kernel)
    encodeDir_stB0Marked_files_le_cap (by decide +kernel)

end Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel58
