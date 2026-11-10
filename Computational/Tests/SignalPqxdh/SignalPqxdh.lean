/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.CwfPrimitives
public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthStatements
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.Headline
public meta import Computational.Proofs.SignalPqxdh.CwfPrimitives -- shake: keep
public meta import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthStatements -- shake: keep
public meta import Computational.Specifications.Assumptions.Assumptions -- shake: keep
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import VCVio.EvalDist.Monad.Basic
public meta import LibsignalBinary.Specifications.SignalPqxdh.Model -- shake: keep
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs

/-!
# PQXDH Specification Tests

Known-answer roundtrips, BJKS24 attack witnesses, and non-vacuity and regression checks for the
PQXDH specification and security statements. Instantiates `WellFormedPrimitives` and
`PqxdhCorrect` via `idealRoundtripPrimitives` and `CryptoWellFormedPrimitives` via
`cwfPrimitives`, and tests key canonicality, domain separation, `KemShCr` malleability, No-OPK
replay deduplication, KCI resistance, and post-game freshness. Also checks `Headline` and costed
statement shapes, query-budget and KOSK non-vacuity, first-message MAC framing against shift
forgery (DEV-PQ31), and the 32-byte effective HKDF salt of `PrfMsgKeys` (DEV-LS25).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace SpecTests.SignalPqxdh

open scoped ENNReal
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Security (KeyIndReductionFamily KeyInd2KeyReductionFamily AuthReductionFamily)

theorem clamp32_length (bs : Bytes) : (clamp32 bs).length = 32 := by
  simp [clamp32, fitBytes_length]

theorem and_7f_idem (b : UInt8) : (b &&& 0x7F) &&& 0x7F = b &&& 0x7F := by
  rw [UInt8.and_assoc]
  rfl

theorem map_and_7f_idem (bs : Bytes) :
    (bs.map (fun b => b &&& 0x7F)).map (fun b => b &&& 0x7F) = bs.map (fun b => b &&& 0x7F) := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.map_cons, and_7f_idem, ih]

theorem clamp32_idem (bs : Bytes) : clamp32 (clamp32 bs) = clamp32 bs := by
  unfold clamp32
  rw [fitBytes_of_length_eq (by simp [fitBytes_length])]
  exact map_and_7f_idem (fitBytes 32 bs)

theorem uint8_and_7f_and_80 (b : UInt8) : ((b &&& 0x7F) &&& 0x80) = 0 := by
  revert b; decide

theorem uint8_and_7f_not_ge_ed (b : UInt8) : decide ((b &&& 0x7F) >= 0xED) = false := by
  revert b; decide

theorem getD_31_clamp32_and_80 (bs : Bytes) : ((clamp32 bs).getD 31 0 &&& 0x80) = 0 := by
  have hlen : (fitBytes 32 bs).length = 32 := fitBytes_length 32 bs
  have hlt : 31 < (fitBytes 32 bs).length := by omega
  unfold clamp32
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt]
  simp only [Option.map_some, Option.getD_some]
  exact uint8_and_7f_and_80 _

theorem getD_0_clamp32_not_ge_ed (bs : Bytes) : decide ((clamp32 bs).getD 0 0 >= 0xED) = false := by
  have hlen : (fitBytes 32 bs).length = 32 := fitBytes_length 32 bs
  have hlt : 0 < (fitBytes 32 bs).length := by omega
  unfold clamp32
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt]
  simp only [Option.map_some, Option.getD_some]
  exact uint8_and_7f_not_ge_ed _

theorem scalarIsInRange_clamp32 (bs : Bytes) : scalarIsInRange (clamp32 bs) = true := by
  unfold scalarIsInRange
  rw [getD_31_clamp32_and_80, getD_0_clamp32_not_ge_ed]
  rfl

theorem isCanonical32_clamp32 (bs : Bytes) : isCanonical32 (clamp32 bs) = true := by
  unfold isCanonical32
  rw [clamp32_length, scalarIsInRange_clamp32]
  rfl

theorem reduceCanon32_eq_of_isCanonical32 {bs : Bytes} (h : isCanonical32 bs = true) :
    reduceCanon32 bs = bs := by
  unfold reduceCanon32
  rw [h]
  rfl

theorem reduceCanon32_length (bs : Bytes) : (reduceCanon32 bs).length = 32 := by
  unfold reduceCanon32
  split <;> rename_i h
  · unfold isCanonical32 at h
    rw [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  · exact clamp32_length bs

theorem isCanonical32_reduceCanon32 (bs : Bytes) : isCanonical32 (reduceCanon32 bs) = true := by
  unfold reduceCanon32
  split <;> rename_i h
  · exact h
  · exact isCanonical32_clamp32 bs

theorem reduceCanon32_idem (bs : Bytes) : reduceCanon32 (reduceCanon32 bs) = reduceCanon32 bs :=
  reduceCanon32_eq_of_isCanonical32 (isCanonical32_reduceCanon32 bs)

theorem clamp32_reduceCanon32 (bs : Bytes) : clamp32 (reduceCanon32 bs) = clamp32 bs := by
  unfold reduceCanon32
  split
  · rfl
  · exact clamp32_idem bs

/-- Deterministic test primitives over 32-byte X25519 keys with `xeddsaVerifyRef` verification. -/
def testPrimitives : Primitives :=
  { testPrimitivesBase with sigVerify := xeddsaVerifyRef testPrimitivesBase }

def sampleIkA : Bytes := fitBytes 32 [0x21, 0x22, 0x23, 0x24]
def sampleEkA : Bytes := fitBytes 32 [0x31, 0x32, 0x33, 0x34]
def sampleEphA1 : Bytes := fitBytes 32 [0x41, 0x42, 0x43, 0x44]
def sampleIkB : Bytes := fitBytes 32 [0x51, 0x52, 0x53, 0x54]
def sampleSpkB : Bytes := fitBytes 32 [0x61, 0x62, 0x63, 0x64]
def sampleOpkB : Bytes := fitBytes 32 [0x71, 0x72, 0x73, 0x74]
def samplePqspkB : Bytes := [0x11, 0x12, 0x13, 0x14]
def sampleKemCoins : Bytes := [0x15, 0x16, 0x17, 0x18]
def sampleSpqrCoins : Bytes := [0x19, 0x1A]
def samplePlaintext : Bytes := [0x48, 0x65, 0x6C, 0x6C, 0x6F]

def sampleSpkSig : Bytes := testPrimitives.sigSign sampleIkB (encodeEC sampleSpkB) []
def samplePqspkSig : Bytes := testPrimitives.sigSign sampleIkB (encodeKEM samplePqspkB) []

def sampleBundleWithOpk : PreKeyBundleInput where
  ikB := sampleIkB
  spkId := 7
  spkB := sampleSpkB
  spkSig := sampleSpkSig
  opkB? := some (42, sampleOpkB)
  pqspkId := 9
  pqspkB := samplePqspkB
  pqspkSig := samplePqspkSig

def sampleBundleNoOpk : PreKeyBundleInput :=
  { sampleBundleWithOpk with opkB? := none }

def sampleInitWithOpk : InitiateInput where
  ikASk := sampleIkA
  ikAPk := sampleIkA
  ekASk := sampleEkA
  kemCoins := sampleKemCoins
  trustedPeer := true
  bundle := sampleBundleWithOpk
  ephASk := sampleEphA1
  spqrCoins := sampleSpqrCoins
  plaintext := samplePlaintext

def sampleInitNoOpk : InitiateInput :=
  { sampleInitWithOpk with bundle := sampleBundleNoOpk }

def sampleAcceptKeysBaseWithOpk (hdr : HandshakeHdr) : AcceptKeysInput where
  ikBSk := sampleIkB
  ikBPk := sampleIkB
  spkBSk := sampleSpkB
  spkBPk := sampleSpkB
  opkBSk? := some sampleOpkB
  pqspkBSk := samplePqspkB
  pqspkBPk := samplePqspkB
  trustedPeer := true
  replayOk := true
  hdr := hdr

def sampleAcceptKeysBaseNoOpk (hdr : HandshakeHdr) : AcceptKeysInput :=
  { sampleAcceptKeysBaseWithOpk hdr with opkBSk? := none }

theorem kat1_initiateKeys_acceptKeys_with_opk_roundtrip :
    (match Model.initiateKeys testPrimitives sampleInitWithOpk.toInitiateKeysInput with
     | some (drKeyA, hdr) =>
       hdr.opkId? == some 42 &&
       Model.acceptKeys testPrimitives (sampleAcceptKeysBaseWithOpk hdr) == some drKeyA
     | none => false) = true := by
  decide

theorem kat2_initiateKeys_acceptKeys_no_opk_roundtrip :
    (match Model.initiateKeys testPrimitives sampleInitNoOpk.toInitiateKeysInput with
     | some (drKeyA, hdr) =>
       hdr.opkId? == none &&
       Model.acceptKeys testPrimitives (sampleAcceptKeysBaseNoOpk hdr) == some drKeyA
     | none => false) = true := by
  decide

theorem kat3_initiate_accept_with_opk_roundtrip :
    (match Model.initiate testPrimitives sampleInitWithOpk with
     | some (drKeyA, rk1A, ck1_1A, msg) =>
       match Model.accept testPrimitives
         { keysInp := sampleAcceptKeysBaseWithOpk msg.hdr, msg := msg } with
       | some (drKeyB, rk1B, ck1_1B, ptB) =>
         drKeyA == drKeyB && rk1A == rk1B && ck1_1A == ck1_1B && ptB == samplePlaintext
       | none => false
     | none => false) = true := by
  decide

theorem kat4_initiate_accept_no_opk_roundtrip :
    (match Model.initiate testPrimitives sampleInitNoOpk with
     | some (drKeyA, rk1A, ck1_1A, msg) =>
       match Model.accept testPrimitives
         { keysInp := sampleAcceptKeysBaseNoOpk msg.hdr, msg := msg } with
       | some (drKeyB, rk1B, ck1_1B, ptB) =>
         drKeyA == drKeyB && rk1A == rk1B && ck1_1A == ck1_1B && ptB == samplePlaintext
       | none => false
     | none => false) = true := by
  decide

theorem kat5_with_opk_ne_no_opk_drkey :
    (match Model.initiateKeys testPrimitives sampleInitWithOpk.toInitiateKeysInput,
           Model.initiateKeys testPrimitives sampleInitNoOpk.toInitiateKeysInput with
     | some (drKeyWithOpk, _), some (drKeyNoOpk, _) => drKeyWithOpk != drKeyNoOpk
     | _, _ => false) = true := by
  decide

/-- `Model.acceptKeys` rejects an `ekAPk` with bit 7 of byte 31 set (`isCanonical = false`) and a
    truncated `ikAPk`. -/
theorem witness_noncanonical_ek_rejected :
    let nonCanonEk : Bytes := List.replicate 31 0x01 ++ [0x80]
    let shortKey : Bytes := [0x01, 0x02, 0x03, 0x04]
    testPrimitives.isCanonical sampleEkA = true ∧
    testPrimitives.isCanonical nonCanonEk = false ∧
    (match Model.initiateKeys testPrimitives sampleInitNoOpk.toInitiateKeysInput with
     | some (_drKeyA, hdr) =>
       let badHdrCanon := { hdr with ekAPk := nonCanonEk }
       let badHdrShort := { hdr with ikAPk := shortKey }
       Model.acceptKeys testPrimitives (sampleAcceptKeysBaseNoOpk badHdrCanon) == none &&
       Model.acceptKeys testPrimitives (sampleAcceptKeysBaseNoOpk badHdrShort) == none
     | none => false) = true := by
  decide

#guard
  match Model.initiate testPrimitives sampleInitWithOpk with
  | some (drKeyA, rk1A, ck1_1A, msg) =>
    match Model.accept testPrimitives
      { keysInp := sampleAcceptKeysBaseWithOpk msg.hdr, msg := msg } with
    | some (drKeyB, rk1B, ck1_1B, ptB) =>
      drKeyA == drKeyB && rk1A == rk1B && ck1_1A == ck1_1B && ptB == samplePlaintext
    | none => false
  | none => false

theorem witness1_domain_separation_disjoint (pkEC pkKEM : Bytes) :
    encodeEC pkEC ≠ encodeKEM pkKEM :=
  encodeEC_ne_encodeKEM pkEC pkKEM

def buggyUntaggedAD (k1 k2 : Bytes) : Bytes :=
  k1 ++ k2

/-- BJKS24 §4.1 public-key confusion: without the `0x05`/`0x08` key-type tags of `encodeEC` and
    `encodeKEM`, shifting bytes between the two keys collides under `buggyUntaggedAD` while
    `firstMsgAD` separates them. -/
theorem witness1_pubkey_confusion_without_domain_sep :
    let ecKey : Bytes := [0x01, 0x02]
    let kemPrefix : Bytes := [0x01]
    let shiftedSecond : Bytes := [0x02, 0x03, 0x04]
    let normalSecond : Bytes := [0x03, 0x04]
    buggyUntaggedAD ecKey normalSecond = buggyUntaggedAD kemPrefix shiftedSecond ∧
    firstMsgAD ecKey normalSecond [] [] ≠ firstMsgAD kemPrefix shiftedSecond [] [] ∧
    encodeEC ecKey ≠ encodeKEM ecKey := by
  decide

def weakSigPrimitives : Primitives :=
  { testPrimitives with sigVerify := fun _ _ _ => true }

/-- Without `SigEufCma` (`weakSigPrimitives`), `Model.initiateKeys` accepts a bundle with an
    unsigned `spkB` that `testPrimitives` rejects. -/
theorem witness1_sig_forgery_without_euf_cma :
    let rogueSpkB : Bytes := fitBytes 32 [0x00, 0x11, 0x22, 0x33]
    let forgedBundle : PreKeyBundleInput := { sampleBundleNoOpk with spkB := rogueSpkB }
    let forgedInp : InitiateKeysInput :=
      { sampleInitNoOpk.toInitiateKeysInput with bundle := forgedBundle }
    (Model.initiateKeys weakSigPrimitives forgedInp).isSome = true ∧
    Model.initiateKeys testPrimitives forgedInp = none := by
  decide

/-- Primitives whose KEM violates `KemShCr`: the shared secret `coins.take 4` is independent of
    the public key, so the same secret re-encapsulates under another key. -/
def nonShCrPrimitives : Primitives :=
  { testPrimitives with
    kemEncaps := fun pk coins =>
      some (coins.take 4, fitBytes kyberCtLen ([0xC0, 0x01] ++ fitBytes 2 pk ++ fitBytes 4 coins))
    kemDecaps := fun _sk ct =>
      if ct.length == kyberCtLen && ct.take 2 == [0xC0, 0x01] then
        some ((ct.drop 4).take 4)
      else none }

/-- BJKS24 §4.2 KEM re-encapsulation: under `nonShCrPrimitives`, a substituted Kyber prekey yields
    the same `DRKey` with distinct `pqspkId` and `kemCt`. -/
theorem witness2_kem_reencaps_malleability_without_shcr :
    let malPqspkB : Bytes := [0x3F, 0x3E, 0x3D, 0x3C]
    let malBundle : PreKeyBundleInput :=
      { sampleBundleNoOpk with
        pqspkId := 999
        pqspkB := malPqspkB
        pqspkSig := testPrimitives.sigSign sampleIkB (encodeKEM malPqspkB) [] }
    let initHon := sampleInitNoOpk.toInitiateKeysInput
    let initMal := { sampleInitNoOpk with bundle := malBundle }.toInitiateKeysInput
    (match Model.initiateKeys nonShCrPrimitives initHon,
           Model.initiateKeys nonShCrPrimitives initMal with
     | some (drKeyHon, hdrHon), some (drKeyMal, hdrMal) =>
       hdrHon.pqspkId != hdrMal.pqspkId &&
       hdrHon.kemCt != hdrMal.kemCt &&
       drKeyHon == drKeyMal &&
       Model.acceptKeys nonShCrPrimitives (sampleAcceptKeysBaseNoOpk hdrMal) == some drKeyHon
     | _, _ => false) = true := by
  decide

/-- Without Kyber prekey replay deduplication (`replayOk = true` twice), a replayed No-OPK
    `PreKeyMsg` is accepted twice with identical keys and plaintext. -/
theorem witness3a_noopk_replay_succeeds_without_dedup :
    (match Model.initiate testPrimitives sampleInitNoOpk with
     | some (drKeyA, rk1A, ck1_1A, msg) =>
       let bobFirstInp : AcceptInput :=
         { keysInp := { sampleAcceptKeysBaseNoOpk msg.hdr with replayOk := true }, msg := msg }
       let bobReplayWithoutStoreDedup : AcceptInput :=
         { keysInp := { sampleAcceptKeysBaseNoOpk msg.hdr with replayOk := true }, msg := msg }
       Model.accept testPrimitives bobFirstInp == some (drKeyA, rk1A, ck1_1A, samplePlaintext) &&
       Model.accept testPrimitives bobReplayWithoutStoreDedup ==
         some (drKeyA, rk1A, ck1_1A, samplePlaintext)
     | none => false) = true := by
  decide

/-- With `checkAndMarkKyberBaseKeySeen`, the first No-OPK delivery is accepted and a replay gets
    `replayOk = false` and is rejected. -/
theorem witness3b_noopk_replay_rejected_with_dedup :
    (match Model.initiate testPrimitives sampleInitNoOpk with
     | some (drKeyA, rk1A, ck1_1A, msg) =>
       let used0 : List (Nat × KeyId × KeyId × Bytes) := []
       let (replayOk1, used1) :=
         checkAndMarkKyberBaseKeySeen used0 1 msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
       let (replayOk2, _used2) :=
         checkAndMarkKyberBaseKeySeen used1 1 msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
       let bobFirstInp : AcceptInput :=
         { keysInp := { sampleAcceptKeysBaseNoOpk msg.hdr with replayOk := replayOk1 }, msg := msg }
       let bobSecondInp : AcceptInput :=
         { keysInp := { sampleAcceptKeysBaseNoOpk msg.hdr with replayOk := replayOk2 }, msg := msg }
       replayOk1 == true &&
       replayOk2 == false &&
       Model.accept testPrimitives bobFirstInp == some (drKeyA, rk1A, ck1_1A, samplePlaintext) &&
       Model.accept testPrimitives bobSecondInp == none
     | none => false) = true := by
  decide

theorem witness3_replay_rejected_when_marked_used (P : Primitives) (inp : AcceptInput)
    (hReplay : inp.keysInp.replayOk = false) :
    Model.accept P inp = none := by
  unfold Model.accept Model.acceptKeys
  simp [hReplay]

/-- BJKS24 §4.4: `firstMsgAD` depends only on `(ikA, ikB, ephAPk, pqRatchetMsg)` and omits
    `pqspkB` and `kemCt`. -/
theorem witness4a_ad_independent_of_pqspk_and_ct (ikA ikB ephAPk pqRatchetMsg : Bytes) :
    firstMsgAD ikA ikB ephAPk pqRatchetMsg =
      encodeEC ikA ++ encodeEC ikB ++ [0x44] ++ pbBytesField 1 (encodeEC ephAPk) ++
        [0x10, 0x00, 0x18, 0x00] ++
        (if pqRatchetMsg.isEmpty then [] else pbBytesField 5 pqRatchetMsg) :=
  rfl

/-- KCI resistance via `DH(IK_A, SPK_B)`: Bob's `ikBSk` without Alice's `ikASk` does not allow a
    forged `PreKeyMsg` for `ikAPk = sampleIkA`. -/
theorem witness4b_kci_resistance_rejects_forged_sender :
    let attackerGuessedIkASk : Bytes := List.replicate 32 0x00
    let kciForgedInit : InitiateInput :=
      { sampleInitWithOpk with
        ikASk := attackerGuessedIkASk
        ikAPk := sampleIkA }
    (match Model.initiate testPrimitives kciForgedInit with
     | some (_forgedDrKey, _forgedRk1, _forgedCk1_1, forgedMsg) =>
       Model.accept testPrimitives
         { keysInp := sampleAcceptKeysBaseWithOpk forgedMsg.hdr, msg := forgedMsg } == none
     | none => false) = true := by
  decide

/-- Joint compromise of Bob's X25519 secrets and `pqspkBSk` recovers `drKeyA` from the public
    handshake header. -/
theorem witness4c_dh_and_kem_compromise_recovers_drkey :
    (match Model.initiateKeys testPrimitives sampleInitWithOpk.toInitiateKeysInput with
     | some (drKeyA, hdr) =>
       let attackerReconstructed :=
         Model.acceptKeys testPrimitives (sampleAcceptKeysBaseWithOpk hdr)
       attackerReconstructed == some drKeyA
     | none => false) = true := by
  decide

def testSetup : Setup where
  N_id := 2
  N_recv := 2
  N_opk := 2
  N_no_opk := 2
  N_send_opk := 2
  N_send_no_opk := 2

/-- Post-game initiator freshness: under `useRo = true` (`-D DH`), peer-IK corruption leaves a
    session fresh when `spkHonest = true` and unfresh when all prekeys are dishonest; under
    `useRo = false` (`-D KEM` HNDL), freshness holds iff `s.fresh && s.pqspkHonest`. -/
theorem regression_c1_post_game_freshness_keyind :
    let sid0 : SessionId testSetup := .sendNoOPK ⟨0, by decide⟩ ⟨0, by decide⟩
    let dummyHdr : HandshakeHdr :=
      { ikAPk := sampleIkA, ekAPk := sampleEkA, spkId := 0, opkId? := none, pqspkId := 0,
        kemCt := [] }
    let dummyDrKey : DRKey := { rootKey := [], chainKey := [], pqrKey := [] }
    let cleanSpkSess : KeyIndInitiatorEntry testSetup :=
      { sid := sid0
        honestPeer := some 1
        peerIkPk := sampleIkB
        peerSpkPk := sampleSpkB
        peerOpkPk? := none
        peerPqspkPk := samplePqspkB
        spkHonest := true
        opkHonest := false
        pqspkHonest := false
        fresh := true
        tested := true
        ekASk := sampleEkA
        drKeyReal := dummyDrKey
        drKeyRand := dummyDrKey
        hdr := dummyHdr }
    let compromisedAllSess : KeyIndInitiatorEntry testSetup :=
      { cleanSpkSess with spkHonest := false, pqspkHonest := false }
    let hndlCleanPqspkSess : KeyIndInitiatorEntry testSetup :=
      { cleanSpkSess with spkHonest := false, pqspkHonest := true }
    keyIndInitCorruptionClause testPrimitives true [] [] cleanSpkSess = true ∧
    keyIndInitCorruptionClause testPrimitives true [] [] compromisedAllSess = false ∧
    keyIndInitCorruptionClause testPrimitives false [] [] cleanSpkSess = false ∧
    keyIndInitCorruptionClause testPrimitives false [] [] hndlCleanPqspkSess = true := by
  decide

theorem deploymentSetup_counts_match_design :
    deploymentSetup.N_id = 2 ^ 20 ∧
    deploymentSetup.N_spk_tot = 2 ^ 25 ∧
    deploymentSetup.N_send_tot = 2 ^ 30 ∧
    deploymentSetup.N_recv_tot = 2 ^ 31 ∧
    deploymentSetup.N_sess_tot = 3 * (2 ^ 30) := by
  decide

theorem clampIdealByte_clamp0 (b : UInt8) :
    clampIdealByte (b &&& 0xF8) = clampIdealByte b := by
  revert b; decide

theorem clampIdealByte_clamp31 (b : UInt8) :
    clampIdealByte ((b &&& 0x7F) ||| 0x40) = clampIdealByte b := by
  revert b; decide

theorem clampIdealByte_not_ge_ed (b : UInt8) :
    decide (clampIdealByte b >= 0xED) = false := by
  revert b; decide

theorem getD_0_clampIdeal32_not_ge_ed (bs : Bytes) :
    decide ((clampIdeal32 bs).getD 0 0 >= 0xED) = false := by
  have hlen : (fitBytes 32 bs).length = 32 := fitBytes_length 32 bs
  have hlt : 0 < (fitBytes 32 bs).length := by omega
  unfold clampIdeal32
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt]
  simp only [Option.map_some, Option.getD_some]
  exact clampIdealByte_not_ge_ed _

theorem scalarIsInRange_clampIdeal32 (bs : Bytes) :
    scalarIsInRange (clampIdeal32 bs) = true := by
  unfold scalarIsInRange
  rw [getD_31_clampIdeal32_and_80, getD_0_clampIdeal32_not_ge_ed]
  rfl

theorem isCanonical32_clampIdeal32 (bs : Bytes) :
    isCanonical32 (clampIdeal32 bs) = true := by
  unfold isCanonical32
  rw [clampIdeal32_length, scalarIsInRange_clampIdeal32]
  rfl

theorem reduceCanonIdeal32_eq_of_isCanonical32 {bs : Bytes} (h : isCanonical32 bs = true) :
    reduceCanonIdeal32 bs = bs := by
  unfold reduceCanonIdeal32
  rw [h]
  rfl

theorem reduceCanonIdeal32_length (bs : Bytes) : (reduceCanonIdeal32 bs).length = 32 := by
  unfold reduceCanonIdeal32
  split <;> rename_i h
  · unfold isCanonical32 at h
    rw [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  · exact clampIdeal32_length bs

theorem isCanonical32_reduceCanonIdeal32 (bs : Bytes) :
    isCanonical32 (reduceCanonIdeal32 bs) = true := by
  unfold reduceCanonIdeal32
  split <;> rename_i h
  · exact h
  · exact isCanonical32_clampIdeal32 bs

theorem reduceCanonIdeal32_idem (bs : Bytes) :
    reduceCanonIdeal32 (reduceCanonIdeal32 bs) = reduceCanonIdeal32 bs :=
  reduceCanonIdeal32_eq_of_isCanonical32 (isCanonical32_reduceCanonIdeal32 bs)

theorem clampIdeal32_reduceCanonIdeal32 (bs : Bytes) :
    clampIdeal32 (reduceCanonIdeal32 bs) = clampIdeal32 bs := by
  unfold reduceCanonIdeal32
  split
  · rfl
  · exact clampIdeal32_idem bs

theorem clampIdeal32_clampScalar25519 (sk : Bytes) :
    clampIdeal32 (clampScalar25519 sk) = clampIdeal32 sk := by
  have hlen : (clampScalar25519 sk).length = 32 := clampScalar25519_length sk
  unfold clampIdeal32
  rw [fitBytes_of_length_eq hlen]
  unfold clampScalar25519
  dsimp only [fitBytesRef]
  rw [List.map_append, List.map_append, List.map_map, List.map_map]
  have hf0 : (clampIdealByte ∘ fun b => b &&& 0xF8) = clampIdealByte := by
    funext b; exact clampIdealByte_clamp0 b
  have hf31 : (clampIdealByte ∘ fun b => (b &&& 0x7F) ||| 0x40) = clampIdealByte := by
    funext b; exact clampIdealByte_clamp31 b
  rw [hf0, hf31, ← List.map_append, ← List.map_append]
  change List.map clampIdealByte
      ((fitBytes 32 sk).take 1 ++ ((fitBytes 32 sk).drop 1).take 30 ++
        ((fitBytes 32 sk).drop 31).take 1) =
    List.map clampIdealByte (fitBytes 32 sk)
  have h1 :
      (fitBytes 32 sk).take 1 ++ ((fitBytes 32 sk).drop 1).take 30 = (fitBytes 32 sk).take 31 := by
    simpa using (List.take_add (i := 1) (j := 30) (l := fitBytes 32 sk)).symm
  have h2 :
      (fitBytes 32 sk).take 31 ++ ((fitBytes 32 sk).drop 31).take 1 = (fitBytes 32 sk).take 32 := by
    simpa using (List.take_add (i := 31) (j := 1) (l := fitBytes 32 sk)).symm
  have h3 : (fitBytes 32 sk).take 32 = fitBytes 32 sk := by
    exact List.take_of_length_le (by rw [fitBytes_length])
  rw [h1, h2, h3]

theorem idealX25519_comm (a b : Bytes) : idealX25519 a b = idealX25519 b a := by
  unfold idealX25519
  rw [xorBytes_comm]

theorem idealX25519_length (a b : Bytes) : (idealX25519 a b).length = 32 := by
  unfold idealX25519
  exact clampIdeal32_length _

theorem clampIdealByte_ne_zero (b : UInt8) : clampIdealByte b ≠ 0 := by
  revert b; decide

theorem clampIdeal32_ne_zero (bs : Bytes) :
    clampIdeal32 bs ≠ List.replicate 32 0 := by
  intro h
  have hlen : (fitBytes 32 bs).length = 32 := fitBytes_length 32 bs
  have hlt : 0 < (fitBytes 32 bs).length := by omega
  have hget := congrArg (fun xs : Bytes => xs.getD 0 0) h
  unfold clampIdeal32 at hget
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt] at hget
  simp only [Option.map_some, Option.getD_some, List.replicate_succ, List.getD_cons_zero] at hget
  exact clampIdealByte_ne_zero _ hget

theorem idealX25519_ne_zero (sk pk : Bytes) :
    idealX25519 sk pk ≠ List.replicate 32 0 :=
  clampIdeal32_ne_zero _

theorem idealRoundtripPrimitives_isCanonical_eq_isCanonicalRef (pk : Bytes) :
    idealRoundtripPrimitives.isCanonical pk = isCanonicalRef idealRoundtripPrimitives pk := by
  dsimp only [idealRoundtripPrimitives, idealLeafPrimitives, isCanonicalRef]
  by_cases hcanon : isCanonical32 pk = true
  · have hpair : pk.length = 32 ∧ scalarIsInRange pk = true := by
      unfold isCanonical32 at hcanon
      rw [Bool.and_eq_true, beq_iff_eq] at hcanon
      exact hcanon
    have hlen : pk.length = 32 := hpair.1
    have hrange : scalarIsInRange pk = true := hpair.2
    have h80 : ((pk.getD 31 0 &&& 0x80) == 0) = true := by
      unfold scalarIsInRange at hrange
      rw [Bool.and_eq_true] at hrange
      exact hrange.1
    have htake : (pk ++ List.replicate 128 0).take 32 = pk := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    rw [hcanon, hlen, h80, hrange]
    simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte, htake, hcanon]
  · have hfalse : isCanonical32 pk = false := Bool.eq_false_iff.mpr hcanon
    simp [hfalse]

theorem clampIdealByte_and_e0 (b : UInt8) :
    clampIdealByte b &&& 0xE0 = 0 := by
  revert b; decide

theorem getD_31_clampIdeal32_and_e0 (bs : Bytes) :
    ((clampIdeal32 bs).getD 31 0 &&& 0xE0) = 0 := by
  have hlen : (fitBytes 32 bs).length = 32 := fitBytes_length 32 bs
  have hlt : 31 < (fitBytes 32 bs).length := by omega
  unfold clampIdeal32
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt]
  simp only [Option.map_some, Option.getD_some]
  exact clampIdealByte_and_e0 _

theorem idealRoundtripPrimitives_sig_corr (sk msg r : Bytes) :
    idealRoundtripPrimitives.sigVerify (idealRoundtripPrimitives.sigPkGen sk) msg
      (idealRoundtripPrimitives.sigSign sk msg r) = true := by
  dsimp only [idealRoundtripPrimitives, idealLeafPrimitives, xeddsaVerifyRef]
  have hpk_len : (clampIdeal32 sk).length = 32 := clampIdeal32_length sk
  have hpk_canon : isCanonical32 (clampIdeal32 sk) = true := isCanonical32_clampIdeal32 sk
  set capR := clampIdeal32 (xorBytes (clampIdeal32 msg) (clampIdeal32 sk))
  have hcapR_len : capR.length = 32 := clampIdeal32_length _
  have hsig_len : (capR ++ capR).length = 64 := by
    rw [List.length_append, hcapR_len]
  have hget63 : (capR ++ capR).getD 63 0 = capR.getD 31 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    rw [List.getD_eq_getElem?_getD, hcapR_len]
  have he0 : ((capR ++ capR).getD 63 0 &&& 0x60) = 0 := by
    rw [hget63]
    exact getD_31_clampIdeal32_and_60 _
  have h80 : ((capR ++ capR).getD 63 0 &&& 0x80) = 0 := by
    rw [hget63]
    exact getD_31_clampIdeal32_and_80 _
  have htake_sig : (capR ++ capR).take 32 = capR :=
    List.take_left' hcapR_len
  have hdrop_sig : (capR ++ capR).drop 32 = capR :=
    List.drop_left' hcapR_len
  have hcond1 :
      ((clampIdeal32 sk).length == 32 && (capR ++ capR).length == 64 &&
        ((capR ++ capR).getD 63 0 &&& 0x60 == 0)) = true := by
    rw [hpk_len, hsig_len, he0]; decide
  have hcond2 : (((capR ++ capR).getD 63 0 &&& 0x80) >>> 7 == 0 &&
      isCanonical32 (clampIdeal32 sk)) = true := by
    rw [h80, hpk_canon]; decide
  have hsScalar : clampIdeal32 (capR.take 31 ++ [capR.getD 31 0 &&& 0x7F]) = capR :=
    clampIdeal32_clamped31 _
  have hfit_take : (fitBytes 160 capR).take 32 = capR := by
    unfold fitBytes
    rw [List.take_append_of_le_length (by rw [List.length_take, hcapR_len]; omega)]
    rw [List.take_take, Nat.min_eq_left (by decide)]
    exact List.take_of_length_le (by omega)
  have hclamp_capR : clampIdeal32 capR = capR := clampIdeal32_idem _
  rw [hcond1, hcond2]
  simp only [↓reduceIte, htake_sig, hdrop_sig, hsScalar, hclamp_capR, hfit_take, beq_self_eq_true]

theorem idealX25519_clamp_left (a y : Bytes) :
    idealX25519 (clampIdeal32 a) y = idealX25519 a y := by
  unfold idealX25519; rw [clampIdeal32_idem]

/-- Every byte string satisfies `onCurveKey` for `idealRoundtripPrimitives`: non-canonical inputs
    satisfy the right disjunct via `clampIdeal32 pk`. -/
theorem idealRoundtripPrimitives_onCurveKey (pk : Bytes) :
    onCurveKey idealRoundtripPrimitives pk := by
  by_cases hc : isCanonical32 pk = true
  · exact Or.inl hc
  · have hf : isCanonical32 pk = false := Bool.eq_false_iff.mpr hc
    refine Or.inr ⟨clampIdeal32 pk, clampIdeal32_length pk, ?_⟩
    show reduceCanonIdeal32 pk = reduceCanonIdeal32 (clampIdeal32 (clampIdeal32 pk))
    rw [clampIdeal32_idem, reduceCanonIdeal32_eq_of_isCanonical32 (isCanonical32_clampIdeal32 pk)]
    unfold reduceCanonIdeal32
    rw [hf]; rfl

theorem idealRoundtripPrimitives_isValidDhTriple_ref (X Y Z : Bytes) :
    idealRoundtripPrimitives.isValidDhTriple X Y Z = true ↔
      isValidDhTripleRef idealRoundtripPrimitives X Y Z := by
  unfold isValidDhTripleRef
  have hOnX : onCurveKey idealRoundtripPrimitives X := idealRoundtripPrimitives_onCurveKey X
  have hOnY : onCurveKey idealRoundtripPrimitives Y := idealRoundtripPrimitives_onCurveKey Y
  show ((clampIdeal32 X == X || clampIdeal32 Y == Y) &&
      reduceCanonIdeal32 Z == reduceCanonIdeal32 (idealX25519 X Y)) = true ↔
    onCurveKey idealRoundtripPrimitives X ∧ onCurveKey idealRoundtripPrimitives Y ∧
      ((∃ a, X = clampIdeal32 a ∧ reduceCanonIdeal32 Z = reduceCanonIdeal32 (idealX25519 a Y)) ∨
        (∃ b, Y = clampIdeal32 b ∧ reduceCanonIdeal32 Z = reduceCanonIdeal32 (idealX25519 b X)))
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hX | hY, hZ⟩
    · exact ⟨hOnX, hOnY, Or.inl ⟨X, hX.symm, hZ⟩⟩
    · exact ⟨hOnX, hOnY, Or.inr ⟨Y, hY.symm, by rw [idealX25519_comm]; exact hZ⟩⟩
  · rintro ⟨_, _, ⟨a, rfl, hZ⟩ | ⟨b, rfl, hZ⟩⟩
    · exact ⟨Or.inl (clampIdeal32_idem a), by rw [idealX25519_clamp_left]; exact hZ⟩
    · exact ⟨Or.inr (clampIdeal32_idem b),
        by rw [idealX25519_comm, idealX25519_clamp_left]; exact hZ⟩

theorem idealRoundtripPrimitives_wellFormed : WellFormedPrimitives idealRoundtripPrimitives where
  isValidDhTriple_eq_ref := idealRoundtripPrimitives_isValidDhTriple_ref
  x25519_comm := by
    intro a b
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives, idealX25519]
    rw [clampIdeal32_idem, clampIdeal32_idem, xorBytes_comm]
  canon_base := isCanonical32_clampIdeal32
  canon_x25519 := fun _ _ _ _ => isCanonical32_clampIdeal32 _
  sigPkGen_eq_x25519Base := rfl
  pow8_idemp := reduceCanonIdeal32_idem
  pow8_x25519_comm := by
    intro a b
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives, idealX25519]
    rw [clampIdeal32_idem, clampIdeal32_idem, xorBytes_comm]
  ddh_consistent := by
    intro a b z
    show ((clampIdeal32 (clampIdeal32 a) == clampIdeal32 a ||
        clampIdeal32 (clampIdeal32 b) == clampIdeal32 b) &&
      reduceCanonIdeal32 z == reduceCanonIdeal32 (idealX25519 (clampIdeal32 a) (clampIdeal32 b)))
        = true ↔ reduceCanonIdeal32 z = reduceCanonIdeal32 (idealX25519 a (clampIdeal32 b))
    simp only [clampIdeal32_idem, idealX25519_clamp_left, beq_self_eq_true, Bool.true_or,
      Bool.true_and, beq_iff_eq]
  ddh_consistent_left := by
    intro a pk z _
    show ((clampIdeal32 (clampIdeal32 a) == clampIdeal32 a || clampIdeal32 pk == pk) &&
      reduceCanonIdeal32 z == reduceCanonIdeal32 (idealX25519 (clampIdeal32 a) pk)) = true ↔
        reduceCanonIdeal32 z = reduceCanonIdeal32 (idealX25519 a pk)
    simp only [clampIdeal32_idem, idealX25519_clamp_left, beq_self_eq_true, Bool.true_or,
      Bool.true_and, beq_iff_eq]
  x25519_congr_of_base_eq := by
    intro a1 a2 pk _ _ _ h
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives] at h ⊢
    unfold idealX25519
    rw [h]
  ddh_symm := by
    intro pk1 pk2 z
    show ((clampIdeal32 pk1 == pk1 || clampIdeal32 pk2 == pk2) &&
        reduceCanonIdeal32 z == reduceCanonIdeal32 (idealX25519 pk1 pk2)) =
      ((clampIdeal32 pk2 == pk2 || clampIdeal32 pk1 == pk1) &&
        reduceCanonIdeal32 z == reduceCanonIdeal32 (idealX25519 pk2 pk1))
    rw [Bool.or_comm, idealX25519_comm]
  x25519_pow8_congr := by
    intro a pk1 pk2 _ _ h
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives, idealX25519] at h ⊢
    have hc : clampIdeal32 pk1 = clampIdeal32 pk2 := by
      rw [← clampIdeal32_reduceCanonIdeal32 pk1, ← clampIdeal32_reduceCanonIdeal32 pk2, h]
    rw [hc]
  canon_pow8_inj := by
    intro pk1 pk2 h1 h2 hpow
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives] at h1 h2 hpow
    rw [reduceCanonIdeal32_eq_of_isCanonical32 h1,
      reduceCanonIdeal32_eq_of_isCanonical32 h2] at hpow
    exact hpow
  x25519_len := idealX25519_length
  x25519Base_len := clampIdeal32_length
  pow8_len := reduceCanonIdeal32_length
  sha512_len := sha512Ref_length idealLeafPrimitives
  scalarMul_len := by
    intro a b
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives]
    rw [xorBytes_length, clampIdeal32_length, clampIdeal32_length]
    rfl
  scalarAdd_len := by
    intro a b
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives]
    rw [xorBytes_length, clampIdeal32_length, clampIdeal32_length]
    rfl
  scalarFromBytesModOrder_len := clampIdeal32_length
  scalarFromWide_len := fun b => clampIdeal32_length (b.take 32)
  montToEd_len := by
    intro u s pt h
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives] at h
    split at h <;> rename_i hcond
    · injection h with hpt
      subst hpt
      rw [Bool.and_eq_true, beq_iff_eq, isCanonical32, Bool.and_eq_true, beq_iff_eq] at hcond
      have hu : u.length = 32 := hcond.2.1
      rw [List.length_append, hu, List.length_replicate]
    · contradiction
  edNeg_len := fun pt => fitBytes_length 160 (clampIdeal32 (pt.take 32))
  doubleScalarMulBasepoint_len := fun _h _a s =>
    fitBytes_length 160 (clampIdeal32 s)
  compress_len := fun pt => clampIdeal32_length (pt.take 32)
  sigVerify_eq_xeddsaVerifyRef := fun _ _ _ => rfl
  isCanonical_eq_isCanonicalRef := idealRoundtripPrimitives_isCanonical_eq_isCanonicalRef
  kemKeyGen_valid := fun seed =>
    ⟨fitBytes_length 1568 (seed.take 32), fitBytes_length 3168 seed⟩
  kemEncaps_len := by
    intro pk r ss ct hEnc
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives] at hEnc
    injection hEnc with hPair
    injection hPair with hSs hCt
    subst hSs
    subst hCt
    refine ⟨fitBytes_length 32 r, ?_⟩
    rw [List.length_append, fitBytes_length, List.length_replicate]
  kemDecaps_len := by
    intro _sk ct ss hDec
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives] at hDec
    injection hDec with hSs
    subst hSs
    exact fitBytes_length 32 (ct.take 32)
  spqrInitSend_some := fun _ _ => rfl
  aead_corr := fun mk ad pt =>
    aes256CbcHmac_roundtrip idealRoundtripPrimitives
      (fun k b => by
        dsimp only [idealRoundtripPrimitives, idealLeafPrimitives]
        rw [xorBytes_length, fitBytes_length, fitBytes_length]; rfl)
      idealAesBlock_corr mk ad pt
  kem_corr := by
    intro seed r ss ct hEnc
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives] at hEnc ⊢
    injection hEnc with hPair
    injection hPair with hSs hCt
    subst hSs
    subst hCt
    congr 1
    have hlen : (fitBytes 32 r).length = 32 := fitBytes_length 32 r
    have htake : (fitBytes 32 r ++ List.replicate 1536 0).take 32 = fitBytes 32 r := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    rw [htake, fitBytes_of_length_eq hlen]
  sig_corr := idealRoundtripPrimitives_sig_corr
  spqr_corr := by
    intro pqrKey coins stA salt? pqMsg hSend
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives] at hSend ⊢
    injection hSend with hTuple
    injection hTuple with hSt hRest
    injection hRest with hSalt _
    exact ⟨pqrKey, by rw [← hSalt]⟩
  spqrInitRecv_salt_len := by
    intro pqrKey pqMsg stB salt hRecv
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives] at hRecv
    injection hRecv with hTuple
    injection hTuple with _ hSalt
    injection hSalt with hSalt
    rw [← hSalt]; simp
  sha256Compress_len := fun st blk => fitBytes_length 32 _
  sha512Compress_len := fun st blk => fitBytes_length 64 _
  aesEncBlock_len := fun k blk => by
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives]
    rw [xorBytes_length, fitBytes_length, fitBytes_length]; rfl
  aesDecBlock_len := fun k blk => by
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives]
    rw [xorBytes_length, fitBytes_length, fitBytes_length]; rfl
  aesBlock_corr := idealAesBlock_corr
  sha512_eq_ref := fun _ => rfl
  hkdfDerive96_eq_ref := fun _ => rfl
  rootCreateChain_eq_ref := fun _ _ => rfl
  chainKdfSeed_eq_ref := fun _ => rfl
  chainKdfNext_eq_ref := fun _ => rfl
  deriveMsgKeys_eq_ref := fun _ _ => rfl
  aeadEnc_eq_ref := fun _ _ _ => rfl
  aeadDec_eq_ref := fun _ _ _ => rfl
  x25519_clamp := by
    intro sk pk
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives, idealX25519]
    rw [clampIdeal32_clampScalar25519]
  x25519Base_clamp := by
    intro sk
    dsimp only [idealRoundtripPrimitives, idealLeafPrimitives]
    exact clampIdeal32_clampScalar25519 sk
  x25519_base_ne_zero := fun a b _ _ =>
    idealX25519_ne_zero a (idealRoundtripPrimitives.x25519Base b)
  x25519_zero_iff := fun a1 a2 pk _ _ _ =>
    ⟨fun h => False.elim (idealX25519_ne_zero a1 pk h),
     fun h => False.elim (idealX25519_ne_zero a2 pk h)⟩
  kemDecaps_isSome := fun _ _ _ _ => rfl
  kemEncaps_isSome := fun _ _ _ _ => rfl

theorem idealRoundtripPrimitives_pqxdhCorrect : PqxdhCorrect idealRoundtripPrimitives :=
  wellFormed_pqxdhCorrect idealRoundtripPrimitives idealRoundtripPrimitives_wellFormed

/-- Boundary checks for `xeddsaVerifyRef`, `scalarIsInRange`, and `isCanonicalRef` around the
    `2^255 - 19` (`0xED, 0xFF^30, 0x7F`) modulus and bit-255 mask. -/
theorem kat_xeddsaVerifyRef_and_isCanonicalRef :
    xeddsaVerifyRef testPrimitives sampleIkB (encodeEC sampleSpkB) sampleSpkSig = true ∧
    xeddsaVerifyRef testPrimitives sampleIkB (encodeKEM samplePqspkB) samplePqspkSig = true ∧
    xeddsaVerifyRef testPrimitives sampleIkB (encodeEC sampleSpkB) (fitBytes 64 [0xFF]) = false ∧
    scalarIsInRange ([0xED] ++ List.replicate 30 0xFF ++ [0x7F]) = false ∧
    scalarIsInRange ([0xEC] ++ List.replicate 30 0xFF ++ [0x7F]) = true ∧
    scalarIsInRange (List.replicate 31 0xFF ++ [0x6D]) = true ∧
    scalarIsInRange (List.replicate 31 0x00 ++ [0x80]) = false ∧
    isCanonicalRef testPrimitives (testPrimitives.x25519Base sampleIkB) = true ∧
    isCanonicalRef testPrimitives ([0xED] ++ List.replicate 30 0xFF ++ [0x7F]) = false ∧
    isCanonicalRef testPrimitives ([0xEC] ++ List.replicate 30 0xFF ++ [0x7F]) = true ∧
    isCanonicalRef testPrimitives (List.replicate 31 0xFF ++ [0x6D]) = true ∧
    isCanonicalRef testPrimitives (List.replicate 31 0x00 ++ [0x80]) = false ∧
    isCanonicalRef testPrimitives (List.replicate 31 0xFF ++ [0x7F]) = false ∧
    isCanonicalRef testPrimitives (List.replicate 31 0x01 ++ [0x80]) = false := by
  decide

theorem headline_closed_and_split (S : Setup) :
    (SignalPqxdh.Security.Headline : Prop) =
      (∀ (P' : Primitives) (S' : Setup),
        (WellFormedPrimitives P' → PqxdhCorrect P') ∧
        PqxdhSecurityStatement S') ∧
    PqxdhSecurityStatement S = (PqxdhKeyIndStatement S ∧ PqxdhAuthStatement S) :=
  ⟨rfl, rfl⟩

theorem keyInd_statement_concrete_shape (S : Setup) :
    PqxdhKeyIndStatement S =
      (∃ R : KeyInd2KeyCostedReductionFamily S,
        KeyInd2KeyCostedReductionBounds S R ∧
        KeyInd2KeyReductionQueryBounds S R.eval ∧
        ∀ (P : Primitives), CryptoWellFormedPrimitives P →
          ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
            KeyIndAdvantage S P A.1 ≤
              pqxdhKeyIndBoundReal S
                (SigEufCma P (R.eval.sig b A))
                (KemShCrReal P (R.eval.shcr b A))
                (GapDH P P.isValidDhTriple P.pow8 (R.eval.gdh b A))) :=
  rfl

theorem keyInd1Key_statement_concrete_shape (S : Setup) :
    SignalPqxdh.Security.PqxdhKeyIndSecureδ S =
      (∃ R : KeyIndCostedReductionFamily S,
        KeyIndCostedReductionBounds S R ∧
        KeyIndReductionQueryBounds S R.eval ∧
        ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
          ∀ (δ : ℝ≥0∞), KemDeltaCorrect P δ →
          ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
            KeyInd1KeyRoAdvantage S P A.1 ≤
              SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b.q_on δ
                (GapSigEufCma P P.isValidDhTriple (R.eval.sig b A))
                (KemShCr P (R.eval.shcr b A))
                (GapDhWithSign P P.isValidDhTriple P.pow8 (R.eval.gdh b A))) :=
  rfl

theorem auth_statement_concrete_shape (S : Setup) :
    PqxdhAuthStatement S =
      (∃ R : AuthCostedReductionFamily S,
        AuthCostedReductionBounds S R ∧
        AuthReductionQueryBounds S R.eval ∧
        PqxdhAuthStatementWith S R.eval) :=
  rfl

theorem costed_security_statement_concrete_shape :
    SignalPqxdhSecurityCosted =
      ((∀ (P : Primitives), WellFormedPrimitives P → PqxdhCorrect P) ∧
       ∀ (S : Setup), ∃ R : PqxdhReds S,
         PqxdhBounds S R ∧
         PqxdhKeyIndStatementWith S R.keyInd.toSimulators ∧
         PqxdhAuthStatementWith S R.auth.toSimulators) :=
  rfl

theorem stepCostBudget_concrete_shape (S : Setup) (b : QueryBudget) :
    stepCostBudget S b =
      let M_dh := min b.q_total S.N_dh
      let M_sess := min b.q_total S.N_sess_tot
      2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) +
        2 ^ 15 * (b.q_total + 1) * (M_dh + M_sess) +
        2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
        2 ^ 11 * M_dh ^ 2 + 2 ^ 8 * M_dh * M_sess :=
  rfl

def sampleWellSizedInitWithOpk : InitiateInput :=
  { sampleInitWithOpk with
    kemCoins  := fitBytes 32 sampleKemCoins
    spqrCoins := fitBytes 32 sampleSpqrCoins
    bundle    :=
      { sampleBundleWithOpk with
        pqspkB := fitBytes 1568 samplePqspkB } }

def sampleWellSizedHdr : HandshakeHdr where
  ikAPk   := sampleIkA
  ekAPk   := sampleEkA
  kemCt   := List.replicate 1568 0x55
  spkId   := 7
  pqspkId := 9
  opkId?  := some 42

def sampleWellSizedAcceptInput : AcceptInput where
  keysInp :=
    { sampleAcceptKeysBaseWithOpk sampleWellSizedHdr with
      ikBPk    := testPrimitives.x25519Base sampleIkB
      pqspkBSk := List.replicate 3168 0x11
      pqspkBPk := List.replicate 1568 0x22 }
  msg :=
    { hdr          := sampleWellSizedHdr
      ephAPk       := sampleEphA1
      pqRatchetMsg := List.replicate 32 0x52
      aeadCt       := List.replicate 64 0xEE }

/-- Test primitives whose `x25519` returns `0^32` on the low-order peer key `0^32`. -/
def lowOrderX25519Primitives : Primitives :=
  { testPrimitives with
    x25519 := fun sk pk =>
      if pk == List.replicate 32 0 then List.replicate 32 0 else testPrimitives.x25519 sk pk }

/-- `Model.initiateKeys`, `Model.acceptKeys`, and `Model.accept` reject a low-order peer key whose
    X25519 shared secret is `0^32`. -/
theorem zeroDh_acceptKeys_and_initiateKeys_reject :
    let lowOrderPk : Bytes := List.replicate 32 0
    Model.acceptKeys lowOrderX25519Primitives
      (sampleAcceptKeysBaseWithOpk { sampleWellSizedHdr with ikAPk := lowOrderPk }) = none ∧
    Model.acceptKeys lowOrderX25519Primitives
      (sampleAcceptKeysBaseWithOpk { sampleWellSizedHdr with ekAPk := lowOrderPk }) = none ∧
    Model.initiateKeys lowOrderX25519Primitives
      { sampleInitWithOpk.toInitiateKeysInput with
        bundle := { sampleBundleWithOpk with spkB := lowOrderPk } } = none ∧
    Model.initiateKeys lowOrderX25519Primitives
      { sampleInitWithOpk.toInitiateKeysInput with
        bundle := { sampleBundleWithOpk with opkB? := some (42, lowOrderPk) } } = none ∧
    Model.accept lowOrderX25519Primitives
      { sampleWellSizedAcceptInput with
        msg := { sampleWellSizedAcceptInput.msg with ephAPk := lowOrderPk } } = none := by
  decide

def trivialKeyIndAdv (S : Setup) : KeyIndAdversary S := ⟨pure false⟩

theorem trivialKeyIndAdv_bounded (S : Setup) (b : QueryBudget) :
    QueryBounded (trivialKeyIndAdv S) b :=
  ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- `KeyIndAdversary` that draws `unifSpec` coins and makes one `.roQuery` (`q_on = 0`,
    `q_ro = 1`, `q_total = 1`). -/
def roAndCoinKeyIndAdv (S : Setup) : KeyIndAdversary S where
  run :=
    liftM ((unifSpec + keyIndSpec S).query (Sum.inl 1)) >>= fun _ =>
    liftM ((unifSpec + keyIndSpec S).query (Sum.inr (.roQuery []))) >>= fun _ =>
    pure false

theorem roAndCoinKeyIndAdv_bounded (S : Setup) :
    QueryBounded (roAndCoinKeyIndAdv S) { q_ro := 1, q_roRoot := 0, q_total := 1, q_on := 0 } := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [roAndCoinKeyIndAdv]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [isKeyIndRoQuery]), fun _ => ?_⟩
    simp only [isKeyIndRoQuery, ↓reduceIte]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩
  · simp only [roAndCoinKeyIndAdv]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [isKeyIndSendQuery]), fun _ => ?_⟩
    simp only [isKeyIndSendQuery, ↓reduceIte]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [isKeyIndSendQuery]), fun _ => trivial⟩
  · simp only [roAndCoinKeyIndAdv]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [isKeyIndRecvQuery]), fun _ => ?_⟩
    simp only [isKeyIndRecvQuery, ↓reduceIte]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [isKeyIndRecvQuery]), fun _ => trivial⟩
  · simp only [roAndCoinKeyIndAdv]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [isGameQuery]), fun _ => ?_⟩
    simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩
  · simp only [roAndCoinKeyIndAdv]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [isKeyIndOnlineQuery]), fun _ => ?_⟩
    simp only [isKeyIndOnlineQuery, ↓reduceIte]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [isKeyIndOnlineQuery]), fun _ => trivial⟩

/-- `KeyIndAdversary` that makes one online `.initPrin u` query (`q_on = 1`, `q_ro = 0`). -/
def initPrinKeyIndAdv (S : Setup) (u : Fin S.N_id) : KeyIndAdversary S where
  run :=
    liftM ((unifSpec + keyIndSpec S).query (Sum.inr (.initPrin u))) >>= fun _ =>
    pure false

theorem initPrinKeyIndAdv_bounded (S : Setup) (u : Fin S.N_id) :
    QueryBounded (initPrinKeyIndAdv S u) { q_ro := 0, q_roRoot := 0, q_total := 1, q_on := 1 } := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [initPrinKeyIndAdv]; rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [isKeyIndRoQuery]), fun _ => trivial⟩
  · simp only [initPrinKeyIndAdv]; rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [isKeyIndSendQuery]), fun _ => trivial⟩
  · simp only [initPrinKeyIndAdv]; rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [isKeyIndRecvQuery]), fun _ => trivial⟩
  · simp only [initPrinKeyIndAdv]; rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩
  · simp only [initPrinKeyIndAdv]; rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

theorem initPrinKeyIndAdv_not_bounded_zero (S : Setup) (u : Fin S.N_id) :
    ¬ QueryBounded (initPrinKeyIndAdv S u) { q_ro := 0, q_roRoot := 0, q_total := 1, q_on := 0 } := by
  intro ⟨_, _, _, _, hOn⟩
  simp only [initPrinKeyIndAdv] at hOn
  rw [OracleComp.isQueryBoundP_query_bind_iff] at hOn
  rcases hOn.1 with hFalse | hPos
  · exact hFalse trivial
  · exact Nat.not_lt_zero _ hPos

def dummyKeyIndSimulators (S : Setup) : KeyIndReductionFamily S where
  sig  := fun _ _ => { run := fun _ => pure ([], []), q_sig := 0, q_ddh := 0, q_prim := 0 }
  shcr := fun _ _ =>
    { State := Unit, choosePk := fun pk _ => pure (pk, ()),
      findCollision := fun _ _ ct => pure ct, q_prim := 0 }
  gdh  := fun _ _ => { run := fun _ _ => pure [], q_ddh := 0, q_sig := 0, q_prim := 0 }

theorem dummyKeyIndSimulators_bounds (S : Setup) :
    KeyIndReductionQueryBounds S (dummyKeyIndSimulators S) where
  sig_bounded  := fun _ _ => ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial⟩
  shcr_bounded := fun _ _ => ⟨fun _ _ => trivial, fun _ _ _ => trivial⟩
  gdh_bounded  := fun _ _ => ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

def dummyKeyInd2KeySimulators (S : Setup) : KeyInd2KeyReductionFamily S where
  sig  := fun _ _ => { run := fun _ => pure ([], []), q_sig := 0, q_prim := 0 }
  shcr := fun _ _ =>
    { State := Unit, choosePk := fun pk _ => pure (pk, ()),
      findCollision := fun _ _ ct => pure ct, q_prim := 0 }
  gdh  := fun _ _ => { run := fun _ _ => pure [], q_ddh := 0, q_prim := 0 }

theorem dummyKeyInd2KeySimulators_bounds (S : Setup) :
    KeyInd2KeyReductionQueryBounds S (dummyKeyInd2KeySimulators S) where
  sig_bounded  := fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩
  shcr_bounded := fun _ _ => ⟨fun _ _ => trivial, fun _ _ _ => trivial⟩
  gdh_bounded  := fun _ _ => ⟨fun _ _ => trivial, fun _ _ => trivial⟩

/-- `GapDhAdv` witness that makes a single `PrimQuery.x25519` call (`q_prim = 1`, `q_ddh = 0`). -/
def primQueryingGapDhAdv : GapDhAdv where
  run := fun U V =>
    (liftM ((PrimBaseSpec + gapDhOracleSpec).query
      (Sum.inl (Sum.inr (PrimQuery.x25519 U V)))) >>= fun z => pure z)
  q_ddh := 0
  q_prim := 1

theorem primQueryingGapDhAdv_bounded : primQueryingGapDhAdv.Bounded :=
  ⟨fun _ _ => by
    simp only [primQueryingGapDhAdv]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl Bool.false_ne_true, fun _ => trivial⟩,
   fun _ _ => by
    simp only [primQueryingGapDhAdv]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩⟩

def primQueryingGapDhWithSignAdv : GapDhWithSignAdv where
  run := fun U V =>
    (liftM ((PrimBaseSpec + sigAndDdhSpec).query
      (Sum.inl (Sum.inr (PrimQuery.x25519 U V)))) >>= fun z => pure z)
  q_ddh := 0
  q_sig := 0
  q_prim := 1

theorem primQueryingGapDhWithSignAdv_bounded : primQueryingGapDhWithSignAdv.Bounded :=
  ⟨fun _ _ => by
    simp only [primQueryingGapDhWithSignAdv]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl Bool.false_ne_true, fun _ => trivial⟩,
   fun _ _ => by
    simp only [primQueryingGapDhWithSignAdv]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl Bool.false_ne_true, fun _ => trivial⟩,
   fun _ _ => by
    simp only [primQueryingGapDhWithSignAdv]
    rw [OracleComp.isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩⟩

def d4Hdr : HandshakeHdr :=
  { ikAPk := sampleIkA, ekAPk := sampleEkA, spkId := 0, opkId? := none, pqspkId := 0,
    kemCt := [0xC0, 0x01] }

def d4DrKey : DRKey := { rootKey := [1], chainKey := [2], pqrKey := [3] }

def d4Init : KeyIndInitiatorEntry testSetup :=
  { sid := .sendNoOPK ⟨0, by decide⟩ ⟨0, by decide⟩
    honestPeer := some 1
    peerIkPk := sampleIkB
    peerSpkPk := sampleSpkB
    peerOpkPk? := none
    peerPqspkPk := samplePqspkB
    spkHonest := true
    opkHonest := false
    pqspkHonest := true
    fresh := true
    tested := true
    ekASk := sampleEkA
    drKeyReal := d4DrKey
    drKeyRand := d4DrKey
    hdr := d4Hdr }

def d4Resp : KeyIndRespEntry testSetup :=
  { sid := .recvNoOPK ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩
    respIkPk := sampleIkB
    spkPk := sampleSpkB
    opkPk? := none
    pqspkPk := samplePqspkB
    hdr := { d4Hdr with spkId := 7, pqspkId := 7 } -- key ids are ignored by partnering
    senderHonest := true
    drKeyReal := d4DrKey
    drKeyRand := d4DrKey
    tested := true }

/-- Partnering and reveal freshness: partnering ignores header key IDs but depends on `kemCt`;
    session-key reveal invalidates freshness of both partners; and an unpartnered tested responder
    is fresh under `useRo = true` only when its claimed sender is uncorrupted, and never under
    `useRo = false` (HNDL). -/
theorem regression_d4_partnering_reveal_freshness :
    let alice : PrincipalEntry :=
      { secIKA0 := [], ikAPk := sampleIkA, secIKAsign := [], ikSignPk := [], corrupted := false }
    let aliceCorr : PrincipalEntry := { alice with corrupted := true }
    let unpartnered : KeyIndRespEntry testSetup :=
      { d4Resp with hdr := { d4Hdr with kemCt := [9] } }
    keyIndPartner testPrimitives d4Init d4Resp = true ∧
    keyIndPartner testPrimitives d4Init unpartnered = false ∧
    isKeyIndInitStillFresh testPrimitives true [] [] [d4Resp] d4Init = true ∧
    isKeyIndInitStillFresh testPrimitives true [] []
      [{ d4Resp with revealed := true }] d4Init = false ∧
    isKeyIndInitStillFresh testPrimitives true [] []
      [d4Resp] { d4Init with revealed := true } = false ∧
    isKeyIndRespStillFresh testPrimitives true [] [] [d4Init] d4Resp = true ∧
    isKeyIndRespStillFresh testPrimitives true [] []
      [{ d4Init with revealed := true }] d4Resp = false ∧
    isKeyIndRespStillFresh testPrimitives true [(0, alice)] [] [d4Init] unpartnered = true ∧
    isKeyIndRespStillFresh testPrimitives true [(0, aliceCorr)] [] [d4Init] unpartnered = false ∧
    isKeyIndRespStillFresh testPrimitives false [(0, alice)] [] [d4Init] unpartnered = false := by
  decide

/-! `cwfPrimitives` instantiates `CryptoWellFormedPrimitives` (which adds `ec_coll_bound`,
`kem_coll_bound`, and `x25519_inj_pow8` to `WellFormedPrimitives`, ruled out for
`idealRoundtripPrimitives`). Here `x25519Base = cwfC` retains the 251 clamp-surviving scalar bits,
`pow8 = cwfP8` projects non-zero 32-byte points via `cwfC` and maps others to `0^32`, and `x25519`
is canonicalized XOR. -/

theorem cwfMask_fix (i : Nat) : cwfFix i &&& cwfMask i = 0 := by
  rcases cwfByte_cases i with ⟨hm, hf⟩ | ⟨hm, hf⟩ | ⟨hm, hf⟩ <;> rw [hm, hf] <;> rfl

theorem cwfC_fit (bs : Bytes) : cwfC (fitBytes 32 bs) = cwfC bs := by
  unfold cwfC; rw [fitBytes_of_length_eq (fitBytes_length 32 bs)]

/-- `goodFirstMsgAD` accepts honest first-message ADs (with or without `pq_ratchet`) and rejects
    truncated inputs. -/
example : goodFirstMsgAD (firstMsgAD (List.replicate 32 1) (List.replicate 32 2)
    (List.replicate 32 3) [7, 8, 9]) = true := by decide
example : goodFirstMsgAD (firstMsgAD (List.replicate 32 1) (List.replicate 32 2)
    (List.replicate 32 3) []) = true := by decide
example : goodFirstMsgAD [0x05, 1, 2] = false := by decide

/-- Off-curve input `cwfZero` in both slots is rejected by `cwfPrimitives.isValidDhTriple`. -/
theorem cwfPrimitives_ddh_off_base (z : Bytes) :
    cwfPrimitives.isValidDhTriple cwfZero cwfZero z = false := by
  show (cwfGood cwfZero && cwfGood cwfZero &&
    (cwfC cwfZero == cwfZero || cwfC cwfZero == cwfZero) &&
    cwfP8 z == cwfP8 (cwfDh cwfZero cwfZero)) = false
  simp [cwfGood_zero]

/-- `cwfPrimitives.isValidDhTriple` rejects an off-curve `cwfZero` input paired with an honest
    base-point output `x25519Base sk`. -/
theorem cwfPrimitives_ddh_twist_right (sk z : Bytes) :
    cwfPrimitives.isValidDhTriple (cwfPrimitives.x25519Base sk) cwfZero z = false := by
  show (cwfGood (cwfC sk) && cwfGood cwfZero &&
    (cwfC (cwfC sk) == cwfC sk || cwfC cwfZero == cwfZero) &&
    cwfP8 z == cwfP8 (cwfDh (cwfC sk) cwfZero)) = false
  simp [cwfGood_zero]

theorem cwfC_fiber_card (c : Bytes) :
    (Finset.univ.filter (fun w : BitVec 256 => cwfC (word256ToBytes w) = c)).card ≤ 32 := by
  calc (Finset.univ.filter (fun w : BitVec 256 => cwfC (word256ToBytes w) = c)).card
      ≤ (Finset.range 8 ×ˢ Finset.range 4).card := by
        apply Finset.card_le_card_of_injOn (fun w => (w.toNat % 8, w.toNat / 2 ^ 254))
        · intro w _
          simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
          exact ⟨Nat.mod_lt _ (by decide), by
            have := w.isLt
            exact (Nat.div_lt_iff_lt_mul (by positivity)).2 (by omega)⟩
        · intro w hw w' hw' heq
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw hw'
          simp only [Prod.mk.injEq] at heq
          exact cwfC_word_eq w w' (hw.trans hw'.symm) heq.1 heq.2
    _ = 32 := by simp

theorem cwfPrimitives_ec_coll_bound (targetPk : Bytes) :
    (𝒟[do
        let sk ← sampleScalar32
        pure (cwfPrimitives.pow8 (cwfPrimitives.x25519Base sk) ==
          cwfPrimitives.pow8 targetPk)] {true}).toReal
        ≤ 1 / (2 : ℝ) ^ 251 := by
  have hc : ∀ sk, cwfPrimitives.pow8 (cwfPrimitives.x25519Base sk) = cwfC sk := fun sk =>
    cwfP8_cwfC sk
  simp only [hc, sampleScalar32, sampleBytes32, bind_pure_comp, Functor.map_map]
  refine le_trans (uniform256_map_bool_le _ 32 ?_) (by norm_num)
  refine le_trans (Finset.card_le_card ?_) (cwfC_fiber_card (cwfPrimitives.pow8 targetPk))
  intro w hw
  simpa using hw

/-- `cwfPrimitives` satisfies `CryptoWellFormedPrimitives`, with `cwfC` fiber cardinality `32`
    (`2^-251 ≤ 2^-250` for `ec_coll_bound`) and 32-byte seed prefixes (`2^-256 ≤ 2^-255` for
    `kem_coll_bound`). -/
theorem cwfPrimitives_cryptoWellFormed : CryptoWellFormedPrimitives cwfPrimitives where
  toWellFormedPrimitives := cwfPrimitives_wellFormed
  ec_coll_bound := fun t =>
    prob_le_one_div_two_pow_of_toReal (le_trans (cwfPrimitives_ec_coll_bound t) (by norm_num))
  kem_coll_bound := fun t =>
    prob_le_one_div_two_pow_of_toReal (cwfPrimitives_kem_coll_bound t)
  x25519_inj_pow8 := fun a pk1 pk2 _ _ _ h => cwfX_inj a pk1 pk2 h
  pow8_base_len := fun p e h => by
    change cwfP8 p = cwfP8 (cwfC e) at h
    have hg := cwfGood_of_P8_eq h
    rw [cwfGood_cwfC] at hg
    exact cwfGood_len hg
  kemDecaps_len_reject := fun _ ct hct => by
    dsimp only [cwfPrimitives, cwfLeafPrimitives]; simp [hct]
  kemEncaps_len_reject := fun pk _ hpk => by
    dsimp only [cwfPrimitives, cwfLeafPrimitives]; simp [hpk]

def koskRegSk : Bytes := List.replicate 32 0x07
def koskRegPk : Bytes := cwfPrimitives.x25519Base koskRegSk
def koskOtherSk : Bytes := List.replicate 32 0x55
def koskOtherPk : Bytes := cwfPrimitives.x25519Base koskOtherSk

def koskRegBundle : PreKeyBundleInput :=
  { ikB := koskRegPk, spkId := 0, spkB := koskRegPk, spkSig := [], opkB? := none,
    pqspkId := 0, pqspkB := [], pqspkSig := [] }

theorem kosk_registerAdvKey_spec (P : Primitives) (advKeys : List (Bytes × Bytes)) (sk : Bytes) :
    registerAdvKey P advKeys sk =
      if sk.length = 32 then
        some (P.x25519Base sk, (sk, P.x25519Base sk) :: advKeys)
      else none := by
  unfold registerAdvKey
  by_cases h : sk.length = 32 <;> simp [h]

theorem kosk_registerAdvKey_concrete :
    registerAdvKey cwfPrimitives [] koskRegSk = some (koskRegPk, [(koskRegSk, koskRegPk)]) ∧
    isAdvRegistered cwfPrimitives [(koskRegSk, koskRegPk)] koskRegPk = true ∧
    registerAdvKey cwfPrimitives [] (List.replicate 31 0x07) = none := by
  refine ⟨rfl, by decide, rfl⟩

/-- A bundle whose identity key and signed prekey are KOSK-registered passes `koskBundleOk` with
    empty game key tables. -/
theorem kosk_registered_bundle_accepted :
    koskBundleOk cwfPrimitives [] [] [] [(koskRegSk, koskRegPk)] koskRegBundle = true := by
  decide

theorem kosk_unregistered_rejected :
    koskBundleOk cwfPrimitives [] [] [] [(koskRegSk, koskRegPk)]
      { koskRegBundle with ikB := koskOtherPk } = false ∧
    koskSenderOk cwfPrimitives [] [(koskRegSk, koskRegPk)] koskOtherPk = false ∧
    koskSenderOk cwfPrimitives [] [(koskRegSk, koskRegPk)] koskRegPk = true := by
  decide

/-- Role separation in `koskBundleOk`: a game-generated OPK is accepted in the OPK slot but
    rejected as `spkB`. -/
theorem kosk_role_strict :
    let opks : List ((Nat × Nat × Nat) × OpkEntry) :=
      [((0, 0, 0), { opkSk := koskOtherSk, opkPk := koskOtherPk, consumed := false })]
    koskBundleOk cwfPrimitives [] [] opks [(koskRegSk, koskRegPk)]
      { koskRegBundle with opkB? := some (0, koskOtherPk) } = true ∧
    koskBundleOk cwfPrimitives [] [] opks [(koskRegSk, koskRegPk)]
      { koskRegBundle with spkB := koskOtherPk } = false := by
  decide

abbrev gapASetup : Setup :=
  { N_id := 1, N_recv := 1, N_opk := 1, N_no_opk := 1, N_send_opk := 1, N_send_no_opk := 1 }

def gapAHdr : HandshakeHdr :=
  { ikAPk := koskRegPk, ekAPk := [0x01], spkId := 0, opkId? := none, pqspkId := 0, kemCt := [0x02] }

def gapAKeyR : DRKey := { rootKey := [0xA1], chainKey := [0xA2], pqrKey := [0xA3] }
def gapAKeyX : DRKey := { rootKey := [0xB1], chainKey := [0xB2], pqrKey := [0xB3] }

def gapAInit : KeyIndInitiatorEntry gapASetup :=
  { sid := .sendNoOPK 0 0, honestPeer := none, peerIkPk := koskOtherPk, peerSpkPk := koskRegPk,
    peerOpkPk? := none, peerPqspkPk := [0x03], spkHonest := false, opkHonest := false,
    pqspkHonest := false, ekASk := [], fresh := false, drKeyReal := gapAKeyX,
    drKeyRand := gapAKeyX, hdr := gapAHdr, tested := false }

def gapAResp : KeyIndRespEntry gapASetup :=
  { sid := .recvNoOPK 0 0 0, respIkPk := koskOtherPk, spkPk := koskRegPk, opkPk? := none,
    pqspkPk := [0x03], hdr := gapAHdr, senderHonest := false, drKeyReal := gapAKeyX,
    drKeyRand := gapAKeyR }

/-- `keyIndPartnerRandKey?` returns the partnered responder's random key and `none` when
    unpartnered. -/
theorem gapA_partner_rand_key_lookup :
    keyIndPartner cwfPrimitives gapAInit gapAResp = true ∧
    keyIndPartnerRandKey? cwfPrimitives [gapAResp] gapAInit = some gapAKeyR ∧
    keyIndPartnerRandKey? cwfPrimitives [] gapAInit = none ∧
    keyIndPartnerRandKey? cwfPrimitives
      [{ gapAResp with hdr := { gapAHdr with kemCt := [0x04] } }] gapAInit = none := by
  decide

def p30SpkEntry : SpkBundleEntry :=
  { spkSk := [], spkPk := sampleSpkB, spkSig := [], pqspkSk := [], pqspkPk := [], pqspkSig := [] }
def p30Bundles (rev : Bool) : List ((Nat × Nat) × SpkBundleEntry) :=
  [((1, 0), { p30SpkEntry with revealed := rev })]

def p30InitOpk : KeyIndInitiatorEntry testSetup :=
  { d4Init with spkHonest := true, opkHonest := true }
def p30InitSpkOnly : KeyIndInitiatorEntry testSetup :=
  { p30InitOpk with opkHonest := false }

/-- After `revealSpkSk`, an initiator session with an honest OPK stays fresh, whereas a session
    whose only honest prekey is the SPK (or an unpartnered responder whose SPK is revealed) loses
    freshness. -/
theorem p30_spk_reveal_freshness :
    let alice : PrincipalEntry :=
      { secIKA0 := [], ikAPk := sampleIkA, secIKAsign := [], ikSignPk := [], corrupted := false }
    let unpartnered : KeyIndRespEntry testSetup :=
      { d4Resp with hdr := { d4Hdr with kemCt := [9] } }
    d4Init.peerSpkPk = sampleSpkB ∧
    keyIndInitCorruptionClause testPrimitives true [] (p30Bundles true) p30InitOpk = true ∧
    keyIndInitCorruptionClause testPrimitives true [] (p30Bundles false) p30InitSpkOnly = true ∧
    keyIndInitCorruptionClause testPrimitives true [] (p30Bundles true) p30InitSpkOnly = false ∧
    isKeyIndRespStillFresh testPrimitives true [(0, alice)]
      (p30Bundles false) [d4Init] unpartnered = true ∧
    isKeyIndRespStillFresh testPrimitives true [(0, alice)]
      (p30Bundles true) [d4Init] unpartnered = false := by
  decide

/-- An honest PQSPK suffices for freshness under `useRo = false` (HNDL) but not under
    `useRo = true` (`-D DH`), and a dishonest claimed sender invalidates freshness for both the
    responder and any partnered initiator. -/
theorem p32_pqspk_and_sender_freshness :
    p30InitSpkOnly.pqspkHonest = true ∧ p30InitSpkOnly.opkHonest = false ∧
    p30InitSpkOnly.peerOpkPk? = none ∧
    keyIndInitCorruptionClause testPrimitives true [] (p30Bundles true) p30InitSpkOnly = false ∧
    keyIndInitCorruptionClause testPrimitives false [] (p30Bundles true) p30InitSpkOnly = true ∧
    isKeyIndInitStillFresh testPrimitives true [] []
      [{ d4Resp with senderHonest := false }] d4Init = false ∧
    isKeyIndRespStillFresh testPrimitives true [] []
      [d4Init] { d4Resp with senderHonest := false } = false := by
  decide

/-- High-bit ratchet keys fail `isCanonical` and are rejected by `Auth` receive handlers. -/
theorem p33_noncanonical_eph_rejected :
    testPrimitives.isCanonical (List.replicate 31 0x01 ++ [0x80]) = false := by
  decide

#guard
  match Model.initiate testPrimitives sampleInitWithOpk,
        Model.initiate testPrimitives sampleInitNoOpk with
  | some (_, _, _, msgOpk), some (_, _, _, msgNoOpk) =>
    testPrimitives.isCanonical msgOpk.ephAPk && testPrimitives.isCanonical msgNoOpk.ephAPk
  | _, _ => false

theorem p34_auth_bound_resp_ek_coll_term (S : Setup) (q_roRoot : ℕ)
    (epsSig epsKemShCr epsGapDh epsPrfCk epsPrfMsgKeys epsAeadCpa epsPrfHmac : ℝ≥0∞) :
    pqxdhAuthBound S q_roRoot epsSig epsKemShCr epsGapDh
      epsPrfCk epsPrfMsgKeys epsAeadCpa epsPrfHmac =
    pqxdhKeyIndBound S epsSig epsKemShCr epsGapDh +
      2 * (S.N_send_tot : ℝ≥0∞) * (S.N_recv_tot : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 250 +
      rootKdfRoTerm S q_roRoot +
      2 * (S.N_sess_tot : ℝ≥0∞) * epsPrfCk +
      2 * (S.N_sess_tot : ℝ≥0∞) * epsPrfMsgKeys +
      2 * (S.N_send_tot : ℝ≥0∞) * epsAeadCpa +
      2 * (2 * (S.N_sess_tot : ℝ≥0∞) * epsPrfHmac + (S.N_recv_tot : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 64) :=
  rfl

/-! Shift-forgery check on the first-message MAC input (DEV-PQ31): moving the first 16-byte
ciphertext block from `aeadCt` into `pqRatchetMsg` changes the length-delimited `aeadMacInput`,
whereas an unframed concatenation `ad ++ ct` collides. -/

/-- FNV-1a toy SHA-256 compression for the DEV-PQ31 check (`idealLeafPrimitives` XOR-folding
    ignores block position and cannot witness MAC rejection). -/
def shiftCompress (st blk : Bytes) : Bytes :=
  let acc : UInt64 := (fitBytes 32 st ++ blk).foldl
    (fun (a : UInt64) (x : UInt8) => (a ^^^ x.toUInt64) * 0x100000001b3) 0xcbf29ce484222325
  (List.range 32).map fun i =>
    (((acc + i.toUInt64) * 0x9e3779b97f4a7c15) >>> 56).toUInt8

def shiftPrims : Primitives :=
  let L : Primitives := { idealLeafPrimitives with sha256Compress := shiftCompress }
  { idealRoundtripPrimitives with
    aeadEnc := aes256CbcHmacEncRef L
    aeadDec := aes256CbcHmacDecRef L }

def shiftMk : MessageKeys :=
  { cipherKey := List.replicate 32 7, macKey := List.replicate 32 9, iv := List.replicate 16 3 }

def shiftAd0 : Bytes :=
  firstMsgAD (List.replicate 32 1) (List.replicate 32 2) (List.replicate 32 4) []

def shiftPt0 : Bytes := List.replicate 40 0x41

def shiftCt0 : Bytes := shiftPrims.aeadEnc shiftMk shiftAd0 shiftPt0

def shiftAd1 : Bytes :=
  firstMsgAD (List.replicate 32 1) (List.replicate 32 2) (List.replicate 32 4) (shiftCt0.take 16)

def shiftCt1 : Bytes := shiftCt0.drop 16

#guard shiftPrims.aeadDec shiftMk shiftAd0 shiftCt0 == some shiftPt0
#guard (encodeEC (List.replicate 32 1) ++ encodeEC (List.replicate 32 2) ++
    encodeEC (List.replicate 32 4) ++ shiftCt0.take 16) ++ (shiftCt1.take (shiftCt1.length - 8)) ==
  (encodeEC (List.replicate 32 1) ++ encodeEC (List.replicate 32 2) ++
    encodeEC (List.replicate 32 4) ++ []) ++ (shiftCt0.take (shiftCt0.length - 8))
#guard aeadMacInput shiftAd1 (shiftCt1.take (shiftCt1.length - 8)) !=
  aeadMacInput shiftAd0 (shiftCt0.take (shiftCt0.length - 8))
#guard shiftPrims.aeadDec shiftMk shiftAd1 shiftCt1 == none
-- Protobuf field order: ciphertext (field 4) precedes `pq_ratchet` (field 5).
#guard aeadMacInput shiftAd1 shiftCt1 ==
  shiftAd0 ++ pbBytesField 4 shiftCt1 ++ pbBytesField 5 (shiftCt0.take 16)
#guard shiftAd0.length == firstMsgHdrLen

/-! Effective 32-byte HKDF salt for `PrfMsgKeys` (DEV-LS25): `none`, `some []`, and `some 0^32`
produce identical HMAC-SHA256 keys under zero-padding, so `PrfMsgKeys` indexes on
`effectiveHkdfSaltBytes` rather than raw `Option Bytes`. -/

#guard effectiveHkdfSaltBytes none == effectiveHkdfSaltBytes (some (List.replicate 32 0))
#guard effectiveHkdfSaltBytes none == effectiveHkdfSaltBytes (some [])
#guard effectiveHkdfSaltBytes (some [1, 2]) == effectiveHkdfSaltBytes (some ([1, 2] ++ List.replicate 30 0))
#guard effectiveHkdfSaltBytes (some [1, 2]) != effectiveHkdfSaltBytes (some [1, 3])
#guard (effectiveHkdfSaltBytes (some (List.replicate 32 7))).toList == List.replicate 32 7
#guard deriveMsgKeysRef idealLeafPrimitives (List.replicate 32 5) none ==
  deriveMsgKeysRef idealLeafPrimitives (List.replicate 32 5) (some (List.replicate 32 0))
#guard deriveMsgKeysRef idealLeafPrimitives (List.replicate 32 5) none ==
  deriveMsgKeysRef idealLeafPrimitives (List.replicate 32 5) (some [])
#guard deriveMsgKeysRef idealLeafPrimitives (List.replicate 32 5) (some [9]) ==
  deriveMsgKeysRef idealLeafPrimitives (List.replicate 32 5) (some (effectiveHkdfSaltBytes (some [9])).toList)

/-- `isKeyIndRespStillFresh` requires every partnered initiator entry to be fresh and unrevealed. -/
theorem p35_resp_still_fresh_checks_all_partners :
    isKeyIndRespStillFresh testPrimitives true [] (p30Bundles false)
      [d4Init] d4Resp = true ∧
    isKeyIndRespStillFresh testPrimitives true [] (p30Bundles false)
      [d4Init, { d4Init with revealed := true }] d4Resp = false ∧
    isKeyIndRespStillFresh testPrimitives true [] (p30Bundles false)
      [d4Init, { d4Init with fresh := false }] d4Resp = false := by
  decide

end SpecTests.SignalPqxdh
