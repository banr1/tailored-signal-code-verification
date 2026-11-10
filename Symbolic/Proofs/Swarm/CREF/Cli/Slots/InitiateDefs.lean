/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPure
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Symbolic.Proofs.Refinement.Composed.Cli.LeakRecordsCompat
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import Symbolic.Proofs.Swarm.CREF.Cli.World.XplTransferPure

/-!
# CLI `init` Coin Splits, Bundle Conversions, and Party State

Defines the 34-piece coin split `initiateDrawsOfCoins` for 192-byte `init`
tapes, relates `BundleTyped` `PublicBundle` values to `PreKeyBundleFields`, and
characterizes Alice's `PqParty` directory state and peer-identity trust check.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.PQXDH.Refinement (preKeyBundleByteLength)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF (entropyBytes)
open Symbolic.Swarm.CREF.CliPure (initiateDrawsOfCoins initiateDrawsOfCoins_lengths initiateDrawsOfCoins_nonempty initiateDrawsOfCoins_flatten)

export Symbolic.Swarm.CREF.CliPure (initiateDrawsOfCoins initiateDrawsOfCoins_lengths initiateDrawsOfCoins_nonempty initiateDrawsOfCoins_flatten)
export DY.Libsignal.Composed.Refinement.Cli (ModelAgree)

/-! ## 34-piece `initiateDrawsOfCoins` and `CoinSplit` lemmas -/

theorem initiateDrawsOfCoins_length (coins : HwBytes) :
    (initiateDrawsOfCoins coins).length = 34 := by
  simp [initiateDrawsOfCoins]

theorem initiateDrawsOfCoins_getD_0 (coins : HwBytes) :
    (initiateDrawsOfCoins coins).getD 0 [] = coins.take 32 := rfl

theorem initiateDrawsOfCoins_getD_33 (coins : HwBytes) :
    (initiateDrawsOfCoins coins).getD 33 [] = (coins.drop 160).take 32 := by
  unfold initiateDrawsOfCoins
  rw [List.append_assoc, List.getD_eq_getElem?_getD]
  dsimp only [List.singleton_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem entropyBytes_initiateDrawsOfCoins (t : List.Vector (BitVec 8) initiateTapeLen) :
    entropyBytes (initiateDrawsOfCoins t.toList) = (initiateKemCoins t).toList := by
  have hlen : t.toList.length = 192 := t.toList_length
  apply List.ext_getElem?
  intro j
  by_cases hj1 : j < 32
  · have hget_chunk : (initiateDrawsOfCoins t.toList).getD (j + 1) [] =
        (t.toList.drop (32 + 4 * j)).take 4 := by
      unfold initiateDrawsOfCoins
      rw [List.append_assoc, List.getD_eq_getElem?_getD]
      dsimp only [List.singleton_append, List.getElem?_cons_succ]
      rw [List.getElem?_append_left (by simp [hj1]), List.getElem?_map,
          List.getElem?_range hj1, Option.map_some, Option.getD_some]
    unfold entropyBytes
    rw [List.getElem?_map, List.getElem?_range hj1, Option.map_some, hget_chunk]
    have hidx : 32 + 4 * j < t.toList.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
        List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hidx, Option.getD_some]
    unfold initiateKemCoins
    simp only [List.Vector.toList_ofFn, List.getElem?_ofFn, hj1, ↓reduceDIte]
    exact congrArg some
      (List.Vector.get_eq_get_toList t ⟨32 + 4 * j, by unfold initiateTapeLen; omega⟩).symm
  · have hl1 : (entropyBytes (initiateDrawsOfCoins t.toList)).length = 32 := by simp [entropyBytes]
    have hl2 : (initiateKemCoins t).toList.length = 32 := List.Vector.toList_length _
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem coinSplit_init_ok (bundle : HwBytes) {coins : HwBytes} (hlen : coins.length = 192) :
    CoinSplit [.recv bundle, .rng coins]
      (.recv bundle :: (initiateDrawsOfCoins coins).map MachineEvent.rng) :=
  Symbolic.Swarm.CREF.CliPure.IniPure.coinSplit_initiate_full bundle hlen

theorem coinSplit_init_reject (bundle coins : HwBytes) :
    CoinSplit [.recv bundle, .rng coins] [.recv bundle] := by
  refine .keep (fun _ h => nomatch h) ?_
  simpa using CoinSplit.split (coins := coins) (pieces := [])
    (by simp) (List.nil_prefix) CoinSplit.nil

/-! ## `BundleTyped` and `PreKeyBundleFields` conversions -/

theorem comp_le32_eq_toLEBytes4 (v : BitVec 32) :
    DY.Libsignal.Composed.Refinement.le32 v =
      CryptoVerification.LibsignalAesCbc.toLEBytes 4 v := by
  simp [DY.Libsignal.Composed.Refinement.le32, CryptoVerification.SignalSession.le32,
    CryptoVerification.LibsignalAesCbc.toLEBytes, List.ofFn_succ, List.ofFn_zero]

/-- Extract a typed `PreKeyBundleFields` from a `PublicBundle` (total via `fitVec`). -/
def bundleEOfPublic (b : PublicBundle) : PreKeyBundleFields where
  regId := b.registrationId
  opk := b.oneTime.map fun (id, key) => (id, fitVec 32 (key.drop 1))
  spkId := b.signedId
  spkPub := fitVec 32 (b.signedKey.drop 1)
  spkSig := fitVec 64 b.signedSig
  kpkId := b.kyberId
  kpkPub := fitVec 1568 (b.kyberKey.drop 1)
  kpkSig := fitVec 64 b.kyberSig
  idPub := fitVec 32 (b.identityKey.drop 1)

theorem fitVec_toList_of_len {n : Nat} {bs : HwBytes} (h : bs.length = n) :
    (fitVec n bs).toList = bs := by
  unfold fitVec
  dsimp only [List.Vector.toList]
  rw [List.take_append_of_le_length (Nat.le_of_eq h.symm), List.take_of_length_le (Nat.le_of_eq h)]

private theorem djbKey_fitVec_drop1 {bs : HwBytes} (hlen : bs.length = 33)
    (hhead : bs.head? = some 0x05#8) :
    djbKey (fitVec 32 (bs.drop 1)) = bs := by
  cases bs with
  | nil => cases hlen
  | cons hd tl =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    have hlen' : tl.length = 32 := by simp at hlen; omega
    unfold djbKey
    rw [List.drop_succ_cons, List.drop_zero, fitVec_toList_of_len hlen']

private theorem kyberKey_fitVec_drop1 {bs : HwBytes} (hlen : bs.length = 1569)
    (hhead : bs.head? = some 0x08#8) :
    CryptoVerification.E2E.kyberKey (fitVec 1568 (bs.drop 1)) = bs := by
  cases bs with
  | nil => cases hlen
  | cons hd tl =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    have hlen' : tl.length = 1568 := by simp at hlen; omega
    unfold CryptoVerification.E2E.kyberKey
    rw [List.drop_succ_cons, List.drop_zero, fitVec_toList_of_len hlen']

theorem publicBundleOf_bundleEOfPublic {b : PublicBundle} (ht : BundleTyped b) :
    publicBundleOf (bundleEOfPublic b) = b := by
  obtain ⟨hid_l, hid_h, hspk_l, hspk_h, hssig_l, hkpk_l, hkpk_h, hksig_l, hopk⟩ := ht
  cases b with
  | mk idKey regId spkId spkKey spkSig kpkId kpkKey kpkSig opk =>
    dsimp only at hid_l hid_h hspk_l hspk_h hssig_l hkpk_l hkpk_h hksig_l hopk
    unfold publicBundleOf bundleEOfPublic
    dsimp only
    rw [djbKey_fitVec_drop1 hid_l hid_h,
        djbKey_fitVec_drop1 hspk_l hspk_h,
        fitVec_toList_of_len hssig_l,
        kyberKey_fitVec_drop1 hkpk_l hkpk_h,
        fitVec_toList_of_len hksig_l]
    congr 1
    cases opk with
    | none => rfl
    | some ik =>
      rcases ik with ⟨oid, okey⟩
      obtain ⟨hok_l, hok_h⟩ := hopk oid okey rfl
      dsimp only [Option.map]
      rw [djbKey_fitVec_drop1 hok_l hok_h]

theorem bundleBlob_publicBundleOf (bE : PreKeyBundleFields) :
    bundleBlob (publicBundleOf bE) = bE.bytes := by
  unfold bundleBlob publicBundleOf PreKeyBundleFields.bytes
  simp only [comp_le32_eq_toLEBytes4]
  cases bE.opk with
  | none => rfl
  | some ik =>
    rcases ik with ⟨oid, okey⟩
    simp [List.cons_append, List.append_assoc]

theorem bundleBlob_publicBundleOf_length (bE : PreKeyBundleFields) :
    (bundleBlob (publicBundleOf bE)).length = preKeyBundleByteLength := by
  rw [bundleBlob_publicBundleOf]
  unfold PreKeyBundleFields.bytes preKeyBundleByteLength djbKey CryptoVerification.E2E.kyberKey
  cases bE.opk with
  | none => simp [CryptoVerification.LibsignalAesCbc.toLEBytes]
  | some ik =>
    rcases ik with ⟨oid, okey⟩
    simp [CryptoVerification.LibsignalAesCbc.toLEBytes]

/-! ## Alice's `PqParty` directory state and peer-identity trust -/

/-- Structural characterization of Alice's `PqParty` state on `r`:
party `.A`, `me = (ikA, regIdA)`, peer identity pinned to Bob's public key, and empty
pre-key stores. -/
structure AlicePqParty (interp : ExternInterpretation) (r : ProtocolSetup) (st : PqParty) : Prop where
  party_eq : st.party = .A
  me_eq : st.me = ⟨vec32 (secretBytes r 0), r.regIdA⟩
  peerId_eq : st.peerId = some ⟨⟨vec32 (pubBytes interp (secretBytes r 1))⟩⟩
  signed_nil : st.signed = []
  oneTime_nil : st.oneTime = []
  kyberOneTime_nil : st.kyberOneTime = []
  kyberLastResort_nil : st.kyberLastResort = []

/-- Initial `PqParty` state of Alice before any session exists (`initDirs`). -/
def aliceInitPqParty (interp : ExternInterpretation) (r : ProtocolSetup) : PqParty where
  party := .A
  me := ⟨vec32 (secretBytes r 0), r.regIdA⟩
  peerId := some ⟨⟨vec32 (pubBytes interp (secretBytes r 1))⟩⟩
  session := none
  signed := []
  oneTime := []
  kyberOneTime := []
  kyberLastResort := []

theorem alicePqParty_aliceInitPqParty (interp : ExternInterpretation) (r : ProtocolSetup) :
    AlicePqParty interp r (aliceInitPqParty interp r) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Peer identity trust check on Alice's pinned Bob identity key:
`st.trusts ⟨⟨bE.idPub⟩⟩ = true` iff `bE.idPub.toList = pubBytes interp (secretBytes r 1)`. -/
theorem alicePqParty_trusts_iff {interp : ExternInterpretation} {r : ProtocolSetup} {st : PqParty}
    (halice : AlicePqParty interp r st) (hEq : ExternCryptoLawsHold interp)
    (bE : PreKeyBundleFields) :
    st.trusts ⟨⟨bE.idPub⟩⟩ = true ↔ bE.idPub.toList = pubBytes interp (secretBytes r 1) := by
  have hpub_len : (pubBytes interp (secretBytes r 1)).length = 32 :=
    hEq.x25519_public_key_length _
  have hvec : (vec32 (pubBytes interp (secretBytes r 1))).toList =
      pubBytes interp (secretBytes r 1) :=
    Proofs.libsignal.Hooks2.vec32_toList_of_length_32' _ hpub_len
  unfold PqParty.trusts
  rw [halice.peerId_eq]
  simp only [decide_eq_true_eq, IdentityKey.mk.injEq, PublicKey.mk.injEq]
  constructor
  · intro h
    rw [← h, hvec]
  · intro h
    apply List.Vector.eq
    rw [hvec, h]

theorem secretBytes_0_length {r : ProtocolSetup} (hwf : ProtocolSetupWF r) :
    (secretBytes r 0).length = 32 := by
  have hmem : ((0 : Nat), (32 : Nat)) ∈ setupRandomsAt r := by
    rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; simp
  simpa [secretBytes, Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1] using hwf.2.1 (0, 32) hmem

theorem clampScalar_toList_eq_composedClamp (v : List.Vector (BitVec 8) 32) :
    (Ratchet.clampScalar v).toList = DY.Libsignal.Composed.Refinement.clamp v.toList := by
  rcases v with ⟨l, hl⟩
  unfold Ratchet.clampScalar DY.Libsignal.Composed.Refinement.clamp
    DY.Libsignal.Composed.Refinement.clampByte
  dsimp only [List.Vector.toList, List.Vector.set, List.Vector.get, Fin.cast]
  simp only [hl, ↓reduceIte, List.get_eq_getElem]
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  simp only [List.getElem_set, List.getElem_mapIdx]
  split_ifs <;> simp_all

theorem keyPairOf_alice_pubKey_eq {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) :
    djbKey (keyPairOf P.C (vec32 (secretBytes r 0))).publicKey.bytes =
      ecKey (pubBytes interp (secretBytes r 0)) := by
  unfold djbKey ecKey keyPairOf pubBytes
  dsimp only
  have hpub := hagree.2.2.2.2.1 (Ratchet.clampScalar (vec32 (secretBytes r 0)))
  have hvec0 : (vec32 (secretBytes r 0)).toList = secretBytes r 0 :=
    Proofs.libsignal.Hooks2.vec32_toList_of_length_32' _ (secretBytes_0_length hwf)
  have hcl : (Ratchet.clampScalar (vec32 (secretBytes r 0))).toList =
      DY.Libsignal.Composed.Refinement.clamp (secretBytes r 0) := by
    rw [clampScalar_toList_eq_composedClamp, hvec0]
  rw [hcl] at hpub
  rw [hpub, Option.getD_some]

private theorem cli_textBytes_eq (s : String) :
    CryptoVerification.SignalSession.textBytes s =
      DY.Libsignal.Composed.Refinement.Cli.textBytes s := by
  unfold CryptoVerification.SignalSession.textBytes
    DY.Libsignal.Composed.Refinement.Cli.textBytes
    CryptoVerification.LibsignalTripleRatchetRepr.utf8
  refine List.map_congr_left fun b _ => ?_
  apply BitVec.eq_of_toNat_eq
  simp

theorem encodeDir_of_alicePqParty {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (hEq : ExternCryptoLawsHold interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {st : PqParty} (halice : AlicePqParty interp r st) :
    encodeDir P st =
      commonFiles interp r r.alice ++
        match st.session with
        | some (x, g) => [(sessionPathOf r r.alice, encodeRecordUnderExtras (fun _ => x) g)]
        | none => [] := by
  have hpub1_len : (pubBytes interp (secretBytes r 1)).length = 32 :=
    hEq.x25519_public_key_length _
  have hvec1 : (vec32 (pubBytes interp (secretBytes r 1))).toList =
      pubBytes interp (secretBytes r 1) :=
    Proofs.libsignal.Hooks2.vec32_toList_of_length_32' _ hpub1_len
  have hvec0 : (vec32 (secretBytes r 0)).toList = secretBytes r 0 :=
    Proofs.libsignal.Hooks2.vec32_toList_of_length_32' _ (secretBytes_0_length hwf)
  unfold encodeDir commonFiles
  rw [halice.party_eq, halice.me_eq, halice.peerId_eq, halice.signed_nil,
      halice.oneTime_nil, halice.kyberOneTime_nil, halice.kyberLastResort_nil]
  simp only [List.map_nil, List.flatten_nil, List.append_nil]
  have haddr : addrOf r r.alice = partyAddress .A := by
    unfold addrOf nameOf partyAddress partyAddressName aliceUuid
    simp
  have hpeer : peerNameOf r r.alice = partyAddressName Party.A.other := by
    unfold peerNameOf partyAddressName Party.other bobUuid
    simp
  have hsessPath : sessionFile (partyAddress Party.A.other) = sessionPathOf r r.alice := by
    unfold sessionPathOf peerOf peerNameOf partyAddress partyAddressName Party.other bobUuid
    simp
  have hidSec : idSecret r r.alice = secretBytes r 0 := by simp [idSecret, ProtocolSetup.ikASecBytes]
  have hpSec : peerIdSecret r r.alice = secretBytes r 1 := by simp [peerIdSecret, ProtocolSetup.ikBSecBytes]
  have hreg : regIdOf r r.alice = r.regIdA := by simp [regIdOf]
  have hser1 : (⟨⟨vec32 (pubBytes interp (secretBytes r 1))⟩⟩ : IdentityKey).serialize =
      ecKey (pubBytes interp (secretBytes r 1)) := by
    unfold IdentityKey.serialize PublicKey.serialize djbType ecKey
    rw [hvec1]
    rfl
  rw [haddr, cli_textBytes_eq, hidSec, hpSec, hreg, hpeer, hsessPath,
      keyPairOf_alice_pubKey_eq hagree hwf, hvec0, hser1]
  cases st.session <;> simp

theorem encodeDir_aliceInitPqParty {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (hEq : ExternCryptoLawsHold interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) :
    encodeDir P (aliceInitPqParty interp r) = commonFiles interp r r.alice := by
  simpa [aliceInitPqParty] using
    encodeDir_of_alicePqParty hagree hEq hwf (alicePqParty_aliceInitPqParty interp r)

theorem encodeVarintAux_length_le :
    ∀ (fuel : Nat) (v : BitVec 64),
      (CryptoVerification.LibsignalProtoCodec.encodeVarintAux fuel v).length ≤ fuel + 1
  | 0, _ => by simp [CryptoVerification.LibsignalProtoCodec.encodeVarintAux]
  | fuel + 1, v => by
    unfold CryptoVerification.LibsignalProtoCodec.encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      have := encodeVarintAux_length_le fuel (v >>> 7)
      omega

theorem encodeVarint_length_le (v : BitVec 64) :
    (CryptoVerification.LibsignalProtoCodec.encodeVarint v).length ≤ 11 :=
  encodeVarintAux_length_le 10 v

theorem encodeKey_length_le (tag : Nat)
    (wt : CryptoVerification.LibsignalProtoCodec.WireType) :
    (CryptoVerification.LibsignalProtoCodec.encodeKey tag wt).length ≤ 11 :=
  encodeVarint_length_le _

theorem encodeBytesField_some_length_le (tag : Nat) (bs : HwBytes) :
    (CryptoVerification.LibsignalProtoCodec.encodeBytesField tag (some bs)).length ≤
      bs.length + 22 := by
  unfold CryptoVerification.LibsignalProtoCodec.encodeBytesField
  simp only [List.length_append]
  have h1 := encodeKey_length_le tag .lengthDelimited
  have h2 := encodeVarint_length_le (BitVec.ofNat 64 bs.length)
  omega

theorem encodeBytes3_length_le (tag : Nat) (bs : HwBytes) :
    (CryptoVerification.RecordCodecs.encodeProto3BytesField tag bs).length ≤ bs.length + 22 := by
  unfold CryptoVerification.RecordCodecs.encodeProto3BytesField
  split
  · simp
  · exact encodeBytesField_some_length_le tag bs

theorem commonFiles_alice_bounded {interp : ExternInterpretation}
    (hEq : ExternCryptoLawsHold interp) {r : ProtocolSetup} (hwf : ProtocolSetupWF r) :
    ∀ f ∈ commonFiles interp r r.alice, f.2.length < 2 ^ 31 := by
  intro f hf
  have hpub0 : (pubBytes interp (secretBytes r 0)).length = 32 := hEq.x25519_public_key_length _
  have hpub1 : (pubBytes interp (secretBytes r 1)).length = 32 := hEq.x25519_public_key_length _
  have hsec0 : (secretBytes r 0).length = 32 := secretBytes_0_length hwf
  unfold commonFiles at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · show (DY.Libsignal.Composed.Refinement.Cli.textBytes (addrOf r r.alice).text).length < 2 ^ 31
    have htext : (addrOf r r.alice).text = aliceUuid ++ ".1" := by
      simp only [addrOf, nameOf, ↓reduceIte, Address.text]
      decide
    have hlen38 :
        (DY.Libsignal.Composed.Refinement.Cli.textBytes (aliceUuid ++ ".1")).length = 38 := by
      decide +kernel
    rw [htext, hlen38]
    omega
  · show (CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
      ⟨ecKey (pubBytes interp (idSecret r r.alice)), idSecret r r.alice⟩).length < 2 ^ 31
    have hid0 : idSecret r r.alice = secretBytes r 0 := by simp [idSecret, ProtocolSetup.ikASecBytes]
    rw [hid0]
    unfold CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
    simp only [List.length_append]
    have hb1 := encodeBytes3_length_le 1 (ecKey (pubBytes interp (secretBytes r 0)))
    have hb2 := encodeBytes3_length_le 2 (secretBytes r 0)
    have hec : (ecKey (pubBytes interp (secretBytes r 0))).length = 33 := by
      simp [ecKey, hpub0]
    rw [hec] at hb1
    rw [hsec0] at hb2
    omega
  · show (CryptoVerification.SignalSession.le32 (regIdOf r r.alice)).length < 2 ^ 31
    simp [CryptoVerification.SignalSession.le32]
  · show (ecKey (pubBytes interp (peerIdSecret r r.alice))).length < 2 ^ 31
    simp [peerIdSecret, ProtocolSetup.ikBSecBytes, ecKey, hpub1]

theorem commonFiles_alice_fileCapBytes {interp : ExternInterpretation}
    (hEq : ExternCryptoLawsHold interp) {r : ProtocolSetup} (hwf : ProtocolSetupWF r) :
    ∀ f ∈ commonFiles interp r r.alice, f.2.length ≤ fileCapBytes := by
  intro f hf
  have hpub0 : (pubBytes interp (secretBytes r 0)).length = 32 := hEq.x25519_public_key_length _
  have hpub1 : (pubBytes interp (secretBytes r 1)).length = 32 := hEq.x25519_public_key_length _
  have hsec0 : (secretBytes r 0).length = 32 := secretBytes_0_length hwf
  unfold commonFiles at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · show (DY.Libsignal.Composed.Refinement.Cli.textBytes (addrOf r r.alice).text).length ≤ fileCapBytes
    have htext : (addrOf r r.alice).text = aliceUuid ++ ".1" := by
      simp only [addrOf, nameOf, ↓reduceIte, Address.text]
      decide
    have hlen38 :
        (DY.Libsignal.Composed.Refinement.Cli.textBytes (aliceUuid ++ ".1")).length = 38 := by
      decide +kernel
    rw [htext, hlen38]
    unfold fileCapBytes
    omega
  · show (CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
      ⟨ecKey (pubBytes interp (idSecret r r.alice)), idSecret r r.alice⟩).length ≤ fileCapBytes
    have hid0 : idSecret r r.alice = secretBytes r 0 := by simp [idSecret, ProtocolSetup.ikASecBytes]
    rw [hid0]
    unfold CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
    simp only [List.length_append]
    have hb1 := encodeBytes3_length_le 1 (ecKey (pubBytes interp (secretBytes r 0)))
    have hb2 := encodeBytes3_length_le 2 (secretBytes r 0)
    have hec : (ecKey (pubBytes interp (secretBytes r 0))).length = 33 := by
      simp [ecKey, hpub0]
    rw [hec] at hb1
    rw [hsec0] at hb2
    unfold fileCapBytes
    omega
  · show (CryptoVerification.SignalSession.le32 (regIdOf r r.alice)).length ≤ fileCapBytes
    simp [CryptoVerification.SignalSession.le32, fileCapBytes]
  · show (ecKey (pubBytes interp (peerIdSecret r r.alice))).length ≤ fileCapBytes
    simp [peerIdSecret, ProtocolSetup.ikBSecBytes, ecKey, hpub1, fileCapBytes]

theorem wfPq_aliceInitPqParty {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (hEq : ExternCryptoLawsHold interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) :
    PqxdhPartyInSpecDomain P (aliceInitPqParty interp r) := by
  unfold PqxdhPartyInSpecDomain
  refine ⟨(fun _ _ hs => nomatch hs), ?_,
    by simp [aliceInitPqParty], by simp [aliceInitPqParty],
    by simp [aliceInitPqParty], by simp [aliceInitPqParty]⟩
  rw [encodeDir_aliceInitPqParty hagree hEq hwf]
  intro f hf
  exact ⟨commonFiles_alice_bounded hEq hwf f hf, fun _ => commonFiles_alice_fileCapBytes hEq hwf f hf⟩

end Symbolic.Swarm.CREF.Cli.Slots
