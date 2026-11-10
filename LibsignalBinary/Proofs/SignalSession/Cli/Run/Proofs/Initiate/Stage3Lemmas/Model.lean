/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model

/-!
# Pure Protocol and Byte-Encoding Bridges for Stage 3

Connects the machine-level Stage 3 byte slices and callees (`pqxdhCalculateAgreementFrozenSpec`,
`signal_session_coins_fill`, `kyberEncapsStubSpec`, `kemCiphertextSerializeSpec`,
`handshakeKeysDeriveSpec`) to `initDef` and `AtStage4.keysOk`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.Initiator (bytesToBv8 fitBv8)
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

/-! ## Byte Conversion Round-Trips and `PreKeyBundleFields` Projections -/

@[simp]
theorem bytesToBv8_eq_ofU8 (bs : List UInt8) : bytesToBv8 bs = ofU8 bs :=
  CryptoVerification.E2E.Pqxdh.ResponderCore.bytesToBv8_eq_ofU8 bs

@[simp]
theorem ofU8_toU8_eq (bs : List (BitVec 8)) : ofU8 (toU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb : UInt8.toBitVec (UInt8.ofBitVec b) = b := by cases b; rfl
    exact congrArg₂ List.cons hb ih

@[simp]
theorem bytesToBv8_toU8_eq (bs : List (BitVec 8)) : bytesToBv8 (toU8 bs) = bs := by
  rw [bytesToBv8_eq_ofU8, ofU8_toU8_eq]

@[simp]
theorem toU8_ofU8_eq (bs : List UInt8) : toU8 (ofU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb : UInt8.ofBitVec (UInt8.toBitVec b) = b := by cases b; rfl
    exact congrArg₂ List.cons hb ih

@[simp]
theorem toU8_length_eq (bs : List (BitVec 8)) : (toU8 bs).length = bs.length :=
  List.length_map _

@[simp]
theorem ofU8_length_eq (bs : List UInt8) : (ofU8 bs).length = bs.length :=
  List.length_map _

theorem modelPrims_x25519_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (a pk : List UInt8) :
    ((modelPrims X W : Pqxdh.Initiator.Primitives).x25519 a pk).length = 32 :=
  Pqxdh.Initiator.e2e_vecU8_length _

theorem u8Vec_toU8_of_len {n : Nat} {bs : List (BitVec 8)} (h : bs.length = n) :
    u8Vec n (toU8 bs) = ⟨bs, h⟩ := by
  apply Subtype.ext
  simp only [u8Vec, fitVec, ofU8_toU8_eq]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

@[simp]
theorem u8Vec_vecU8_eq {n : Nat} (v : List.Vector (BitVec 8) n) :
    u8Vec n (E2E.vecU8 v) = v := by
  rcases v with ⟨bs, hbs⟩
  exact u8Vec_toU8_of_len hbs

theorem bundleEOf_props {b : BundleV} {be : PreKeyBundleFields} (h : bundleEOf? b = some be) :
    b.idKey.publicKey.bytes.toList.length = 32 ∧
      b.spk.bytes.toList.length = 32 ∧
      b.kpk.length = 1568 ∧
      (∀ oid ok, b.opk = some (oid, ok) → ok.bytes.toList.length = 32) ∧
      be.opk = (b.opk.map fun (i, k) => (i, k.bytes)) ∧
      be.spkPub = b.spk.bytes ∧
      be.kpkPub.toList = b.kpk ∧
      be.idPub = b.idKey.publicKey.bytes := by
  unfold bundleEOf? at h
  split at h
  · split at h
    · split at h
      · rename_i h3
        injection h with hbe
        subst hbe
        exact ⟨b.idKey.publicKey.bytes.toList_length, b.spk.bytes.toList_length, h3,
          fun _ ok _ => ok.bytes.toList_length, rfl, rfl, rfl, rfl⟩
      · simp at h
    · simp at h
  · simp at h

/-! ## X25519 Scalar Clamping Idempotence and `DH1..DH4` Alignment -/

private theorem clamp_byte0_idem (b : BitVec 8) :
    (b &&& 0xf8#8) &&& 0xf8#8 = b &&& 0xf8#8 := by
  revert b; decide

private theorem clamp_byte31_idem (b : BitVec 8) :
    (((b &&& 0x7f#8) ||| 0x40#8) &&& 0x7f#8) ||| 0x40#8 =
      (b &&& 0x7f#8) ||| 0x40#8 := by
  revert b; decide

theorem clampScalar_idem (v : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (Ratchet.clampScalar v) = Ratchet.clampScalar v := by
  apply List.Vector.ext
  intro j
  by_cases h31 : j = 31
  · subst h31
    simp only [Ratchet.clampScalar, List.Vector.get_set_same, clamp_byte31_idem]
  · by_cases h0 : j = 0
    · subst h0
      simp only [Ratchet.clampScalar, List.Vector.get_set_of_ne (Ne.symm h31),
        List.Vector.get_set_same, clamp_byte0_idem]
    · simp only [Ratchet.clampScalar, List.Vector.get_set_of_ne (Ne.symm h31),
        List.Vector.get_set_of_ne (Ne.symm h0)]

theorem dh1_model_eq (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (kp : IdentityKeyPair) (b : BundleV) (be : PreKeyBundleFields) (coins : List (BitVec 8))
    (hb : bundleEOf? b = some be) :
    ((modelPrims X W : Pqxdh.Initiator.Primitives).x25519
      (toU8 kp.privateKey.bytes.toList) (toU8 b.spk.bytes.toList)) =
      (modelPrims X W).x25519
        (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ikASk
        (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).bundle.spkB := by
  have hbp := bundleEOf_props hb
  change E2E.vecU8 (W.C.X (Ratchet.clampScalar (u8Vec 32 (E2E.vecU8 kp.privateKey.bytes)))
      (u8Vec 32 (E2E.vecU8 b.spk.bytes))) =
    E2E.vecU8 (W.C.X
      (Ratchet.clampScalar (u8Vec 32 (E2E.vecU8 (Ratchet.clampScalar kp.privateKey.bytes))))
      (u8Vec 32 (E2E.vecU8 be.spkPub)))
  rw [u8Vec_vecU8_eq, u8Vec_vecU8_eq, u8Vec_vecU8_eq, u8Vec_vecU8_eq,
    clampScalar_idem, hbp.2.2.2.2.2.1]

theorem dh_ek_model_eq (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (kp : IdentityKeyPair) (be : PreKeyBundleFields) (coins : List (BitVec 8))
    (ekASk : List (BitVec 8))
    (hek : ekASk = (keyPairOf W.C ⟨(padCoins coins).toList.take 32, by simp; decide⟩).privateKey.bytes.toList)
    (pk : List UInt8) :
    ((modelPrims X W : Pqxdh.Initiator.Primitives).x25519 (toU8 ekASk) pk) =
      (modelPrims X W).x25519
        (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk pk := by
  let raw : List.Vector (BitVec 8) 32 := ⟨(padCoins coins).toList.take 32, by simp; decide⟩
  have hek' : toU8 ekASk = E2E.vecU8 (Ratchet.clampScalar raw) := by
    rw [hek]; rfl
  have hinp : (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk = E2E.vecU8 raw :=
    rfl
  rw [hek', hinp]
  change E2E.vecU8 (W.C.X (Ratchet.clampScalar (u8Vec 32 (E2E.vecU8 (Ratchet.clampScalar raw))))
      (u8Vec 32 pk)) =
    E2E.vecU8 (W.C.X (Ratchet.clampScalar (u8Vec 32 (E2E.vecU8 raw))) (u8Vec 32 pk))
  rw [u8Vec_vecU8_eq, u8Vec_vecU8_eq, clampScalar_idem]

theorem dh2_model_eq (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (kp : IdentityKeyPair) (b : BundleV) (be : PreKeyBundleFields) (coins : List (BitVec 8))
    (ekASk : List (BitVec 8)) (hb : bundleEOf? b = some be)
    (hek : ekASk = (keyPairOf W.C ⟨(padCoins coins).toList.take 32, by simp; decide⟩).privateKey.bytes.toList) :
    ((modelPrims X W : Pqxdh.Initiator.Primitives).x25519
      (toU8 ekASk) (toU8 b.idKey.publicKey.bytes.toList)) =
      (modelPrims X W).x25519
        (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk
        (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).bundle.ikB := by
  have hbp := bundleEOf_props hb
  rw [dh_ek_model_eq X W kp be coins ekASk hek]
  change _ = (modelPrims X W).x25519 _ (E2E.vecU8 be.idPub)
  rw [hbp.2.2.2.2.2.2.2]
  rfl

theorem dh3_model_eq (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (kp : IdentityKeyPair) (b : BundleV) (be : PreKeyBundleFields) (coins : List (BitVec 8))
    (ekASk : List (BitVec 8)) (hb : bundleEOf? b = some be)
    (hek : ekASk = (keyPairOf W.C ⟨(padCoins coins).toList.take 32, by simp; decide⟩).privateKey.bytes.toList) :
    ((modelPrims X W : Pqxdh.Initiator.Primitives).x25519
      (toU8 ekASk) (toU8 b.spk.bytes.toList)) =
      (modelPrims X W).x25519
        (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk
        (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).bundle.spkB := by
  have hbp := bundleEOf_props hb
  rw [dh_ek_model_eq X W kp be coins ekASk hek]
  change _ = (modelPrims X W).x25519 _ (E2E.vecU8 be.spkPub)
  rw [hbp.2.2.2.2.2.1]
  rfl

theorem dh4_none_opt (W : PEParams) (kp : IdentityKeyPair) (b : BundleV) (be : PreKeyBundleFields)
    (coins : List (BitVec 8)) (hb : bundleEOf? b = some be) (hnone : b.opk = none) :
    (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).bundle.opkB? = none := by
  have hbp := bundleEOf_props hb
  change be.opk.map _ = none
  rw [hbp.2.2.2.2.1, hnone]
  rfl

theorem dh4_some_eq (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (kp : IdentityKeyPair) (b : BundleV) (be : PreKeyBundleFields) (coins : List (BitVec 8))
    (ekASk : List (BitVec 8)) (oid : BitVec 32) (ok : PublicKey)
    (hb : bundleEOf? b = some be) (hsome : b.opk = some (oid, ok))
    (hek : ekASk = (keyPairOf W.C ⟨(padCoins coins).toList.take 32, by simp; decide⟩).privateKey.bytes.toList) :
    ((initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).bundle.opkB?.map
      fun (_, opkPk) => (modelPrims X W).x25519
        (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk opkPk) =
      some (((modelPrims X W : Pqxdh.Initiator.Primitives).x25519 (toU8 ekASk)
        (toU8 ok.bytes.toList))) := by
  have hbp := bundleEOf_props hb
  have hopk : be.opk = some (oid, ok.bytes) := by
    rw [hbp.2.2.2.2.1, hsome]; rfl
  have hopkB : (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).bundle.opkB? =
      some (u32 oid, E2E.vecU8 ok.bytes) := by
    change be.opk.map _ = _
    rw [hopk]; rfl
  rw [hopkB, Option.map_some, dh_ek_model_eq X W kp be coins ekASk hek]
  rfl

/-! ## Zero-DH Early Rejection -/

private theorem initiateKeys_none_of_dh_bad (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (me : LocalIdentity) (be : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen)
    (hbad :
      let P := modelPrims X W
      let inp := initiateInput W me be t
      P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0 ∨
        P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0 ∨
        P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0 ∨
        SignalPqxdh.dhOptNonZero
          (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) = false) :
    SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me be t) = none := by
  let P := modelPrims X W
  let inp := initiateInput W me be t
  have htr : inp.trustedPeer = true := rfl
  unfold SignalPqxdh.Model.initiateKeys
  dsimp only [_root_.guard, bind, Option.bind]
  rw [if_pos htr]
  by_cases hs1 : P.sigVerify inp.bundle.ikB (SignalPqxdh.encodeEC inp.bundle.spkB) inp.bundle.spkSig = true
  swap
  · rw [if_neg hs1]; rfl
  rw [if_pos hs1]
  by_cases hs2 : P.sigVerify inp.bundle.ikB (SignalPqxdh.encodeKEM inp.bundle.pqspkB) inp.bundle.pqspkSig = true
  swap
  · rw [if_neg hs2]; rfl
  rw [if_pos hs2]
  rcases hkem : P.kemEncaps inp.bundle.pqspkB inp.kemCoins with _ | ⟨ss, ct⟩
  · rfl
  dsimp only [P, inp] at hbad ⊢
  by_cases hd1 : (modelPrims X W).x25519 (initiateInput W me be t).ikASk (initiateInput W me be t).bundle.spkB =
      List.replicate 32 0
  · rw [if_neg (by simp [hd1])]; rfl
  rw [if_pos (bne_iff_ne.mpr hd1)]
  by_cases hd2 : (modelPrims X W).x25519 (initiateInput W me be t).ekASk (initiateInput W me be t).bundle.ikB =
      List.replicate 32 0
  · rw [if_neg (by simp [hd2])]; rfl
  rw [if_pos (bne_iff_ne.mpr hd2)]
  by_cases hd3 : (modelPrims X W).x25519 (initiateInput W me be t).ekASk (initiateInput W me be t).bundle.spkB =
      List.replicate 32 0
  · rw [if_neg (by simp [hd3])]; rfl
  rw [if_pos (bne_iff_ne.mpr hd3)]
  have hd4 : SignalPqxdh.dhOptNonZero
      ((initiateInput W me be t).bundle.opkB?.map fun (_, opkPk) =>
        (modelPrims X W).x25519 (initiateInput W me be t).ekASk opkPk) = false := by
    rcases hbad with h1 | h2 | h3 | h4
    · exact absurd h1 hd1
    · exact absurd h2 hd2
    · exact absurd h3 hd3
    · exact h4
  rw [if_neg (by simp [hd4])]; rfl

theorem initDef_some_none_of_dh_bad (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (F : FsFiles) (peer me : AddrVal) (b : BundleV) (be : PreKeyBundleFields)
    (kp : IdentityKeyPair) (coins : List (BitVec 8))
    (hb : bundleEOf? b = some be)
    (htr : StoresGhost.opened.identity.trusted cliIo.rd F peer b.idKey = .ok true)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hbad :
      let P := modelPrims X W
      let inp := initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)
      P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0 ∨
        P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0 ∨
        P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0 ∨
        SignalPqxdh.dhOptNonZero
          (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) = false) :
    initDef X W F peer me b coins = some none := by
  dsimp only [initDef]
  rw [hb, htr, hkp]
  rcases hreg : StoresGhost.opened.identity.regId cliIo.rd F with _ | reg
  · rfl
  · have hinp_eq :
        initiateInput W ⟨kp.privateKey.bytes, reg⟩ be (padCoins coins) =
          initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins) := rfl
    have hnone :
        SignalPqxdh.Model.initiateKeys (modelPrims X W)
          (initiateInput W ⟨kp.privateKey.bytes, reg⟩ be (padCoins coins)) = none := by
      rw [hinp_eq]
      exact initiateKeys_none_of_dh_bad X W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins) hbad
    simp only [initiateState, hnone]

/-! ## 32×4 KEM Seed Unroll and Stage 4 Handshake Keys Bridge -/

theorem truncate8_pack4 (b0 b1 b2 b3 : BitVec 8) :
    ((b3 ++ b2 ++ b1 ++ b0) : BitVec 32).truncate 8 = b0 := by
  change ((b3 ++ b2 ++ b1 ++ b0) : BitVec 32).setWidth 8 = b0
  ext i hi_lt
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    hi_lt, decide_true, Bool.true_and, ↓reduceIte]

theorem drop_take_four_of_vec192 (t : List.Vector (BitVec 8) initiateTapeLen)
    (i : Nat) (hi : i < 32) :
    (t.toList.drop (32 + 4 * i)).take 4 =
      [t.get ⟨32 + 4 * i, by unfold initiateTapeLen; omega⟩,
       t.get ⟨32 + 4 * i + 1, by unfold initiateTapeLen; omega⟩,
       t.get ⟨32 + 4 * i + 2, by unfold initiateTapeLen; omega⟩,
       t.get ⟨32 + 4 * i + 3, by unfold initiateTapeLen; omega⟩] := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, t.toList_length, List.length_cons,
      List.length_nil]
    unfold initiateTapeLen; omega
  · intro j hj1 hj2
    simp only [List.length_cons, List.length_nil] at hj2
    simp only [List.getElem_take, List.getElem_drop, List.Vector.get]
    rcases j with _ | _ | _ | _ | j
    · rfl
    · rfl
    · rfl
    · rfl
    · omega

theorem kemEncaps_out_eq (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (be : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) :
    let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
    ((Pqxdh.Initiator.initiatorModelPrims X W).kemEncaps
      (toU8 be.kpkPub.toList) (toU8 (initiateKemCoins t).toList)).isSome = true ∧
      fitBv8 1600 (Pqxdh.Initiator.kyberEncapsOutBytes
        (Pqxdh.Initiator.initiatorModelPrims X W)
        (toU8 be.kpkPub.toList) (toU8 (initiateKemCoins t).toList)) =
        ct.toList ++ ss.toList := by
  have hkpk : u8Vec 1568 (toU8 be.kpkPub.toList) = be.kpkPub := u8Vec_vecU8_eq be.kpkPub
  have hcoins : u8Vec 32 (toU8 (initiateKemCoins t).toList) = initiateKemCoins t :=
    u8Vec_vecU8_eq (initiateKemCoins t)
  let p := W.Q.encaps be.kpkPub (initiateKemCoins t)
  have henc : (Pqxdh.Initiator.initiatorModelPrims X W).kemEncaps
      (toU8 be.kpkPub.toList) (toU8 (initiateKemCoins t).toList) =
      some (E2E.vecU8 p.2, E2E.vecU8 p.1) := by
    change (modelPrims X W).kemEncaps (toU8 be.kpkPub.toList) (toU8 (initiateKemCoins t).toList) = _
    dsimp only [modelPrims, blockLevelPrims, SignalPqxdh.kyberPkLen]
    have hpkLen : ((toU8 be.kpkPub.toList).length == 1568) = true := by
      simp [Pqxdh.Initiator.e2e_toU8_length]
    simp only [hpkLen, ↓reduceIte]
    rw [hkpk, hcoins]
  refine ⟨by simp [henc], ?_⟩
  simp only [Pqxdh.Initiator.kyberEncapsOutBytes, henc, fitBv8]
  have hct : bytesToBv8 (E2E.vecU8 p.1) = p.1.toList := bytesToBv8_toU8_eq p.1.toList
  have hss : bytesToBv8 (E2E.vecU8 p.2) = p.2.toList := bytesToBv8_toU8_eq p.2.toList
  have hlen : (bytesToBv8 (E2E.vecU8 p.1 ++ E2E.vecU8 p.2)).length = 1600 := by
    rw [bytesToBv8_eq_ofU8, ofU8_length_eq, List.length_append,
      Pqxdh.Initiator.e2e_vecU8_length, Pqxdh.Initiator.e2e_vecU8_length]
  rw [List.take_of_length_le (by omega),
    show 1600 - (bytesToBv8 (E2E.vecU8 p.1 ++ E2E.vecU8 p.2)).length = 0 from by omega,
    List.replicate_zero, List.append_nil, bytesToBv8_eq_ofU8, ofU8, List.map_append]
  rw [bytesToBv8_eq_ofU8] at hct hss
  exact congrArg₂ List.append hct hss

private theorem modelPrims_hkdfDerive96_lens (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (secrets : List UInt8) :
    ((modelPrims X W).hkdfDerive96 secrets).rootKey.length = 32 ∧
      ((modelPrims X W).hkdfDerive96 secrets).chainKey.length = 32 ∧
      ((modelPrims X W).hkdfDerive96 secrets).pqrKey.length = 32 := by
  dsimp only [modelPrims, SignalPqxdh.hkdfDerive96Ref, SignalPqxdh.hkdfExpand96Ref]
  exact ⟨SignalPqxdh.hmacSha256Ref_length _ _ _,
    SignalPqxdh.hmacSha256Ref_length _ _ _,
    SignalPqxdh.hmacSha256Ref_length _ _ _⟩

theorem stage4_keysOk_of_parts (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (kp : IdentityKeyPair) (be : PreKeyBundleFields) (coins : List (BitVec 8))
    (hsigs : PreKeyBundleFields.signaturesVerify X W be = true)
    (hdh1 : (modelPrims X W).x25519
      (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ikASk
      (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).bundle.spkB ≠
        List.replicate 32 0)
    (hdh2 : (modelPrims X W).x25519
      (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk
      (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).bundle.ikB ≠
        List.replicate 32 0)
    (hdh3 : (modelPrims X W).x25519
      (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk
      (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).bundle.spkB ≠
        List.replicate 32 0)
    (hdh4 : SignalPqxdh.dhOptNonZero
      ((initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).bundle.opkB?.map
        fun (_, opkPk) => (modelPrims X W).x25519
          (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk opkPk) = true) :
    let P := modelPrims X W
    let inp := initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)
    let ct := (W.Q.encaps be.kpkPub (initiateKemCoins (padCoins coins))).1
    let ss := (W.Q.encaps be.kpkPub (initiateKemCoins (padCoins coins))).2
    let dh1 := P.x25519 inp.ikASk inp.bundle.spkB
    let dh2 := P.x25519 inp.ekASk inp.bundle.ikB
    let dh3 := P.x25519 inp.ekASk inp.bundle.spkB
    let dh4? := inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk
    let secrets := Pqxdh.Initiator.buildSecrets dh1 dh2 dh3 dh4? (E2E.vecU8 ss)
    let dk := P.hkdfDerive96 secrets
    let hdr : SignalPqxdh.HandshakeHdr :=
      { ikAPk := inp.ikAPk
        ekAPk := P.x25519Base inp.ekASk
        spkId := inp.bundle.spkId
        opkId? := inp.bundle.opkB?.map Prod.fst
        pqspkId := inp.bundle.pqspkId
        kemCt := E2E.vecU8 ct }
    SignalPqxdh.Model.initiateKeys P inp = some (dk, hdr) ∧
      (8#8 :: ct.toList) = 8#8 :: ofU8 hdr.kemCt ∧
      bytesToBv8 (Pqxdh.Initiator.handshakeKeysBytes100
        (Pqxdh.Initiator.Model.deriveDRKeys (P : Pqxdh.Initiator.Primitives) secrets)) =
        ofU8 (dk.rootKey ++ dk.pqrKey ++ dk.chainKey ++ [0, 0, 0, 0]) ∧
      (8#8 :: ct.toList).length = 1569 ∧
      (ofU8 (dk.rootKey ++ dk.pqrKey ++ dk.chainKey ++ [0, 0, 0, 0])).length = 100 := by
  dsimp only
  simp only [PreKeyBundleFields.signaturesVerify, Bool.and_eq_true] at hsigs
  rcases hsigs with ⟨hsig1, hsig2⟩
  let P := modelPrims X W
  let inp := initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)
  have hbund :
      (initiateInput W ⟨List.Vector.replicate 32 0#8, 0⟩ be
        (List.Vector.replicate initiateTapeLen 0#8)).bundle = inp.bundle := rfl
  rw [hbund] at hsig1 hsig2
  have htr : inp.trustedPeer = true := rfl
  have hkem : P.kemEncaps inp.bundle.pqspkB inp.kemCoins =
      some (E2E.vecU8 (W.Q.encaps be.kpkPub (initiateKemCoins (padCoins coins))).2,
        E2E.vecU8 (W.Q.encaps be.kpkPub (initiateKemCoins (padCoins coins))).1) := by
    dsimp only [P, inp, modelPrims, blockLevelPrims, SignalPqxdh.kyberPkLen, initiateInput]
    have hpkLen : ((E2E.vecU8 be.kpkPub).length == 1568) = true := by
      rw [Pqxdh.Initiator.e2e_vecU8_length]; rfl
    simp only [hpkLen, ↓reduceIte]
    rw [u8Vec_vecU8_eq, u8Vec_vecU8_eq]
  have hkeys : SignalPqxdh.Model.initiateKeys P inp =
      some (P.hkdfDerive96 (SignalPqxdh.buildSecrets
          (P.x25519 inp.ikASk inp.bundle.spkB)
          (P.x25519 inp.ekASk inp.bundle.ikB)
          (P.x25519 inp.ekASk inp.bundle.spkB)
          (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk)
          (E2E.vecU8 (W.Q.encaps be.kpkPub (initiateKemCoins (padCoins coins))).2)),
        { ikAPk := inp.ikAPk
          ekAPk := P.x25519Base inp.ekASk
          spkId := inp.bundle.spkId
          opkId? := inp.bundle.opkB?.map Prod.fst
          pqspkId := inp.bundle.pqspkId
          kemCt := E2E.vecU8 (W.Q.encaps be.kpkPub (initiateKemCoins (padCoins coins))).1 }) := by
    unfold SignalPqxdh.Model.initiateKeys
    dsimp only [_root_.guard, bind, Option.bind]
    rw [if_pos htr, if_pos hsig1, if_pos hsig2, hkem,
      if_pos (bne_iff_ne.mpr hdh1), if_pos (bne_iff_ne.mpr hdh2),
      if_pos (bne_iff_ne.mpr hdh3), if_pos hdh4]
    rfl
  have hct_eq :
      (W.Q.encaps be.kpkPub (initiateKemCoins (padCoins coins))).1.toList =
        ofU8 (E2E.vecU8 (W.Q.encaps be.kpkPub (initiateKemCoins (padCoins coins))).1) :=
    (ofU8_toU8_eq _).symm
  let secrets := Pqxdh.Initiator.buildSecrets
    (P.x25519 inp.ikASk inp.bundle.spkB)
    (P.x25519 inp.ekASk inp.bundle.ikB)
    (P.x25519 inp.ekASk inp.bundle.spkB)
    (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk)
    (E2E.vecU8 (W.Q.encaps be.kpkPub (initiateKemCoins (padCoins coins))).2)
  have hlen100 :
      (ofU8 ((P.hkdfDerive96 secrets).rootKey ++ (P.hkdfDerive96 secrets).pqrKey ++
        (P.hkdfDerive96 secrets).chainKey ++ [0, 0, 0, 0])).length = 100 := by
    rcases modelPrims_hkdfDerive96_lens X W secrets with ⟨hrk, hck, hpqr⟩
    dsimp only [P]
    simp only [ofU8_length_eq, List.length_append, List.length_cons, List.length_nil]
    omega
  exact ⟨hkeys, congrArg (8#8 :: ·) hct_eq, bytesToBv8_eq_ofU8 _,
    by simp [List.Vector.toList_length], hlen100⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
