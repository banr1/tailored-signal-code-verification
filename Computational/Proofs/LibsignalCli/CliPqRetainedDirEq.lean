/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Game.StatementPq
public import Computational.Proofs.LibsignalCli.CliPqHandshakeStepCore
public import Computational.Proofs.LibsignalCli.Entry.CliPqSessionCap
public import Computational.Proofs.E2E.Relabel.GameEq

@[expose] public section

set_option autoImplicit false

/-!
# Equivalence of the retained-directory CLI game and the projected `BinState` staging game

**Checked by Lean.** Shows that projecting `CliDriverState` to `ModelDriverState` commutes with
every oracle of `Dir.cliDrvImpl` under `CliSpecPqxdh run X W` and `l < 10 ^ 6` (`DEV-CLI18`),
yielding exact equality of `cliPqExp` with `cliPqExpProj` and `CliPqxdhAdvantage` with
`CliPqxdhAdvantageProj`.
-/

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession
  CryptoVerification.LibsignalCli.Entry
  CryptoVerification.E2E.Relabel.GameEq

/-! ## `PqParty` directory and wire helpers -/

private theorem encodeVarintAux_len_le_ret : ∀ (k : Nat) (v : BitVec 64),
    (encodeVarintAux k v).length ≤ k
  | 0, _ => by simp [encodeVarintAux]
  | k + 1, v => by
    unfold encodeVarintAux; split_ifs
    · simp
    · simp only [List.length_cons]
      exact Nat.add_le_add_right (encodeVarintAux_len_le_ret k (v >>> 7)) 1

private theorem encodeBytes3_len_le_ret (tag : Nat) (v : List (BitVec 8)) :
    (RecordCodecs.encodeProto3BytesField tag v).length ≤ 20 + v.length := by
  unfold RecordCodecs.encodeProto3BytesField
  split_ifs
  · simp
  · unfold encodeBytesField encodeKey LibsignalProtoCodec.encodeVarint
    have h1 := encodeVarintAux_len_le_ret 10 (BitVec.ofNat 64 (tag * 8 + WireType.lengthDelimited.toNat))
    have h2 := encodeVarintAux_len_le_ret 10 (BitVec.ofNat 64 v.length)
    simp only [List.length_append]
    omega

private theorem encodeUint32_3_len_le_ret (tag : Nat) (v : BitVec 32) :
    (RecordCodecs.encodeProto3Uint32Field tag v).length ≤ 20 := by
  unfold RecordCodecs.encodeProto3Uint32Field
  split_ifs
  · simp
  · unfold LibsignalProtoCodec.encodeUint32Field encodeKey LibsignalProtoCodec.encodeVarint
    have h1 := encodeVarintAux_len_le_ret 10 (BitVec.ofNat 64 (tag * 8 + WireType.varint.toNat))
    have h2 := encodeVarintAux_len_le_ret 10 (v.zeroExtend 64)
    simp only [List.length_append]
    omega

private theorem byteArray_toList_eq_data_ret : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8Encode_size_le_ret (cs : List Char) :
    (List.utf8Encode cs).size ≤ 4 * cs.length := by
  induction cs with
  | nil => simp [List.utf8Encode_nil]
  | cons c cs htl =>
    rw [List.utf8Encode_cons, ByteArray.size_append]
    have hc : (List.utf8Encode [c]).size ≤ 4 := by
      unfold List.utf8Encode List.flatMap
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [String.utf8EncodeChar.eq_def, List.size_toByteArray]
      dsimp only
      split_ifs <;> simp
    simp only [List.length_cons]
    omega

private theorem textBytes_B_len_lt_ret :
    (textBytes (partyAddress Party.B).text).length ≤ fileCapBytes := by
  have hlen : ∀ s : String, (textBytes s).length ≤ 4 * s.toList.length := by
    intro s
    obtain ⟨cs, rfl⟩ := s.exists_eq_ofList
    unfold textBytes CryptoVerification.LibsignalTripleRatchetRepr.utf8
    rw [String.toUTF8_eq_toByteArray, List.length_map, byteArray_toList_eq_data_ret,
      Array.length_toList, String.toList_ofList, String.toByteArray_ofList]
    exact utf8Encode_size_le_ret cs
  have h1 : (Nat.repr 1).toList.length = 1 := by
    rw [Nat.repr_eq_ofList_toDigits, Nat.toDigits_of_lt_base (by decide),
      Nat.digitChar_eq_one.mpr rfl, String.toList_ofList]
    rfl
  have hB : (partyAddress Party.B).text.toList.length = 38 := by
    unfold partyAddress CryptoVerification.SignalSession.Address.text partyAddressName
    dsimp only
    rw [Nat.toString_eq_repr, String.toList_append, String.toList_append,
      List.length_append, List.length_append, h1]
    decide
  have h := hlen (partyAddress Party.B).text
  unfold fileCapBytes
  omega

private theorem wfPq_cliPqDirB0_ret {S : SignalPqxdh.Setup} {l : Nat}
    (W : PEParams) (bi : ModelDriverInstance S l)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64) :
    PqxdhPartyInSpecDomain W (cliPqxdhDirBobBeforeAccept bi sigs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ h; simp [cliPqxdhDirBobBeforeAccept] at h
  · intro f hf
    suffices h : f.2.length ≤ fileCapBytes by
      exact ⟨by unfold fileCapBytes at h; omega, fun _ => h⟩
    unfold cliPqxdhDirBobBeforeAccept encodeDir at hf
    simp only [List.map_nil, List.append_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map] at hf
    rcases hf with ((((h1 | h2 | h3) | h4) | ⟨⟨i, k⟩, hm, rfl⟩) | ⟨⟨i, ok⟩, hm, rfl⟩) | hf_lr
    · subst h1; exact textBytes_B_len_lt_ret
    · subst h2
      dsimp [RecordCodecs.IdentityKeyPairStructure.encode]
      simp only [List.length_append]
      have h_pk := encodeBytes3_len_le_ret 1 (djbKey (keyPairOf W.C bi.meB.idPriv).publicKey.bytes)
      have h_sk := encodeBytes3_len_le_ret 2 bi.meB.idPriv.toList
      have hdjb : (djbKey (keyPairOf W.C bi.meB.idPriv).publicKey.bytes).length = 33 := by simp [djbKey]
      have hpriv : bi.meB.idPriv.toList.length = 32 := bi.meB.idPriv.2
      unfold fileCapBytes; omega
    · subst h3; simp [le32, fileCapBytes]
    · subst h4; simp [IdentityKey.serialize, PublicKey.serialize, fileCapBytes]
    · simp only [Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      dsimp [signedRecordBytes, RecordCodecs.SignedPreKeyRecordStructure.encode]
      simp only [List.length_append]
      have a1 := encodeUint32_3_len_le_ret 1 bi.keysB.spkId
      have a2 := encodeBytes3_len_le_ret 2 (djbKey (keyPairOf W.C bi.keysB.spkPriv).publicKey.bytes)
      have a3 := encodeBytes3_len_le_ret 3 bi.keysB.spkPriv.toList
      have a4 := encodeBytes3_len_le_ret 4 sigs.1.toList
      have a5 : (RecordCodecs.encodeProto3Fixed64Field 5 0#64).length = 0 := rfl
      have l2 : (djbKey (keyPairOf W.C bi.keysB.spkPriv).publicKey.bytes).length = 33 := by simp [djbKey]
      have l3 : bi.keysB.spkPriv.toList.length = 32 := bi.keysB.spkPriv.2
      have l4 : sigs.1.toList.length = 64 := sigs.1.2
      unfold fileCapBytes; omega
    · rcases h_opk : bi.keysB.opk with _ | ⟨oid, osk⟩ <;> rw [h_opk] at hm
      · simp at hm
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        dsimp [oneTimeRecordBytes, RecordCodecs.PreKeyRecordStructure.encode]
        simp only [List.length_append]
        have a1 := encodeUint32_3_len_le_ret 1 i
        have a2 := encodeBytes3_len_le_ret 2 (djbKey (keyPairOf W.C osk).publicKey.bytes)
        have a3 := encodeBytes3_len_le_ret 3 osk.toList
        have l2 : (djbKey (keyPairOf W.C osk).publicKey.bytes).length = 33 := by simp [djbKey]
        have l3 : osk.toList.length = 32 := osk.2
        unfold fileCapBytes; omega
    · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hf_lr
      rcases hf_lr with rfl | rfl
      · dsimp [kyberRecordBytes, RecordCodecs.SignedPreKeyRecordStructure.encode]
        simp only [List.length_append]
        have a1 := encodeUint32_3_len_le_ret 1 bi.keysB.kpkId
        have a2 := encodeBytes3_len_le_ret 2 (kyberKey bi.keysB.kpkPub)
        have a3 := encodeBytes3_len_le_ret 3 (0x08#8 :: bi.keysB.kpkSec.toList)
        have a4 := encodeBytes3_len_le_ret 4 sigs.2.toList
        have a5 : (RecordCodecs.encodeProto3Fixed64Field 5 0#64).length = 0 := rfl
        have l2 : (kyberKey bi.keysB.kpkPub).length = 1569 := by simp [kyberKey]
        have l3 : (0x08#8 :: bi.keysB.kpkSec.toList).length = 3169 := by simp
        have l4 : sigs.2.toList.length = 64 := sigs.2.2
        unfold fileCapBytes; omega
      · simp [baseKeysBytes, fileCapBytes]
  · simp [cliPqxdhDirBobBeforeAccept]
  · unfold cliPqxdhDirBobBeforeAccept; dsimp only
    cases bi.keysB.opk <;> simp
  · simp [cliPqxdhDirBobBeforeAccept]
  · simp [cliPqxdhDirBobBeforeAccept]

private theorem map_fst_clear_opt_ret {α β : Type} [DecidableEq α] (l : List (α × Option β)) (j : α) :
    ((l.map fun (i, k) => if i = j then (i, none) else (i, k)).map (·.1)) = l.map (·.1) := by
  induction l with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨i, k⟩; simp only [List.map_cons, ih]; split_ifs <;> rfl

private theorem map_fst_append_seen_ret {α β γ : Type} [DecidableEq α]
    (l : List (α × β × List γ)) (j : α) (u : γ) :
    ((l.map fun (i, k, s) => if i = j then (i, k, s ++ [u]) else (i, k, s)).map (·.1)) =
      l.map (·.1) := by
  induction l with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨i, k, s⟩; simp only [List.map_cons, ih]; split_ifs <;> rfl

private theorem cliPqDirB1_props_ret {S : SignalPqxdh.Setup} {l : Nat}
    (bi : ModelDriverInstance S l) (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64) :
    (cliPqxdhDirBobAfterAccept bi sigs).party = .B ∧
    (cliPqxdhDirBobAfterAccept bi sigs).me = bi.meB ∧
    (cliPqxdhDirBobAfterAccept bi sigs).peerId = some (bhIdKeyOf bi.hdr.ikAPk) ∧
    (cliPqxdhDirBobAfterAccept bi sigs).session = none ∧
    lastResortUses (cliPqxdhDirBobAfterAccept bi sigs) ≤ 1 ∧
    cliPqPartyPathsOf (cliPqxdhDirBobAfterAccept bi sigs) =
      cliPqPartyPathsOf (cliPqxdhDirBobBeforeAccept bi sigs) := by
  unfold cliPqxdhDirBobAfterAccept
  set m0 := bhExpectedPreKeyMsg bi.meA.regId bi.hdr []
  set d0 := cliPqxdhDirBobBeforeAccept bi sigs
  have hrm : ∀ (st : PqParty),
      (removeOpk st m0).party = st.party ∧
      (removeOpk st m0).me = st.me ∧
      (removeOpk st m0).peerId = st.peerId ∧
      (removeOpk st m0).session = st.session ∧
      lastResortUses (removeOpk st m0) = lastResortUses st ∧
      cliPqPartyPathsOf (removeOpk st m0) = cliPqPartyPathsOf st := by
    intro st; unfold removeOpk
    cases m0.opkId with
    | none => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | some j =>
      refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
      unfold cliPqPartyPathsOf
      dsimp only
      rw [map_fst_clear_opt_ret]
  obtain ⟨hp, hme, hpeer, hsess, hlr, hpaths⟩ := hrm ((markKyberUsed d0 m0).getD d0)
  have hd0 :
      ((markKyberUsed d0 m0).getD d0).party = .B ∧
      ((markKyberUsed d0 m0).getD d0).me = bi.meB ∧
      ((markKyberUsed d0 m0).getD d0).peerId = some (bhIdKeyOf bi.hdr.ikAPk) ∧
      ((markKyberUsed d0 m0).getD d0).session = none ∧
      lastResortUses ((markKyberUsed d0 m0).getD d0) ≤ 1 ∧
      cliPqPartyPathsOf ((markKyberUsed d0 m0).getD d0) = cliPqPartyPathsOf d0 := by
    unfold markKyberUsed
    have hkot : List.lookup m0.kpkId d0.kyberOneTime = none := by simp [d0, cliPqxdhDirBobBeforeAccept]
    rw [hkot]
    by_cases hk : (m0.kpkId == bi.keysB.kpkId) = true
    · have hk_eq : m0.kpkId = bi.keysB.kpkId := beq_iff_eq.mp hk
      have hklr : List.lookup m0.kpkId d0.kyberLastResort =
          some ({ pub := bi.keysB.kpkPub, sec := bi.keysB.kpkSec, sig := sigs.2, timestamp := 0#64 }, []) := by
        simp [d0, cliPqxdhDirBobBeforeAccept, List.lookup, hk]
      rw [hklr]
      refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
      · simp [d0, cliPqxdhDirBobBeforeAccept, hk_eq, lastResortUses, fileCapBytes]
      · simp only [List.length_nil, Nat.mul_zero, fileCapBytes, Nat.not_lt_zero, List.not_mem_nil,
          or_self, ↓reduceIte, Option.getD_some]
        unfold cliPqPartyPathsOf; dsimp only; rw [map_fst_append_seen_ret]
    · have hk_false : (m0.kpkId == bi.keysB.kpkId) = false := Bool.eq_false_iff.mpr hk
      have hklr : List.lookup m0.kpkId d0.kyberLastResort = none := by
        simp [d0, cliPqxdhDirBobBeforeAccept, List.lookup, hk_false]
      rw [hklr]
      exact ⟨rfl, rfl, rfl, rfl, by simp [d0, cliPqxdhDirBobBeforeAccept, lastResortUses], rfl⟩
  exact ⟨hp.trans hd0.1, hme.trans hd0.2.1, hpeer.trans hd0.2.2.1,
    hsess.trans hd0.2.2.2.1, hlr ▸ hd0.2.2.2.2.1, hpaths.trans hd0.2.2.2.2.2⟩

private theorem prost_key_lt128_ret (t w : Nat) (h : 8 * t + w < 128) :
    Prost.key t w = [BitVec.ofNat 8 (8 * t + w)] := by
  unfold Prost.key
  rw [Prost.varint]
  simp [h]

private theorem take_drop_append_ret (xs ys : List (BitVec 8)) :
    (xs ++ ys).take xs.length = xs ∧ (xs ++ ys).drop xs.length = ys :=
  ⟨List.take_left, List.drop_left⟩

private theorem bhDecodePreKeyMsgE_wirePrekey_ret (m : PreKeyMessageFields) :
    bhDecodePreKeyMsgE (wirePrekey :: m.bytes) = some m := by
  have hraw : bhDecodePreKeyMsgERaw (wirePrekey :: m.bytes) = some m := by
    rcases m with ⟨regId, opkId, spkId, kpkId, ⟨kyberCtL, hct⟩, ⟨baseKeyL, hbk⟩, ⟨idPubL, hid⟩, inner⟩
    have hf2 : Prost.bytesField 2 (some (djbKey ⟨baseKeyL, hbk⟩)) = [0x12#8, 0x21#8, 0x05#8] ++ baseKeyL := by
      unfold Prost.bytesField djbKey
      simp only [List.Vector.toList_mk, List.length_cons, hbk,
        show 32 + 1 = 33 from rfl,
        show Prost.key 2 2 = [0x12#8] by rw [prost_key_lt128_ret 2 2 (by omega)],
        show Prost.varint 33 = [0x21#8] by rw [Prost.varint]; simp,
        List.cons_append, List.nil_append]
    have hf3 : Prost.bytesField 3 (some (djbKey ⟨idPubL, hid⟩)) = [0x1a#8, 0x21#8, 0x05#8] ++ idPubL := by
      unfold Prost.bytesField djbKey
      simp only [List.Vector.toList_mk, List.length_cons, hid,
        show 32 + 1 = 33 from rfl,
        show Prost.key 3 2 = [0x1a#8] by rw [prost_key_lt128_ret 3 2 (by omega)],
        show Prost.varint 33 = [0x21#8] by rw [Prost.varint]; simp,
        List.cons_append, List.nil_append]
    have hf4 : Prost.bytesField 4 (some inner) = [0x22#8] ++ Prost.varint inner.length ++ inner := by
      unfold Prost.bytesField
      rw [show Prost.key 4 2 = [0x22#8] by rw [prost_key_lt128_ret 4 2 (by omega)]]
    have hf5 : Prost.uint32Field 5 (some regId) = [0x28#8] ++ Prost.varint regId.toNat := by
      unfold Prost.uint32Field
      rw [show Prost.key 5 0 = [0x28#8] by rw [prost_key_lt128_ret 5 0 (by omega)]]
    have hf6 : Prost.uint32Field 6 (some spkId) = [0x30#8] ++ Prost.varint spkId.toNat := by
      unfold Prost.uint32Field
      rw [show Prost.key 6 0 = [0x30#8] by rw [prost_key_lt128_ret 6 0 (by omega)]]
    have hf7 : Prost.uint32Field 7 (some kpkId) = [0x38#8] ++ Prost.varint kpkId.toNat := by
      unfold Prost.uint32Field
      rw [show Prost.key 7 0 = [0x38#8] by rw [prost_key_lt128_ret 7 0 (by omega)]]
    have hv1569 : Prost.varint 1569 = [0xa1#8, 0x0c#8] := by
      rw [Prost.varint]
      simp only [show ¬(1569 < 128) by omega, ↓reduceDIte]
      rw [Prost.varint]
      simp [show 1569 / 128 < 128 by omega]
    have hf8 : Prost.bytesField 8 (some (kyberKey ⟨kyberCtL, hct⟩)) =
        [0x42#8, 0xa1#8, 0x0c#8, 0x08#8] ++ kyberCtL := by
      unfold Prost.bytesField kyberKey
      simp only [List.Vector.toList_mk, List.length_cons, hct,
        show 1568 + 1 = 1569 from rfl,
        show Prost.key 8 2 = [0x42#8] by rw [prost_key_lt128_ret 8 2 (by omega)],
        hv1569, List.cons_append, List.nil_append]
    let tail8 : List (BitVec 8) := 0x42#8 :: 0xa1#8 :: 0x0c#8 :: 0x08#8 :: kyberCtL
    let tail7 : List (BitVec 8) := 0x38#8 :: (Prost.varint kpkId.toNat ++ tail8)
    let tail6 : List (BitVec 8) := 0x30#8 :: (Prost.varint spkId.toNat ++ tail7)
    let tail5 : List (BitVec 8) := 0x28#8 :: (Prost.varint regId.toNat ++ tail6)
    let tail4 : List (BitVec 8) := 0x22#8 :: (Prost.varint inner.length ++ (inner ++ tail5))
    let tail3 : List (BitVec 8) := 0x1a#8 :: 0x21#8 :: 0x05#8 :: (idPubL ++ tail4)
    let tail2 : List (BitVec 8) := 0x12#8 :: 0x21#8 :: 0x05#8 :: (baseKeyL ++ tail3)
    have hbytes : (PreKeyMessageFields.mk regId opkId spkId kpkId ⟨kyberCtL, hct⟩ ⟨baseKeyL, hbk⟩ ⟨idPubL, hid⟩ inner).bytes =
        versionByte currentVersion :: (Prost.uint32Field 1 opkId ++ tail2) := by
      unfold PreKeyMessageFields.bytes ProtoPreKeySignalMessage.encode
      rw [hf2, hf3, hf4, hf5, hf6, hf7, hf8]
      simp [tail2, tail3, tail4, tail5, tail6, tail7, tail8, List.append_assoc]
    have hopk_parse : bhParseOptPreKeyId (Prost.uint32Field 1 opkId ++ tail2) =
        some (opkId.map (fun v => UInt32.ofNat v.toNat), tail2) := by
      cases opkId with
      | none =>
        simp [Prost.uint32Field, tail2, bhParseOptPreKeyId, show (0x12#8 == 0x08#8) = false by decide]
      | some v =>
        have hf1 : Prost.uint32Field 1 (some v) = 0x08#8 :: Prost.varint v.toNat := by
          unfold Prost.uint32Field
          rw [show Prost.key 1 0 = [0x08#8] by rw [prost_key_lt128_ret 1 0 (by omega)]]
          rfl
        rw [hf1, List.cons_append]
        simp [bhParseOptPreKeyId, bhReadProstVarint_varint_append]
    rw [hbytes]
    unfold bhDecodePreKeyMsgERaw
    simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte, hopk_parse, Option.bind]
    obtain ⟨ht1, hd1⟩ := take_drop_append_ret baseKeyL tail3
    rw [hbk] at ht1 hd1
    obtain ⟨ht2, hd2⟩ := take_drop_append_ret idPubL tail4
    rw [hid] at ht2 hd2
    obtain ⟨ht3, hd3⟩ := take_drop_append_ret inner tail5
    have ht4 : kyberCtL.take 1568 = kyberCtL := by simp [hct]
    cases opkId <;>
      simp [tail2, tail3, tail4, tail5, tail6, tail7, tail8,
        bhParseDjbKeyField, bhParseInnerMsgFieldWithRest, bhReadProstVarint_varint_append,
        bhParseUint32Field, bhParseKyberCtField, Option.bind,
        ht1, hd1, ht2, hd2, ht3, hd3, ht4, hbk, hid, hct]
  unfold bhDecodePreKeyMsgE
  rw [hraw]
  simp

private theorem bhDecodePreKeyMsgE_eq_some_imp_ret {c : Bytes} {m : PreKeyMessageFields}
    (h : bhDecodePreKeyMsgE c = some m) :
    c = wirePrekey :: m.bytes ∧ c.head? = some wirePrekey := by
  unfold bhDecodePreKeyMsgE at h
  rcases hraw : bhDecodePreKeyMsgERaw c with _ | m' <;> rw [hraw] at h
  · cases h
  · dsimp only at h
    by_cases heq : (c == wirePrekey :: m'.bytes) = true
    · simp only [heq, ↓reduceIte, Option.some.injEq] at h; subst h
      have hc : c = wirePrekey :: m'.bytes := beq_iff_eq.mp heq
      exact ⟨hc, by rw [hc]; rfl⟩
    · simp [heq] at h

/-! ## Per-party retained-directory invariant -/

private theorem dirCliPqAfter_pqObserve_eq {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {st : PqParty} (hnd : PqDirIdsNodup st) (P : Party) (i : Inputs)
    (r : Option (Option (PqParty × List (BitVec 8))))
    (h_ok : ∀ st' out, r = some (some (st', out)) →
      st'.party = P ∧ PqStep X W st st' ∧ ∃ x' g', st'.session = some (x', g')) :
    Dir.cliPqAfter P (cliPqPartyPathsOf st) (some (pqxdhExpectedOutcome W i r)) =
      r.join.map (fun (st', out) =>
        (encodeDir W st',
         match st'.session with
         | some (x', g') => encodeRecordUnderExtras (fun _ => x') g'
         | none => [],
         out)) ∧
    cliPqAfter P (some (pqxdhExpectedOutcome W i r)) =
      r.join.map (fun (st', out) =>
        (match st'.session with
         | some (x', g') => encodeRecordUnderExtras (fun _ => x') g'
         | none => [],
         out)) := by
  have hpaths : cliPqPartyPathsOf st = pqPartyCandidatePathsOf st := rfl
  have hread : cliPqReadBack = readBackDir := rfl
  rcases r with _ | (_ | ⟨st', out⟩)
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · obtain ⟨hp, hstep, x', g', hsess⟩ := h_ok st' out rfl
    have hdir : readBackDir (pqPartyCandidatePathsOf st) (filesOf (i.files ++ encodeDir W st')) =
        encodeDir W st' :=
      readBackDir_pqObserve_ok_eq i.files hnd hstep
    have hrec : filesOf (i.files ++ encodeDir W st') (sessionFile (partyAddress P.other)) =
        some (encodeRecordUnderExtras (fun _ => x') g') := by
      rw [← hp]
      exact filesOf_append_encodeDir_sessionFile_eq W i.files st' x' g' hsess
    simp [Dir.cliPqAfter, cliPqAfter, pqxdhExpectedOutcome, observe,
      hpaths, hread, hdir, hrec, hsess]

private theorem trusts_false_eq_peerId {st : PqParty} {peer k : IdentityKey}
    (hp : st.peerId = some peer) (hnt : (!st.trusts k) = false) :
    some k = st.peerId := by
  have ht : st.trusts k = true := by simpa using hnt
  unfold PqParty.trusts at ht
  rw [hp, decide_eq_true_eq] at ht
  rw [hp, ht]

/-- Per-party retained-directory invariant in a promoted CLI instance `bi`. -/
def CliPartyDirInv {S : SignalPqxdh.Setup} {l : Nat} (W : PEParams)
    (bi : ModelDriverInstance S l)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64) :
    Party → CliPartyState → Prop
  | .A, s =>
    ∃ x g,
      PqxdhPartyInSpecDomain W { cliPqDirA bi with session := some (x, g) } ∧
      s.bin.party = .A ∧
      s.bin.bytes = encodeRecordUnderExtras (fun _ => x) g ∧
      s.paths = cliPqPartyPathsOf (cliPqDirA bi) ∧
      s.dir = encodeDir W { cliPqDirA bi with session := some (x, g) }
  | .B, s =>
    s = cliPartyStateB0 W bi sigs ∨
    ∃ x g,
      PqxdhPartyInSpecDomain W { cliPqxdhDirBobAfterAccept bi sigs with session := some (x, g) } ∧
      x.aliceBaseKey = djbKey (u8Vec 32 bi.hdr.ekAPk) ∧
      s.bin.party = .B ∧
      s.bin.bytes = encodeRecordUnderExtras (fun _ => x) g ∧
      s.paths = cliPqPartyPathsOf (cliPqxdhDirBobBeforeAccept bi sigs) ∧
      s.dir = encodeDir W { cliPqxdhDirBobAfterAccept bi sigs with session := some (x, g) }

private theorem cliPartyDirInv_bi_gs {S : SignalPqxdh.Setup} {l : Nat} (W : PEParams)
    (bi : ModelDriverInstance S l)
    (gs1 gs2 : Option (SM.GameState BinState (Plain l) Bytes))
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (P : Party) (s : CliPartyState) :
    CliPartyDirInv W { bi with gs := gs1 } sigs P s ↔
      CliPartyDirInv W { bi with gs := gs2 } sigs P s := by
  cases P <;> rfl

/-! ## Step bridges for `cliPqInit`, `cliPqSend`, and `cliPqReceive` -/

theorem cliPqInit_dir_eq_proj {S : SignalPqxdh.Setup} {l : Nat}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W)
    (bi : ModelDriverInstance S l)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (bundleE : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    (Dir.cliPqInit run W (cliPqDirA bi) bundleE t).map CliPartyState.bin =
      cliPqInit run W (cliPqDirA bi) bundleE t ∧
    (∀ stA0, Dir.cliPqInit run W (cliPqDirA bi) bundleE t = some stA0 →
      CliPartyDirInv W bi sigs .A stA0) := by
  set dA := cliPqDirA bi
  have hwf : PqxdhPartyInSpecDomain W dA := wfPq_cliPqDirA W bi
  have hrun := (hCli dA hwf).1 bundleE t rfl
  have hok : ∀ st' out, pqInitModel X W dA bundleE t = some (some (st', out)) →
      st'.party = .A ∧ PqStep X W dA st' ∧ ∃ x' g', st'.session = some (x', g') ∧
        st' = { dA with session := some (x', g') } ∧ PqxdhPartyInSpecDomain W st' := by
    intro st' out hmod
    have hstep : PqStep X W dA st' := PqStep.init bundleE t st' out rfl hmod
    unfold pqInitModel at hmod
    by_cases hnt : (!dA.trusts ⟨⟨bundleE.idPub⟩⟩) = true
    · simp [hnt] at hmod
    · simp only [Bool.not_eq_true] at hnt
      rw [hnt] at hmod
      simp only [Bool.false_eq_true, ↓reduceIte] at hmod
      rcases hi : initiateState X W dA.party dA.me bundleE t with _ | ⟨x, g⟩ <;> rw [hi] at hmod
      · cases hmod
      · simp only [Option.some.injEq, Prod.mk.injEq] at hmod
        rcases hmod with ⟨rfl, rfl⟩
        have hpeer : some (⟨⟨bundleE.idPub⟩⟩ : IdentityKey) = dA.peerId :=
          trusts_false_eq_peerId (peer := bhIdKeyOf bi.idBBytes) rfl hnt
        let st1 : PqParty := { dA with peerId := some ⟨⟨bundleE.idPub⟩⟩, session := some (x, g) }
        have hst_eq : st1 = { dA with session := some (x, g) } := by
          dsimp only [st1]; rw [hpeer]
        have hlr : lastResortUses st1 < 2 ^ 25 := by
          simp [st1, dA, cliPqDirA, lastResortUses]
        have hwf' := (wfPq_step_r3 hwf hstep hlr).1
        exact ⟨rfl, hstep, x, g, rfl, hst_eq, hwf'⟩
  obtain ⟨ha_dir, ha_proj⟩ := dirCliPqAfter_pqObserve_eq (pqDirIdsNodup_of_wfPq hwf) .A
    (pqInitInputs W dA bundleE t) (pqInitModel X W dA bundleE t)
    (fun st' out hm =>
      let ⟨hp, hs, x', g', hsess, _, _⟩ := hok st' out hm
      ⟨hp, hs, x', g', hsess⟩)
  unfold Dir.cliPqInit cliPqInit
  dsimp only
  rw [hrun, ha_dir, ha_proj]
  refine ⟨?_, ?_⟩
  · rcases pqInitModel X W dA bundleE t with _ | (_ | ⟨st', out⟩) <;> rfl
  · rcases hm : pqInitModel X W dA bundleE t with _ | (_ | ⟨st', out⟩)
    · intro _ h; cases h
    · intro _ h; cases h
    · obtain ⟨_, _, x, g, hsess, hst_eq, hwf'⟩ := hok st' out hm
      simp only [Option.join_some, Option.map_some, Option.some.injEq, hsess]
      rintro stA0 rfl
      exact ⟨x, g, hst_eq ▸ hwf', rfl, rfl, rfl, by rw [hst_eq]⟩

private theorem pqSendModel_step_session {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {d : PqParty} {peer : IdentityKey} {x : RecordExtras} {g : GhostState Bytes}
    (hwf : PqxdhPartyInSpecDomain W { d with session := some (x, g) })
    (hpeer : d.peerId = some peer) (hlr : lastResortUses d ≤ 1)
    (m : List (BitVec 8)) (hm : m.length < 2 ^ 32) (rs : BitVec 512)
    {st' : PqParty} {out : List (BitVec 8)}
    (hmod : pqSendModel W { d with session := some (x, g) } m (LibsignalSpqrV1.coinBytes rs) =
      some (some (st', out))) :
    st'.party = d.party ∧
    PqStep X W { d with session := some (x, g) } st' ∧
    ∃ g', st'.session = some (x, g') ∧
      st' = { d with session := some (x, g') } ∧
      PqxdhPartyInSpecDomain W st' := by
  set st : PqParty := { d with session := some (x, g) }
  have hstep : PqStep X W st st' :=
    PqStep.send m (coinBytesVec64 rs) st' out hm (by simpa [coinBytesVec64_toList] using hmod)
  unfold pqSendModel at hmod
  dsimp only [st] at hmod
  rcases henc : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).sendAddrs g.party) m (LibsignalSpqrV1.coinBytes rs) g.session with
    ⟨err | msg, s'⟩ <;> rw [henc] at hmod
  · cases err <;> simp at hmod
  · dsimp only at hmod
    rcases hrem : g.session.remoteIdentity with _ | k <;> rw [hrem] at hmod
    · simp at hmod
    · dsimp only at hmod
      by_cases hnt : (!st.trusts k) = true
      · simp [st, hnt] at hmod
      · simp only [Bool.not_eq_true] at hnt
        have hnt' : (!({ d with session := some (x, g) } : PqParty).trusts k) = false := hnt
        rw [hnt'] at hmod
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hmod
        rcases hmod with ⟨rfl, rfl⟩
        have hpk : some k = st.peerId := trusts_false_eq_peerId hpeer hnt
        let st1 : PqParty := { st with peerId := some k, session := some (x, { g with session := s' }) }
        have hst' : st1 = { d with session := some (x, { g with session := s' }) } := by
          dsimp only [st1]; rw [hpk]
        have hlr' : lastResortUses st1 < 2 ^ 25 := by
          change lastResortUses d < 2 ^ 25
          omega
        have hwf' := (wfPq_step_r3 hwf hstep hlr').1
        exact ⟨rfl, hstep, { g with session := s' }, rfl, hst', hwf'⟩

theorem cliPqSend_dir_eq_proj {S : SignalPqxdh.Setup} {l : Nat}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W)
    {bi : ModelDriverInstance S l}
    {sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64}
    {P : Party} {s : CliPartyState}
    (hInv : CliPartyDirInv W bi sigs P s)
    (m : List (BitVec 8)) (hm : m.length < 2 ^ 32) (rs : BitVec 512) :
    (Dir.cliPqSend run s m rs).1.bin =
      (cliPqSend run W (cliPqDirOf bi sigs s.bin) s.bin m rs).1 ∧
    (Dir.cliPqSend run s m rs).2 =
      (cliPqSend run W (cliPqDirOf bi sigs s.bin) s.bin m rs).2 ∧
    CliPartyDirInv W bi sigs P (Dir.cliPqSend run s m rs).1 := by
  have hraw : cliPqDirRaw = cliPqDirRawSpec := rfl
  cases P with
  | A =>
    rcases hInv with ⟨x, g, hwf, hp, hbytes, hpaths, hdir⟩
    set st : PqParty := { cliPqDirA bi with session := some (x, g) }
    have hraw_eq : cliPqDirRaw W (cliPqDirOf bi sigs s.bin) s.bin.bytes = encodeDir W st := by
      simp only [cliPqDirOf, hp, hbytes, hraw]
      exact cliPqDirRawSpec_encodeRecordX_eq_encodeDir W (cliPqDirA bi) x g
    have hinp_dir : cliPqDirInputs s.dir (.send (partyAddress s.bin.party.other)) []
        (LibsignalSpqrV1.coinBytes rs) m = pqSendInputs W st m (coinBytesVec64 rs) := by
      simp [cliPqDirInputs, pqSendInputs, pqInputs, hdir, hp, st, cliPqDirA, coinBytesVec64_toList]
    have hinp_proj : cliPqInputs W (cliPqDirOf bi sigs s.bin) s.bin.bytes
        (.send (partyAddress s.bin.party.other)) [] (LibsignalSpqrV1.coinBytes rs) m =
        pqSendInputs W st m (coinBytesVec64 rs) := by
      simp [cliPqInputs, pqSendInputs, pqInputs, hraw_eq, hp, st, cliPqDirA, coinBytesVec64_toList]
    have hpaths_st : s.paths = cliPqPartyPathsOf st := hpaths
    have hrun := (hCli st hwf).2.1 m (coinBytesVec64 rs) hm
    rw [coinBytesVec64_toList] at hrun
    by_cases hm_sc : m.length > stdinCapBytes
    · simp only [hm_sc, ↓reduceIte] at hrun
      unfold Dir.cliPqSend cliPqSend cliPqSendInp
      rw [hinp_dir, hinp_proj, hrun]
      exact ⟨rfl, rfl, ⟨x, g, hwf, hp, hbytes, hpaths, hdir⟩⟩
    · by_cases hm_pc : m.length > maxPlaintextBytes
      · simp only [hm_sc, hm_pc, ↓reduceIte] at hrun
        unfold Dir.cliPqSend cliPqSend cliPqSendInp
        rw [hinp_dir, hinp_proj, hrun]
        exact ⟨rfl, rfl, ⟨x, g, hwf, hp, hbytes, hpaths, hdir⟩⟩
      · simp only [hm_sc, hm_pc, ↓reduceIte] at hrun
        obtain ⟨ha_dir, ha_proj⟩ := dirCliPqAfter_pqObserve_eq (pqDirIdsNodup_of_wfPq hwf) .A
          (pqSendInputs W st m (coinBytesVec64 rs)) (pqSendModel W st m (LibsignalSpqrV1.coinBytes rs))
          (fun st' out hm' =>
            let ⟨hp', hs', g', hsess', _, _⟩ :=
              pqSendModel_step_session (X := X) hwf (peer := bhIdKeyOf bi.idBBytes) rfl
                (by simp [cliPqDirA, lastResortUses]) m hm rs hm'
            ⟨hp', hs', x, g', hsess'⟩)
        unfold Dir.cliPqSend cliPqSend cliPqSendInp
        rw [hinp_dir, hinp_proj, hp, hpaths_st, hrun, ha_dir, ha_proj]
        rcases hm' : pqSendModel W st m (LibsignalSpqrV1.coinBytes rs) with _ | (_ | ⟨st', out⟩)
        · exact ⟨rfl, rfl, ⟨x, g, hwf, hp, hbytes, hpaths, hdir⟩⟩
        · exact ⟨rfl, rfl, ⟨x, g, hwf, hp, hbytes, hpaths, hdir⟩⟩
        · obtain ⟨_, _, g', hsess', hst', hwf'⟩ :=
            pqSendModel_step_session (X := X) hwf (peer := bhIdKeyOf bi.idBBytes) rfl
              (by simp [cliPqDirA, lastResortUses]) m hm rs hm'
          dsimp only [Option.join, Option.bind, id, Option.map]
          rw [hsess']
          dsimp only
          exact ⟨rfl, rfl, ⟨x, g', hst' ▸ hwf', rfl, rfl, hpaths_st.symm.trans hpaths, by rw [hst']⟩⟩
  | B =>
    rcases hInv with rfl | ⟨x, g, hwf, habk, hp, hbytes, hpaths, hdir⟩
    · set d0 := cliPqxdhDirBobBeforeAccept bi sigs
      have hwf0 := wfPq_cliPqDirB0_ret W bi sigs
      have hraw_eq : cliPqDirRaw W (cliPqDirOf bi sigs (cliPartyStateB0 W bi sigs).bin)
          (cliPartyStateB0 W bi sigs).bin.bytes = encodeDir W d0 := by
        simp only [cliPqDirOf, cliPartyStateB0, List.isEmpty_nil, ↓reduceIte, hraw]
        exact cliPqDirRawSpec_nil_eq_encodeDir W d0
      have hinp_dir : cliPqDirInputs (cliPartyStateB0 W bi sigs).dir
          (.send (partyAddress (cliPartyStateB0 W bi sigs).bin.party.other)) []
          (LibsignalSpqrV1.coinBytes rs) m = pqSendInputs W d0 m (coinBytesVec64 rs) := by
        simp [cliPqDirInputs, pqSendInputs, pqInputs, cliPartyStateB0, d0,
          cliPqxdhDirBobBeforeAccept, coinBytesVec64_toList]
      have hinp_proj : cliPqInputs W (cliPqDirOf bi sigs (cliPartyStateB0 W bi sigs).bin)
          (cliPartyStateB0 W bi sigs).bin.bytes
          (.send (partyAddress (cliPartyStateB0 W bi sigs).bin.party.other)) []
          (LibsignalSpqrV1.coinBytes rs) m = pqSendInputs W d0 m (coinBytesVec64 rs) := by
        unfold cliPqInputs
        rw [hraw_eq]
        simp [pqSendInputs, pqInputs, cliPartyStateB0, d0,
          cliPqxdhDirBobBeforeAccept, coinBytesVec64_toList]
      have hrun := (hCli d0 hwf0).2.1 m (coinBytesVec64 rs) hm
      rw [coinBytesVec64_toList] at hrun
      by_cases hm_sc : m.length > stdinCapBytes
      · simp only [hm_sc, ↓reduceIte] at hrun
        unfold Dir.cliPqSend cliPqSend cliPqSendInp
        rw [hinp_dir, hinp_proj, hrun]
        exact ⟨rfl, rfl, Or.inl rfl⟩
      · by_cases hm_pc : m.length > maxPlaintextBytes
        · simp only [hm_sc, hm_pc, ↓reduceIte] at hrun
          unfold Dir.cliPqSend cliPqSend cliPqSendInp
          rw [hinp_dir, hinp_proj, hrun]
          exact ⟨rfl, rfl, Or.inl rfl⟩
        · simp only [hm_sc, hm_pc, ↓reduceIte] at hrun
          have hmod : pqSendModel W d0 m (LibsignalSpqrV1.coinBytes rs) = some none := rfl
          unfold Dir.cliPqSend cliPqSend cliPqSendInp
          rw [hinp_dir, hinp_proj, hrun, hmod]
          exact ⟨rfl, rfl, Or.inl rfl⟩
    · obtain ⟨hp1, _, hpeer1, _, hlr1, hpaths1⟩ := cliPqDirB1_props_ret bi sigs
      set d1 := cliPqxdhDirBobAfterAccept bi sigs
      set st : PqParty := { d1 with session := some (x, g) }
      have hraw_eq : cliPqDirRaw W (cliPqDirOf bi sigs s.bin) s.bin.bytes = encodeDir W st := by
        simp only [cliPqDirOf, hp, hbytes, encodeRecordX_isEmpty_eq_false,
          Bool.false_eq_true, ↓reduceIte, hraw]
        exact cliPqDirRawSpec_encodeRecordX_eq_encodeDir W d1 x g
      have hstP : st.party = .B := hp1
      have hinp_dir : cliPqDirInputs s.dir (.send (partyAddress s.bin.party.other)) []
          (LibsignalSpqrV1.coinBytes rs) m = pqSendInputs W st m (coinBytesVec64 rs) := by
        simp [cliPqDirInputs, pqSendInputs, pqInputs, hdir, hp, hstP, coinBytesVec64_toList]
      have hinp_proj : cliPqInputs W (cliPqDirOf bi sigs s.bin) s.bin.bytes
          (.send (partyAddress s.bin.party.other)) [] (LibsignalSpqrV1.coinBytes rs) m =
          pqSendInputs W st m (coinBytesVec64 rs) := by
        simp [cliPqInputs, pqSendInputs, pqInputs, hraw_eq, hp, hstP, coinBytesVec64_toList]
      have hpaths_st : s.paths = cliPqPartyPathsOf st := by
        have hps : cliPqPartyPathsOf st = cliPqPartyPathsOf d1 := rfl
        rw [hps, hpaths1, hpaths]
      have hrun := (hCli st hwf).2.1 m (coinBytesVec64 rs) hm
      rw [coinBytesVec64_toList] at hrun
      by_cases hm_sc : m.length > stdinCapBytes
      · simp only [hm_sc, ↓reduceIte] at hrun
        unfold Dir.cliPqSend cliPqSend cliPqSendInp
        rw [hinp_dir, hinp_proj, hrun]
        exact ⟨rfl, rfl, Or.inr ⟨x, g, hwf, habk, hp, hbytes, hpaths, hdir⟩⟩
      · by_cases hm_pc : m.length > maxPlaintextBytes
        · simp only [hm_sc, hm_pc, ↓reduceIte] at hrun
          unfold Dir.cliPqSend cliPqSend cliPqSendInp
          rw [hinp_dir, hinp_proj, hrun]
          exact ⟨rfl, rfl, Or.inr ⟨x, g, hwf, habk, hp, hbytes, hpaths, hdir⟩⟩
        · simp only [hm_sc, hm_pc, ↓reduceIte] at hrun
          obtain ⟨ha_dir, ha_proj⟩ := dirCliPqAfter_pqObserve_eq (pqDirIdsNodup_of_wfPq hwf) .B
            (pqSendInputs W st m (coinBytesVec64 rs)) (pqSendModel W st m (LibsignalSpqrV1.coinBytes rs))
            (fun st' out hm' =>
              let ⟨hp', hs', g', hsess', _, _⟩ :=
                pqSendModel_step_session (X := X) hwf hpeer1 hlr1 m hm rs hm'
              ⟨hp'.trans hp1, hs', x, g', hsess'⟩)
          unfold Dir.cliPqSend cliPqSend cliPqSendInp
          rw [hinp_dir, hinp_proj, hp, hpaths_st, hrun, ha_dir, ha_proj]
          rcases hm' : pqSendModel W st m (LibsignalSpqrV1.coinBytes rs) with _ | (_ | ⟨st', out⟩)
          · exact ⟨rfl, rfl, Or.inr ⟨x, g, hwf, habk, hp, hbytes, hpaths, hdir⟩⟩
          · exact ⟨rfl, rfl, Or.inr ⟨x, g, hwf, habk, hp, hbytes, hpaths, hdir⟩⟩
          · obtain ⟨_, _, g', hsess', hst', hwf'⟩ :=
              pqSendModel_step_session (X := X) hwf hpeer1 hlr1 m hm rs hm'
            dsimp only [Option.join, Option.bind, id, Option.map]
            rw [hsess']
            dsimp only
            exact ⟨rfl, rfl, Or.inr ⟨x, g', hst' ▸ hwf', habk, rfl, rfl,
              hpaths_st.symm.trans hpaths, by rw [hst']⟩⟩

/-! ### `cliPqReceive` step bridges -/

private theorem cliPqRecv_of_after_eq {S : SignalPqxdh.Setup} {l : Nat}
    {run : CliRun} {W : PEParams}
    {bi : ModelDriverInstance S l}
    {sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64}
    {P : Party} {s : CliPartyState} {d : PqParty}
    (c : List (BitVec 8)) (rc : BitVec 256)
    (ha_eq :
      (Dir.cliPqAfter s.bin.party s.paths (run (cliPqDirInputs s.dir
          (.recv (partyAddress s.bin.party.other)) [] (HMAC.keyToBytes32 rc) c))).map
        (fun (_, recB, pt) => (recB, pt)) =
      cliPqAfter s.bin.party (run (cliPqInputs W d s.bin.bytes
        (.recv (partyAddress s.bin.party.other)) [] (HMAC.keyToBytes32 rc) c)))
    (ha_inv : ∀ dir' recB pt ep',
      Dir.cliPqAfter s.bin.party s.paths (run (cliPqDirInputs s.dir
          (.recv (partyAddress s.bin.party.other)) [] (HMAC.keyToBytes32 rc) c)) =
        some (dir', recB, pt) →
      CliPartyDirInv W bi sigs P
        { bin := { party := s.bin.party, bytes := recB, epochs := ep' }
          paths := s.paths, dir := dir' }) :
    (Dir.cliPqRecv run s c rc).map (fun x => (x.1.bin, x.2.1, x.2.2.1, x.2.2.2)) =
      cliPqRecv run W d s.bin c rc ∧
    ∀ x, Dir.cliPqRecv run s c rc = some x → CliPartyDirInv W bi sigs P x.1 := by
  unfold Dir.cliPqRecv cliPqRecv
  rw [← ha_eq]
  rcases ha : Dir.cliPqAfter s.bin.party s.paths (run (cliPqDirInputs s.dir
      (.recv (partyAddress s.bin.party.other)) [] (HMAC.keyToBytes32 rc) c)) with
    _ | ⟨dir', recB, pt⟩
  · exact ⟨rfl, fun _ h => by cases h⟩
  · simp only [Option.map_some]
    cases (bhWireInnerBytes c).map (SignalMessage.tryFrom protoSignalCodec) with
    | none =>
      refine ⟨rfl, ?_⟩
      rintro _ ⟨rfl⟩
      exact ha_inv dir' recB pt s.bin.epochs ha
    | some res =>
      cases res with
      | error _ =>
        refine ⟨rfl, ?_⟩
        rintro _ ⟨rfl⟩
        exact ha_inv dir' recB pt s.bin.epochs ha
      | ok msg =>
        refine ⟨rfl, ?_⟩
        rintro _ ⟨rfl⟩
        exact ha_inv dir' recB pt (s.bin.epochs.recv msg.senderRatchetKey).2 ha

private theorem pqRecvWhisperModel_step_session {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {d : PqParty} {peer : IdentityKey} {x : RecordExtras} {g : GhostState Bytes}
    (hwf : PqxdhPartyInSpecDomain W { d with session := some (x, g) })
    (hpeer : d.peerId = some peer) (hlr : lastResortUses d ≤ 1)
    (body : List (BitVec 8)) (hbody : body.length < 2 ^ 32) (rc : BitVec 256)
    {st' : PqParty} {out : List (BitVec 8)}
    (hmod : pqRecvWhisperModel W { d with session := some (x, g) } body rc =
      some (some (st', out))) :
    st'.party = d.party ∧
    PqStep X W { d with session := some (x, g) } st' ∧
    ∃ g', st'.session = some (x, g') ∧
      st' = { d with session := some (x, g') } ∧
      PqxdhPartyInSpecDomain W st' := by
  set st : PqParty := { d with session := some (x, g) }
  have hstep : PqStep X W st st' := PqStep.recvWhisper body rc st' out hbody hmod
  unfold pqRecvWhisperModel pqxdhSessionDecryptModel at hmod
  dsimp only [st] at hmod
  rcases htry : SignalMessage.tryFrom protoSignalCodec body with _ | msg <;> rw [htry] at hmod
  · simp at hmod
  · dsimp only at hmod
    rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session with
      ⟨err | pt, s'⟩ <;> rw [hdec] at hmod
    · cases err <;> simp at hmod
    · dsimp only at hmod
      rcases hrem : s'.remoteIdentity with _ | k <;> rw [hrem] at hmod
      · simp at hmod
      · dsimp only at hmod
        by_cases hnt : (!st.trusts k) = true
        · simp [st, hnt] at hmod
        · simp only [Bool.not_eq_true] at hnt
          have hnt' : (!({ d with session := some (x, g) } : PqParty).trusts k) = false := hnt
          rw [hnt'] at hmod
          simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hmod
          rcases hmod with ⟨rfl, rfl⟩
          have hpk : some k = st.peerId := trusts_false_eq_peerId hpeer hnt
          let st1 : PqParty := { st with peerId := some k, session := some (x, { g with session := s' }) }
          have hst' : st1 = { d with session := some (x, { g with session := s' }) } := by
            dsimp only [st1]; rw [hpk]
          have hlr' : lastResortUses st1 < 2 ^ 25 := by
            change lastResortUses d < 2 ^ 25
            omega
          have hwf' := (wfPq_step_r3 hwf hstep hlr').1
          exact ⟨rfl, hstep, { g with session := s' }, rfl, hst', hwf'⟩

private theorem pqRecvPrekeyModel_step_b0 {S : SignalPqxdh.Setup} {l : Nat}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (bi : ModelDriverInstance S l)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (m : PreKeyMessageFields) (hm_eq : m = bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner)
    (hinner : m.inner.length + 2048 < 2 ^ 32) (rc : BitVec 256)
    {st' : PqParty} {out : List (BitVec 8)}
    (hmod : pqRecvPrekeyModel X W (cliPqxdhDirBobBeforeAccept bi sigs) m rc =
      some (some (st', out))) :
    st'.party = .B ∧
    PqStep X W (cliPqxdhDirBobBeforeAccept bi sigs) st' ∧
    ∃ x' g', st'.session = some (x', g') ∧
      st' = { cliPqxdhDirBobAfterAccept bi sigs with session := some (x', g') } ∧
      x'.aliceBaseKey = djbKey (u8Vec 32 bi.hdr.ekAPk) ∧
      PqxdhPartyInSpecDomain W st' := by
  set d0 := cliPqxdhDirBobBeforeAccept bi sigs
  set d1 := cliPqxdhDirBobAfterAccept bi sigs
  have hwf0 := wfPq_cliPqDirB0_ret W bi sigs
  obtain ⟨hp1, _, hpeer1, _, hlr1, _⟩ := cliPqDirB1_props_ret bi sigs
  have hstep : PqStep X W d0 st' :=
    PqStep.recvPrekey m rc st' out hinner (by simp [d0, cliPqxdhDirBobBeforeAccept]) hmod
  unfold pqRecvPrekeyModel at hmod
  rcases htry : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner <;> rw [htry] at hmod
  · simp at hmod
  · dsimp only at hmod
    by_cases hnt : (!d0.trusts ⟨⟨m.idPub⟩⟩) = true
    · simp [hnt] at hmod
    · simp only [Bool.not_eq_true] at hnt
      rw [hnt] at hmod
      simp only [Bool.false_eq_true, ↓reduceIte] at hmod
      have hs0 : d0.session = none := rfl
      rw [hs0] at hmod
      dsimp only at hmod
      rcases hpk : preKeysNamedBy d0 m with _ | k <;> rw [hpk] at hmod
      · simp at hmod
      · dsimp only at hmod
        rcases hrec : recvPrekeyState X W d0.party d0.me k m rc with _ | (_ | ⟨x', g', pt⟩) <;>
          rw [hrec] at hmod
        · simp at hmod
        · simp at hmod
        · dsimp only at hmod
          rcases hmk : markKyberUsed d0 m with _ | st1 <;> rw [hmk] at hmod
          · simp at hmod
          · simp only [Option.some.injEq, Prod.mk.injEq] at hmod
            rcases hmod with ⟨rfl, rfl⟩
            have hd1_eq : removeOpk st1 m = d1 := by
              set m0 := bhExpectedPreKeyMsg bi.meA.regId bi.hdr []
              have hmk0 : markKyberUsed d0 m0 = markKyberUsed d0 m := by rw [hm_eq]; rfl
              have hrm0 : removeOpk st1 m = removeOpk st1 m0 := by rw [hm_eq]; rfl
              unfold d1 cliPqxdhDirBobAfterAccept
              change removeOpk st1 m = removeOpk ((markKyberUsed d0 m0).getD d0) m0
              rw [hmk0, hmk, hrm0]; rfl
            have hid_eq : some (⟨⟨m.idPub⟩⟩ : IdentityKey) = d1.peerId := by
              rw [hpeer1, hm_eq]; rfl
            let st2 : PqParty := { removeOpk st1 m with peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', g') }
            have hst' : st2 = { d1 with session := some (x', g') } := by
              dsimp only [st2]; rw [hd1_eq, hid_eq]
            have habk : x'.aliceBaseKey = djbKey (u8Vec 32 bi.hdr.ekAPk) := by
              unfold recvPrekeyState at hrec
              rw [htry] at hrec
              dsimp only at hrec
              split_ifs at hrec
              · simp at hrec
              · rcases hak : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W d0.me k m) with
                  _ | dk <;> rw [hak] at hrec
                · simp at hrec
                · dsimp only at hrec
                  split at hrec
                  · simp only [Option.some.injEq, Prod.mk.injEq] at hrec
                    rcases hrec with ⟨rfl, _, _⟩
                    rw [hm_eq]; rfl
                  · cases hrec
                  · simp at hrec
            have hlr' : lastResortUses st2 < 2 ^ 25 := by
              rw [hst']
              change lastResortUses (cliPqxdhDirBobAfterAccept bi sigs) < 2 ^ 25
              omega
            have hwf' := (wfPq_step_r3 hwf0 hstep hlr').1
            have hp2 : st2.party = .B := by
              have h := congrArg PqParty.party hst'
              simpa [d1, hp1] using h
            exact ⟨hp2, hstep, x', g', rfl, hst', habk, hwf'⟩

private theorem pqRecvPrekeyModel_step_b1 {S : SignalPqxdh.Setup} {l : Nat}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (bi : ModelDriverInstance S l)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    {x : RecordExtras} {g : GhostState Bytes}
    (hwf : PqxdhPartyInSpecDomain W { cliPqxdhDirBobAfterAccept bi sigs with session := some (x, g) })
    (habk : x.aliceBaseKey = djbKey (u8Vec 32 bi.hdr.ekAPk))
    (m : PreKeyMessageFields) (hbk : m.baseKey = u8Vec 32 bi.hdr.ekAPk)
    (hinner : m.inner.length + 2048 < 2 ^ 32) (rc : BitVec 256) :
    (∀ x0 g0, ({ cliPqxdhDirBobAfterAccept bi sigs with session := some (x, g) } : PqParty).session =
        some (x0, g0) → PqSessionMatches x0 g0 m) ∧
    (∀ st' out,
      pqRecvPrekeyModel X W { cliPqxdhDirBobAfterAccept bi sigs with session := some (x, g) } m rc =
        some (some (st', out)) →
      st'.party = .B ∧
      PqStep X W { cliPqxdhDirBobAfterAccept bi sigs with session := some (x, g) } st' ∧
      ∃ g', st'.session = some (x, g') ∧
        st' = { cliPqxdhDirBobAfterAccept bi sigs with session := some (x, g') } ∧
        PqxdhPartyInSpecDomain W st') := by
  set d1 := cliPqxdhDirBobAfterAccept bi sigs
  set st : PqParty := { d1 with session := some (x, g) }
  obtain ⟨hp1, _, hpeer1, _, hlr1, _⟩ := cliPqDirB1_props_ret bi sigs
  have hmatch : ∀ x0 g0, st.session = some (x0, g0) → PqSessionMatches x0 g0 m := by
    rintro x0 g0 ⟨rfl, rfl⟩
    obtain ⟨⟨g₀, hR, _, hgs⟩, _, _⟩ := hwf.1 x g rfl
    exact ⟨by rw [habk, hbk], by rw [← hgs, (reachPq_invCli hR).sessionVersion_eq]⟩
  refine ⟨hmatch, fun st' out hmod => ?_⟩
  have hstep : PqStep X W st st' := PqStep.recvPrekey m rc st' out hinner hmatch hmod
  unfold pqRecvPrekeyModel at hmod
  rcases htry : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner <;> rw [htry] at hmod
  · simp at hmod
  · dsimp only at hmod
    by_cases hnt : (!st.trusts ⟨⟨m.idPub⟩⟩) = true
    · simp [st, hnt] at hmod
    · simp only [Bool.not_eq_true] at hnt
      have hnt' : (!({ d1 with session := some (x, g) } : PqParty).trusts ⟨⟨m.idPub⟩⟩) = false := hnt
      rw [hnt'] at hmod
      simp only [Bool.false_eq_true, ↓reduceIte] at hmod
      dsimp only [st] at hmod
      simp only [hmatch x g rfl, ↓reduceIte] at hmod
      split_ifs at hmod
      · simp at hmod
      · rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs g.party) inner .preKey rc g.session with
          ⟨err | pt, s'⟩ <;> rw [hdec] at hmod
        · cases err <;> simp at hmod
        · simp only [Option.some.injEq, Prod.mk.injEq] at hmod
          rcases hmod with ⟨rfl, rfl⟩
          have hpk : some (⟨⟨m.idPub⟩⟩ : IdentityKey) = st.peerId :=
            trusts_false_eq_peerId hpeer1 hnt
          let st1 : PqParty := { d1 with peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, { g with session := s' }) }
          have hst' : st1 = { d1 with session := some (x, { g with session := s' }) } := by
            dsimp only [st1]; rw [hpk]
          have hlr' : lastResortUses st1 < 2 ^ 25 := by
            change lastResortUses (cliPqxdhDirBobAfterAccept bi sigs) < 2 ^ 25
            omega
          have hwf' := (wfPq_step_r3 hwf hstep hlr').1
          exact ⟨hp1, hstep, { g with session := s' }, rfl, hst', hwf'⟩

theorem cliPqReceive_dir_eq_proj {S : SignalPqxdh.Setup} {l l' : Nat}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W)
    {bi : ModelDriverInstance S l'}
    {sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64}
    {P : Party} {s : CliPartyState}
    (hInv : CliPartyDirInv W bi sigs P s)
    (c : List (BitVec 8)) (rc : BitVec 256) :
    (Dir.cliPqReceive run l bi s c rc).map (fun x => (x.1.bin, x.2.1, x.2.2.1, x.2.2.2)) =
      cliPqReceive run W l bi sigs s.bin c rc ∧
    ∀ x, Dir.cliPqReceive run l bi s c rc = some x → CliPartyDirInv W bi sigs P x.1 := by
  have hraw : cliPqDirRaw = cliPqDirRawSpec := rfl
  have wrapCall :
      ((Dir.cliPqRecv run s c rc).map (fun x => (x.1.bin, x.2.1, x.2.2.1, x.2.2.2)) =
        cliPqRecv run W (cliPqDirOf bi sigs s.bin) s.bin c rc ∧
       ∀ x, Dir.cliPqRecv run s c rc = some x → CliPartyDirInv W bi sigs P x.1) →
      ((Dir.cliPqRecv run s c rc).map
          (fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain l x.2.2.2))).map
        (fun x => (x.1.bin, x.2.1, x.2.2.1, x.2.2.2)) =
        (cliPqRecv run W (cliPqDirOf bi sigs s.bin) s.bin c rc).map
          (fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain l x.2.2.2)) ∧
      ∀ y, (Dir.cliPqRecv run s c rc).map
          (fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain l x.2.2.2)) = some y →
        CliPartyDirInv W bi sigs P y.1 := by
    rintro ⟨heq, hinv⟩
    rw [← heq]
    rcases hr : Dir.cliPqRecv run s c rc with _ | x
    · exact ⟨rfl, fun _ h => by cases h⟩
    · refine ⟨rfl, ?_⟩
      rintro _ ⟨rfl⟩
      exact hinv x hr
  unfold Dir.cliPqReceive cliPqReceive
  dsimp only
  by_cases hlen : (!cliPqLenOk c) = true
  · simp [hlen]
  · simp only [Bool.not_eq_true] at hlen
    rw [hlen]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hlen_ok : cliPqLenOk c = true := by simpa using hlen
    have hclen : c.length < 2 ^ 32 := by
      unfold cliPqLenOk shortCiphertext at hlen_ok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hlen_ok
      exact hlen_ok.1
    cases P with
    | A =>
      rcases hInv with ⟨x, g, hwf, hp, hbytes, hpaths, hdir⟩
      rw [hp]
      dsimp only
      by_cases hpk : (c.head? == some wirePrekey) = true
      · simp [hpk]
      · simp only [Bool.not_eq_true] at hpk
        rw [hpk]
        simp only [Bool.false_eq_true, ↓reduceIte]
        apply wrapCall
        set st : PqParty := { cliPqDirA bi with session := some (x, g) }
        have hraw_eq : cliPqDirRaw W (cliPqDirOf bi sigs s.bin) s.bin.bytes = encodeDir W st := by
          simp only [cliPqDirOf, hp, hbytes, hraw]
          exact cliPqDirRawSpec_encodeRecordX_eq_encodeDir W (cliPqDirA bi) x g
        have hinp_dir : cliPqDirInputs s.dir (.recv (partyAddress s.bin.party.other)) []
            (HMAC.keyToBytes32 rc) c = pqRecvInputs W st c rc := by
          simp [cliPqDirInputs, pqRecvInputs, pqInputs, hdir, hp, st, cliPqDirA]
        have hinp_proj : cliPqInputs W (cliPqDirOf bi sigs s.bin) s.bin.bytes
            (.recv (partyAddress s.bin.party.other)) [] (HMAC.keyToBytes32 rc) c =
            pqRecvInputs W st c rc := by
          simp [cliPqInputs, pqRecvInputs, pqInputs, hraw_eq, hp, st, cliPqDirA]
        apply cliPqRecv_of_after_eq c rc
        · by_cases hwh : c.head? = some wireWhisper
          · rcases c with _ | ⟨t, body⟩
            · cases hwh
            · simp only [List.head?_cons, Option.some.injEq] at hwh; subst hwh
              have hbody : body.length < 2 ^ 32 := by simp at hclen; omega
              have hrun := (hCli st hwf).2.2.1 body rc hbody
              by_cases hc_cap : (wireWhisper :: body).length > stdinCapBytes
              · simp only [hc_cap, ↓reduceIte] at hrun
                rw [hinp_dir, hinp_proj, hrun]
                rfl
              · simp only [hc_cap, ↓reduceIte] at hrun
                obtain ⟨ha_dir, ha_proj⟩ := dirCliPqAfter_pqObserve_eq (pqDirIdsNodup_of_wfPq hwf) .A
                  (pqRecvInputs W st (wireWhisper :: body) rc) (pqRecvWhisperModel W st body rc)
                  (fun st' out hm' =>
                    let ⟨hp', hs', g', hsess', _, _⟩ :=
                      pqRecvWhisperModel_step_session (X := X) hwf (peer := bhIdKeyOf bi.idBBytes) rfl
                        (by simp [cliPqDirA, lastResortUses]) body hbody rc hm'
                    ⟨hp', hs', x, g', hsess'⟩)
                rw [hinp_dir, hinp_proj, hp, show s.paths = cliPqPartyPathsOf st from hpaths,
                  hrun, ha_dir, ha_proj]
                rcases pqRecvWhisperModel W st body rc with _ | (_ | ⟨st', out⟩) <;> rfl
          · have hnp : c.head? ≠ some wirePrekey := fun hc => by simp [hc] at hpk
            have hrun := (hCli st hwf).2.2.2.2 c rc hclen hwh hnp
            by_cases hc_cap : c.length > stdinCapBytes <;> {
              simp only [hc_cap, ↓reduceIte] at hrun
              rw [hinp_dir, hinp_proj, hrun]
              rfl }
        · intro dir' recB pt ep' ha
          by_cases hwh : c.head? = some wireWhisper
          · rcases c with _ | ⟨t, body⟩
            · cases hwh
            · simp only [List.head?_cons, Option.some.injEq] at hwh; subst hwh
              have hbody : body.length < 2 ^ 32 := by simp at hclen; omega
              have hrun := (hCli st hwf).2.2.1 body rc hbody
              by_cases hc_cap : (wireWhisper :: body).length > stdinCapBytes
              · simp only [hc_cap, ↓reduceIte] at hrun
                rw [hinp_dir, hrun] at ha
                cases ha
              · simp only [hc_cap, ↓reduceIte] at hrun
                obtain ⟨ha_dir, _⟩ := dirCliPqAfter_pqObserve_eq (pqDirIdsNodup_of_wfPq hwf) .A
                  (pqRecvInputs W st (wireWhisper :: body) rc) (pqRecvWhisperModel W st body rc)
                  (fun st' out hm' =>
                    let ⟨hp', hs', g', hsess', _, _⟩ :=
                      pqRecvWhisperModel_step_session (X := X) hwf (peer := bhIdKeyOf bi.idBBytes) rfl
                        (by simp [cliPqDirA, lastResortUses]) body hbody rc hm'
                    ⟨hp', hs', x, g', hsess'⟩)
                rw [hinp_dir, hp, show s.paths = cliPqPartyPathsOf st from hpaths, hrun, ha_dir] at ha
                rcases hm' : pqRecvWhisperModel W st body rc with _ | (_ | ⟨st', out⟩) <;>
                  rw [hm'] at ha
                · cases ha
                · cases ha
                · obtain ⟨_, _, g', hsess', hst', hwf'⟩ :=
                    pqRecvWhisperModel_step_session (X := X) hwf (peer := bhIdKeyOf bi.idBBytes) rfl
                      (by simp [cliPqDirA, lastResortUses]) body hbody rc hm'
                  simp only [Option.join_some, Option.map_some, Option.some.injEq, Prod.mk.injEq,
                    hsess'] at ha
                  rcases ha with ⟨rfl, rfl, rfl⟩
                  exact ⟨x, g', hst' ▸ hwf', hp, rfl, hpaths, by rw [hst']⟩
          · have hnp : c.head? ≠ some wirePrekey := fun hc => by simp [hc] at hpk
            have hrun := (hCli st hwf).2.2.2.2 c rc hclen hwh hnp
            by_cases hc_cap : c.length > stdinCapBytes <;> {
              simp only [hc_cap, ↓reduceIte] at hrun
              rw [hinp_dir, hrun] at ha
              cases ha }
    | B =>
      have hsB : s.bin.party = .B := by
        rcases hInv with rfl | ⟨_, _, _, _, hp, _, _, _⟩
        · rfl
        · exact hp
      rw [hsB]
      dsimp only
      rcases hdec : bhDecodePreKeyMsgE c with _ | m
      ·
        by_cases hemp : (s.bin.bytes.isEmpty || s.bin.epochs.epoch == 0) = true
        · simp [hemp]
        · simp only [Bool.not_eq_true] at hemp
          rw [hemp]
          simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hwh : (c.head? == some wireWhisper) = true
          · rw [hwh]
            simp only [↓reduceIte]
            apply wrapCall
            rcases hInv with rfl | ⟨x, g, hwf, habk, hp, hbytes, hpaths, hdir⟩
            · simp [cliPartyStateB0] at hemp
            · have hwh_eq : c.head? = some wireWhisper := beq_iff_eq.mp hwh
              rcases c with _ | ⟨t, body⟩
              · cases hwh_eq
              · simp only [List.head?_cons, Option.some.injEq] at hwh_eq; subst hwh_eq
                have hbody : body.length < 2 ^ 32 := by simp at hclen; omega
                obtain ⟨hp1, _, hpeer1, _, hlr1, hpaths1⟩ := cliPqDirB1_props_ret bi sigs
                set d1 := cliPqxdhDirBobAfterAccept bi sigs
                set st : PqParty := { d1 with session := some (x, g) }
                have hraw_eq : cliPqDirRaw W (cliPqDirOf bi sigs s.bin) s.bin.bytes = encodeDir W st := by
                  simp only [cliPqDirOf, hp, hbytes, encodeRecordX_isEmpty_eq_false,
                    Bool.false_eq_true, ↓reduceIte, hraw]
                  exact cliPqDirRawSpec_encodeRecordX_eq_encodeDir W d1 x g
                have hstP : st.party = .B := hp1
                have hinp_dir : cliPqDirInputs s.dir (.recv (partyAddress s.bin.party.other)) []
                    (HMAC.keyToBytes32 rc) (wireWhisper :: body) =
                    pqRecvInputs W st (wireWhisper :: body) rc := by
                  simp [cliPqDirInputs, pqRecvInputs, pqInputs, hdir, hp, hstP]
                have hinp_proj : cliPqInputs W (cliPqDirOf bi sigs s.bin) s.bin.bytes
                    (.recv (partyAddress s.bin.party.other)) [] (HMAC.keyToBytes32 rc)
                    (wireWhisper :: body) = pqRecvInputs W st (wireWhisper :: body) rc := by
                  simp [cliPqInputs, pqRecvInputs, pqInputs, hraw_eq, hp, hstP]
                have hpaths_st : s.paths = cliPqPartyPathsOf st := by
                  have hps : cliPqPartyPathsOf st = cliPqPartyPathsOf d1 := rfl
                  rw [hps, hpaths1, hpaths]
                have hrun := (hCli st hwf).2.2.1 body rc hbody
                by_cases hc_cap : (wireWhisper :: body).length > stdinCapBytes
                · simp only [hc_cap, ↓reduceIte] at hrun
                  apply cliPqRecv_of_after_eq (wireWhisper :: body) rc
                  · rw [hinp_dir, hinp_proj, hrun]; rfl
                  · intro dir' recB pt ep' ha; rw [hinp_dir, hrun] at ha; cases ha
                · simp only [hc_cap, ↓reduceIte] at hrun
                  obtain ⟨ha_dir, ha_proj⟩ := dirCliPqAfter_pqObserve_eq (pqDirIdsNodup_of_wfPq hwf) .B
                    (pqRecvInputs W st (wireWhisper :: body) rc) (pqRecvWhisperModel W st body rc)
                    (fun st' out hm' =>
                      let ⟨hp', hs', g', hsess', _, _⟩ :=
                        pqRecvWhisperModel_step_session (X := X) hwf hpeer1 hlr1 body hbody rc hm'
                      ⟨hp'.trans hp1, hs', x, g', hsess'⟩)
                  apply cliPqRecv_of_after_eq (wireWhisper :: body) rc
                  · rw [hinp_dir, hinp_proj, hp, hpaths_st, hrun, ha_dir, ha_proj]
                    rcases pqRecvWhisperModel W st body rc with _ | (_ | ⟨st', out⟩) <;> rfl
                  · intro dir' recB pt ep' ha
                    rw [hinp_dir, hp, hpaths_st, hrun, ha_dir] at ha
                    rcases hm' : pqRecvWhisperModel W st body rc with _ | (_ | ⟨st', out⟩) <;>
                      rw [hm'] at ha
                    · cases ha
                    · cases ha
                    · obtain ⟨_, _, g', hsess', hst', hwf'⟩ :=
                        pqRecvWhisperModel_step_session (X := X) hwf hpeer1 hlr1 body hbody rc hm'
                      simp only [Option.join_some, Option.map_some, Option.some.injEq, Prod.mk.injEq,
                        hsess'] at ha
                      rcases ha with ⟨rfl, rfl, rfl⟩
                      exact Or.inr ⟨x, g', hst' ▸ hwf', habk, hp, rfl, hpaths, by rw [hst']⟩
          · simp only [Bool.not_eq_true] at hwh
            simp [hwh]
      ·
        have hc_eq : c = wirePrekey :: m.bytes := (bhDecodePreKeyMsgE_eq_some_imp_ret hdec).1
        have hinner : m.inner.length + 2048 < 2 ^ 32 := by
          unfold cliPqLenOk at hlen_ok
          rw [hdec] at hlen_ok
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hlen_ok
          exact hlen_ok.2
        have hPrekeyCall :
            ((s.bin.bytes.isEmpty = true → m = bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner) ∧
             m.baseKey = u8Vec 32 bi.hdr.ekAPk) →
            ((Dir.cliPqRecv run s c rc).map
                (fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain l x.2.2.2))).map
              (fun x => (x.1.bin, x.2.1, x.2.2.1, x.2.2.2)) =
              (cliPqRecv run W (cliPqDirOf bi sigs s.bin) s.bin c rc).map
                (fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain l x.2.2.2)) ∧
            ∀ y, (Dir.cliPqRecv run s c rc).map
                (fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain l x.2.2.2)) = some y →
              CliPartyDirInv W bi sigs .B y.1 := by
          rintro ⟨hm_if_empty, hbk⟩
          apply wrapCall
          rcases hInv with rfl | ⟨x, g, hwf, habk, hp, hbytes, hpaths, hdir⟩
          ·
            have hm_eq : m = bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner := hm_if_empty rfl
            set d0 := cliPqxdhDirBobBeforeAccept bi sigs
            have hwf0 := wfPq_cliPqDirB0_ret W bi sigs
            have hraw_eq : cliPqDirRaw W (cliPqDirOf bi sigs (cliPartyStateB0 W bi sigs).bin)
                (cliPartyStateB0 W bi sigs).bin.bytes = encodeDir W d0 := by
              simp only [cliPqDirOf, cliPartyStateB0, List.isEmpty_nil, ↓reduceIte, hraw]
              exact cliPqDirRawSpec_nil_eq_encodeDir W d0
            have hinp_dir : cliPqDirInputs (cliPartyStateB0 W bi sigs).dir
                (.recv (partyAddress (cliPartyStateB0 W bi sigs).bin.party.other)) []
                (HMAC.keyToBytes32 rc) c = pqRecvInputs W d0 (wirePrekey :: m.bytes) rc := by
              simp [cliPqDirInputs, pqRecvInputs, pqInputs, cliPartyStateB0, d0,
                cliPqxdhDirBobBeforeAccept, hc_eq]
            have hinp_proj : cliPqInputs W (cliPqDirOf bi sigs (cliPartyStateB0 W bi sigs).bin)
                (cliPartyStateB0 W bi sigs).bin.bytes
                (.recv (partyAddress (cliPartyStateB0 W bi sigs).bin.party.other)) []
                (HMAC.keyToBytes32 rc) c = pqRecvInputs W d0 (wirePrekey :: m.bytes) rc := by
              unfold cliPqInputs
              rw [hraw_eq]
              simp [pqRecvInputs, pqInputs, cliPartyStateB0, d0,
                cliPqxdhDirBobBeforeAccept, hc_eq]
            have hrun := (hCli d0 hwf0).2.2.2.1 m rc hinner (by simp [d0, cliPqxdhDirBobBeforeAccept])
            by_cases hc_cap : (wirePrekey :: m.bytes).length > stdinCapBytes
            · simp only [hc_cap, ↓reduceIte] at hrun
              apply cliPqRecv_of_after_eq c rc
              · rw [hinp_dir, hinp_proj, hrun]; rfl
              · intro dir' recB pt ep' ha; rw [hinp_dir, hrun] at ha; cases ha
            · simp only [hc_cap, ↓reduceIte] at hrun
              obtain ⟨ha_dir, ha_proj⟩ := dirCliPqAfter_pqObserve_eq (pqDirIdsNodup_of_wfPq hwf0) .B
                (pqRecvInputs W d0 (wirePrekey :: m.bytes) rc) (pqRecvPrekeyModel X W d0 m rc)
                (fun st' out hm' =>
                  let ⟨hp', hs', x', g', hsess', _, _, _⟩ :=
                    pqRecvPrekeyModel_step_b0 bi sigs m hm_eq hinner rc hm'
                  ⟨hp', hs', x', g', hsess'⟩)
              apply cliPqRecv_of_after_eq c rc
              · rw [hinp_dir, hinp_proj, hrun]
                change (Dir.cliPqAfter .B (cliPqPartyPathsOf d0) _).map _ = cliPqAfter .B _
                rw [ha_dir, ha_proj]
                rcases pqRecvPrekeyModel X W d0 m rc with _ | (_ | ⟨st', out⟩) <;> rfl
              · intro dir' recB pt ep' ha
                rw [hinp_dir, hrun] at ha
                change Dir.cliPqAfter .B (cliPqPartyPathsOf d0) _ = _ at ha
                rw [ha_dir] at ha
                rcases hm' : pqRecvPrekeyModel X W d0 m rc with _ | (_ | ⟨st', out⟩) <;>
                  rw [hm'] at ha
                · cases ha
                · cases ha
                · obtain ⟨_, _, x', g', hsess', hst', habk', hwf'⟩ :=
                    pqRecvPrekeyModel_step_b0 bi sigs m hm_eq hinner rc hm'
                  simp only [Option.join_some, Option.map_some, Option.some.injEq, Prod.mk.injEq,
                    hsess'] at ha
                  rcases ha with ⟨rfl, rfl, rfl⟩
                  exact Or.inr ⟨x', g', hst' ▸ hwf', habk', rfl, rfl, rfl, by rw [hst']⟩
          ·
            obtain ⟨hp1, _, _, _, _, hpaths1⟩ := cliPqDirB1_props_ret bi sigs
            set d1 := cliPqxdhDirBobAfterAccept bi sigs
            set st : PqParty := { d1 with session := some (x, g) }
            obtain ⟨hmatch, hok1⟩ := pqRecvPrekeyModel_step_b1 (X := X) bi sigs hwf habk m hbk hinner rc
            have hraw_eq : cliPqDirRaw W (cliPqDirOf bi sigs s.bin) s.bin.bytes = encodeDir W st := by
              simp only [cliPqDirOf, hp, hbytes, encodeRecordX_isEmpty_eq_false,
                Bool.false_eq_true, ↓reduceIte, hraw]
              exact cliPqDirRawSpec_encodeRecordX_eq_encodeDir W d1 x g
            have hstP : st.party = .B := hp1
            have hinp_dir : cliPqDirInputs s.dir (.recv (partyAddress s.bin.party.other)) []
                (HMAC.keyToBytes32 rc) c = pqRecvInputs W st (wirePrekey :: m.bytes) rc := by
              simp [cliPqDirInputs, pqRecvInputs, pqInputs, hdir, hp, hstP, hc_eq]
            have hinp_proj : cliPqInputs W (cliPqDirOf bi sigs s.bin) s.bin.bytes
                (.recv (partyAddress s.bin.party.other)) [] (HMAC.keyToBytes32 rc) c =
                pqRecvInputs W st (wirePrekey :: m.bytes) rc := by
              simp [cliPqInputs, pqRecvInputs, pqInputs, hraw_eq, hp, hstP, hc_eq]
            have hpaths_st : s.paths = cliPqPartyPathsOf st := by
              have hps : cliPqPartyPathsOf st = cliPqPartyPathsOf d1 := rfl
              rw [hps, hpaths1, hpaths]
            have hrun := (hCli st hwf).2.2.2.1 m rc hinner hmatch
            by_cases hc_cap : (wirePrekey :: m.bytes).length > stdinCapBytes
            · simp only [hc_cap, ↓reduceIte] at hrun
              apply cliPqRecv_of_after_eq c rc
              · rw [hinp_dir, hinp_proj, hrun]; rfl
              · intro dir' recB pt ep' ha; rw [hinp_dir, hrun] at ha; cases ha
            · simp only [hc_cap, ↓reduceIte] at hrun
              obtain ⟨ha_dir, ha_proj⟩ := dirCliPqAfter_pqObserve_eq (pqDirIdsNodup_of_wfPq hwf) .B
                (pqRecvInputs W st (wirePrekey :: m.bytes) rc) (pqRecvPrekeyModel X W st m rc)
                (fun st' out hm' =>
                  let ⟨hp', hs', g', hsess', _, _⟩ := hok1 st' out hm'
                  ⟨hp', hs', x, g', hsess'⟩)
              apply cliPqRecv_of_after_eq c rc
              · rw [hinp_dir, hinp_proj, hp, hpaths_st, hrun, ha_dir, ha_proj]
                rcases pqRecvPrekeyModel X W st m rc with _ | (_ | ⟨st', out⟩) <;> rfl
              · intro dir' recB pt ep' ha
                rw [hinp_dir, hp, hpaths_st, hrun, ha_dir] at ha
                rcases hm' : pqRecvPrekeyModel X W st m rc with _ | (_ | ⟨st', out⟩) <;>
                  rw [hm'] at ha
                · cases ha
                · cases ha
                · obtain ⟨_, _, g', hsess', hst', hwf'⟩ := hok1 st' out hm'
                  simp only [Option.join_some, Option.map_some, Option.some.injEq, Prod.mk.injEq,
                    hsess'] at ha
                  rcases ha with ⟨rfl, rfl, rfl⟩
                  exact Or.inr ⟨x, g', hst' ▸ hwf', habk, hp, rfl, hpaths, by rw [hst']⟩
        by_cases hemp : (s.bin.bytes.isEmpty || s.bin.epochs.epoch == 0) = true
        · rw [hemp]; simp only [↓reduceIte]
          by_cases hexp : (c == wirePrekey :: (bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner).bytes) = true
          · rw [hexp]; simp only [↓reduceIte]
            have hm_eq : m = bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner := by
              have hc' : c = wirePrekey :: (bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner).bytes :=
                beq_iff_eq.mp hexp
              have hd' := bhDecodePreKeyMsgE_wirePrekey_ret (bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner)
              rw [← hc', hdec] at hd'
              exact Option.some.inj hd'
            exact hPrekeyCall ⟨fun _ => hm_eq, by rw [hm_eq]; rfl⟩
          · simp only [Bool.not_eq_true] at hexp
            simp [hexp]
        · simp only [Bool.not_eq_true] at hemp
          rw [hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hhdr : (bhHdrOfPreKeyMsg m == bi.hdr) = true
          · rw [hhdr]; simp only [↓reduceIte]
            have hh_eq : bhHdrOfPreKeyMsg m = bi.hdr := beq_iff_eq.mp hhdr
            have hbk : m.baseKey = u8Vec 32 bi.hdr.ekAPk := by
              have h1 : vecU8 m.baseKey = bi.hdr.ekAPk := congrArg SignalPqxdh.HandshakeHdr.ekAPk hh_eq
              rw [← h1, u8Vec_vecU8_eq]
            exact hPrekeyCall ⟨fun he => by simp [he] at hemp, hbk⟩
          · simp only [Bool.not_eq_true] at hhdr
            simp [hhdr]

/-! ## SM oracle and driver commutation with `projCliDrv` -/

private theorem cliPartyDirInv_update {S : SignalPqxdh.Setup} {l : Nat} {W : PEParams}
    {bi : ModelDriverInstance S l}
    {sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64}
    {st : Party → CliPartyState} (hGs : ∀ Q, CliPartyDirInv W bi sigs Q (st Q))
    {P : Party} {s' : CliPartyState} (hs' : CliPartyDirInv W bi sigs P s') :
    ∀ Q, CliPartyDirInv W bi sigs Q (Function.update st P s' Q) := by
  intro Q
  by_cases hQ : Q = P
  · subst hQ; simpa using hs'
  · simp [Function.update_of_ne hQ]; exact hGs Q

theorem cliOracleImplR_transmit_step {S : SignalPqxdh.Setup} {l : Nat} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hl : l < 10 ^ 6)
    (qep : Nat) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (bi : ModelDriverInstance S l)
    (gsProj : Option (SM.GameState BinState (Plain l) Bytes))
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (stA0 stB0 : CliPartyState) (stA0' stB0' : BinState)
    (gs : SM.GameState CliPartyState (Plain l) Bytes)
    (hGs : ∀ P, CliPartyDirInv W bi sigs P (gs.st P))
    (q : Party × Plain l × Option (BitVec 512)) :
    let schemeDir := Dir.cliPqScheme run l bi stA0 stB0
    let schemeProj := cliPqScheme run W l { bi with gs := gsProj } sigs stA0' stB0'
    let cfgDir := cliConfigSpkS (St := CliPartyState) (Msg := Plain l) decT encT
    let cfgProj := bhConfigSpkS (Msg := Plain l) decT encT
    Prod.map id (mapSt CliPartyState.bin) <$>
      ((SM.transmitR schemeDir (2 + 1) qep cfgDir q).run gs) =
      (SM.transmitR schemeProj (2 + 1) qep cfgProj q).run (mapSt CliPartyState.bin gs) ∧
    ∀ z ∈ support ((SM.transmitR schemeDir (2 + 1) qep cfgDir q).run gs),
      ∀ P, CliPartyDirInv W bi sigs P (z.2.st P) := by
  rcases q with ⟨P, m, rCoins⟩
  intro schemeDir schemeProj cfgDir cfgProj
  have hsendOK : cfgProj.sendOK (mapSt CliPartyState.bin gs) P = cfgDir.sendOK gs P := rfl
  unfold SM.transmitR SM.transmitImpl
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK]
  by_cases hok : (!(cfgDir.sendOK gs P)) = true
  · simp [hok, hGs]
  · simp only [Bool.not_eq_true] at hok
    rw [hok]
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
      mapSt_win]
    by_cases hwin : gs.win = true
    · simp [hwin, hGs]
    · simp only [Bool.not_eq_true] at hwin
      simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, map_bind]
      have hm : m.toList.length < 2 ^ 32 := by rw [List.Vector.toList_length]; omega
      refine ⟨bind_congr_of_forall_mem_support _ fun cb _ => ?_, ?_⟩
      · rcases cb with ⟨coins, bad⟩
        dsimp only
        rw [mapSt_epMgmt]
        rcases hep : gs.epMgmt (2 + 1) qep P bad with _ | gs₁
        · simp
        · dsimp only [Option.map]
          have hst1 : gs₁.st = gs.st := (epMgmt_st_trans hep).1
          obtain ⟨hs1, hs2, _⟩ := cliPqSend_dir_eq_proj hCli (hst1 ▸ hGs P) m.toList hm coins
          have hs_proj :
              (schemeProj.send ((mapSt CliPartyState.bin gs₁).st P) m coins) =
              ((schemeDir.send (gs₁.st P) m coins).1.bin, (schemeDir.send (gs₁.st P) m coins).2) := by
            dsimp only [schemeProj, schemeDir, cliPqScheme, Dir.cliPqScheme, mapSt_st]
            exact Prod.ext hs1.symm hs2.symm
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure,
            Prod.map_apply, id_eq, SMSchemeR.sendPart, mapSt_epoch, mapSt_idx]
          congr 1
          change (some (schemeDir.send (gs₁.st P) m coins).2,
              mapSt CliPartyState.bin (gs₁.record (2 + 1) P (schemeDir.send (gs₁.st P) m coins).1
                ⟨⟨P, gs₁.epoch P, gs₁.idx P + 1⟩, m, (schemeDir.send (gs₁.st P) m coins).2⟩ false)) =
            (some (schemeProj.send ((mapSt CliPartyState.bin gs₁).st P) m coins).2,
              (mapSt CliPartyState.bin gs₁).record (2 + 1) P
                (schemeProj.send ((mapSt CliPartyState.bin gs₁).st P) m coins).1
                ⟨⟨P, gs₁.epoch P, gs₁.idx P + 1⟩, m,
                  (schemeProj.send ((mapSt CliPartyState.bin gs₁).st P) m coins).2⟩ false)
          rw [hs_proj, ← mapSt_record]
      · intro z hz P'
        rw [mem_support_bind_iff] at hz
        obtain ⟨⟨coins, bad⟩, _, hz⟩ := hz
        dsimp only at hz
        rcases hep : gs.epMgmt (2 + 1) qep P bad with _ | gs₁ <;> rw [hep] at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hGs P'
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz
          have hst1 : gs₁.st = gs.st := (epMgmt_st_trans hep).1
          obtain ⟨_, _, hinv'⟩ := cliPqSend_dir_eq_proj hCli (hst1 ▸ hGs P) m.toList hm coins
          exact cliPartyDirInv_update (hst1 ▸ hGs) hinv' P'

private theorem cliOracleImplR_chall_step {S : SignalPqxdh.Setup} {l : Nat} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hl : l < 10 ^ 6)
    (qep : Nat) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (bi : ModelDriverInstance S l)
    (gsProj : Option (SM.GameState BinState (Plain l) Bytes))
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (stA0 stB0 : CliPartyState) (stA0' stB0' : BinState)
    (gs : SM.GameState CliPartyState (Plain l) Bytes)
    (hGs : ∀ P, CliPartyDirInv W bi sigs P (gs.st P))
    (q : Party × Plain l × Plain l × Option (BitVec 512)) :
    let schemeDir := Dir.cliPqScheme run l bi stA0 stB0
    let schemeProj := cliPqScheme run W l { bi with gs := gsProj } sigs stA0' stB0'
    let cfgDir := cliConfigSpkS (St := CliPartyState) (Msg := Plain l) decT encT
    let cfgProj := bhConfigSpkS (Msg := Plain l) decT encT
    Prod.map id (mapSt CliPartyState.bin) <$>
      ((SM.challR schemeDir (2 + 1) qep cfgDir q).run gs) =
      (SM.challR schemeProj (2 + 1) qep cfgProj q).run (mapSt CliPartyState.bin gs) ∧
    ∀ z ∈ support ((SM.challR schemeDir (2 + 1) qep cfgDir q).run gs),
      ∀ P, CliPartyDirInv W bi sigs P (z.2.st P) := by
  rcases q with ⟨P, m₀, m₁, rCoins⟩
  intro schemeDir schemeProj cfgDir cfgProj
  have hsendOK : cfgProj.sendOK (mapSt CliPartyState.bin gs) P = cfgDir.sendOK gs P := rfl
  have hbase : cfgProj.base = cfgDir.base := rfl
  unfold SM.challR SM.challImpl
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK, hbase]
  by_cases hok : (!(cfgDir.sendOK gs P)) = true
  · simp [hok, hGs]
  · simp only [Bool.not_eq_true] at hok
    rw [hok]
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
      mapSt_win]
    by_cases hwin : gs.win = true
    · simp [hwin, hGs]
    · simp only [Bool.not_eq_true] at hwin
      simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, map_bind]
      refine ⟨bind_congr_of_forall_mem_support _ fun cb _ => ?_, ?_⟩
      · rcases cb with ⟨coins, bad⟩
        dsimp only
        rw [mapSt_epMgmt]
        rcases hep : gs.epMgmt (2 + 1) qep P bad with _ | gs₁
        · simp
        · dsimp only [Option.map]
          simp only [mapSt_safeCh, mapSt_epoch, mapSt_b, mapSt_idx]
          by_cases hch : (!(gs₁.safeCh (2 + 1) P) || !(cfgDir.base.challAllowedIn (gs₁.epoch P))) = true
          · simp [hch]
          · simp only [Bool.not_eq_true] at hch
            simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, map_pure, Prod.map_apply, id_eq, SMSchemeR.sendPart]
            set m := (cfgDir.base.challMsg (gs₁.epoch P)).getD (if gs.b = true then m₁ else m₀)
            have hm : m.toList.length < 2 ^ 32 := by rw [List.Vector.toList_length]; omega
            have hst1 : gs₁.st = gs.st := (epMgmt_st_trans hep).1
            obtain ⟨hs1, hs2, _⟩ := cliPqSend_dir_eq_proj hCli (hst1 ▸ hGs P) m.toList hm coins
            have hs_proj :
                (schemeProj.send ((mapSt CliPartyState.bin gs₁).st P) m coins) =
                ((schemeDir.send (gs₁.st P) m coins).1.bin, (schemeDir.send (gs₁.st P) m coins).2) := by
              dsimp only [schemeProj, schemeDir, cliPqScheme, Dir.cliPqScheme, mapSt_st]
              exact Prod.ext hs1.symm hs2.symm
            congr 1
            change (some (schemeDir.send (gs₁.st P) m coins).2,
                mapSt CliPartyState.bin (gs₁.record (2 + 1) P (schemeDir.send (gs₁.st P) m coins).1
                  ⟨⟨P, gs₁.epoch P, gs₁.idx P + 1⟩, m, (schemeDir.send (gs₁.st P) m coins).2⟩ true)) =
              (some (schemeProj.send ((mapSt CliPartyState.bin gs₁).st P) m coins).2,
                (mapSt CliPartyState.bin gs₁).record (2 + 1) P
                  (schemeProj.send ((mapSt CliPartyState.bin gs₁).st P) m coins).1
                  ⟨⟨P, gs₁.epoch P, gs₁.idx P + 1⟩, m,
                    (schemeProj.send ((mapSt CliPartyState.bin gs₁).st P) m coins).2⟩ true)
            rw [hs_proj, ← mapSt_record]
      · intro z hz P'
        rw [mem_support_bind_iff] at hz
        obtain ⟨⟨coins, bad⟩, _, hz⟩ := hz
        dsimp only at hz
        rcases hep : gs.epMgmt (2 + 1) qep P bad with _ | gs₁ <;> rw [hep] at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hGs P'
        · dsimp only at hz
          by_cases hch : (!(gs₁.safeCh (2 + 1) P) || !(cfgDir.base.challAllowedIn (gs₁.epoch P))) = true
          · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hGs P'
          · simp only [Bool.not_eq_true] at hch
            simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            set m := (cfgDir.base.challMsg (gs₁.epoch P)).getD (if gs.b then m₁ else m₀)
            have hm : m.toList.length < 2 ^ 32 := by rw [List.Vector.toList_length]; omega
            have hst1 : gs₁.st = gs.st := (epMgmt_st_trans hep).1
            obtain ⟨_, _, hinv'⟩ := cliPqSend_dir_eq_proj hCli (hst1 ▸ hGs P) m.toList hm coins
            exact cliPartyDirInv_update (hst1 ▸ hGs) hinv' P'

private theorem cliOracleImplR_deliver_step {S : SignalPqxdh.Setup} {l : Nat} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (bi : ModelDriverInstance S l)
    (gsProj : Option (SM.GameState BinState (Plain l) Bytes))
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (stA0 stB0 : CliPartyState) (stA0' stB0' : BinState)
    (gs : SM.GameState CliPartyState (Plain l) Bytes)
    (hGs : ∀ P, CliPartyDirInv W bi sigs P (gs.st P))
    (q : Party × Bytes) :
    let schemeDir := Dir.cliPqScheme run l bi stA0 stB0
    let schemeProj := cliPqScheme run W l { bi with gs := gsProj } sigs stA0' stB0'
    let cfgDir := cliConfigSpkS (St := CliPartyState) (Msg := Plain l) decT encT
    let cfgProj := bhConfigSpkS (Msg := Plain l) decT encT
    Prod.map id (mapSt CliPartyState.bin) <$>
      ((SM.deliverR schemeDir cfgDir q).run gs) =
      (SM.deliverR schemeProj cfgProj q).run (mapSt CliPartyState.bin gs) ∧
    ∀ z ∈ support ((SM.deliverR schemeDir cfgDir q).run gs),
      ∀ P, CliPartyDirInv W bi sigs P (z.2.st P) := by
  rcases q with ⟨P, c⟩
  intro schemeDir schemeProj cfgDir cfgProj
  unfold SM.deliverR
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind, mapSt_win, mapSt_inTransit]
  by_cases hwin : gs.win = true
  · simp [hwin, hGs]
  · simp only [Bool.not_eq_true] at hwin
    rw [hwin]; simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hit : gs.inTransit P.other c with _ | r
    · simp [hGs]
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        map_bind]
      refine ⟨bind_congr_of_forall_mem_support _ fun rc _ => ?_, ?_⟩
      · have hmust : (cfgProj.base.deliverWin && cfgProj.must (mapSt CliPartyState.bin gs) P r) =
            (cfgDir.base.deliverWin && cfgDir.must gs P r) := rfl
        have hchall : (mapSt CliPartyState.bin gs).chall = gs.chall := rfl
        obtain ⟨hrec_eq, _⟩ := cliPqReceive_dir_eq_proj (l := l) hCli (hGs P) c rc
        have hrec_proj : schemeProj.receive ((mapSt CliPartyState.bin gs).st P) c rc =
            (schemeDir.receive (gs.st P) c rc).map (fun x => (x.1.bin, x.2.1, x.2.2.1, x.2.2.2)) := by
          dsimp only [schemeProj, schemeDir, cliPqScheme, Dir.cliPqScheme, mapSt_st]
          exact hrec_eq.symm
        rw [hmust, hrec_proj, hchall]
        rcases hrec : schemeDir.receive (gs.st P) c rc with _ | ⟨st', t', i', m'⟩
        · dsimp only [Option.map]
          cases cfgDir.base.deliverWin && cfgDir.must gs P r <;> simp [mapSt]
        · dsimp only [Option.map]
          rw [mapSt_accept]
          cases (cfgDir.base.deliverWin && cfgDir.must gs P r) &&
              !(decide ((t', i', m') = (r.pos.epoch, r.pos.idx, r.msg))) <;>
            simp [mapSt]
      · intro z hz P'
        rw [mem_support_bind_iff] at hz
        obtain ⟨rc, _, hz⟩ := hz
        obtain ⟨_, hrec_inv⟩ := cliPqReceive_dir_eq_proj (l := l) hCli (hGs P) c rc
        rcases hrec : schemeDir.receive (gs.st P) c rc with _ | ⟨st', t', i', m'⟩ <;>
          rw [hrec] at hz
        · dsimp only at hz
          cases hmust : cfgDir.base.deliverWin && cfgDir.must gs P r <;>
            (simp [hmust] at hz; subst hz; exact hGs P')
        · dsimp only at hz
          have hst' : CliPartyDirInv W bi sigs P st' := hrec_inv (st', t', i', m') hrec
          cases hmust : (cfgDir.base.deliverWin && cfgDir.must gs P r) &&
              !(decide ((t', i', m') = (r.pos.epoch, r.pos.idx, r.msg))) <;>
            (simp at hz; subst hz; exact cliPartyDirInv_update hGs hst' P')

private theorem cliOracleImplR_inject_step {S : SignalPqxdh.Setup} {l : Nat} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W)
    (qep : Nat) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (bi : ModelDriverInstance S l)
    (gsProj : Option (SM.GameState BinState (Plain l) Bytes))
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (stA0 stB0 : CliPartyState) (stA0' stB0' : BinState)
    (gs : SM.GameState CliPartyState (Plain l) Bytes)
    (hGs : ∀ P, CliPartyDirInv W bi sigs P (gs.st P))
    (q : Party × Bytes) :
    let schemeDir := Dir.cliPqScheme run l bi stA0 stB0
    let schemeProj := cliPqScheme run W l { bi with gs := gsProj } sigs stA0' stB0'
    let cfgDir := cliConfigSpkS (St := CliPartyState) (Msg := Plain l) decT encT
    let cfgProj := bhConfigSpkS (Msg := Plain l) decT encT
    Prod.map id (mapSt CliPartyState.bin) <$>
      ((SM.injectR schemeDir (2 + 1) qep cfgDir q).run gs) =
      (SM.injectR schemeProj (2 + 1) qep cfgProj q).run (mapSt CliPartyState.bin gs) ∧
    ∀ z ∈ support ((SM.injectR schemeDir (2 + 1) qep cfgDir q).run gs),
      ∀ P, CliPartyDirInv W bi sigs P (z.2.st P) := by
  rcases q with ⟨P, c⟩
  intro schemeDir schemeProj cfgDir cfgProj
  have hinjOK : cfgProj.injOK = cfgDir.injOK := rfl
  have hbase : cfgProj.base = cfgDir.base := rfl
  unfold SM.injectR
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind, mapSt_win, mapSt_inTransit,
    mapSt_safeInj, hinjOK, hbase]
  by_cases hguard : (gs.win || (gs.inTransit P.other c).isSome || !(gs.safeInj (2 + 1)) ||
      !(cfgDir.injOK c)) = true
  · simp [hguard, hGs]
  · simp only [Bool.not_eq_true] at hguard
    rw [hguard]; simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, bind_assoc, pure_bind, map_bind]
    refine ⟨bind_congr_of_forall_mem_support _ fun rc _ => ?_, ?_⟩
    · obtain ⟨hrec_eq, _⟩ := cliPqReceive_dir_eq_proj (l := l) hCli (hGs P) c rc
      have hrec_proj : schemeProj.receive ((mapSt CliPartyState.bin gs).st P) c rc =
          (schemeDir.receive (gs.st P) c rc).map (fun x => (x.1.bin, x.2.1, x.2.2.1, x.2.2.2)) := by
        dsimp only [schemeProj, schemeDir, cliPqScheme, Dir.cliPqScheme, mapSt_st]
        exact hrec_eq.symm
      rw [hrec_proj]
      rcases hrec : schemeDir.receive (gs.st P) c rc with _ | ⟨st', t', i', m'⟩
      · simp
      · dsimp only [Option.map]
        by_cases hqep : qep + 1 < t'
        · simp [hqep]
        · simp only [hqep, ↓reduceIte, mapSt_trivial]
          by_cases htriv : gs.trivial (2 + 1) ⟨P.other, t', i'⟩ = true
          · simp [htriv, mapSt_accept]
          · simp only [Bool.not_eq_true] at htriv
            simp only [htriv, Bool.false_eq_true, ↓reduceIte]
            cases cfgDir.base.injectFull t' <;> simp [mapSt]
    · intro z hz P'
      rw [mem_support_bind_iff] at hz
      obtain ⟨rc, _, hz⟩ := hz
      obtain ⟨_, hrec_inv⟩ := cliPqReceive_dir_eq_proj (l := l) hCli (hGs P) c rc
      rcases hrec : schemeDir.receive (gs.st P) c rc with _ | ⟨st', t', i', m'⟩ <;>
        rw [hrec] at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hGs P'
      · dsimp only at hz
        have hst' : CliPartyDirInv W bi sigs P st' := hrec_inv (st', t', i', m') hrec
        by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hGs P'
        · simp only [hqep, ↓reduceIte] at hz
          by_cases htriv : gs.trivial (2 + 1) ⟨P.other, t', i'⟩ = true
          · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact cliPartyDirInv_update hGs hst' P'
          · simp only [Bool.not_eq_true] at htriv
            rw [htriv] at hz
            cases cfgDir.base.injectFull t' <;>
              simp only [Bool.false_eq_true, ↓reduceIte] at hz <;>
              (subst hz; exact hGs P')

private theorem cliOracleImplR_corr_step {S : SignalPqxdh.Setup} {l : Nat} {Pt : Type}
    {W : PEParams}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (bi : ModelDriverInstance S l)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (gs : SM.GameState CliPartyState (Plain l) Bytes)
    (hGs : ∀ P, CliPartyDirInv W bi sigs P (gs.st P))
    (P : Party) :
    let cfgDir := cliConfigSpkS (St := CliPartyState) (Msg := Plain l) decT encT
    let cfgProj := bhConfigSpkS (Msg := Plain l) decT encT
    Prod.map id (mapSt CliPartyState.bin) <$>
      (((Option.map CliPartyState.bin <$> SM.corrR cfgDir P) :
          StateT (SM.GameState CliPartyState (Plain l) Bytes) ProbComp (Option BinState)).run gs) =
      (SM.corrR cfgProj P).run (mapSt CliPartyState.bin gs) ∧
    ∀ z ∈ support (((Option.map CliPartyState.bin <$> SM.corrR cfgDir P) :
        StateT (SM.GameState CliPartyState (Plain l) Bytes) ProbComp (Option BinState)).run gs),
      ∀ Q, CliPartyDirInv W bi sigs Q (z.2.st Q) := by
  intro cfgDir cfgProj
  have hguard_eq :
      ((mapSt CliPartyState.bin gs).win || !((mapSt CliPartyState.bin gs).corrAllowed P) ||
        (cfgProj.r1 && inWindow (mapSt CliPartyState.bin gs) P) ||
        !(cfgProj.corrOK (mapSt CliPartyState.bin gs) P)) =
      (gs.win || !(gs.corrAllowed P) || (cfgDir.r1 && inWindow gs P) || !(cfgDir.corrOK gs P)) := rfl
  unfold SM.corrR
  simp only [StateT.run_map, StateT.run_bind, StateT.run_get, pure_bind, hguard_eq]
  by_cases hg : (gs.win || !(gs.corrAllowed P) || (cfgDir.r1 && inWindow gs P) ||
      !(cfgDir.corrOK gs P)) = true
  · simp [hg, hGs]
  · simp only [Bool.not_eq_true] at hg
    rw [hg]
    have hst : (gs.afterCorr P).st = gs.st := rfl
    simp [mapSt_afterCorr, hst, hGs]

theorem cliOracleImplR_step {S : SignalPqxdh.Setup} {l : Nat} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hl : l < 10 ^ 6)
    (qep : Nat) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (bi : ModelDriverInstance S l)
    (gsProj : Option (SM.GameState BinState (Plain l) Bytes))
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (stA0 stB0 : CliPartyState) (stA0' stB0' : BinState)
    (gs : SM.GameState CliPartyState (Plain l) Bytes)
    (hGs : ∀ P, CliPartyDirInv W bi sigs P (gs.st P))
    (q : (cliGameSmSpec l (BitVec 512)).Domain) :
    let schemeDir := Dir.cliPqScheme run l bi stA0 stB0
    let schemeProj := cliPqScheme run W l { bi with gs := gsProj } sigs stA0' stB0'
    let cfgDir := cliConfigSpkS (St := CliPartyState) (Msg := Plain l) decT encT
    let cfgProj := bhConfigSpkS (Msg := Plain l) decT encT
    Prod.map id (mapSt CliPartyState.bin) <$>
      ((cliOracleImplR CliPartyState.bin schemeDir (2 + 1) qep cfgDir q).run gs) =
      (SM.oracleImplR schemeProj (2 + 1) qep cfgProj q).run (mapSt CliPartyState.bin gs) ∧
    ∀ z ∈ support ((cliOracleImplR CliPartyState.bin schemeDir (2 + 1) qep cfgDir q).run gs),
      ∀ P, CliPartyDirInv W bi sigs P (z.2.st P) := by
  intro schemeDir schemeProj cfgDir cfgProj
  rcases q with (((q₁ | q₂) | q₃) | q₄) | q₅
  · exact cliOracleImplR_transmit_step hCli hl qep decT encT bi gsProj sigs stA0 stB0 stA0' stB0' gs hGs q₁
  · exact cliOracleImplR_chall_step hCli hl qep decT encT bi gsProj sigs stA0 stB0 stA0' stB0' gs hGs q₂
  · exact cliOracleImplR_deliver_step hCli decT encT bi gsProj sigs stA0 stB0 stA0' stB0' gs hGs q₃
  · exact cliOracleImplR_inject_step hCli qep decT encT bi gsProj sigs stA0 stB0 stA0' stB0' gs hGs q₄
  · exact cliOracleImplR_corr_step decT encT bi sigs gs hGs q₅

/-! ### `KeyInd` `spkLookup` invariance and `projCliDrv` state invariant -/

def spkLookup (idx₀ : Nat × Nat)
    (bs : List ((Nat × Nat) × SignalPqxdh.SpkBundleEntry)) :
    Option (SignalPqxdh.Bytes × SignalPqxdh.Bytes) :=
  (bs.find? (fun (idx, _) => idx == idx₀)).map (fun (_, e) => (e.spkSig, e.pqspkSig))

theorem cliPqSigsOf_eq_of_spkLookup {S : SignalPqxdh.Setup} {l : Nat}
    {kst₁ kst₂ : SignalPqxdh.KeyIndState S} {bi : ModelDriverInstance S l}
    {sigPair : SignalPqxdh.Bytes × SignalPqxdh.Bytes}
    (h₁' : spkLookup (bi.respSlot.1.val, bi.respSlot.2.val) kst₁.spkBundles = some sigPair)
    (h₂' : spkLookup (bi.respSlot.1.val, bi.respSlot.2.val) kst₂.spkBundles = some sigPair) :
    cliPqSigsOf kst₂ bi = cliPqSigsOf kst₁ bi := by
  rcases sigPair with ⟨sig1, sig2⟩
  unfold spkLookup at h₁' h₂'
  unfold cliPqSigsOf
  rcases hf₁ : kst₁.spkBundles.find? (fun (idx, _) => idx == (bi.respSlot.1.val, bi.respSlot.2.val)) with
    _ | ⟨_, e₁⟩ <;> rw [hf₁] at h₁'
  · cases h₁'
  · rcases hf₂ : kst₂.spkBundles.find? (fun (idx, _) => idx == (bi.respSlot.1.val, bi.respSlot.2.val)) with
      _ | ⟨_, e₂⟩ <;> rw [hf₂] at h₂'
    · cases h₂'
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h₁' h₂'
      rw [hf₁, hf₂]
      dsimp only
      rw [h₁'.1, h₁'.2, h₂'.1, h₂'.2]

private theorem spkLookup_cons_of_any_false {idx₀ k : Nat × Nat}
    {bEntry : SignalPqxdh.SpkBundleEntry}
    {bs : List ((Nat × Nat) × SignalPqxdh.SpkBundleEntry)}
    {sigPair : SignalPqxdh.Bytes × SignalPqxdh.Bytes}
    (hany : bs.any (fun (x, _) => x == k) = false)
    (hl : spkLookup idx₀ bs = some sigPair) :
    spkLookup idx₀ ((k, bEntry) :: bs) = some sigPair := by
  unfold spkLookup at hl ⊢
  rcases hf : bs.find? (fun (idx, _) => idx == idx₀) with _ | ⟨idx, e⟩ <;> rw [hf] at hl
  · cases hl
  · have hmem := List.mem_of_find?_eq_some hf
    have heq_idx : (idx == idx₀) = true := by simpa using List.find?_some hf
    have hnek : (idx == k) = false := by
      by_contra hcon
      have hk_true : (idx == k) = true := Bool.eq_true_of_not_eq_false hcon
      have hany_true : bs.any (fun (x, _) => x == k) = true :=
        List.any_eq_true.mpr ⟨(idx, e), hmem, hk_true⟩
      rw [hany] at hany_true
      cases hany_true
    have hkne : (k == idx₀) = false := by
      by_contra hcon
      have hk0 : k = idx₀ := beq_iff_eq.mp (Bool.eq_true_of_not_eq_false hcon)
      have hi0 : idx = idx₀ := beq_iff_eq.mp heq_idx
      have hik : (idx == k) = true := beq_iff_eq.mpr (hi0.trans hk0.symm)
      rw [hnek] at hik
      cases hik
    simp [List.find?, hkne, hf, hl]

private theorem spkLookup_map_reveal (idx₀ target : Nat × Nat)
    (bs : List ((Nat × Nat) × SignalPqxdh.SpkBundleEntry)) :
    spkLookup idx₀ (bs.map (fun (idx, b) =>
      if idx == target then (idx, { b with revealed := true }) else (idx, b))) =
      spkLookup idx₀ bs := by
  unfold spkLookup
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨idx, b⟩
    simp only [List.map_cons]
    by_cases ht : (idx == target) = true
    · rw [ht]; simp only [↓reduceIte, List.find?_cons]
      cases h : (idx == idx₀)
      · exact ih
      · rfl
    · simp only [Bool.not_eq_true] at ht
      rw [ht]; simp only [Bool.false_eq_true, ↓reduceIte, List.find?_cons]
      cases h : (idx == idx₀)
      · exact ih
      · rfl

private theorem pqxdhKeyIndImpl_preserves_spkLookup {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (q : SignalPqxdh.KeyIndQuery S)
    (kst : SignalPqxdh.KeyIndState S)
    {z : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hz : z ∈ support ((SignalPqxdh.pqxdhKeyIndImpl false S P q).run kst)) :
    ∀ idx₀ sigPair, spkLookup idx₀ kst.spkBundles = some sigPair →
      spkLookup idx₀ z.2.spkBundles = some sigPair := by
  have hInit : ∀ sid u bnd,
      ∀ w ∈ support ((SignalPqxdh.runKeyIndInitiate false S P sid u bnd).run kst),
        w.2.spkBundles = kst.spkBundles := by
    intro sid u bnd w hw
    unfold SignalPqxdh.runKeyIndInitiate at hw
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hw
    by_cases h1 : kst.sessions.any (fun e => e.sid == sid) = true
    · simp [h1] at hw; subst hw; rfl
    · simp only [Bool.not_eq_true] at h1
      rw [h1] at hw; simp only [Bool.false_eq_true, ↓reduceIte] at hw
      rcases hfp : kst.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩ <;>
        rw [hfp] at hw
      · simp at hw; subst hw; rfl
      · dsimp only at hw
        by_cases h2 : (!SignalPqxdh.koskBundleOk P kst.principals kst.spkBundles
            kst.opkEntries kst.advKeys bnd) = true
        · simp [h2] at hw; subst hw; rfl
        · simp only [Bool.not_eq_true] at h2
          rw [h2] at hw
          simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
            monadLift_self, bind_assoc, pure_bind, mem_support_bind_iff] at hw
          obtain ⟨ekASk, _, kemCoins, _, hw⟩ := hw
          by_cases h3 : (!(P.sigVerify (SignalPqxdh.resolveSigPk P kst.principals bnd.ikB)
              (SignalPqxdh.encodeEC bnd.spkB) bnd.spkSig &&
            P.sigVerify (SignalPqxdh.resolveSigPk P kst.principals bnd.ikB)
              (SignalPqxdh.encodeKEM bnd.pqspkB) bnd.pqspkSig)) = true
          · simp [h3] at hw; subst hw; rfl
          · simp only [Bool.not_eq_true] at h3
            rw [h3] at hw; simp only [Bool.false_eq_true, ↓reduceIte] at hw
            rcases hkem : P.kemEncaps bnd.pqspkB kemCoins with _ | ⟨ss, kemCt⟩ <;>
              rw [hkem] at hw
            · simp at hw; subst hw; rfl
            · dsimp only at hw
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                bind_assoc, pure_bind, mem_support_bind_iff] at hw
              obtain ⟨⟨drKeyReal, roCache'⟩, _, hw⟩ := hw
              rcases hpart : SignalPqxdh.keyIndPartnerRandKey? P kst.respSessions _ with _ | k <;>
                rw [hpart] at hw
              · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                  StateT.run_set, bind_assoc, pure_bind,
                  mem_support_bind_iff] at hw
                obtain ⟨drKeyRand, _, hw⟩ := hw
                rcases hfh : SignalPqxdh.findHonestPrincipal P kst.principals bnd.ikB with
                  _ | ⟨_, _⟩ <;>
                  (rw [hfh] at hw;
                   simp only [StateT.run_pure,
                     support_pure, Set.mem_singleton_iff] at hw;
                   subst hw; rfl)
              · simp only [StateT.run_bind, StateT.run_set, pure_bind] at hw
                rcases hfh : SignalPqxdh.findHonestPrincipal P kst.principals bnd.ikB with
                  _ | ⟨_, _⟩ <;>
                  (rw [hfh] at hw;
                   simp only [StateT.run_pure,
                     support_pure, Set.mem_singleton_iff] at hw;
                   subst hw; rfl)
  have hRecResp : ∀ (st₀ : SignalPqxdh.KeyIndState S) (r : SignalPqxdh.KeyIndRespEntry S),
      ∀ w ∈ support ((SignalPqxdh.recordKeyIndResp S P r).run st₀),
        w.2.spkBundles = st₀.spkBundles := by
    intro st₀ r w hw
    unfold SignalPqxdh.recordKeyIndResp at hw
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hw
    rcases hf : st₀.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s r) with _ | s <;>
      rw [hf] at hw
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
      obtain ⟨_, _, rfl⟩ := hw; rfl
    · simp only [StateT.run_set,
        support_pure, Set.mem_singleton_iff] at hw
      subst hw; rfl
  unfold SignalPqxdh.pqxdhKeyIndImpl at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases q with
  | initPrin u =>
    dsimp only at hz
    by_cases hp : kst.principals.any (fun (idx, _) => idx == u.val) = true
    · simp [hp] at hz; subst hz; exact fun _ _ h => h
    · simp only [Bool.not_eq_true] at hp
      rw [hp] at hz
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨_, _, _, _, rfl⟩ := hz; exact fun _ _ h => h
  | corruptIK u =>
    dsimp only at hz
    rcases hf : kst.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, entry⟩ <;>
      rw [hf] at hz
    · simp at hz; subst hz; exact fun _ _ h => h
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact fun _ _ h => h
  | genSPK u j =>
    dsimp only at hz
    by_cases hany : kst.spkBundles.any (fun (k, _) => k == (u.val, j.val)) = true
    · simp [hany] at hz; subst hz; exact fun _ _ h => h
    · simp only [Bool.not_eq_true] at hany
      rw [hany] at hz; simp only [Bool.false_eq_true, ↓reduceIte] at hz
      rcases hf : kst.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩ <;>
        rw [hf] at hz
      · simp at hz; subst hz; exact fun _ _ h => h
      · dsimp only at hz
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hz
        obtain ⟨_, _, _, _, ⟨_, _⟩, _, _, _, rfl⟩ := hz
        exact fun idx₀ sigPair h => spkLookup_cons_of_any_false hany h
  | genOPK u j o =>
    dsimp only at hz
    by_cases hany : kst.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) = true
    · simp [hany] at hz; subst hz; exact fun _ _ h => h
    · simp only [Bool.not_eq_true] at hany
      rw [hany] at hz
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨_, _, rfl⟩ := hz; exact fun _ _ h => h
  | initiateOPK u i bnd =>
    dsimp only at hz
    by_cases hn : bnd.opkB?.isNone = true
    · simp [hn] at hz; subst hz; exact fun _ _ h => h
    · simp only [Bool.not_eq_true] at hn
      rw [hn] at hz; simp only [Bool.false_eq_true, ↓reduceIte] at hz
      rw [hInit _ _ _ z hz]; exact fun _ _ h => h
  | initiateNoOPK u i bnd =>
    dsimp only at hz
    by_cases hs : bnd.opkB?.isSome = true
    · simp [hs] at hz; subst hz; exact fun _ _ h => h
    · simp only [Bool.not_eq_true] at hs
      rw [hs] at hz; simp only [Bool.false_eq_true, ↓reduceIte] at hz
      rw [hInit _ _ _ z hz]; exact fun _ _ h => h
  | acceptOPK k j o hdr =>
    dsimp only at hz
    by_cases hg1 : (!(hdr.spkId == UInt32.ofNat j.val &&
        hdr.pqspkId == UInt32.ofNat j.val &&
        hdr.opkId? == some (UInt32.ofNat o.val) &&
        hdr.ikAPk.length == 32 &&
        hdr.ekAPk.length == 32)) = true
    · rw [hg1] at hz
      simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact fun _ _ h => h
    · simp only [Bool.not_eq_true] at hg1; rw [hg1] at hz
      simp only [Bool.false_eq_true, ↓reduceIte] at hz
      by_cases hg2 : kst.usedRecvOPK.contains (k.val, j.val, o.val) = true
      · rw [hg2] at hz
        simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact fun _ _ h => h
      · simp only [Bool.not_eq_true] at hg2; rw [hg2] at hz
        simp only [Bool.false_eq_true, ↓reduceIte] at hz
        by_cases hg3 : (!SignalPqxdh.koskSenderOk P kst.principals kst.advKeys hdr.ikAPk) = true
        · simp [hg3] at hz; subst hz; exact fun _ _ h => h
        · simp only [Bool.not_eq_true] at hg3; rw [hg3] at hz
          simp only [Bool.false_eq_true, ↓reduceIte] at hz
          rcases hfp : kst.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩ <;>
            rw [hfp] at hz
          · simp at hz; subst hz; exact fun _ _ h => h
          · dsimp only at hz
            rcases hfs : kst.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
              _ | ⟨_, bEntry⟩ <;> rw [hfs] at hz
            · simp at hz; subst hz; exact fun _ _ h => h
            · dsimp only at hz
              rcases hfo : kst.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
                _ | ⟨_, oEntry⟩ <;> rw [hfo] at hz
              · simp at hz; subst hz; exact fun _ _ h => h
              · dsimp only at hz
                by_cases hcon : oEntry.consumed = true
                · simp [hcon] at hz; subst hz; exact fun _ _ h => h
                · simp only [Bool.not_eq_true] at hcon; rw [hcon] at hz
                  simp only [Bool.false_eq_true, ↓reduceIte] at hz
                  rcases hacc : SignalPqxdh.Model.acceptKeys P _ with _ | _ <;> rw [hacc] at hz
                  · simp at hz; subst hz; exact fun _ _ h => h
                  · dsimp only at hz
                    rcases hkem : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss <;>
                      rw [hkem] at hz
                    · simp at hz; subst hz; exact fun _ _ h => h
                    · dsimp only at hz
                      simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                        StateT.run_set, bind_assoc, pure_bind, mem_support_bind_iff] at hz
                      obtain ⟨⟨drKey, roCache'⟩, _, w, hw, hz⟩ := hz
                      have hsp := hRecResp _ _ w hw
                      rcases hfh : SignalPqxdh.findHonestPrincipal P kst.principals hdr.ikAPk with
                        _ | ⟨_, _⟩ <;>
                        (rw [hfh] at hz;
                         simp only [StateT.run_pure,
                           support_pure, Set.mem_singleton_iff] at hz;
                         subst hz; dsimp only; rw [hsp]; exact fun _ _ h => h)
  | acceptNoOPK k j l hdr =>
    dsimp only at hz
    by_cases hg1 : (!(hdr.spkId == UInt32.ofNat j.val &&
        hdr.pqspkId == UInt32.ofNat j.val &&
        hdr.opkId? == none &&
        hdr.ikAPk.length == 32 &&
        hdr.ekAPk.length == 32)) = true
    · rw [hg1] at hz
      simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact fun _ _ h => h
    · simp only [Bool.not_eq_true] at hg1; rw [hg1] at hz
      simp only [Bool.false_eq_true, ↓reduceIte] at hz
      by_cases hg2 : kst.usedRecvNoOPK.contains (k.val, j.val, l.val) = true
      · rw [hg2] at hz
        simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact fun _ _ h => h
      · simp only [Bool.not_eq_true] at hg2; rw [hg2] at hz
        simp only [Bool.false_eq_true, ↓reduceIte] at hz
        by_cases hg3 : (!SignalPqxdh.koskSenderOk P kst.principals kst.advKeys hdr.ikAPk) = true
        · simp [hg3] at hz; subst hz; exact fun _ _ h => h
        · simp only [Bool.not_eq_true] at hg3; rw [hg3] at hz
          simp only [Bool.false_eq_true, ↓reduceIte] at hz
          rcases hfp : kst.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩ <;>
            rw [hfp] at hz
          · simp at hz; subst hz; exact fun _ _ h => h
          · dsimp only at hz
            rcases hfs : kst.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
              _ | ⟨_, bEntry⟩ <;> rw [hfs] at hz
            · simp at hz; subst hz; exact fun _ _ h => h
            · dsimp only at hz
              rcases hacc : SignalPqxdh.Model.acceptKeys P _ with _ | _ <;> rw [hacc] at hz
              · simp at hz; subst hz; exact fun _ _ h => h
              · dsimp only at hz
                rcases hkem : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss <;>
                  rw [hkem] at hz
                · simp at hz; subst hz; exact fun _ _ h => h
                · dsimp only at hz
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                    StateT.run_set, bind_assoc, pure_bind, mem_support_bind_iff] at hz
                  obtain ⟨⟨drKey, roCache'⟩, _, w, hw, hz⟩ := hz
                  have hsp := hRecResp _ _ w hw
                  rcases hfh : SignalPqxdh.findHonestPrincipal P kst.principals hdr.ikAPk with
                    _ | ⟨_, _⟩ <;>
                    (rw [hfh] at hz;
                     simp only [StateT.run_pure,
                       support_pure, Set.mem_singleton_iff] at hz;
                     subst hz; dsimp only; rw [hsp]; exact fun _ _ h => h)
  | testSession sid =>
    dsimp only at hz
    by_cases ht : (!SignalPqxdh.isKeyIndSessionTestable kst sid) = true
    · simp [ht] at hz; subst hz; exact fun _ _ h => h
    · simp only [Bool.not_eq_true] at ht; rw [ht] at hz
      simp only [Bool.false_eq_true, ↓reduceIte] at hz
      rcases hfs : kst.sessions.find? (fun e => e.sid == sid) with _ | e <;> rw [hfs] at hz
      · dsimp only at hz
        rcases hfr : kst.respSessions.find? (fun r => r.sid == sid) with _ | r <;> rw [hfr] at hz
        · simp at hz; subst hz; exact fun _ _ h => h
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact fun _ _ h => h
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact fun _ _ h => h
  | revealSessionKey sid =>
    dsimp only at hz
    rcases hfs : kst.sessions.find? (fun e => e.sid == sid) with _ | e <;> rw [hfs] at hz
    · dsimp only at hz
      rcases hfr : kst.respSessions.find? (fun r => r.sid == sid) with _ | r <;> rw [hfr] at hz
      · simp at hz; subst hz; exact fun _ _ h => h
      · dsimp only at hz
        by_cases hrt : r.tested = true
        · simp [hrt] at hz; subst hz; exact fun _ _ h => h
        · simp only [Bool.not_eq_true] at hrt; rw [hrt] at hz
          simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact fun _ _ h => h
    · dsimp only at hz
      by_cases het : e.tested = true
      · simp [het] at hz; subst hz; exact fun _ _ h => h
      · simp only [Bool.not_eq_true] at het; rw [het] at hz
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact fun _ _ h => h
  | revealSpkSk u j =>
    dsimp only at hz
    rcases hfs : kst.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
      _ | ⟨_, bEntry⟩ <;> rw [hfs] at hz
    · simp at hz; subst hz; exact fun _ _ h => h
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz
      intro idx₀ sigPair h
      dsimp only
      rw [spkLookup_map_reveal]
      exact h
  | registerKey sk =>
    dsimp only at hz
    rcases hreg : SignalPqxdh.registerAdvKey P kst.advKeys sk with _ | ⟨pk, advKeys'⟩ <;>
      rw [hreg] at hz
    · simp at hz; subst hz; exact fun _ _ h => h
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact fun _ _ h => h
  | roQuery secrets =>
    simp at hz; subst hz; exact fun _ _ h => h
  | revealDhSecrets =>
    simp at hz; subst hz; exact fun _ _ h => h

/-- Projects `bhInsts` for `CliDriverState` by mapping party states through `CliPartyState.bin`. -/
def projInsts {S : SignalPqxdh.Setup} {l : Nat} (cds : CliDriverState S l) :
    List (ModelDriverInstance S l) :=
  cds.bhInsts.zipWith
    (fun bi gsOpt => { bi with gs := gsOpt.map (mapSt CliPartyState.bin) })
    cds.instGs

/-- Project `CliDriverState` to `ModelDriverState` for `cliDrvImpl`. -/
def projCliDrv {S : SignalPqxdh.Setup} {l : Nat} (cds : CliDriverState S l) :
    ModelDriverState S l :=
  { cds.toModelDriverState with bhInsts := projInsts cds }

/-- Driver + `KeyInd` state invariant for the retained-directory CLI game. -/
def CliRetainedStateInv {S : SignalPqxdh.Setup} {l : Nat} (W : PEParams)
    (cds : CliDriverState S l) (kst : SignalPqxdh.KeyIndState S) : Prop :=
  cds.instGs.length = cds.bhInsts.length ∧
  ∀ (i : Nat) (bi : ModelDriverInstance S l), cds.bhInsts[i]? = some bi →
    (∃ gsOpt : Option (SM.GameState CliPartyState (Plain l) Bytes),
      cds.instGs[i]? = some gsOpt ∧
      bi.gs = gsOpt.map (cliMapGameState CliPartyState.bin)) ∧
    (∃ sigPair, spkLookup (bi.respSlot.1.val, bi.respSlot.2.val) kst.spkBundles = some sigPair) ∧
    (∀ gs : SM.GameState CliPartyState (Plain l) Bytes,
      cds.instGs[i]? = some (some gs) →
      ∀ P, CliPartyDirInv W bi (cliPqSigsOf kst bi) P (gs.st P))

theorem cliRetainedStateInv_init {S : SignalPqxdh.Setup} {l : Nat} (W : PEParams)
    (kst : SignalPqxdh.KeyIndState S) :
    CliRetainedStateInv (S := S) (l := l) W {} kst :=
  ⟨rfl, fun i _ h => by simp at h⟩

theorem cliRetainedStateInv_of_spkLookup {S : SignalPqxdh.Setup} {l : Nat} {W : PEParams}
    {cds cds' : CliDriverState S l} {kst kst' : SignalPqxdh.KeyIndState S}
    (hInv : CliRetainedStateInv W cds kst)
    (hbi : cds'.bhInsts = cds.bhInsts) (higs : cds'.instGs = cds.instGs)
    (hspk : ∀ idx₀ sigPair, spkLookup idx₀ kst.spkBundles = some sigPair →
      spkLookup idx₀ kst'.spkBundles = some sigPair) :
    CliRetainedStateInv W cds' kst' := by
  refine ⟨by rw [higs, hbi, hInv.1], fun i bi hget => ?_⟩
  rw [hbi] at hget
  obtain ⟨⟨gsOpt, hgsOpt, hbigs⟩, ⟨sigPair, hsig⟩, hdir⟩ := hInv.2 i bi hget
  have hsig' := hspk _ _ hsig
  refine ⟨⟨gsOpt, by rw [higs]; exact hgsOpt, hbigs⟩, ⟨sigPair, hsig'⟩, fun gs hgs P => ?_⟩
  rw [higs] at hgs
  rw [cliPqSigsOf_eq_of_spkLookup (h₁' := hsig) (h₂' := hsig')]
  exact hdir gs hgs P

private theorem zipWith_length_of_eq {α β γ : Type} (f : α → β → γ) :
    ∀ (xs : List α) (ys : List β), ys.length = xs.length → (xs.zipWith f ys).length = xs.length
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
    simp only [List.length_cons, List.zipWith_cons_cons] at h ⊢
    rw [zipWith_length_of_eq f xs ys (Nat.succ.inj h)]

private theorem zipWith_getElem?_ret {α β γ : Type} (f : α → β → γ) :
    ∀ (xs : List α) (ys : List β) (i : Nat),
      (xs.zipWith f ys)[i]? = match xs[i]?, ys[i]? with
        | some x, some y => some (f x y)
        | _, _ => none
  | [], [], _ => by simp
  | [], _ :: _, _ => by simp
  | _ :: _, [], _ => by simp
  | x :: xs, y :: ys, 0 => rfl
  | _ :: xs, _ :: ys, i + 1 => zipWith_getElem?_ret f xs ys i

private theorem zipWith_append_singleton_ret {α β γ : Type} (f : α → β → γ) :
    ∀ (xs : List α) (ys : List β) (x : α) (y : β),
      ys.length = xs.length →
      (xs ++ [x]).zipWith f (ys ++ [y]) = xs.zipWith f ys ++ [f x y]
  | [], [], _, _, _ => rfl
  | a :: xs, b :: ys, x, y, h => by
    simp only [List.length_cons] at h
    simp [zipWith_append_singleton_ret f xs ys x y (Nat.succ.inj h)]

private theorem zipWith_set_ret {α β γ : Type} (f : α → β → γ) :
    ∀ (xs : List α) (ys : List β) (i : Nat) (x : α) (y : β),
      (xs.set i x).zipWith f (ys.set i y) = (xs.zipWith f ys).set i (f x y)
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, _, _ => by simp
  | _ :: xs, _ :: ys, 0, x, y => rfl
  | a :: xs, b :: ys, i + 1, x, y => by simp [zipWith_set_ret f xs ys i x y]

private theorem zipWith_any_congr_ret {α β γ : Type} (f : α → β → γ) (p : γ → Bool) (q : α → Bool)
    (hpq : ∀ x y, p (f x y) = q x) :
    ∀ (xs : List α) (ys : List β), ys.length = xs.length → (xs.zipWith f ys).any p = xs.any q
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [List.length_cons] at h
    simp [hpq, zipWith_any_congr_ret f p q hpq xs ys (Nat.succ.inj h)]

theorem bhDrvInstClean_projCliDrv {S : SignalPqxdh.Setup} {l : Nat}
    {cds : CliDriverState S l} (hlen : cds.instGs.length = cds.bhInsts.length) (i : Nat) :
    bhDrvInstClean (projCliDrv cds) i = bhDrvInstClean cds.toModelDriverState i := by
  unfold bhDrvInstClean projCliDrv projInsts
  dsimp only
  rw [zipWith_getElem?_ret]
  rcases hbi : cds.bhInsts[i]? with _ | bi
  · rfl
  · have hi : i < cds.instGs.length := hlen ▸ (List.getElem?_eq_some_iff.mp hbi).1
    rw [List.getElem?_eq_getElem hi]
    cases cds.instMeta[i]? <;> rfl

theorem bhDrvGuard_projCliDrv {S : SignalPqxdh.Setup} {l : Nat}
    {cds : CliDriverState S l} (hlen : cds.instGs.length = cds.bhInsts.length)
    (sid : SignalPqxdh.SessionId S) :
    bhDrvGuard (projCliDrv cds) sid = bhDrvGuard cds.toModelDriverState sid := by
  unfold bhDrvGuard projCliDrv projInsts
  dsimp only
  rw [zipWith_any_congr_ret _ _ (fun bi => bi.sid == sid)
    (fun _ _ => rfl) cds.bhInsts cds.instGs hlen]
  cases cds.sends.find? (fun (s, _, _) => s == sid) with
  | none => rfl
  | some sh =>
    rcases sh with ⟨_, bnd, hdr⟩
    dsimp only
    rw [zipWith_any_congr_ret _ _ (fun bi => bi.hdr.ekAPk == hdr.ekAPk)
      (fun _ _ => rfl) cds.bhInsts cds.instGs hlen]

theorem driverSomeInstanceWon_projCliDrv {S : SignalPqxdh.Setup} {l : Nat} {W : PEParams}
    {cds : CliDriverState S l} {kst : SignalPqxdh.KeyIndState S}
    (hInv : CliRetainedStateInv W cds kst) (b : Bool) :
    driverSomeInstanceWon (projCliDrv cds) b = driverSomeInstanceWon cds.toModelDriverState b := by
  unfold driverSomeInstanceWon projCliDrv projInsts
  dsimp only
  have haux : ∀ (xs : List (ModelDriverInstance S l))
      (ys : List (Option (SM.GameState CliPartyState (Plain l) Bytes))),
      ys.length = xs.length →
      (∀ (i : Nat) (bi : ModelDriverInstance S l), xs[i]? = some bi →
        ∃ gsOpt : Option (SM.GameState CliPartyState (Plain l) Bytes),
          ys[i]? = some gsOpt ∧ bi.gs = gsOpt.map (cliMapGameState CliPartyState.bin)) →
      (xs.zipWith (fun bi gsOpt => { bi with gs := gsOpt.map (mapSt CliPartyState.bin) }) ys).any
        (fun bi => match bi.gs with | some gs => gs.b == b && gs.win | none => false) =
      xs.any (fun bi => match bi.gs with | some gs => gs.b == b && gs.win | none => false) := by
    intro xs ys hl hrel
    induction xs generalizing ys with
    | nil => cases ys <;> simp at hl ⊢
    | cons bi xtl ih =>
      rcases ys with _ | ⟨gsOpt, ytl⟩
      · cases hl
      · simp only [List.length_cons] at hl
        obtain ⟨gsOpt', h0, hbigs⟩ := hrel 0 bi rfl
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
        subst h0
        have hhd :
            (match (gsOpt.map (mapSt CliPartyState.bin)) with
              | some gs => gs.b == b && gs.win | none => false) =
            (match bi.gs with | some gs => gs.b == b && gs.win | none => false) := by
          rw [hbigs]; cases gsOpt <;> rfl
        simp only [List.zipWith_cons_cons, List.any_cons, hhd]
        rw [ih ytl (Nat.succ.inj hl) (fun i bi' hi => hrel (i + 1) bi' hi)]
  exact haux cds.bhInsts cds.instGs hInv.1 (fun i bi hi => (hInv.2 i bi hi).1)

/-! ### Driver oracle commutation -/

private theorem bhRunInitiate_withInsts {S : SignalPqxdh.Setup} {l : Nat}
    (P : SignalPqxdh.Primitives) (sid : SignalPqxdh.SessionId S)
    (u : Fin S.N_id) (bnd : SignalPqxdh.PreKeyBundleInput)
    (ds : ModelDriverState S l) (insts : List (ModelDriverInstance S l))
    (kst : SignalPqxdh.KeyIndState S) :
    Prod.map (Prod.map id (fun ds' => { ds' with bhInsts := insts })) id <$>
      (((bhRunInitiate S P sid u bnd false).run ds).run kst) =
      ((bhRunInitiate S P sid u bnd false).run { ds with bhInsts := insts }).run kst ∧
    ∀ z ∈ support (((bhRunInitiate S P sid u bnd false).run ds).run kst),
      z.1.2.bhInsts = ds.bhInsts ∧ z.2.spkBundles = kst.spkBundles := by
  unfold bhRunInitiate
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_get,
    pure_bind, bind_assoc]
  by_cases hs : kst.sessions.any (fun e => e.sid == sid) = true
  · simp [hs]
  · simp only [Bool.not_eq_true] at hs; rw [hs]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hfp : kst.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩ <;>
      rw [hfp]
    · simp
    · dsimp only
      split_ifs
      · simp
      · simp
      · simp only [StateT.run_bind, StateT.run_lift, StateT.run_liftM, StateT.run_pure,
          bind_assoc, pure_bind, map_bind, map_pure, Prod.map_apply, id_eq]
        refine ⟨trivial, fun z hz => ?_⟩
        rw [mem_support_bind_iff] at hz
        obtain ⟨_, _, hz⟩ := hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨rfl, rfl⟩
      · simp only [StateT.run_bind, StateT.run_lift,
          StateT.run_liftM, bind_assoc, pure_bind,
          map_bind]
        refine ⟨bind_congr_of_forall_mem_support _ fun t_init _ => ?_, ?_⟩
        · rcases P.kemEncaps bnd.pqspkB (tapeKemCoins t_init) with _ | ⟨ss, kemCt⟩
          · simp
          · dsimp only
            simp only [StateT.run_bind, StateT.run_lift, StateT.run_liftM,
              bind_assoc, pure_bind, map_bind]
            refine bind_congr_of_forall_mem_support _ fun ⟨drKeyReal, roCache'⟩ _ => ?_
            dsimp only
            rcases SignalPqxdh.keyIndPartnerRandKey? P kst.respSessions _ with _ | dk
            · simp only [StateT.run_bind, StateT.run_lift, StateT.run_liftM,
                StateT.run_set, StateT.run_modify, bind_assoc, pure_bind, map_bind]
              exact bind_congr_of_forall_mem_support _ fun _ _ => by
                cases SignalPqxdh.findHonestPrincipal P kst.principals bnd.ikB <;> simp
            · cases SignalPqxdh.findHonestPrincipal P kst.principals bnd.ikB <;> simp
        · intro z hz
          rw [mem_support_bind_iff] at hz
          obtain ⟨t_init, _, hz⟩ := hz
          rcases hkem : P.kemEncaps bnd.pqspkB (tapeKemCoins t_init) with _ | ⟨ss, kemCt⟩ <;>
            rw [hkem] at hz
          · simp at hz; subst hz; exact ⟨rfl, rfl⟩
          · dsimp only at hz
            simp only [StateT.run_bind, StateT.run_lift, StateT.run_liftM,
              bind_assoc, pure_bind, mem_support_bind_iff] at hz
            obtain ⟨⟨drKeyReal, roCache'⟩, _, hz⟩ := hz
            rcases hpart : SignalPqxdh.keyIndPartnerRandKey? P kst.respSessions _ with _ | dk <;>
              rw [hpart] at hz
            · simp only [StateT.run_bind, StateT.run_lift, StateT.run_liftM,
                StateT.run_set, StateT.run_modify, bind_assoc, pure_bind, mem_support_bind_iff] at hz
              obtain ⟨_, _, hz⟩ := hz
              cases hfh : SignalPqxdh.findHonestPrincipal P kst.principals bnd.ikB <;>
                (simp [hfh] at hz; subst hz; exact ⟨rfl, rfl⟩)
            · cases hfh : SignalPqxdh.findHonestPrincipal P kst.principals bnd.ikB <;>
                (simp [hfh] at hz; subst hz; exact ⟨rfl, rfl⟩)

theorem bhDrvKeyInd_step_proj {S : SignalPqxdh.Setup} {l : Nat} {W : PEParams}
    (P : SignalPqxdh.Primitives) (q : SignalPqxdh.KeyIndQuery S)
    (cds : CliDriverState S l) (kst : SignalPqxdh.KeyIndState S)
    (hInv : CliRetainedStateInv W cds kst) :
    Prod.map (Prod.map id projCliDrv) id <$>
      (((bhLiftCli (bhDrvKeyInd S l P false q)).run cds).run kst) =
      ((bhDrvKeyInd S l P false q).run (projCliDrv cds)).run kst ∧
    ∀ z ∈ support (((bhLiftCli (bhDrvKeyInd S l P false q)).run cds).run kst),
      CliRetainedStateInv W z.1.2 z.2 := by
  have hMirrorProj : ∀ (ds' : ModelDriverState S l) (q' : SignalPqxdh.KeyIndQuery S)
      (r : SignalPqxdh.KeyIndResponse),
      ds'.bhInsts = cds.bhInsts →
      projCliDrv { cds with toModelDriverState := bhDrvMirror ds' q' r } =
        bhDrvMirror { ds' with bhInsts := projInsts cds } q' r := by
    intro ds' q' r hbi
    unfold projCliDrv projInsts bhDrvMirror
    dsimp only
    rw [hbi]
  have hLiftKeyInd : ∀ (q' : SignalPqxdh.KeyIndQuery S),
      Prod.map (Prod.map id projCliDrv) id <$>
        (((bhLiftCli (do
            let r ← StateT.lift (SignalPqxdh.pqxdhKeyIndImpl false S P q')
            modify (fun ds => bhDrvMirror ds q' r); return r)).run cds).run kst) =
        ((do
            let r ← StateT.lift (SignalPqxdh.pqxdhKeyIndImpl false S P q')
            modify (fun ds => bhDrvMirror ds q' r); return r : BHDrvM S l _).run (projCliDrv cds)).run kst ∧
      ∀ z ∈ support (((bhLiftCli (do
            let r ← StateT.lift (SignalPqxdh.pqxdhKeyIndImpl false S P q')
            modify (fun ds => bhDrvMirror ds q' r); return r)).run cds).run kst),
        CliRetainedStateInv W z.1.2 z.2 := by
    intro q'
    unfold bhLiftCli
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_modify,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_bind]
    refine ⟨bind_congr_of_forall_mem_support _ fun rk _ => ?_, ?_⟩
    · rcases rk with ⟨r, kst'⟩
      simp only [map_pure, Prod.map_apply, id_eq]
      rw [hMirrorProj cds.toModelDriverState q' r rfl]
      rfl
    · intro z hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨⟨r, kst'⟩, hrk, hz⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact cliRetainedStateInv_of_spkLookup hInv rfl rfl
        (pqxdhKeyIndImpl_preserves_spkLookup P q' kst hrk)
  cases q with
  | testSession sid =>
    unfold bhDrvKeyInd bhLiftCli
    simp [projCliDrv, hInv]
  | revealDhSecrets =>
    unfold bhDrvKeyInd bhLiftCli
    simp [projCliDrv, hInv]
  | initPrin u =>
    unfold bhDrvKeyInd bhLiftCli
    simp only [Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_lift,
      StateT.run_modify, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc,
      map_bind]
    by_cases hp : kst.principals.any (fun (idx, _) => idx == u.val) = true
    · simp only [hp, ↓reduceIte, StateT.run_pure, pure_bind, map_pure, Prod.map_apply, id_eq]
      rw [hMirrorProj cds.toModelDriverState (.initPrin u) .noneResp rfl]
      refine ⟨rfl, fun z hz => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact cliRetainedStateInv_of_spkLookup hInv rfl rfl (fun _ _ h => h)
    · simp only [Bool.not_eq_true] at hp; rw [hp]
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine ⟨bind_congr_of_forall_mem_support _ fun secIKA0 _ => ?_, ?_⟩
      · simp only [map_pure, Prod.map_apply, id_eq]
        rw [hMirrorProj cds.toModelDriverState (.initPrin u) _ rfl]
        rfl
      · intro z hz
        rw [mem_support_bind_iff] at hz
        obtain ⟨secIKA0, _, hz⟩ := hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact cliRetainedStateInv_of_spkLookup hInv rfl rfl (fun _ _ h => h)
  | initiateOPK u i bnd =>
    unfold bhDrvKeyInd
    have hbase : (projCliDrv cds).toModelDriverBase = cds.toModelDriverState.toModelDriverBase := rfl
    unfold bhLiftCli
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
      pure_bind, hbase]
    split_ifs
    · simp [projCliDrv, hInv]
    · obtain ⟨hinit_eq, hinit_supp⟩ :=
        bhRunInitiate_withInsts P (.sendOPK u i) u bnd cds.toModelDriverState (projInsts cds) kst
      simp only [bind_assoc, map_bind]
      let stepL :
          (SignalPqxdh.KeyIndResponse × ModelDriverState S l) × SignalPqxdh.KeyIndState S →
            ProbComp ((SignalPqxdh.KeyIndResponse × CliDriverState S l) × SignalPqxdh.KeyIndState S) :=
        fun z =>
          let cds' : CliDriverState S l :=
            { cds with toModelDriverState := bhDrvMirror z.1.2 (.initiateOPK u i bnd) z.1.1 }
          pure ((z.1.1, cds'), z.2)
      have hlhs :
          (Prod.map (Prod.map id projCliDrv) id <$>
            ((((bhRunInitiate S P (.sendOPK u i) u bnd false).run cds.toModelDriverState).run kst) >>= stepL)) =
          ((((bhRunInitiate S P (.sendOPK u i) u bnd false).run { cds.toModelDriverState with bhInsts := projInsts cds }).run kst) >>=
            fun w => pure (((w.1.1, bhDrvMirror w.1.2 (.initiateOPK u i bnd) w.1.1), w.2))) := by
        rw [← hinit_eq, map_bind, bind_map_left]
        exact bind_congr_of_forall_mem_support _ fun z hz => by
          obtain ⟨hbi, _⟩ := hinit_supp z hz
          simp only [stepL, map_pure, Prod.map_apply, id_eq]
          rw [hMirrorProj z.1.2 (.initiateOPK u i bnd) z.1.1 hbi]
          rfl
      refine ⟨by simpa [stepL, projCliDrv, map_eq_bind_pure_comp, bind_assoc] using hlhs, ?_⟩
      intro z hz
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨hbi, hspk⟩ := hinit_supp w hw
      exact cliRetainedStateInv_of_spkLookup hInv hbi rfl (fun _ _ h => by rw [hspk]; exact h)
  | initiateNoOPK u i bnd =>
    unfold bhDrvKeyInd
    have hbase : (projCliDrv cds).toModelDriverBase = cds.toModelDriverState.toModelDriverBase := rfl
    unfold bhLiftCli
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
      pure_bind, hbase]
    split_ifs
    · simp [projCliDrv, hInv]
    · obtain ⟨hinit_eq, hinit_supp⟩ :=
        bhRunInitiate_withInsts P (.sendNoOPK u i) u bnd cds.toModelDriverState (projInsts cds) kst
      simp only [bind_assoc, map_bind]
      let stepL :
          (SignalPqxdh.KeyIndResponse × ModelDriverState S l) × SignalPqxdh.KeyIndState S →
            ProbComp ((SignalPqxdh.KeyIndResponse × CliDriverState S l) × SignalPqxdh.KeyIndState S) :=
        fun z =>
          let cds' : CliDriverState S l :=
            { cds with toModelDriverState := bhDrvMirror z.1.2 (.initiateNoOPK u i bnd) z.1.1 }
          pure ((z.1.1, cds'), z.2)
      have hlhs :
          (Prod.map (Prod.map id projCliDrv) id <$>
            ((((bhRunInitiate S P (.sendNoOPK u i) u bnd false).run cds.toModelDriverState).run kst) >>= stepL)) =
          ((((bhRunInitiate S P (.sendNoOPK u i) u bnd false).run { cds.toModelDriverState with bhInsts := projInsts cds }).run kst) >>=
            fun w => pure (((w.1.1, bhDrvMirror w.1.2 (.initiateNoOPK u i bnd) w.1.1), w.2))) := by
        rw [← hinit_eq, map_bind, bind_map_left]
        exact bind_congr_of_forall_mem_support _ fun z hz => by
          obtain ⟨hbi, _⟩ := hinit_supp z hz
          simp only [stepL, map_pure, Prod.map_apply, id_eq]
          rw [hMirrorProj z.1.2 (.initiateNoOPK u i bnd) z.1.1 hbi]
          rfl
      refine ⟨by simpa [stepL, projCliDrv, map_eq_bind_pure_comp, bind_assoc] using hlhs, ?_⟩
      intro z hz
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨hbi, hspk⟩ := hinit_supp w hw
      exact cliRetainedStateInv_of_spkLookup hInv hbi rfl (fun _ _ h => by rw [hspk]; exact h)
  | acceptOPK k j o hdr =>
    unfold bhDrvKeyInd
    dsimp only
    have hbase : (projCliDrv cds).toModelDriverBase = cds.toModelDriverBase := rfl
    by_cases hok : bhDrvAcceptIkOk cds.toModelDriverBase hdr = true
    · have h1 := hLiftKeyInd (.acceptOPK k j o hdr)
      unfold bhLiftCli at h1 ⊢
      simpa [StateT.run_bind, StateT.run_get, pure_bind, hbase, hok] using h1
    · simp only [Bool.not_eq_true] at hok
      unfold bhLiftCli
      simp [hok, projCliDrv, hInv]
  | acceptNoOPK k j l hdr =>
    unfold bhDrvKeyInd
    dsimp only
    have hbase : (projCliDrv cds).toModelDriverBase = cds.toModelDriverBase := rfl
    by_cases hok : bhDrvAcceptIkOk cds.toModelDriverBase hdr = true
    · have h1 := hLiftKeyInd (.acceptNoOPK k j l hdr)
      unfold bhLiftCli at h1 ⊢
      simpa [StateT.run_bind, StateT.run_get, pure_bind, hbase, hok] using h1
    · simp only [Bool.not_eq_true] at hok
      unfold bhLiftCli
      simp [hok, projCliDrv, hInv]
  | roQuery secrets =>
    unfold bhDrvKeyInd bhLiftCli
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_liftM,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_bind]
    refine ⟨bind_congr_of_forall_mem_support _ fun _ _ => by simp [projCliDrv], ?_⟩
    intro z hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨⟨_, _⟩, _, hz⟩ := hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact cliRetainedStateInv_of_spkLookup hInv rfl rfl (fun _ _ h => h)
  | corruptIK u =>
    unfold bhDrvKeyInd
    dsimp only
    have hmeta : (projCliDrv cds).instMeta = cds.toModelDriverState.instMeta := rfl
    by_cases hprom : bhNoOpkRespPromoted cds.toModelDriverState.instMeta u = true
    · unfold bhLiftCli
      simp [hprom, projCliDrv, hInv]
    · simp only [Bool.not_eq_true] at hprom
      have h1 := hLiftKeyInd (.corruptIK u)
      unfold bhLiftCli at h1 ⊢
      simpa [StateT.run_bind, StateT.run_get, pure_bind, hmeta, hprom] using h1
  | genSPK u j => exact hLiftKeyInd (.genSPK u j)
  | genOPK u j o => exact hLiftKeyInd (.genOPK u j o)
  | revealSessionKey sid => exact hLiftKeyInd (.revealSessionKey sid)
  | revealSpkSk u j => exact hLiftKeyInd (.revealSpkSk u j)
  | registerKey sk => exact hLiftKeyInd (.registerKey sk)

theorem cliDrvStart_step_proj {S : SignalPqxdh.Setup} {l : Nat}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W)
    (P : SignalPqxdh.Primitives) (mode : BHDrvMode S) (sid : SignalPqxdh.SessionId S)
    (cds : CliDriverState S l) (kst : SignalPqxdh.KeyIndState S)
    (hInv : CliRetainedStateInv W cds kst) :
    Prod.map (Prod.map id projCliDrv) id <$>
      (((Dir.cliDrvStart S l P run W mode sid).run cds).run kst) =
      ((cliDrvStart S l P run W mode sid).run (projCliDrv cds)).run kst ∧
    ∀ z ∈ support (((Dir.cliDrvStart S l P run W mode sid).run cds).run kst),
      CliRetainedStateInv W z.1.2 z.2 := by
  have hg := bhDrvGuard_projCliDrv hInv.1 sid
  have htapes : (projCliDrv cds).initTapes = cds.initTapes := rfl
  have hlen_proj : (projCliDrv cds).bhInsts.length = cds.bhInsts.length :=
    zipWith_length_of_eq _ cds.bhInsts cds.instGs hInv.1
  rw [Dir.cliDrvStart_eq]
  unfold cliDrvStart
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hg]
  rcases bhDrvGuard cds.toModelDriverState sid with _ | ⟨hdr, bnd, u_resp, j_resp⟩
  · simp [hInv]
  · dsimp only
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_liftM, StateT.run_get,
      bind_assoc, pure_bind, map_bind]
    have finishStart : ∀ (st : SignalPqxdh.KeyIndState S)
        (hspk_st : ∀ idx₀ sigPair, spkLookup idx₀ kst.spkBundles = some sigPair →
          spkLookup idx₀ st.spkBundles = some sigPair)
        (t_init : List.Vector (BitVec 8) 160) (t_dr : List.Vector (BitVec 8) 32)
        (u_init : Fin S.N_id) (initPrinEntry respPrinEntry : SignalPqxdh.PrincipalEntry)
        (respSpkEntry : SignalPqxdh.SpkBundleEntry)
        (hfind_spk : st.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) =
          some ((u_resp.val, j_resp.val), respSpkEntry) ∨
          ∃ k0, st.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) =
            some (k0, respSpkEntry))
        (opkOpt : Option (Nat × SignalPqxdh.Bytes))
        (spkSk : SignalPqxdh.Bytes),
        let mDir : CliDrvM S l (Option Nat) := do
          let some meA := mkMeEStrict u_init.val initPrinEntry.secIKA0 | return none
          let some meB := mkMeEStrict u_resp.val respPrinEntry.secIKA0 | return none
          let some keysB := mkKeysEStrict j_resp.val respSpkEntry opkOpt | return none
          let some bundleE := mkBundleEStrict u_resp.val bnd | return none
          let dA : PqParty :=
            { party := .A, me := meA, peerId := some (bhIdKeyOf bnd.ikB), session := none,
              signed := [], oneTime := [], kyberOneTime := [], kyberLastResort := [] }
          let some stA0 := Dir.cliPqInit run W dA bundleE (appendInitiateTape t_init t_dr) | return none
          let stB0Bin : BinState := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
          let bi0 : ModelDriverInstance S l :=
            { sid := sid, hdr := hdr, idBBytes := bnd.ikB, respSlot := (u_resp, j_resp),
              meA := meA, meB := meB, keysB := keysB, stA0 := stA0.bin, stB0 := stB0Bin, gs := none }
          let stB0 := cliPartyStateB0 W bi0 (cliPqSigsOf st bi0)
          let scheme := Dir.cliPqScheme run l bi0 stA0 stB0
          let gsDir := (mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB spkSk).map
            (fun b => SM.initState scheme.sendPart () b)
          let gs := gsDir.map (cliMapGameState CliPartyState.bin)
          let bi := { bi0 with gs := gs }
          let im0 : ModelDriverInstanceMeta S :=
            { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := bnd.opkB?.map Prod.fst }
          StateT.lift (set st)
          set { cds with bhInsts := cds.bhInsts ++ [bi], instMeta := cds.instMeta ++ [im0],
                         instGs := cds.instGs ++ [gsDir] }
          return some cds.bhInsts.length
        let mProj : BHDrvM S l (Option Nat) := do
          let some meA := mkMeEStrict u_init.val initPrinEntry.secIKA0 | return none
          let some meB := mkMeEStrict u_resp.val respPrinEntry.secIKA0 | return none
          let some keysB := mkKeysEStrict j_resp.val respSpkEntry opkOpt | return none
          let some bundleE := mkBundleEStrict u_resp.val bnd | return none
          let dA : PqParty :=
            { party := .A, me := meA, peerId := some (bhIdKeyOf bnd.ikB), session := none,
              signed := [], oneTime := [], kyberOneTime := [], kyberLastResort := [] }
          let some stA0 := cliPqInit run W dA bundleE (appendInitiateTape t_init t_dr) | return none
          let stB0 : BinState := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
          let bi0 : ModelDriverInstance S l :=
            { sid := sid, hdr := hdr, idBBytes := bnd.ikB, respSlot := (u_resp, j_resp),
              meA := meA, meB := meB, keysB := keysB, stA0 := stA0, stB0 := stB0, gs := none }
          let scheme := cliPqScheme run W l bi0 (cliPqSigsOf st bi0) stA0 stB0
          let gs := (mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB spkSk).map
            (fun b => SM.initState scheme.sendPart () b)
          let bi := { bi0 with gs := gs }
          let im0 : ModelDriverInstanceMeta S :=
            { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := bnd.opkB?.map Prod.fst }
          StateT.lift (set st)
          set { projCliDrv cds with bhInsts := (projCliDrv cds).bhInsts ++ [bi],
                                    instMeta := (projCliDrv cds).instMeta ++ [im0] }
          return some (projCliDrv cds).bhInsts.length
        Prod.map (Prod.map id projCliDrv) id <$> ((mDir.run cds).run kst) =
          (mProj.run (projCliDrv cds)).run kst ∧
        ∀ z ∈ support ((mDir.run cds).run kst), CliRetainedStateInv W z.1.2 z.2 := by
      intro st hspk_st t_init t_dr u_init initPrinEntry respPrinEntry respSpkEntry hfind_spk
        opkOpt spkSk mDir mProj
      have hInv_st : CliRetainedStateInv W cds st :=
        cliRetainedStateInv_of_spkLookup hInv rfl rfl hspk_st
      dsimp only [mDir, mProj]
      rcases mkMeEStrict u_init.val initPrinEntry.secIKA0 with _ | meA
      · simp [hInv]
      · rcases mkMeEStrict u_resp.val respPrinEntry.secIKA0 with _ | meB
        · simp [hInv]
        · rcases mkKeysEStrict j_resp.val respSpkEntry opkOpt with _ | keysB
          · simp [hInv]
          · rcases mkBundleEStrict u_resp.val bnd with _ | bundleE
            · simp [hInv]
            · dsimp only
              let stB0Bin : BinState := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
              let biDummy : ModelDriverInstance S l :=
                { sid := sid, hdr := hdr, idBBytes := bnd.ikB, respSlot := (u_resp, j_resp),
                  meA := meA, meB := meB, keysB := keysB, stA0 := stB0Bin, stB0 := stB0Bin, gs := none }
              obtain ⟨hinit_eq, hinit_inv⟩ :=
                cliPqInit_dir_eq_proj hCli biDummy (cliPqSigsOf st biDummy) bundleE
                  (appendInitiateTape t_init t_dr)
              dsimp only [cliPqDirA, biDummy] at hinit_eq
              rw [← hinit_eq]
              rcases hinit : Dir.cliPqInit run W
                  { party := .A, me := meA, peerId := some (bhIdKeyOf bnd.ikB),
                    session := none, signed := [], oneTime := [], kyberOneTime := [],
                    kyberLastResort := [] }
                  bundleE (appendInitiateTape t_init t_dr) with _ | stA0
              · simp only [Option.map_none]
                simp [hInv]
              · simp only [Option.map_some]
                let bi0 : ModelDriverInstance S l :=
                  { sid := sid, hdr := hdr, idBBytes := bnd.ikB, respSlot := (u_resp, j_resp),
                    meA := meA, meB := meB, keysB := keysB, stA0 := stA0.bin, stB0 := stB0Bin, gs := none }
                let stB0 := cliPartyStateB0 W bi0 (cliPqSigsOf st bi0)
                let schemeDir := Dir.cliPqScheme run l bi0 stA0 stB0
                let schemeProj := cliPqScheme run W l bi0 (cliPqSigsOf st bi0) stA0.bin stB0Bin
                have hgs_eq : ∀ b : Bool,
                    mapSt CliPartyState.bin (SM.initState schemeDir.sendPart () b) =
                      SM.initState schemeProj.sendPart () b := by
                  intro b
                  unfold mapSt SM.initState
                  dsimp only [schemeDir, schemeProj, Dir.cliPqScheme, cliPqScheme, SMSchemeR.sendPart]
                  congr 1
                  funext P; cases P <;> rfl
                let gsDir := (mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB spkSk).map
                  (fun b => SM.initState schemeDir.sendPart () b)
                have hgsProj : gsDir.map (mapSt CliPartyState.bin) =
                    (mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB spkSk).map
                      (fun b => SM.initState schemeProj.sendPart () b) := by
                  dsimp only [gsDir]
                  cases mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB spkSk with
                  | none => rfl
                  | some b => exact congrArg some (hgs_eq b)
                simp only [StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
                  bind_assoc, pure_bind, map_pure, Prod.map_apply, id_eq, hlen_proj]
                let gsProjVal := (mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB spkSk).map
                  (fun b => SM.initState schemeProj.sendPart () b)
                let im0 : ModelDriverInstanceMeta S :=
                  { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := bnd.opkB?.map Prod.fst }
                let cdsNext : CliDriverState S l :=
                  { cds with bhInsts := cds.bhInsts ++ [{ bi0 with gs := gsDir.map (cliMapGameState CliPartyState.bin) }],
                             instMeta := cds.instMeta ++ [im0],
                             instGs := cds.instGs ++ [gsDir] }
                let dsProjNext : ModelDriverState S l :=
                  { projCliDrv cds with bhInsts := (projCliDrv cds).bhInsts ++ [{ bi0 with gs := gsProjVal }],
                                        instMeta := (projCliDrv cds).instMeta ++ [im0] }
                have hproj_eq : projCliDrv cdsNext = dsProjNext := by
                  unfold projCliDrv projInsts cdsNext dsProjNext
                  dsimp only
                  have hzip := zipWith_append_singleton_ret
                    (fun (bi : ModelDriverInstance S l)
                         (gsOpt : Option (SM.GameState CliPartyState (Plain l) Bytes)) =>
                      { bi with gs := gsOpt.map (mapSt CliPartyState.bin) })
                    cds.bhInsts cds.instGs
                    { bi0 with gs := gsDir.map (cliMapGameState CliPartyState.bin) }
                    gsDir hInv_st.1
                  rw [hzip, hgsProj]
                  rfl
                refine ⟨by rw [hproj_eq], ?_⟩
                intro z hz
                simp only [support_pure, Set.mem_singleton_iff] at hz
                subst hz
                refine ⟨by simp [hInv_st.1], fun i bi' hi => ?_⟩
                by_cases hlt : i < cds.bhInsts.length
                · have hi_old : cds.bhInsts[i]? = some bi' := by
                    rwa [List.getElem?_append_left hlt] at hi
                  have hlt_gs : i < cds.instGs.length := hInv_st.1 ▸ hlt
                  obtain ⟨⟨gsOpt, hgsOpt, hbigs⟩, hsig, hdir⟩ := hInv_st.2 i bi' hi_old
                  refine ⟨⟨gsOpt, ?_, hbigs⟩, hsig, fun gs hgs P => ?_⟩
                  · rw [List.getElem?_append_left hlt_gs]; exact hgsOpt
                  · rw [List.getElem?_append_left hlt_gs] at hgs
                    exact hdir gs hgs P
                · have hge : cds.bhInsts.length ≤ i := Nat.le_of_not_lt hlt
                  rw [List.getElem?_append_right hge] at hi
                  rcases Nat.eq_zero_or_pos (i - cds.bhInsts.length) with hi0 | hipos
                  · have hi_eq : i = cds.bhInsts.length := by omega
                    subst hi_eq
                    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hi
                    subst hi
                    have higs_end : (cds.instGs ++ [gsDir])[cds.bhInsts.length]? = some gsDir := by
                      rw [← hInv_st.1, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
                    have hsig_new : ∃ sigPair,
                        spkLookup (u_resp.val, j_resp.val) st.spkBundles = some sigPair := by
                      rcases hfind_spk with hf | ⟨k0, hf⟩ <;>
                        exact ⟨(respSpkEntry.spkSig, respSpkEntry.pqspkSig),
                          by unfold spkLookup; rw [hf]; rfl⟩
                    refine ⟨⟨gsDir, higs_end, rfl⟩, hsig_new, fun gs hgs P => ?_⟩
                    rw [higs_end] at hgs
                    simp only [Option.some.injEq] at hgs
                    rcases hm : mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB spkSk with _ | b_m <;>
                      simp only [gsDir, hm, Option.map] at hgs
                    · cases hgs
                    · simp only [Option.some.injEq] at hgs
                      subst hgs
                      cases P with
                      | A =>
                        have hA : CliPartyDirInv W biDummy (cliPqSigsOf st biDummy) .A stA0 :=
                          hinit_inv stA0 hinit
                        exact hA
                      | B => exact Or.inl rfl
                  · cases hp : i - cds.bhInsts.length with
                    | zero => omega
                    | succ n => simp [hp] at hi
    refine ⟨bind_congr_of_forall_mem_support _ fun rk₁ h₁ => ?_, ?_⟩
    · rcases rk₁ with ⟨r₁, kst₁⟩
      have hspk₁ := pqxdhKeyIndImpl_preserves_spkLookup P (.testSession sid) kst h₁
      cases r₁ <;>
        try (dsimp only; simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq])
      rename_i dk_unused
      dsimp only
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_liftM,
        bind_assoc, pure_bind, map_bind]
      refine bind_congr_of_forall_mem_support _ fun rk₂ h₂ => ?_
      rcases rk₂ with ⟨r₂, st⟩
      have hspk₂ : ∀ idx₀ sigPair, spkLookup idx₀ kst.spkBundles = some sigPair →
          spkLookup idx₀ st.spkBundles = some sigPair :=
        fun idx₀ sigPair h => pqxdhKeyIndImpl_preserves_spkLookup P (.revealSpkSk u_resp j_resp) kst₁ h₂
          idx₀ sigPair (hspk₁ idx₀ sigPair h)
      cases r₂ <;>
        try (dsimp only; simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq])
      rename_i spkSk
      dsimp only
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_liftM,
        bind_assoc, pure_bind, map_bind,
        htapes]
      refine bind_congr_of_forall_mem_support _ fun t_dr _ => ?_
      rcases hft : cds.initTapes.find? (fun x => x.1 == sid) with
        _ | ⟨_, u_init, _, t_init⟩ <;> rw [hft]
      · dsimp only; simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
      · dsimp only
        rcases hfp₁ : st.principals.find? (fun x => x.1 == u_init.val) with
          _ | ⟨_, initPrinEntry⟩ <;> rw [hfp₁]
        · dsimp only; simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
        · dsimp only
          rcases hfp₂ : st.principals.find? (fun x => x.1 == u_resp.val) with
            _ | ⟨_, respPrinEntry⟩ <;> rw [hfp₂]
          · dsimp only; simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
          · dsimp only
            rcases hf_spk : st.spkBundles.find? (fun x => x.1 == (u_resp.val, j_resp.val)) with
              _ | ⟨k0, respSpkEntry⟩ <;> rw [hf_spk]
            · dsimp only; simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
            · dsimp only
              cases hdr.opkId? with
              | none =>
                dsimp only
                exact (finishStart st hspk₂ t_init t_dr u_init initPrinEntry respPrinEntry
                  respSpkEntry (Or.inr ⟨k0, hf_spk⟩) none spkSk).1
              | some opkId =>
                dsimp only
                rcases hf_opk : st.opkEntries.find?
                    (fun x => x.1 == (u_resp.val, j_resp.val, opkId.toNat)) with
                  _ | ⟨_, oe⟩ <;> rw [hf_opk]
                · dsimp only; simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
                · dsimp only
                  exact (finishStart st hspk₂ t_init t_dr u_init initPrinEntry respPrinEntry
                    respSpkEntry (Or.inr ⟨k0, hf_spk⟩) (some (opkId.toNat, oe.opkSk)) spkSk).1
    · intro z hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨⟨r₁, kst₁⟩, h₁, hz⟩ := hz
      have hspk₁ := pqxdhKeyIndImpl_preserves_spkLookup P (.testSession sid) kst h₁
      cases r₁ <;>
        try (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz;
             subst hz; exact hInv)
      dsimp only at hz
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_liftM,
        bind_assoc, pure_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨r₂, st⟩, h₂, hz⟩ := hz
      have hspk₂ : ∀ idx₀ sigPair, spkLookup idx₀ kst.spkBundles = some sigPair →
          spkLookup idx₀ st.spkBundles = some sigPair :=
        fun idx₀ sigPair h => pqxdhKeyIndImpl_preserves_spkLookup P (.revealSpkSk u_resp j_resp) kst₁ h₂
          idx₀ sigPair (hspk₁ idx₀ sigPair h)
      cases r₂ <;>
        try (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz;
             subst hz; exact hInv)
      rename_i spkSk
      dsimp only at hz
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_liftM,
        bind_assoc, pure_bind, mem_support_bind_iff] at hz
      obtain ⟨t_dr, _, hz⟩ := hz
      rcases hft : cds.initTapes.find? (fun (s, _, _, _) => s == sid) with
        _ | ⟨_, u_init, _, t_init⟩ <;> rw [hft] at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hInv
      · dsimp only at hz
        rcases hfp₁ : st.principals.find? (fun (idx, _) => idx == u_init.val) with
          _ | ⟨_, initPrinEntry⟩ <;> rw [hfp₁] at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hInv
        · dsimp only at hz
          rcases hfp₂ : st.principals.find? (fun (idx, _) => idx == u_resp.val) with
            _ | ⟨_, respPrinEntry⟩ <;> rw [hfp₂] at hz
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hInv
          · rcases hf_spk : st.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) with
              _ | ⟨k0, respSpkEntry⟩ <;> rw [hf_spk] at hz
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hInv
            · dsimp only at hz
              cases hopk : hdr.opkId? <;> rw [hopk] at hz
              · dsimp only at hz
                exact (finishStart st hspk₂ t_init t_dr u_init initPrinEntry respPrinEntry
                  respSpkEntry (Or.inr ⟨k0, hf_spk⟩) none spkSk).2 z hz
              · rename_i opkId
                dsimp only at hz
                rcases hf_opk : st.opkEntries.find?
                    (fun (idx, _) => idx == (u_resp.val, j_resp.val, opkId.toNat)) with
                  _ | ⟨_, oe⟩ <;> rw [hf_opk] at hz
                · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
                  subst hz; exact hInv
                · dsimp only at hz
                  exact (finishStart st hspk₂ t_init t_dr u_init initPrinEntry respPrinEntry
                    respSpkEntry (Or.inr ⟨k0, hf_spk⟩) (some (opkId.toNat, oe.opkSk)) spkSk).2 z hz

private theorem bhAlignTransForBob_mapSt {St₁ St₂ Msg : Type} (φ : St₁ → St₂)
    (bobAcc : Bool) (regId : BitVec 32) (hdr : SignalPqxdh.HandshakeHdr) (c : Bytes)
    (gs : SM.GameState St₁ Msg Bytes) :
    bhAlignTransForBob bobAcc regId hdr c (mapSt φ gs) =
      mapSt φ (bhAlignTransForBob bobAcc regId hdr c gs) := by
  unfold bhAlignTransForBob
  split_ifs
  · rfl
  · cases bhPartneredInnerBytes true regId hdr c <;> rfl

private theorem bhAlignTransForBob_st {St Msg : Type}
    (bobAcc : Bool) (regId : BitVec 32) (hdr : SignalPqxdh.HandshakeHdr) (c : Bytes)
    (gs : SM.GameState St Msg Bytes) :
    (bhAlignTransForBob bobAcc regId hdr c gs).st = gs.st := by
  unfold bhAlignTransForBob
  split_ifs
  · rfl
  · cases bhPartneredInnerBytes true regId hdr c <;> rfl

theorem cliRunStdSM_step_proj {S : SignalPqxdh.Setup} {l : Nat} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hl : l < 10 ^ 6)
    (qep : Nat) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (cds : CliDriverState S l) (kst : SignalPqxdh.KeyIndState S)
    (hInv : CliRetainedStateInv W cds kst)
    (i : Nat) (bi : ModelDriverInstance S l) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState CliPartyState (Plain l) Bytes)
    (hbi : cds.bhInsts[i]? = some bi) (higs : cds.instGs[i]? = some (some gs))
    (q : (cliGameSmSpec l (BitVec 512)).Domain) :
    let biProj : ModelDriverInstance S l := { bi with gs := some (mapSt CliPartyState.bin gs) }
    Prod.map (Prod.map id projCliDrv) id <$>
      (((Dir.cliRunStdSM S l run qep decT encT cds i bi im gs q).run cds).run kst) =
      ((cliRunStdSM S l run W qep decT encT (projCliDrv cds) i biProj im
          (mapSt CliPartyState.bin gs) q).run (projCliDrv cds)).run kst ∧
    ∀ z ∈ support (((Dir.cliRunStdSM S l run qep decT encT cds i bi im gs q).run cds).run kst),
      CliRetainedStateInv W z.1.2 z.2 := by
  intro biProj
  obtain ⟨_, hsig, hdir_all⟩ := hInv.2 i bi hbi
  have hGs : ∀ P, CliPartyDirInv W bi (cliPqSigsOf kst bi) P (gs.st P) := hdir_all gs higs
  have hsigs_biProj : cliPqSigsOf kst biProj = cliPqSigsOf kst bi := rfl
  have hstep : ∀ (q₀ : (cliGameSmSpec l (BitVec 512)).Domain)
      (gsIn : SM.GameState CliPartyState (Plain l) Bytes)
      (gsProjIn : SM.GameState BinState (Plain l) Bytes)
      (fDir : (cliGameSmSpec l (BitVec 512)).Range q₀ × SM.GameState CliPartyState (Plain l) Bytes →
        SM.GameState CliPartyState (Plain l) Bytes)
      (fProj : (cliGameSmSpec l (BitVec 512)).Range q₀ × SM.GameState BinState (Plain l) Bytes →
        SM.GameState BinState (Plain l) Bytes),
      gsProjIn = mapSt CliPartyState.bin gsIn →
      gsIn.st = gs.st →
      (∀ r gsOut,
        mapSt CliPartyState.bin (fDir (r, gsOut)) = fProj (r, mapSt CliPartyState.bin gsOut) ∧
        (fDir (r, gsOut)).st = gsOut.st) →
      (((cliOracleImplR CliPartyState.bin
          (Dir.cliPqScheme run l bi (gs.st .A) (gs.st .B))
          (2 + 1) qep (cliConfigSpkS decT encT) q₀).run gsIn >>= fun a =>
        pure ((a.1, projCliDrv
          { cds with
            bhInsts := cds.bhInsts.set i { bi with gs := some (cliMapGameState CliPartyState.bin (fDir a)) },
            instMeta := cds.instMeta.set i (bhMetaAfterSM cds.toModelDriverState bi im q₀ a.1),
            instGs := cds.instGs.set i (some (fDir a)) }), kst)) =
       ((SM.oracleImplR
          (cliPqScheme run W l biProj (cliPqSigsOf kst bi) biProj.stA0 biProj.stB0)
          (2 + 1) qep (bhConfigSpkS decT encT) q₀).run gsProjIn >>= fun a =>
        pure ((a.1,
          { projCliDrv cds with
            bhInsts := (projCliDrv cds).bhInsts.set i { biProj with gs := some (fProj a) },
            instMeta := (projCliDrv cds).instMeta.set i (bhMetaAfterSM (projCliDrv cds) biProj im q₀ a.1) }),
          kst))) ∧
      ∀ z ∈ support
        ((cliOracleImplR CliPartyState.bin
          (Dir.cliPqScheme run l bi (gs.st .A) (gs.st .B))
          (2 + 1) qep (cliConfigSpkS decT encT) q₀).run gsIn >>= fun a =>
        pure ((a.1,
          { cds with
            bhInsts := cds.bhInsts.set i { bi with gs := some (cliMapGameState CliPartyState.bin (fDir a)) },
            instMeta := cds.instMeta.set i (bhMetaAfterSM cds.toModelDriverState bi im q₀ a.1),
            instGs := cds.instGs.set i (some (fDir a)) }), kst)),
        CliRetainedStateInv W z.1.2 z.2 := by
    intro q₀ gsIn gsProjIn fDir fProj hgsIn_map hgsIn_st hpost
    have hGsIn : ∀ P, CliPartyDirInv W bi (cliPqSigsOf kst bi) P (gsIn.st P) := fun P => by
      rw [hgsIn_st]; exact hGs P
    obtain ⟨horacle_eq, horacle_inv⟩ :=
      cliOracleImplR_step hCli hl qep decT encT bi (some (mapSt CliPartyState.bin gs))
        (cliPqSigsOf kst bi) (gs.st .A) (gs.st .B) bi.stA0 bi.stB0 gsIn hGsIn q₀
    subst hgsIn_map
    have hscheme_eq : cliPqScheme run W l biProj (cliPqSigsOf kst bi) biProj.stA0 biProj.stB0 =
        cliPqScheme run W l biProj (cliPqSigsOf kst bi) bi.stA0 bi.stB0 := rfl
    rw [hscheme_eq, ← horacle_eq, bind_map_left]
    refine ⟨bind_congr_of_forall_mem_support _ fun ⟨r, gsOut⟩ _ => ?_, ?_⟩
    · obtain ⟨hgs'_map, _⟩ := hpost r gsOut
      have him : bhMetaAfterSM (projCliDrv cds) biProj im q₀ r =
          bhMetaAfterSM cds.toModelDriverState bi im q₀ r := rfl
      dsimp only [Prod.map, id]
      rw [him]
      congr 3
      unfold projCliDrv projInsts cliMapGameState
      dsimp only [Option.map]
      rw [zipWith_set_ret]
      dsimp only [Option.map]
      rw [hgs'_map]
    · intro z hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨⟨r, gsOut⟩, hro, hz⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨_, hgs'_st⟩ := hpost r gsOut
      have hGsOut := horacle_inv (r, gsOut) hro
      have hlt_bi : i < cds.bhInsts.length := by
        by_contra hcon
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hcon)] at hbi
        cases hbi
      have hlt_gs : i < cds.instGs.length := hInv.1 ▸ hlt_bi
      refine ⟨by simp [hInv.1], fun j bj hj => ?_⟩
      by_cases hji : i = j
      · subst hji
        rw [List.getElem?_set_self hlt_bi] at hj
        simp only [Option.some.injEq] at hj
        subst hj
        rw [List.getElem?_set_self hlt_gs]
        refine ⟨⟨_, rfl, rfl⟩, hsig, fun gs'' hgs'' P => ?_⟩
        simp only [Option.some.injEq] at hgs''
        subst hgs''
        change CliPartyDirInv W
          { bi with gs := some (cliMapGameState CliPartyState.bin (fDir (r, gsOut))) }
          (cliPqSigsOf kst bi) P _
        rw [cliPartyDirInv_bi_gs W bi
          (some (cliMapGameState CliPartyState.bin (fDir (r, gsOut)))) bi.gs, hgs'_st]
        exact hGsOut P
      · rw [List.getElem?_set_ne hji] at hj
        rw [List.getElem?_set_ne hji]
        exact hInv.2 j bj hj
  rw [Dir.cliRunStdSM_eq]
  unfold cliRunStdSM
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_liftM,
    StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_bind,
    map_pure, Prod.map_apply, id_eq, hsigs_biProj]
  rcases q with (((q_tr | q_ch) | ⟨p, c⟩) | q_inj) | q_corr
  · dsimp only
    exact hstep _ gs (mapSt CliPartyState.bin gs) (fun a => a.2) (fun a => a.2)
      rfl rfl (fun _ _ => ⟨rfl, rfl⟩)
  · dsimp only
    exact hstep _ gs (mapSt CliPartyState.bin gs) (fun a => a.2) (fun a => a.2)
      rfl rfl (fun _ _ => ⟨rfl, rfl⟩)
  · cases p
    · dsimp only
      exact hstep _ gs (mapSt CliPartyState.bin gs) (fun a => a.2) (fun a => a.2)
        rfl rfl (fun _ _ => ⟨rfl, rfl⟩)
    · exact hstep _ _ _ _ _
        (bhAlignTransForBob_mapSt CliPartyState.bin im.bobAccepted bi.meA.regId bi.hdr c gs)
        (bhAlignTransForBob_st im.bobAccepted bi.meA.regId bi.hdr c gs)
        (fun r gsOut => by
          rcases r with _ | (_ | _)
          · exact ⟨rfl, rfl⟩
          · exact ⟨rfl, rfl⟩
          · dsimp only
            rw [bhAlignTransForBob_mapSt CliPartyState.bin im.bobAccepted bi.meA.regId bi.hdr c gs,
              mapSt_inTransit]
            cases (bhAlignTransForBob im.bobAccepted bi.meA.regId bi.hdr c gs).inTransit .A c <;>
              exact ⟨rfl, rfl⟩)
  · dsimp only
    exact hstep _ gs (mapSt CliPartyState.bin gs) (fun a => a.2) (fun a => a.2)
      rfl rfl (fun _ _ => ⟨rfl, rfl⟩)
  · dsimp only
    exact hstep _ gs (mapSt CliPartyState.bin gs) (fun a => a.2) (fun a => a.2)
      rfl rfl (fun _ _ => ⟨rfl, rfl⟩)

theorem cliStepLocalSM_step_proj {S : SignalPqxdh.Setup} {l : Nat} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hl : l < 10 ^ 6)
    (qep : Nat) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (cds : CliDriverState S l) (kst : SignalPqxdh.KeyIndState S)
    (hInv : CliRetainedStateInv W cds kst)
    (i : Nat) (bi : ModelDriverInstance S l) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState CliPartyState (Plain l) Bytes)
    (hbi : cds.bhInsts[i]? = some bi) (higs : cds.instGs[i]? = some (some gs))
    (q : (cliGameSmSpec l (BitVec 512)).Domain) :
    let biProj : ModelDriverInstance S l := { bi with gs := some (mapSt CliPartyState.bin gs) }
    Prod.map (Prod.map id projCliDrv) id <$>
      (((Dir.cliStepLocalSM S l run qep decT encT cds i bi im gs q).run cds).run kst) =
      ((cliStepLocalSM S l run W qep decT encT (projCliDrv cds) i biProj im
          (mapSt CliPartyState.bin gs) q).run (projCliDrv cds)).run kst ∧
    ∀ z ∈ support (((Dir.cliStepLocalSM S l run qep decT encT cds i bi im gs q).run cds).run kst),
      CliRetainedStateInv W z.1.2 z.2 := by
  rcases q with (((q₁ | q₂) | ⟨p, c⟩) | ⟨p, c⟩) | p
  · exact cliRunStdSM_step_proj hCli hl qep decT encT cds kst hInv i bi im gs hbi higs _
  · exact cliRunStdSM_step_proj hCli hl qep decT encT cds kst hInv i bi im gs hbi higs _
  · cases p with
    | A =>
      dsimp only [Dir.cliStepLocalSM, Dir.cliStepLocalSMM, cliStepLocalSM]
      by_cases hd : (bhDecodePreKeyMsgE c).isSome = true
      · simp only [hd, ↓reduceIte, StateT.run_pure, map_pure, Prod.map_apply, id_eq,
          support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
      · simp only [Bool.not_eq_true] at hd; rw [hd]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact cliRunStdSM_step_proj hCli hl qep decT encT cds kst hInv i bi im gs hbi higs _
    | B =>
      dsimp only [Dir.cliStepLocalSM, Dir.cliStepLocalSMM, cliStepLocalSM]
      by_cases hn : (bhPartneredInnerBytes im.bobAccepted bi.meA.regId bi.hdr c).isNone = true
      · simp only [hn, ↓reduceIte, StateT.run_pure, map_pure, Prod.map_apply, id_eq,
          support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
      · simp only [Bool.not_eq_true] at hn; rw [hn]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact cliRunStdSM_step_proj hCli hl qep decT encT cds kst hInv i bi im gs hbi higs _
  · cases p with
    | A =>
      dsimp only [Dir.cliStepLocalSM, Dir.cliStepLocalSMM, cliStepLocalSM]
      by_cases hd : (bhDecodePreKeyMsgE c).isSome = true
      · simp only [hd, ↓reduceIte, StateT.run_pure, map_pure, Prod.map_apply, id_eq,
          support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
      · simp only [Bool.not_eq_true] at hd; rw [hd]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact cliRunStdSM_step_proj hCli hl qep decT encT cds kst hInv i bi im gs hbi higs _
    | B =>
      dsimp only [Dir.cliStepLocalSM, Dir.cliStepLocalSMM, cliStepLocalSM]
      have hit_eq :
          bhPartneredInTransitA true bi.meA.regId bi.hdr c (mapSt CliPartyState.bin gs) =
            bhPartneredInTransitA true bi.meA.regId bi.hdr c gs := rfl
      rw [hit_eq]
      by_cases hb : (!im.bobAccepted) = true
      · simp only [hb, ↓reduceIte, StateT.run_pure, map_pure, Prod.map_apply, id_eq,
          support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
      · simp only [Bool.not_eq_true] at hb; rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hg : ((bhPartneredInnerBytes true bi.meA.regId bi.hdr c).isNone ||
            bhPartneredInTransitA true bi.meA.regId bi.hdr c gs) = true
        · simp only [hg, ↓reduceIte, StateT.run_pure, map_pure, Prod.map_apply, id_eq,
            support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
        · simp only [Bool.not_eq_true] at hg; rw [hg]; simp only [Bool.false_eq_true, ↓reduceIte]
          exact cliRunStdSM_step_proj hCli hl qep decT encT cds kst hInv i bi im gs hbi higs _
  · exact cliRunStdSM_step_proj hCli hl qep decT encT cds kst hInv i bi im gs hbi higs _

theorem cliDrvSM_step_proj {S : SignalPqxdh.Setup} {l : Nat} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hl : l < 10 ^ 6)
    (qep : Nat) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (cds : CliDriverState S l) (kst : SignalPqxdh.KeyIndState S)
    (hInv : CliRetainedStateInv W cds kst)
    (tq : (cliGameDrSpec l (BitVec 512)).Domain) :
    Prod.map (Prod.map id projCliDrv) id <$>
      (((Dir.cliDrvSM S l run qep decT encT bhNoExtWithSpqr tq).run cds).run kst) =
      ((cliDrvSM S l run W qep decT encT bhNoExtWithSpqr tq).run (projCliDrv cds)).run kst ∧
    ∀ z ∈ support (((Dir.cliDrvSM S l run qep decT encT bhNoExtWithSpqr tq).run cds).run kst),
      CliRetainedStateInv W z.1.2 z.2 := by
  rcases tq with ⟨i, q⟩
  have hclean := bhDrvInstClean_projCliDrv hInv.1 i
  have himeta : (projCliDrv cds).instMeta = cds.instMeta := rfl
  unfold Dir.cliDrvSM Dir.cliDrvSMM cliDrvSM
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hclean, himeta]
  split_ifs
  · simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq,
      support_pure, Set.mem_singleton_iff]
    exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
  · rcases hbi : cds.bhInsts[i]? with _ | bi
    · have hproj_none : (projCliDrv cds).bhInsts[i]? = none := by
        unfold projCliDrv projInsts; dsimp only
        rw [zipWith_getElem?_ret, hbi]
      rw [hproj_none]
      simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq,
        support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
    · obtain ⟨⟨gsOpt, higs, _⟩, _⟩ := hInv.2 i bi hbi
      have hproj_some : (projCliDrv cds).bhInsts[i]? =
          some { bi with gs := gsOpt.map (mapSt CliPartyState.bin) } := by
        unfold projCliDrv projInsts; dsimp only
        rw [zipWith_getElem?_ret, hbi, higs]
      rw [hproj_some, higs]
      rcases cds.instMeta[i]? with _ | im
      · simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq,
          support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ hz => hz ▸ hInv⟩
      · dsimp only
        have hik_eq : bhInstIkACorrupted (projCliDrv cds)
            { bi with gs := gsOpt.map (mapSt CliPartyState.bin) } =
            bhInstIkACorrupted cds.toModelDriverState bi := rfl
        rw [hik_eq]
        split_ifs
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            map_pure, Prod.map_apply, id_eq]
          refine ⟨rfl, fun z hz => ?_⟩
          simp only [support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact cliRetainedStateInv_of_spkLookup hInv rfl rfl (fun _ _ h => h)
        · cases gsOpt with
          | none =>
            dsimp only [Option.map]
            unfold bhNoExtWithSpqr
            simp only [StateT.run_bind, StateT.run_pure, StateT.run_set, pure_bind,
              map_pure, Prod.map_apply, id_eq]
            have hm_eq : bhMetaAfterSM (projCliDrv cds) { bi with gs := none } im q
                (bhSmDefaultWithSpqr q) =
                bhMetaAfterSM cds.toModelDriverState bi im q (bhSmDefaultWithSpqr q) := rfl
            rw [hm_eq]
            refine ⟨rfl, fun z hz => ?_⟩
            simp only [support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact cliRetainedStateInv_of_spkLookup hInv rfl rfl (fun _ _ h => h)
          | some gs =>
            dsimp only [Option.map]
            exact cliStepLocalSM_step_proj hCli hl qep decT encT cds kst hInv i bi im gs hbi higs q

theorem cliDrvImpl_step_proj {S : SignalPqxdh.Setup} {l : Nat} {Pt : Type}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hl : l < 10 ^ 6)
    (P : SignalPqxdh.Primitives) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (mode : BHDrvMode S)
    (cds : CliDriverState S l) (kst : SignalPqxdh.KeyIndState S)
    (hInv : CliRetainedStateInv W cds kst)
    (t : (cliGameSpec S l (BitVec 512)).Domain) :
    Prod.map (Prod.map id projCliDrv) id <$>
      (((Dir.cliDrvImpl S l P run W qep decT encT bhNoExtWithSpqr mode t).run cds).run kst) =
      ((cliDrvImpl S l P run W qep decT encT bhNoExtWithSpqr mode t).run (projCliDrv cds)).run kst ∧
    ∀ z ∈ support
        (((Dir.cliDrvImpl S l P run W qep decT encT bhNoExtWithSpqr mode t).run cds).run kst),
      CliRetainedStateInv W z.1.2 z.2 := by
  rcases t with ((t_unif | t_ki) | t_ctl) | t_sm
  · change Prod.map (Prod.map id projCliDrv) id <$>
        ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (CliDrvM S l) t_unif).run cds).run kst) =
        (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (BHDrvM S l) t_unif).run
          (projCliDrv cds)).run kst ∧
      ∀ z ∈ support
          ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (CliDrvM S l) t_unif).run cds).run kst),
        CliRetainedStateInv W z.1.2 z.2
    simp only [QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_bind,
      StateT.run_monadLift, monadLift_self, StateT.run_pure,
      bind_assoc, pure_bind, map_bind, map_pure, Prod.map_apply, id_eq]
    refine ⟨trivial, fun z hz => ?_⟩
    rw [mem_support_bind_iff] at hz
    obtain ⟨u, _, hz⟩ := hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hInv
  · exact bhDrvKeyInd_step_proj P t_ki cds kst hInv
  · cases t_ctl with
    | startDR sid => exact cliDrvStart_step_proj hCli P mode sid cds kst hInv
  · exact cliDrvSM_step_proj hCli hl qep decT encT cds kst hInv t_sm

/-! ## Experiment and advantage equivalence -/

theorem simulateQ_twoState_proj {ι : Type} {ospec : OracleSpec.{0, 0} ι}
    {α σ₁ σ₂ τ : Type}
    (impl₁ : QueryImpl ospec (StateT σ₁ (StateT τ ProbComp)))
    (impl₂ : QueryImpl ospec (StateT σ₂ (StateT τ ProbComp)))
    (inv : σ₁ → τ → Prop) (proj : σ₁ → σ₂)
    (hstep : ∀ t s kst, inv s kst →
      Prod.map (Prod.map id proj) id <$> (((impl₁ t).run s).run kst) =
        ((impl₂ t).run (proj s)).run kst ∧
      ∀ z ∈ support (((impl₁ t).run s).run kst), inv z.1.2 z.2)
    (oa : OracleComp ospec α) :
    ∀ (s : σ₁) (kst : τ), inv s kst →
      Prod.map (Prod.map id proj) id <$> (((simulateQ impl₁ oa).run s).run kst) =
        ((simulateQ impl₂ oa).run (proj s)).run kst ∧
      ∀ z ∈ support (((simulateQ impl₁ oa).run s).run kst), inv z.1.2 z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s kst hs
    simp only [simulateQ_pure, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff]
    exact ⟨rfl, fun z hz => by subst hz; exact hs⟩
  | query_bind t k ih =>
    intro s kst hs
    obtain ⟨hproj_t, hinv_t⟩ := hstep t s kst hs
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    refine ⟨?_, ?_⟩
    · rw [← hproj_t, bind_map_left]
      exact bind_congr_of_forall_mem_support _ fun z hz => by
        simpa using (ih z.1.1 z.1.2 z.2 (hinv_t z hz)).1
    · intro w hw
      rw [mem_support_bind_iff] at hw
      obtain ⟨z, hz, hw⟩ := hw
      exact (ih z.1.1 z.1.2 z.2 (hinv_t z hz)).2 w hw

/-- Exact equivalence of `cliPqExp` and `cliPqExpProj` under `CliSpecPqxdh run X W` and `l < 10 ^ 6`
(`DEV-CLI18`). -/
theorem cliPqExp_eq_proj (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512))
    (hCli : CliSpecPqxdh run X W) (hl : l < 10 ^ 6) :
    cliPqExp S run X W l qep decT encT A = cliPqExpProj S run X W l qep decT encT A := by
  unfold cliPqExp cliPqExpProj composedExp cliIface cliIfaceProj
  dsimp only
  refine bind_congr_of_forall_mem_support ($ᵗ Bool) fun b _ => ?_
  let mode : BHDrvMode S := fun _ _ _ _ _ => some b
  let kst₀ := SignalPqxdh.KeyIndState.empty S true
  obtain ⟨hsim_eq, hsim_inv⟩ := simulateQ_twoState_proj
    (Dir.cliDrvImpl S l (modelPrims X W) run W qep decT encT bhNoExtWithSpqr mode)
    (cliDrvImpl S l (modelPrims X W) run W qep decT encT bhNoExtWithSpqr mode)
    (CliRetainedStateInv W) projCliDrv
    (fun t cds kst hInv =>
      cliDrvImpl_step_proj hCli hl (modelPrims X W) qep decT encT mode cds kst hInv t)
    A.run {} kst₀ (cliRetainedStateInv_init W kst₀)
  change ((((simulateQ (Dir.cliDrvImpl S l (modelPrims X W) run W qep decT encT
          bhNoExtWithSpqr mode) A.run).run {}).run kst₀) >>= _) =
    ((((simulateQ (cliDrvImpl S l (modelPrims X W) run W qep decT encT
          bhNoExtWithSpqr mode) A.run).run (projCliDrv {})).run kst₀) >>= _)
  rw [← hsim_eq, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun z hz => ?_
  have hInv_z := hsim_inv z hz
  dsimp only [Prod.map, id]
  rw [driverSomeInstanceWon_projCliDrv hInv_z b]

/-- Exact advantage equality `CliPqxdhAdvantage = CliPqxdhAdvantageProj` under `CliSpecPqxdh run X W`
and `l < 10 ^ 6` (`DEV-CLI18`). -/
theorem cliPqxdhAdvantage_eq_proj (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512))
    (hCli : CliSpecPqxdh run X W) (hl : l < 10 ^ 6) :
    CliPqxdhAdvantage S run X W l qep decT encT A =
      CliPqxdhAdvantageProj S run X W l qep decT encT A := by
  unfold CliPqxdhAdvantage CliPqxdhAdvantageProj
  rw [cliPqExp_eq_proj S run X W l qep decT encT A hCli hl]

end CryptoVerification.E2E
