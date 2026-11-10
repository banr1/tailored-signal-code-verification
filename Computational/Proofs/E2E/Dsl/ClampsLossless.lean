/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables
public import Computational.Specifications.Assumptions.KemCorrect
public import Computational.Proofs.SpqrV1Sync.TopStateTight
import LibsignalBinary.Proofs.SpqrV1Sync.TopSize
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import Computational.Proofs.E2E.ComposedBinaryLinkV1

/-!
# Losslessness of Capacity Clamps in `CompositionCostedTables`

Proves roundtrip and clamp-losslessness theorems for the pure and cryptographic operations in
`CompositionCostedTables`, covering SPQR V1 state and message codecs, `GhostState` and
`SessionRecord` serialization, `WellFormedPrimitivesδ` cryptographic outputs, and session wire
framing.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.ClampsLossless

open CryptoGames (Party)
open CryptoGames.HMAC (toBEBytes keyToBytes32 hmacSha256Trunc8)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.CBC (Plain Block nBlocks cbcPkcs7EncryptOnly blockToBytesLE)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey IdentityKey KeyPair PrivateKey
  ChainKey SenderChain ReceiverChain MessageKeyGenerator SessionState GhostState SpqrDirection
  ProtoSignalMessage SignalMessage serializeContent computeMac macLength aesCbcEncrypt
  currentVersion versionByte)
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarintAux decodeVarint decodeKey
  skipBytes skipScalar skipField skipGroup recursionLimit mergeBytes mergeUint32 mergeField
  decodeLoop emptyProtoSignalMessage decode encodeBytesField encodeUint32Field encode
  protoSignalCodec encodeVarintAux encodeVarint encodeKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem PolyApi Direction Version ChainParamsPB
  EpochDirectionPB ChainEpochPB ChainPB VersionNegotiationPB V1State PqRatchetState Chain
  ChainEpoch ChainEpochDirection EpochSecret States Message MessageType spqrPolyApi spqrAuthApi
  spqrDeps spqrHkdfWith spqrV1Init pbToPqRatchetState pqRatchetStateToPb initInner encode_varint
  encodeVarintLoop encode_chunk MAX_VARINT_BYTES_LEN Authenticator PolynomialDecoder
  ProtoAuthenticator hkdfToVecUnchecked hkdfToSliceUnchecked decodeVarintLoop decode_varint
  msg_preamble msgPreamble MsgPreamble)
open CryptoVerification.SpqrV1.Top.StateSize (optRaw rawVN rawChain rawV1State)
open CryptoVerification.SpqrV1Sync.InSync (St freshDec decoderNew_eq)
open CryptoVerification.SpqrV1Sync.ChainSync (ChainOk genAt seedAt)
open LibsignalBinary.Proofs.SpqrV1Sync.ChainSyncBase (length_nextAt length_seedAt length_genAt)
open CryptoVerification.SpqrV1Sync.TopSync (topPb topBytes vnOf SendPrevNil topBytes_length_le)
open CryptoVerification.SpqrV1Sync.Codec (spqrDecodeState_encodeState)
open CryptoVerification.SpqrV1Sync.SendTotal (isEkSide chainCur_le_phiB BOkTight RecvSmallTight
  TopStateTight TopStateTightW topStateTightW_length_le st_bSize_tight st_bSendClosed_tight
  st_bRecvEk_tight st_bRecvCt_tight)
open CryptoVerification.E2E (Bytes BinState RecordExtras PreKeyMessageFields wirePrekey wireWhisper
  djbKey lenField bytesField uint32Field msgField
  encChainKey encMessageKey encSenderChain encReceiverChain optUint32FieldX int32FieldX
  uint64FieldX encPendingPreKeyX encPendingKyberX encStateUnderExtras encodeRecordUnderExtras
  binStateOfUnderExtras kyberKey u8Vec keyToBytes32_bytesToKey32 bytesToKey32_keyToBytes32)
open CryptoVerification.E2E.Costed (B E2EPureOp E2ECryptoOp e2ePureOps e2eCryptoOps spqrStatePartsT
  hdrT hdrV hdrOfV e2eDecodePreKeyRaw e2eDecodePreKeyMsg e2eHdrOfPreKeyMsg e2eExpectedPreKeyMsg
  e2eWireInnerBytes e2ePartneredInnerBytes
  e2eReadU32BE splitSpqrPrev joinSpqrPrev spqrParamsToV spqrParamsOfV spqrVnToV spqrVnOfV
  spqrDirToV spqrDirOfV spqrChainToV spqrChainOfV spqrSplitEval spqrJoinEval partyToBool
  boolToParty ghostSplitEval ghostJoinEval e2eRecordExtras e2eEncodeSessionRecord
  spqrMsgPayloadSuffix spqrNegotiateInitEval spqrChainNextKeyEval)

/-! ## Key-history roundtrips -/

private theorem length_keyToBytes32 (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

private theorem extractLsb'_e2eReadU32BE_24 (b0 b1 b2 b3 : BitVec 8) :
    (e2eReadU32BE [b0, b1, b2, b3]).extractLsb' 24 8 = b0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [e2eReadU32BE, BitVec.zeroExtend, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h1 : 24 + i < 32 := by omega
  have h2 : ¬ (24 + i < 24) := by omega
  have h3 : ¬ (24 + i < 16) := by omega
  have h4 : ¬ (24 + i < 8) := by omega
  have h5 : 24 + i - 24 = i := by omega
  have hb1 : b1.getLsbD (24 + i - 16) = false := BitVec.getLsbD_of_ge _ _ (by omega)
  have hb2 : b2.getLsbD (24 + i - 8) = false := BitVec.getLsbD_of_ge _ _ (by omega)
  have hb3 : b3.getLsbD (24 + i) = false := BitVec.getLsbD_of_ge _ _ (by omega)
  have hi32 : i < 32 := by omega
  simp [h1, h2, h3, h4, h5, hb1, hb2, hb3, hi, hi32]

private theorem extractLsb'_e2eReadU32BE_16 (b0 b1 b2 b3 : BitVec 8) :
    (e2eReadU32BE [b0, b1, b2, b3]).extractLsb' 16 8 = b1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [e2eReadU32BE, BitVec.zeroExtend, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h1 : 16 + i < 32 := by omega
  have h2 : 16 + i < 24 := by omega
  have h3 : ¬ (16 + i < 16) := by omega
  have h4 : ¬ (16 + i < 8) := by omega
  have h5 : 16 + i - 16 = i := by omega
  have hb2 : b2.getLsbD (16 + i - 8) = false := BitVec.getLsbD_of_ge _ _ (by omega)
  have hb3 : b3.getLsbD (16 + i) = false := BitVec.getLsbD_of_ge _ _ (by omega)
  have hi32 : i < 32 := by omega
  simp [h1, h2, h3, h4, h5, hb2, hb3, hi, hi32]

private theorem extractLsb'_e2eReadU32BE_8 (b0 b1 b2 b3 : BitVec 8) :
    (e2eReadU32BE [b0, b1, b2, b3]).extractLsb' 8 8 = b2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [e2eReadU32BE, BitVec.zeroExtend, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h1 : 8 + i < 32 := by omega
  have h2 : 8 + i < 24 := by omega
  have h3 : 8 + i < 16 := by omega
  have h4 : ¬ (8 + i < 8) := by omega
  have h5 : 8 + i - 8 = i := by omega
  have hi32 : i < 32 := by omega
  simp [h1, h2, h3, h4, h5, hi, hi32]

private theorem extractLsb'_e2eReadU32BE_0 (b0 b1 b2 b3 : BitVec 8) :
    (e2eReadU32BE [b0, b1, b2, b3]).extractLsb' 0 8 = b3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [e2eReadU32BE, BitVec.zeroExtend, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, Nat.zero_add, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  have h1 : i < 32 := by omega
  have h2 : i < 24 := by omega
  have h3 : i < 16 := by omega
  simp [h1, h2, h3, hi]

theorem toBEBytes4_e2eReadU32BE (b0 b1 b2 b3 : BitVec 8) :
    toBEBytes 4 (e2eReadU32BE [b0, b1, b2, b3]) = [b0, b1, b2, b3] := by
  have hfn : toBEBytes 4 (e2eReadU32BE [b0, b1, b2, b3]) =
      [(e2eReadU32BE [b0, b1, b2, b3]).extractLsb' 24 8,
       (e2eReadU32BE [b0, b1, b2, b3]).extractLsb' 16 8,
       (e2eReadU32BE [b0, b1, b2, b3]).extractLsb' 8 8,
       (e2eReadU32BE [b0, b1, b2, b3]).extractLsb' 0 8] := rfl
  rw [hfn, extractLsb'_e2eReadU32BE_24, extractLsb'_e2eReadU32BE_16,
    extractLsb'_e2eReadU32BE_8, extractLsb'_e2eReadU32BE_0]

/-- `joinSpqrPrev` inverts `splitSpqrPrev fuel` on byte strings of length at most `36 * fuel + 35`. -/
theorem joinSpqrPrev_splitSpqrPrev :
    ∀ (fuel : ℕ) (bs : Bytes), bs.length ≤ 36 * fuel + 35 →
      joinSpqrPrev (splitSpqrPrev fuel bs).1 (splitSpqrPrev fuel bs).2 = bs
  | 0, bs, hlen => by
    simp only [splitSpqrPrev, joinSpqrPrev, List.flatMap_nil, List.nil_append, List.take_take,
      Nat.min_self]
    exact List.take_of_length_le (by omega)
  | fuel + 1, bs, hlen => by
    unfold splitSpqrPrev
    by_cases hlt : bs.length < 36
    · simp only [hlt, ↓reduceIte, joinSpqrPrev, List.flatMap_nil, List.nil_append]
      exact List.take_of_length_le (by omega)
    · simp only [hlt, ↓reduceIte]
      rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest4⟩⟩⟩⟩
      · simp at hlt
      · simp at hlt
      · simp at hlt
      · simp at hlt
      · have hrest_ge : 32 ≤ rest4.length := by
          simp only [List.length_cons] at hlt
          omega
        have htake32 : (rest4.take 32).length = 32 := by
          simp [List.length_take, hrest_ge]
        have hdrop : (rest4.drop 32).length ≤ 36 * fuel + 35 := by
          simp only [List.length_cons] at hlen
          simp only [List.length_drop]
          omega
        have ih := joinSpqrPrev_splitSpqrPrev fuel (rest4.drop 32) hdrop
        have htake4 : (b0 :: b1 :: b2 :: b3 :: rest4).take 4 = [b0, b1, b2, b3] := rfl
        have hdrop4 : (b0 :: b1 :: b2 :: b3 :: rest4).drop 4 = rest4 := rfl
        have hdrop36 : (b0 :: b1 :: b2 :: b3 :: rest4).drop 36 = rest4.drop 32 := rfl
        rw [htake4, hdrop4, hdrop36]
        unfold joinSpqrPrev at ih ⊢
        rw [List.flatMap_cons, List.append_assoc, ih]
        dsimp only
        rw [toBEBytes4_e2eReadU32BE, keyToBytes32_bytesToKey32 _ htake32]
        simp [List.take_append_drop]

/-! ## SPQR state split/join roundtrips -/

@[simp] theorem spqrParams_roundtrip {ℓ : ℕ} (p : ChainParamsPB) :
    spqrParamsOfV (spqrParamsToV (ℓ := ℓ) p) = p := by
  cases p
  rfl

theorem spqrVn_roundtrip {ℓ : ℕ} (vn : VersionNegotiationPB) (h : vn.authKey.length ≤ 64) :
    spqrVnOfV (spqrVnToV (ℓ := ℓ) vn) = vn := by
  rcases vn with ⟨ak, dir, minV, cp⟩
  cases cp <;> simp [spqrVnToV, spqrVnOfV, List.take_of_length_le h]

theorem spqrDir_roundtrip {ℓ : ℕ} (d : EpochDirectionPB)
    (hnext : d.next.length ≤ 64) (hprev : d.prev.length ≤ 2201 * 36 + 35) :
    spqrDirOfV (spqrDirToV (ℓ := ℓ) d) = d := by
  rcases d with ⟨ctr, next, prev⟩
  simp [spqrDirToV, spqrDirOfV, List.take_of_length_le hnext,
    joinSpqrPrev_splitSpqrPrev 2201 prev hprev]

private theorem map_spqrEpochLink_roundtrip {ℓ : ℕ} :
    ∀ (lks : List ChainEpochPB),
      (∀ lk ∈ lks,
        (∀ s ∈ lk.send, s.next.length ≤ 64 ∧ s.prev.length ≤ 2201 * 36 + 35) ∧
        (∀ r ∈ lk.recv, r.next.length ≤ 64 ∧ r.prev.length ≤ 2201 * 36 + 35)) →
      (lks.map (fun lk => (lk.send.map (spqrDirToV (ℓ := ℓ)), lk.recv.map (spqrDirToV (ℓ := ℓ))))).map
        (fun sr => ({ send := sr.1.map spqrDirOfV, recv := sr.2.map spqrDirOfV } : ChainEpochPB)) =
      lks
  | [], _ => rfl
  | lk :: rest, hlk => by
    obtain ⟨hs, hr⟩ := hlk lk List.mem_cons_self
    have htail :=
      map_spqrEpochLink_roundtrip (ℓ := ℓ) rest (fun x hx => hlk x (List.mem_cons_of_mem _ hx))
    rcases lk with ⟨s?, r?⟩
    simp only [List.map_cons, htail, List.cons.injEq, and_true]
    congr 1
    · cases s? with
      | none => rfl
      | some s =>
        obtain ⟨hsn, hsp⟩ := hs s rfl
        simp [spqrDir_roundtrip s hsn hsp]
    · cases r? with
      | none => rfl
      | some r =>
        obtain ⟨hrn, hrp⟩ := hr r rfl
        simp [spqrDir_roundtrip r hrn hrp]

theorem spqrChain_roundtrip {ℓ : ℕ} (c : ChainPB)
    (hlinks : c.links.length ≤ 4)
    (hroot : c.nextRoot.length ≤ 64)
    (hlk : ∀ lk ∈ c.links,
      (∀ s ∈ lk.send, s.next.length ≤ 64 ∧ s.prev.length ≤ 2201 * 36 + 35) ∧
      (∀ r ∈ lk.recv, r.next.length ≤ 64 ∧ r.prev.length ≤ 2201 * 36 + 35)) :
    spqrChainOfV (spqrChainToV (ℓ := ℓ) c) = c := by
  rcases c with ⟨dir, curEp, links, nextRoot, sendEp, params⟩
  dsimp only [spqrChainToV, spqrChainOfV]
  rw [List.take_of_length_le hlinks, List.take_of_length_le hroot,
    map_spqrEpochLink_roundtrip links hlk]
  cases params <;> simp

def spqrJoinRaw {ℓ : ℕ} (parts : (spqrStatePartsT (ℓ := ℓ)).denote) : Bytes :=
  let (v1?, (vn?, ch?)) := parts
  CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
    VersionNegotiationPB.encodeRaw 1#32 (vn?.map spqrVnOfV) ++
  CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
    ChainPB.encodeRaw 2#32 (ch?.map spqrChainOfV) ++
  match v1? with
  | none => []
  | some v1Raw => CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage id 3#32 v1Raw

theorem spqrJoinEval_lossless_of_length_le {ℓ : ℕ}
    (parts : (spqrStatePartsT (ℓ := ℓ)).denote)
    (h : (spqrJoinRaw parts).length ≤ 32 * 11000) :
    spqrJoinEval parts = spqrJoinRaw parts := by
  rcases parts with ⟨v1?, vn?, ch?⟩
  unfold spqrJoinRaw at h
  unfold spqrJoinEval spqrJoinRaw
  exact List.take_of_length_le h

theorem v1State_encodeRaw_take64000_of_bOkTight (F : ShaCompress) (K : MlKem) (st : St F)
    (hbok : BOkTight st) :
    (V1State.encodeRaw st.into_pb).take 64000 = V1State.encodeRaw st.into_pb := by
  have hb : rawV1State st.into_pb ≤ 46880 := st_bSize_tight F st hbok
  have htop := topBytes_length_le F K st none none
  have hsub : (V1State.encodeRaw st.into_pb).length ≤ (topBytes F K st none none).length := by
    have heq : topBytes F K st none none =
        CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage V1State.encodeRaw 3#32 st.into_pb := rfl
    rw [heq]
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, List.length_append]
    omega
  have hopt1 : optRaw rawVN none = 0 := rfl
  have hopt2 : optRaw rawChain (none.map Chain.intoPb) = 0 := rfl
  rw [hopt1, hopt2] at htop
  exact List.take_of_length_le (by omega)

private theorem spqrChain_roundtrip_of_chainOk {ℓ : ℕ} (F : ShaCompress)
    (authKey : Bytes) (dir : Direction) (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ)
    (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (hok : ChainOk F authKey dir secret sendCtr recvSet ch)
    (hsp : SendPrevNil ch) (hsmall : RecvSmallTight ch)
    (hlen4 : ch.links.length ≤ 4) :
    spqrChainOfV (spqrChainToV (ℓ := ℓ) ch.intoPb) = ch.intoPb := by
  refine spqrChain_roundtrip ch.intoPb (by simpa [Chain.intoPb] using hlen4) ?_ ?_
  · dsimp only [Chain.intoPb]
    rw [hok.hroot]
    exact Nat.le_trans (List.length_take_le 32 _) (by decide)
  · intro lk hlk_mem
    dsimp only [Chain.intoPb] at hlk_mem
    rcases List.mem_map.mp hlk_mem with ⟨l, hl_mem, rfl⟩
    obtain ⟨i, hi_lt, hl_get⟩ := List.mem_iff_getElem.mp hl_mem
    have hl_opt : ch.links[i]? = some l := by simp [hi_lt, hl_get]
    let e := ch.sendEpoch.toNat - 1 + i
    have hlen := hok.hlen
    have hsend_le := hok.hsend_le
    have he_lo : ch.sendEpoch.toNat - 1 ≤ e := Nat.le_add_right _ _
    have he_hi : e ≤ ch.currentEpoch.toNat := by omega
    have he_idx : e - (ch.sendEpoch.toNat - 1) = i := Nat.add_sub_cancel_left _ _
    refine ⟨?_, ?_⟩
    · intro s hs
      simp only [Option.mem_def, Option.some.injEq] at hs
      subst hs
      dsimp only [ChainEpochDirection.intoPb]
      refine ⟨?_, ?_⟩
      · by_cases hold : i = 0 ∧ 1 ≤ ch.sendEpoch.toNat
        · rcases hold with ⟨rfl, hpos⟩
          rw [hok.hsendOld l hpos hl_opt]
          decide
        · have hse : ch.sendEpoch.toNat ≤ e := by omega
          obtain ⟨l', hl', hsok⟩ := hok.hsendDir e hse he_hi
          rw [he_idx, hl_opt] at hl'
          injection hl' with hl'_eq
          subst hl'_eq
          rw [hsok.hnext, length_nextAt F _ (length_seedAt F authKey secret dir e)]
          decide
      · rw [hsp l hl_mem]
        decide
    · intro r hr
      simp only [Option.mem_def, Option.some.injEq] at hr
      subst hr
      dsimp only [ChainEpochDirection.intoPb]
      refine ⟨?_, ?_⟩
      · obtain ⟨l', hl', hrok⟩ := hok.hrecvDir e he_lo he_hi
        rw [he_idx, hl_opt] at hl'
        injection hl' with hl'_eq
        subst hl'_eq
        rw [hrok.hnext, length_nextAt F _ (length_seedAt F authKey secret dir.switch e)]
        decide
      · exact Nat.le_trans (hsmall l hl_mem) (by decide)

/-- Every `TopStateTight` SPQR V1 state fits in `286,196` bytes and roundtrips through `spqrSplitEval`/`spqrJoinEval`. -/
theorem spqrSplitJoin_topStateTight {ℓ : ℕ} (F : ShaCompress) (K : MlKem) {bytes : Bytes}
    (h : TopStateTight F K bytes) :
    bytes.length ≤ 286196 ∧ (spqrSplitEval (ℓ := ℓ) bytes).map spqrJoinEval = some bytes := by
  obtain ⟨w, hw⟩ := h
  have hlen : bytes.length ≤ 286196 := topStateTightW_length_le F K hw
  refine ⟨hlen, ?_⟩
  have hlt64 : bytes.length < 2 ^ 64 := by omega
  have hbytes := hw.htop.hbytes
  have henc : bytes =
      CryptoVerification.LibsignalSpqrV1.Proto.encodeState
        (pbToPqRatchetState (topPb w.st w.vn? w.ch?)) := hbytes
  have hdec :
      CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState bytes =
        .ok (pbToPqRatchetState (topPb w.st w.vn? w.ch?)) := by
    rw [henc]
    exact spqrDecodeState_encodeState _ (henc ▸ hlt64)
  unfold spqrSplitEval
  rw [hdec]
  dsimp only [pbToPqRatchetState, topPb]
  change Option.map spqrJoinEval
      (some (some ((V1State.encodeRaw w.st.into_pb).take 64000),
       (w.vn?.map (spqrVnToV (ℓ := ℓ)),
        (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ))))) = some bytes
  rw [v1State_encodeRaw_take64000_of_bOkTight F K w.st hw.hbok]
  have hvn_rt : (w.vn?.map (spqrVnToV (ℓ := ℓ))).map spqrVnOfV = w.vn? := by
    rcases hw.htop.hvn with hvn | hvn <;> rw [hvn]
    · rfl
    · dsimp only [Option.map]
      congr 1
      apply spqrVn_roundtrip
      simp [vnOf, hw.hauth]
  have hch_rt : ((w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ))).map spqrChainOfV =
      w.ch?.map Chain.intoPb := by
    rcases hw.htop.hch with hch | ⟨hch, -, -⟩ <;> rw [hch]
    · dsimp only [Option.map]
      congr 1
      have hlen_ch := hw.htop.hok.hlen
      have hcur := hw.htop.hcur
      have hsendEp := hw.htop.hsendEp
      have hcur_le := chainCur_le_phiB w.st
      have hphi := hw.hphi
      exact spqrChain_roundtrip_of_chainOk F w.authKey w.dir w.secret w.sendCtr w.recvSet w.chE
        hw.htop.hok hw.htop.hsendPrev hw.hsmall (by omega)
    · rfl
  rw [Option.map_some]
  congr 1
  unfold spqrJoinEval
  dsimp only
  rw [hvn_rt, hch_rt]
  have hraw :
      CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        VersionNegotiationPB.encodeRaw 1#32 w.vn? ++
      CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        ChainPB.encodeRaw 2#32 (w.ch?.map Chain.intoPb) ++
      CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage id 3#32
        (V1State.encodeRaw w.st.into_pb) = bytes := henc.symm
  rw [hraw]
  exact List.take_of_length_le (by omega)

/-! ## SPQR braid, init, and chain clamps -/

theorem bSendClosed_encodeRaw_take64000 (F : ShaCompress) (K : MlKem) {st st' : St F}
    {tape tape' : Bytes} {m : Message spqrPolyApi} {key : Option EpochSecret}
    (hbok : BOkTight st)
    (hsend : st.send K tape = .ok ({ msg := m, key := key, state := st' }, tape')) :
    (V1State.encodeRaw st'.into_pb).take 64000 = V1State.encodeRaw st'.into_pb :=
  v1State_encodeRaw_take64000_of_bOkTight F K st' (st_bSendClosed_tight F K hbok hsend)

theorem bRecvClosed_encodeRaw_take64000 (F : ShaCompress) (K : MlKem) {st st' : St F}
    {m : Message spqrPolyApi} {key : Option EpochSecret}
    (hbok : BOkTight st)
    (hrecv : st.recv K m = .ok { key := key, state := st' }) :
    (V1State.encodeRaw st'.into_pb).take 64000 = V1State.encodeRaw st'.into_pb := by
  cases hek : isEkSide st with
  | true =>
    exact v1State_encodeRaw_take64000_of_bOkTight F K st' (st_bRecvEk_tight F K hek hbok hrecv)
  | false =>
    exact v1State_encodeRaw_take64000_of_bOkTight F K st' (st_bRecvCt_tight F K hek hbok hrecv)

private theorem spqr_encodeVarintLoop_length_le :
    ∀ (fuel : ℕ) (a : BitVec 64), (encodeVarintLoop fuel a).length ≤ fuel
  | 0, _ => Nat.le_refl 0
  | fuel + 1, a => by
    unfold encodeVarintLoop
    dsimp only
    split_ifs with hlt
    · simp
    · simp only [List.length_cons]
      have ih := spqr_encodeVarintLoop_length_le fuel (a >>> 7)
      omega

def spqrMsgPayloadSuffixRaw {P : PolyApi} (m : Message P) : Bytes :=
  let tByte := [(MessageType.from_payload m.payload).toU8]
  let body :=
    match m.payload with
    | .hdr c | .ek c | .ekCt1Ack c | .ct1 c | .ct2 c => encode_chunk c []
    | .none | .ct1Ack _ => []
  tByte ++ body

theorem spqrMsgPayloadSuffix_lossless {P : PolyApi} (m : Message P) :
    (spqrMsgPayloadSuffixRaw m).length ≤ 43 ∧
      spqrMsgPayloadSuffix m = spqrMsgPayloadSuffixRaw m := by
  have hlen : (spqrMsgPayloadSuffixRaw m).length ≤ 43 := by
    unfold spqrMsgPayloadSuffixRaw
    cases m.payload with
    | none | ct1Ack _ => simp
    | hdr c | ek c | ekCt1Ack c | ct1 c | ct2 c =>
      simp only [encode_chunk, encode_varint, List.nil_append, List.singleton_append,
        List.length_cons, List.length_append, List.Vector.toList_length]
      have hv := spqr_encodeVarintLoop_length_le MAX_VARINT_BYTES_LEN ((P.chunkIndex c).zeroExtend 64)
      simp only [MAX_VARINT_BYTES_LEN] at hv ⊢
      omega
  exact ⟨hlen, List.take_of_length_le (Nat.le_trans hlen (by decide))⟩

theorem spqrAssembleMsg_spqrMsgPayloadSuffix {ℓ : ℕ} {P : PolyApi}
    (m : Message P) (idx : BitVec 32) :
    (e2ePureOps ℓ).eval .spqrAssembleMsg (m.epoch, (idx, spqrMsgPayloadSuffix m)) =
      m.serialize idx := by
  obtain ⟨hsfx_len, hsfx_eq⟩ := spqrMsgPayloadSuffix_lossless m
  have hsfx64 : (spqrMsgPayloadSuffix m).take 64 = spqrMsgPayloadSuffixRaw m := by
    rw [hsfx_eq]
    exact List.take_of_length_le (Nat.le_trans hsfx_len (by decide))
  dsimp only [e2ePureOps, CryptoVerification.E2E.Costed.E2EPureOp.eval]
  rw [hsfx64]
  have hpre_eq :
      encode_varint (idx.zeroExtend 64) (encode_varint m.epoch [1#8]) ++ spqrMsgPayloadSuffixRaw m =
        m.serialize idx := by
    unfold Message.serialize spqrMsgPayloadSuffixRaw
    cases m.payload <;>
      simp [encode_chunk, encode_varint, List.append_assoc]
  have htot_len : (m.serialize idx).length ≤ 64 := by
    rw [← hpre_eq, List.length_append]
    simp only [encode_varint, List.length_append, List.length_singleton]
    have hv1 := spqr_encodeVarintLoop_length_le MAX_VARINT_BYTES_LEN m.epoch
    have hv2 := spqr_encodeVarintLoop_length_le MAX_VARINT_BYTES_LEN (idx.zeroExtend 64)
    simp only [MAX_VARINT_BYTES_LEN] at hv1 hv2 ⊢
    omega
  rw [hpre_eq]
  exact List.take_of_length_le (Nat.le_trans htot_len (by decide))

def spqrChainNextKeyRaw {ℓ : ℕ} (F : ShaCompress) (next : Bytes) (ctr : BitVec 32) :
    Bool × Option ((B (ℓ := ℓ) 32).denote × BitVec 32 × BitVec 256) :=
  match ChainEpochDirection.nextKeyInternal (spqrHkdfWith F) next ctr with
  | .error _ => (true, none)
  | .ok (next', _, (idx, mkBytes)) =>
    (false, some (next', (idx, bytesToKey32 mkBytes)))

theorem spqrChainNextKeyEval_take32_lossless {ℓ : ℕ} (F : ShaCompress)
    (next : Bytes) (ctr : BitVec 32) :
    spqrChainNextKeyEval (ℓ := ℓ) F next ctr = spqrChainNextKeyRaw (ℓ := ℓ) F next ctr := by
  unfold spqrChainNextKeyEval spqrChainNextKeyRaw ChainEpochDirection.nextKeyInternal
  split_ifs <;> simp [List.take_take]

private theorem isEmpty_false_of_length_32 {bs : Bytes} (h : bs.length = 32) :
    bs.isEmpty = false := by
  cases bs with
  | nil => cases h
  | cons _ _ => rfl

private theorem spqr_encodeBytesField_of_length_32 {tag : BitVec 32} {bs : Bytes}
    (h : bs.length = 32) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField tag bs =
      CryptoVerification.LibsignalSpqrV1.Proto.encodeKey tag .lengthDelimited ++ [0x20#8] ++ bs := by
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField,
    isEmpty_false_of_length_32 h, Bool.false_eq_true, ↓reduceIte,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond, h]
  rfl

private theorem auth_new_lengths (F : ShaCompress) (ak : Bytes) :
    (Authenticator.new F ak 1#64).rootKey.length = 32 ∧
    (Authenticator.new F ak 1#64).macKey.length = 32 := by
  unfold Authenticator.new Authenticator.update
  dsimp only
  have h64 : (hkdfToVecUnchecked F (List.replicate 32 0)
      (List.replicate 32 0 ++ ak)
      (Authenticator.updateLabel ++ toBEBytes 8 1#64) 64).length = 64 := by
    simp [hkdfToVecUnchecked, hkdfToSliceUnchecked]
  exact ⟨by simp only [List.length_take, h64]; omega, by simp only [List.length_drop, h64]⟩

private theorem init_a_v1State_length_aux (rk mk : Bytes)
    (hrk : rk.length = 32) (hmk : mk.length = 32) :
    (V1State.encodeRaw
      { innerState := some (.keysUnsampled
          { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } }) }).length = 76 := by
  have hk1 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := rfl
  have hk2 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited = [0x12#8] := rfl
  have hAuthLen : (ProtoAuthenticator.encodeRaw { rootKey := rk, macKey := mk }).length = 68 := by
    simp [ProtoAuthenticator.encodeRaw, spqr_encodeBytesField_of_length_32 hrk,
      spqr_encodeBytesField_of_length_32 hmk, hk1, hk2, hrk, hmk]
  have hUcLen : (V1State.Unchunked.KeysUnsampled.encodeRaw
      { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } }).length = 72 := by
    simp only [V1State.Unchunked.KeysUnsampled.encodeRaw,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, List.length_append, hAuthLen]
    rfl
  have hChkLen : (V1State.Chunked.KeysUnsampled.encodeRaw
      { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } }).length = 74 := by
    simp only [V1State.Chunked.KeysUnsampled.encodeRaw,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, List.length_append, hUcLen]
    rfl
  simp only [V1State.encodeRaw, V1State.InnerState.encode,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, List.length_append, hChkLen]
  rfl

private theorem init_a_v1State_length (F : ShaCompress) (ak : Bytes) :
    (V1State.encodeRaw
      { innerState := some (.keysUnsampled
          { uc := some { epoch := 1#64, auth := some {
              rootKey := (Authenticator.new F ak 1#64).rootKey,
              macKey := (Authenticator.new F ak 1#64).macKey } } }) }).length = 76 := by
  obtain ⟨hrk, hmk⟩ := auth_new_lengths F ak
  exact init_a_v1State_length_aux _ _ hrk hmk

private theorem init_b_v1State_length_aux (rk mk : Bytes)
    (hrk : rk.length = 32) (hmk : mk.length = 32) :
    let pd0 : PolynomialDecoder :=
      { ptsNeeded := 48#32, polys := 16#32, pts := List.replicate 16 [], isComplete := false }
    (V1State.encodeRaw
      { innerState := some (.noHeaderReceived
          { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } },
            receivingHdr := some pd0 }) }).length = 114 := by
  intro pd0
  have hk1 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := rfl
  have hk2 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited = [0x12#8] := rfl
  have hAuthLen : (ProtoAuthenticator.encodeRaw { rootKey := rk, macKey := mk }).length = 68 := by
    simp [ProtoAuthenticator.encodeRaw, spqr_encodeBytesField_of_length_32 hrk,
      spqr_encodeBytesField_of_length_32 hmk, hk1, hk2, hrk, hmk]
  have hUcLen : (V1State.Unchunked.NoHeaderReceived.encodeRaw
      { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } }).length = 72 := by
    simp only [V1State.Unchunked.NoHeaderReceived.encodeRaw,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, List.length_append, hAuthLen]
    rfl
  have hPdLen : (PolynomialDecoder.encodeRaw pd0).length = 36 := rfl
  have hChkLen : (V1State.Chunked.NoHeaderReceived.encodeRaw
      { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } },
        receivingHdr := some pd0 }).length = 112 := by
    simp only [V1State.Chunked.NoHeaderReceived.encodeRaw,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, List.length_append, hUcLen, hPdLen]
    rfl
  simp only [V1State.encodeRaw, V1State.InnerState.encode,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, List.length_append, hChkLen]
  rfl

private theorem init_b_v1State_length (F : ShaCompress) (ak : Bytes) :
    let pd0 : PolynomialDecoder :=
      { ptsNeeded := 48#32, polys := 16#32, pts := List.replicate 16 [], isComplete := false }
    (V1State.encodeRaw
      { innerState := some (.noHeaderReceived
          { uc := some { epoch := 1#64, auth := some {
              rootKey := (Authenticator.new F ak 1#64).rootKey,
              macKey := (Authenticator.new F ak 1#64).macKey } },
            receivingHdr := some pd0 }) }).length = 114 := by
  obtain ⟨hrk, hmk⟩ := auth_new_lengths F ak
  exact init_b_v1State_length_aux _ _ hrk hmk

private theorem encodeState_vn_v1_length (vn : VersionNegotiationPB) (v1 : V1State)
    (hvn : (VersionNegotiationPB.encodeRaw vn).length ≤ 40)
    (hv1 : (V1State.encodeRaw v1).length ≤ 114) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeState
      (pbToPqRatchetState { inner := some v1, versionNegotiation := some vn, chain := none })).length ≤ 158 := by
  dsimp only [pbToPqRatchetState, CryptoVerification.LibsignalSpqrV1.Proto.encodeState,
    PqRatchetState.encode, PqRatchetState.encodeRaw,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, PqRatchetState.Inner.encode,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, Option.map]
  simp only [List.append_nil, List.length_append]
  have h1 := lenField_spqr_vn vn hvn
  have h2 := lenField_spqr_v1 v1 hv1
  omega
where
  lenField_spqr_vn (vn : VersionNegotiationPB) (hvn : (VersionNegotiationPB.encodeRaw vn).length ≤ 40) :
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited).length +
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
          (BitVec.ofNat 64 (VersionNegotiationPB.encodeRaw vn).length)).length ≤ 2 := by
    have hk : (CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited).length = 1 := rfl
    have hv : (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
        (BitVec.ofNat 64 (VersionNegotiationPB.encodeRaw vn).length)).length = 1 := by
      unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
        CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux
      have hlt : (BitVec.ofNat 64 (VersionNegotiationPB.encodeRaw vn).length) < 0x80#64 := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        change (VersionNegotiationPB.encodeRaw vn).length < 128
        omega
      simp [hlt]
    omega
  lenField_spqr_v1 (v1 : V1State) (hv1 : (V1State.encodeRaw v1).length ≤ 114) :
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 3#32 .lengthDelimited).length +
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
          (BitVec.ofNat 64 (V1State.encodeRaw v1).length)).length ≤ 2 := by
    have hk : (CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 3#32 .lengthDelimited).length = 1 := rfl
    have hv : (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
        (BitVec.ofNat 64 (V1State.encodeRaw v1).length)).length = 1 := by
      unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
        CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux
      have hlt : (BitVec.ofNat 64 (V1State.encodeRaw v1).length) < 0x80#64 := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        change (V1State.encodeRaw v1).length < 128
        omega
      simp [hlt]
    omega

theorem spqrV1Init_length_le_158 (F : ShaCompress) (K : MlKem) (dir : SpqrDirection)
    (k : BitVec 256) : (spqrV1Init F K dir k).length ≤ 158 := by
  have hak : (keyToBytes32 k).length = 32 := length_keyToBytes32 k
  cases dir with
  | a2b =>
    have hVnLen : (VersionNegotiationPB.encodeRaw {
        authKey := keyToBytes32 k, direction := 0#32, minVersion := 1#32,
        chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } }).length = 38 := by
      have hk1 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := rfl
      have hdir : CryptoVerification.LibsignalSpqrV1.Proto.encodeInt32Field 2#32 0#32 = [] := rfl
      simp only [VersionNegotiationPB.encodeRaw, spqr_encodeBytesField_of_length_32 hak, hk1, hdir,
        List.length_append, hak]
      rfl
    have hV1Len := init_a_v1State_length F (keyToBytes32 k)
    have hInit : spqrV1Init F K .a2b k =
        CryptoVerification.LibsignalSpqrV1.Proto.encodeState (pbToPqRatchetState {
          inner := some { innerState := some (.keysUnsampled {
            uc := some { epoch := 1#64, auth := some {
              rootKey := (Authenticator.new F (keyToBytes32 k) 1#64).rootKey,
              macKey := (Authenticator.new F (keyToBytes32 k) 1#64).macKey } } }) },
          versionNegotiation := some {
            authKey := keyToBytes32 k, direction := 0#32, minVersion := 1#32,
            chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } },
          chain := none }) := rfl
    rw [hInit]
    exact encodeState_vn_v1_length _ _ (by omega) (by omega)
  | b2a =>
    have hVnLen : (VersionNegotiationPB.encodeRaw {
        authKey := keyToBytes32 k, direction := 1#32, minVersion := 1#32,
        chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } }).length = 40 := by
      have hk1 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := rfl
      have hdir : CryptoVerification.LibsignalSpqrV1.Proto.encodeInt32Field 2#32 1#32 = [0x10#8, 0x01#8] := rfl
      simp only [VersionNegotiationPB.encodeRaw, spqr_encodeBytesField_of_length_32 hak, hk1, hdir,
        List.length_append, hak]
      rfl
    have hV1Len := init_b_v1State_length F (keyToBytes32 k)
    have hInit : spqrV1Init F K .b2a k =
        CryptoVerification.LibsignalSpqrV1.Proto.encodeState (pbToPqRatchetState {
          inner := some { innerState := some (.noHeaderReceived {
            uc := some { epoch := 1#64, auth := some {
              rootKey := (Authenticator.new F (keyToBytes32 k) 1#64).rootKey,
              macKey := (Authenticator.new F (keyToBytes32 k) 1#64).macKey } },
            receivingHdr := some {
              ptsNeeded := 48#32, polys := 16#32, pts := List.replicate 16 [],
              isComplete := false } }) },
          versionNegotiation := some {
            authKey := keyToBytes32 k, direction := 1#32, minVersion := 1#32,
            chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } },
          chain := none }) := by
      have hdec : spqrPolyApi.decoder_new 96 = .ok (.ok (freshDec 96)) := by
        simp only [spqrPolyApi, decoderNew_eq 96 (by decide), Except.mapError]
      unfold spqrV1Init CryptoVerification.LibsignalSpqrV1.spqrV1InitialStateFor
        CryptoVerification.LibsignalSpqrV1.initialState initInner
      dsimp only [spqrDeps, spqrAuthApi, CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams,
        CryptoVerification.LibsignalSpqrV1.libsignalChainParams, Direction.ofSpqrDirection,
        States.init_b, CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.new,
        CryptoVerification.LibsignalSpqrV1.HEADER_SIZE,
        CryptoVerification.LibsignalSpqrV1.AUTHENTICATOR_MACSIZE]
      rw [hdec]
      rfl
    rw [hInit]
    exact encodeState_vn_v1_length _ _ (by omega) (by omega)

theorem spqrV1InitOp_eval_lossless (ℓ : ℕ) (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : MlKem) (isAlice : Bool) (pqrKey : BitVec 256) :
    (e2eCryptoOps ℓ P C K).eval .spqrV1InitOp (isAlice, pqrKey) =
      spqrV1Init C.F K (if isAlice then .a2b else .b2a) pqrKey := by
  dsimp only [e2eCryptoOps, CryptoVerification.E2E.Costed.E2ECryptoOp.eval]
  exact List.take_of_length_le
    (Nat.le_trans (spqrV1Init_length_le_158 C.F K _ pqrKey) (by decide))

def spqrNegotiateInitRaw {ℓ : ℕ} (F : ShaCompress) (K : MlKem)
    (verByte : BitVec 8) (dirI32 : BitVec 32) (authKey : Bytes) :
    Bool × Option (Option (B (ℓ := ℓ) 32).denote) :=
  match Version.fromU8? verByte with
  | none => (true, none)
  | some v =>
    match Direction.fromI32? dirI32 with
    | none => (false, none)
    | some dir =>
      match initInner (spqrDeps F K) v dir authKey with
      | .error _ => (true, none)
      | .ok pb? =>
        (false, some (pb?.map V1State.encodeRaw))

theorem spqrNegotiateInitEval_clamp_lossless {ℓ : ℕ} (F : ShaCompress) (K : MlKem)
    (verByte : BitVec 8) (dirI32 : BitVec 32) (authKey : Bytes) :
    spqrNegotiateInitEval (ℓ := ℓ) F K verByte dirI32 authKey =
      spqrNegotiateInitRaw (ℓ := ℓ) F K verByte dirI32 authKey := by
  unfold spqrNegotiateInitEval spqrNegotiateInitRaw
  cases Version.fromU8? verByte with
  | none => rfl
  | some v =>
    cases Direction.fromI32? dirI32 with
    | none => rfl
    | some dir =>
      cases v with
      | v0 => rfl
      | v1 =>
        cases dir with
        | a2b =>
          change (false, some (some ((V1State.encodeRaw { innerState := some (.keysUnsampled
              { uc := some { epoch := 1#64, auth := some {
                  rootKey := (Authenticator.new F authKey 1#64).rootKey,
                  macKey := (Authenticator.new F authKey 1#64).macKey } } }) }).take 48000))) =
            (false, some (some (V1State.encodeRaw { innerState := some (.keysUnsampled
              { uc := some { epoch := 1#64, auth := some {
                  rootKey := (Authenticator.new F authKey 1#64).rootKey,
                  macKey := (Authenticator.new F authKey 1#64).macKey } } }) })))
          rw [List.take_of_length_le
            (Nat.le_trans (Nat.le_of_eq (init_a_v1State_length F authKey)) (by decide))]
        | b2a =>
          have hdec : spqrPolyApi.decoder_new 96 = .ok (.ok (freshDec 96)) := by
            simp only [spqrPolyApi, decoderNew_eq 96 (by decide), Except.mapError]
          have hinit : initInner (spqrDeps F K) .v1 .b2a authKey =
              (.ok (some { innerState := some (.noHeaderReceived
                { uc := some { epoch := 1#64, auth := some {
                    rootKey := (Authenticator.new F authKey 1#64).rootKey,
                    macKey := (Authenticator.new F authKey 1#64).macKey } },
                  receivingHdr := some {
                    ptsNeeded := 48#32, polys := 16#32, pts := List.replicate 16 [],
                    isComplete := false } }) }) : Except _ (Option V1State)) := by
            unfold initInner
            dsimp only [spqrDeps, spqrAuthApi, States.init_b,
              CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.new,
              CryptoVerification.LibsignalSpqrV1.HEADER_SIZE,
              CryptoVerification.LibsignalSpqrV1.AUTHENTICATOR_MACSIZE]
            rw [hdec]
            rfl
          change (match (initInner (spqrDeps F K) .v1 .b2a authKey : Except _ (Option V1State)) with
            | .error _ => (true, none)
            | .ok pb? => (false, some (pb?.map (fun pb => (V1State.encodeRaw pb).take 48000)))) =
            (match (initInner (spqrDeps F K) .v1 .b2a authKey : Except _ (Option V1State)) with
            | .error _ => (true, none)
            | .ok pb? => (false, some (pb?.map V1State.encodeRaw)))
          rw [hinit]
          dsimp only [Option.map]
          rw [List.take_of_length_le
            (Nat.le_trans (Nat.le_of_eq (init_b_v1State_length F authKey)) (by decide))]

/-! ## Session state and record serialization -/

private theorem boolToParty_partyToBool (p : Party) : boolToParty (partyToBool p) = p := by
  cases p <;> rfl

private theorem keyVec_bytesToKey32 (v : List.Vector (BitVec 8) 32) :
    keyToBytesVec32 (bytesToKey32 v.toList) = v := by
  apply Subtype.ext
  exact keyToBytes32_bytesToKey32 v.toList v.toList_length

private theorem map_msgKeys_roundtrip :
    ∀ (mks : List MessageKeyGenerator),
      (∀ mkg ∈ mks, mkg.seed.length = 32) →
      (mks.map (fun mkg => (bytesToKey32 mkg.seed, mkg.counter))).map
        (fun sc => ({ seed := keyToBytes32 sc.1, counter := sc.2 } : MessageKeyGenerator)) = mks
  | [], _ => rfl
  | mkg :: rest, hmk => by
    have h0 := hmk mkg List.mem_cons_self
    have htail := map_msgKeys_roundtrip rest (fun x hx => hmk x (List.mem_cons_of_mem _ hx))
    rcases mkg with ⟨seed, ctr⟩
    dsimp only at h0
    simp [htail, keyToBytes32_bytesToKey32 seed h0]

private theorem map_recvChains_roundtrip :
    ∀ (rcs : List ReceiverChain),
      (∀ rc ∈ rcs, ∀ mk ∈ rc.messageKeys, mk.seed.length = 32) →
      (rcs.map (fun rc =>
        (rc.senderRatchetKey,
         (rc.chainKey.map (fun ck => (ck.key, ck.index)),
          rc.messageKeys.map (fun mk => (bytesToKey32 mk.seed, mk.counter)))))).map
        (fun p =>
          ({ senderRatchetKey := p.1,
             chainKey := p.2.1.map (fun ci => ({ key := ci.1, index := ci.2 } : ChainKey)),
             messageKeys := p.2.2.map (fun sc =>
               ({ seed := keyToBytes32 sc.1, counter := sc.2 } : MessageKeyGenerator)) } :
            ReceiverChain)) = rcs
  | [], _ => rfl
  | rc :: rest, hrc => by
    have h0 := hrc rc List.mem_cons_self
    have htail := map_recvChains_roundtrip rest (fun x hx => hrc x (List.mem_cons_of_mem _ hx))
    rcases rc with ⟨srk, ck?, mks⟩
    dsimp only at h0
    simp only [List.map_cons, htail, map_msgKeys_roundtrip mks h0, List.cons.injEq, and_true]
    cases ck? with
    | none => rfl
    | some ck =>
      rcases ck with ⟨k, idx⟩
      rfl

/-- `ghostJoinEval` inverts `ghostSplitEval` whenever `g.session.receiverChains.length ≤ 5` and
every stored message-key generator has a 32-byte seed. -/
theorem ghostJoinEval_ghostSplitEval {ℓ : ℕ} (g : GhostState Bytes)
    (hrc_len : g.session.receiverChains.length ≤ 5)
    (hmk_len : ∀ rc ∈ g.session.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length = 32) :
    ghostJoinEval (ghostSplitEval (ℓ := ℓ) g) = g := by
  rcases g with ⟨party, st, ep, cEps⟩
  rcases st with ⟨ver, locId, remId?, rk, prevCtr, sc?, rcs, pend, pqSt⟩
  dsimp only at hrc_len hmk_len
  unfold ghostSplitEval ghostJoinEval
  dsimp only
  have htake1 : rcs.take 5 = rcs := List.take_of_length_le hrc_len
  rw [htake1]
  have htake2 :
      ((rcs.map fun rc =>
          (rc.senderRatchetKey,
           (rc.chainKey.map (fun ck => (ck.key, ck.index)),
            rc.messageKeys.map (fun mk => (bytesToKey32 mk.seed, mk.counter))))).take 5) =
        rcs.map fun rc =>
          (rc.senderRatchetKey,
           (rc.chainKey.map (fun ck => (ck.key, ck.index)),
            rc.messageKeys.map (fun mk => (bytesToKey32 mk.seed, mk.counter)))) :=
    List.take_of_length_le (by simpa using hrc_len)
  rw [htake2, map_recvChains_roundtrip rcs hmk_len, boolToParty_partyToBool]
  congr 2
  cases sc? with
  | none => rfl
  | some sc =>
    rcases sc with ⟨⟨pub, ⟨privVec⟩⟩, ⟨ck, idx⟩⟩
    simp [keyVec_bytesToKey32]

private theorem proto_encodeVarintAux_length_le :
    ∀ (k : ℕ) (v : BitVec 64), (encodeVarintAux k v).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    unfold encodeVarintAux
    split_ifs with hlt
    · simp
    · simp only [List.length_cons]
      have ih := proto_encodeVarintAux_length_le k (v >>> 7)
      omega

private theorem proto_encodeVarint_length_le_10 (v : BitVec 64) :
    (encodeVarint v).length ≤ 10 :=
  proto_encodeVarintAux_length_le 10 v

private theorem proto_encodeVarintAux_length_le_of_lt :
    ∀ (m k : ℕ), 1 ≤ m → m ≤ k → ∀ (v : BitVec 64), v.toNat < 128 ^ m →
      (encodeVarintAux k v).length ≤ m
  | 0, _, hm, _, _, _ => by omega
  | 1, 0, _, hk, _, _ => by omega
  | 1, k + 1, _, _, v, hv => by
    have hv' : v.toNat < 0x80 := by simpa using hv
    simp [encodeVarintAux, hv']
  | m + 2, 0, _, hk, _, _ => by omega
  | m + 2, k + 1, _, hk, v, hv => by
    unfold encodeVarintAux
    split_ifs with hlt
    · simp
    · simp only [List.length_cons]
      have hshr : (v >>> 7).toNat < 128 ^ (m + 1) := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        exact Nat.div_lt_of_lt_mul (by
          have hp : 2 ^ 7 * 128 ^ (m + 1) = 128 ^ (m + 2) := by ring
          omega)
      have ih := proto_encodeVarintAux_length_le_of_lt (m + 1) k (by omega) (by omega) (v >>> 7) hshr
      omega

private theorem wireType_toNat_le_5 (wt : WireType) : wt.toNat ≤ 5 := by
  cases wt <;> decide

private theorem proto_encodeKey_length_le_1 (tag : ℕ) (htag : tag ≤ 15) (wt : WireType) :
    (encodeKey tag wt).length ≤ 1 := by
  unfold encodeKey encodeVarint
  apply proto_encodeVarintAux_length_le_of_lt 1 10 (by decide) (by decide)
  have hw := wireType_toNat_le_5 wt
  rw [BitVec.toNat_ofNat]
  omega

private theorem proto_encodeVarint_u32_length_le_5 (v : BitVec 32) :
    (encodeVarint (v.setWidth 64)).length ≤ 5 := by
  apply proto_encodeVarintAux_length_le_of_lt 5 10 (by decide) (by decide)
  rw [BitVec.toNat_setWidth_of_le (by decide)]
  have hv := v.isLt
  omega

private theorem uint32Field_length_le_6 (tag : ℕ) (htag : tag ≤ 15) (v : BitVec 32) :
    (uint32Field tag v).length ≤ 6 := by
  unfold uint32Field
  split_ifs
  · simp
  · rw [List.length_append]
    have hk := proto_encodeKey_length_le_1 tag htag .varint
    have hv := proto_encodeVarint_u32_length_le_5 v
    omega

private theorem optUint32FieldX_length_le_6 (tag : ℕ) (htag : tag ≤ 15)
    (v? : Option (BitVec 32)) : (optUint32FieldX tag v?).length ≤ 6 := by
  cases v? with
  | none => simp [optUint32FieldX]
  | some v =>
    simp only [optUint32FieldX, List.length_append]
    have hk := proto_encodeKey_length_le_1 tag htag .varint
    have hv := proto_encodeVarint_u32_length_le_5 v
    omega

private theorem int32FieldX_length_le_11 (tag : ℕ) (htag : tag ≤ 15) (v : BitVec 32) :
    (int32FieldX tag v).length ≤ 11 := by
  unfold int32FieldX
  split_ifs
  · simp
  · rw [List.length_append]
    have hk := proto_encodeKey_length_le_1 tag htag .varint
    have hv := proto_encodeVarint_length_le_10 (v.signExtend 64)
    omega

private theorem uint64FieldX_length_le_11 (tag : ℕ) (htag : tag ≤ 15) (v : BitVec 64) :
    (uint64FieldX tag v).length ≤ 11 := by
  unfold uint64FieldX
  split_ifs
  · simp
  · rw [List.length_append]
    have hk := proto_encodeKey_length_le_1 tag htag .varint
    have hv := proto_encodeVarint_length_le_10 v
    omega

private theorem lenField_length_le_of_lt (tag m : ℕ) (htag : tag ≤ 15)
    (hm1 : 1 ≤ m) (hm10 : m ≤ 10) (hm_lt : 128 ^ m ≤ 2 ^ 64)
    (payload : Bytes) (hp : payload.length < 128 ^ m) :
    (lenField tag payload).length ≤ payload.length + m + 1 := by
  unfold lenField
  simp only [List.length_append]
  have hk := proto_encodeKey_length_le_1 tag htag .lengthDelimited
  have hv : (encodeVarint (BitVec.ofNat 64 payload.length)).length ≤ m := by
    apply proto_encodeVarintAux_length_le_of_lt m 10 hm1 hm10
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hp
  omega

private theorem bytesField_length_le_1 (tag : ℕ) (htag : tag ≤ 15) (v : Bytes)
    (hv : v.length < 128) : (bytesField tag v).length ≤ v.length + 2 := by
  unfold bytesField
  split_ifs
  · simp
  · have h := lenField_length_le_of_lt tag 1 htag (by decide) (by decide) (by decide) v
      (by simpa using hv)
    omega

private theorem bytesField_length_le_2 (tag : ℕ) (htag : tag ≤ 15) (v : Bytes)
    (hv : v.length < 16384) : (bytesField tag v).length ≤ v.length + 3 := by
  unfold bytesField
  split_ifs
  · simp
  · have h := lenField_length_le_of_lt tag 2 htag (by decide) (by decide) (by decide) v
      (by simpa using hv)
    omega

private theorem bytesField_length_le_3 (tag : ℕ) (htag : tag ≤ 15) (v : Bytes)
    (hv : v.length < 2097152) : (bytesField tag v).length ≤ v.length + 4 := by
  unfold bytesField
  split_ifs
  · simp
  · have h := lenField_length_le_of_lt tag 3 htag (by decide) (by decide) (by decide) v
      (by simpa using hv)
    omega

private theorem msgField_length_le_1 (tag bnd : ℕ) (htag : tag ≤ 15) (hbnd : bnd < 128)
    (o : Option Bytes) (ho : ∀ b ∈ o, b.length ≤ bnd) :
    (msgField tag o).length ≤ bnd + 2 := by
  cases o with
  | none => simp [msgField]
  | some b =>
    have hb := ho b rfl
    have h := lenField_length_le_of_lt tag 1 htag (by decide) (by decide) (by decide) b
      (by omega)
    dsimp only [msgField]
    omega

private theorem msgField_length_le_2 (tag bnd : ℕ) (htag : tag ≤ 15) (hbnd : bnd < 16384)
    (o : Option Bytes) (ho : ∀ b ∈ o, b.length ≤ bnd) :
    (msgField tag o).length ≤ bnd + 3 := by
  cases o with
  | none => simp [msgField]
  | some b =>
    have hb := ho b rfl
    have h := lenField_length_le_of_lt tag 2 htag (by decide) (by decide) (by decide) b
      (by omega)
    dsimp only [msgField]
    omega

private theorem msgField_length_le_3 (tag bnd : ℕ) (htag : tag ≤ 15) (hbnd : bnd < 2097152)
    (o : Option Bytes) (ho : ∀ b ∈ o, b.length ≤ bnd) :
    (msgField tag o).length ≤ bnd + 4 := by
  cases o with
  | none => simp [msgField]
  | some b =>
    have hb := ho b rfl
    have h := lenField_length_le_of_lt tag 3 htag (by decide) (by decide) (by decide) b
      (by omega)
    dsimp only [msgField]
    omega

private theorem flatten_map_length_le {α : Type} (f : α → Bytes) (c : ℕ) :
    ∀ (xs : List α), (∀ x ∈ xs, (f x).length ≤ c) →
      (xs.map f).flatten.length ≤ xs.length * c
  | [], _ => by simp
  | x :: rest, hx => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have h0 := hx x List.mem_cons_self
    have htail := flatten_map_length_le f c rest (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    have hmul : (rest.length + 1) * c = rest.length * c + c := by ring
    omega

private theorem publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [PublicKey.serialize]

private theorem identityKey_serialize_length (ik : IdentityKey) : ik.serialize.length = 33 := by
  simp [IdentityKey.serialize, PublicKey.serialize]

private theorem encChainKey_length_le (ck : ChainKey) : (encChainKey ck).length ≤ 40 := by
  unfold encChainKey
  rw [List.length_append]
  have h1 := uint32Field_length_le_6 1 (by decide) ck.index
  have h2 := bytesField_length_le_1 2 (by decide) (keyToBytes32 ck.key)
    (by rw [length_keyToBytes32]; decide)
  rw [length_keyToBytes32] at h2
  omega

private theorem encSenderChain_length_le (sc : SenderChain) : (encSenderChain sc).length ≤ 111 := by
  unfold encSenderChain
  simp only [List.length_append]
  have h1 := bytesField_length_le_1 1 (by decide) sc.ratchetKey.publicKey.serialize
    (by rw [publicKey_serialize_length]; decide)
  rw [publicKey_serialize_length] at h1
  have h2 := bytesField_length_le_1 2 (by decide) sc.ratchetKey.privateKey.bytes.toList
    (by simp)
  simp only [List.Vector.toList_length] at h2
  have h3 := msgField_length_le_1 3 40 (by decide) (by decide) (some (encChainKey sc.chainKey))
    (fun _ hb => by cases hb; exact encChainKey_length_le sc.chainKey)
  omega

private theorem encReceiverChain_length_le (rc : ReceiverChain)
    (hlen : rc.messageKeys.length ≤ 2000)
    (hseed : ∀ mkg ∈ rc.messageKeys, mkg.seed.length ≤ 32) :
    (encReceiverChain rc).length ≤ 84077 := by
  unfold encReceiverChain
  simp only [List.length_append]
  have h1 := bytesField_length_le_1 1 (by decide) rc.senderRatchetKey.serialize
    (by rw [publicKey_serialize_length]; decide)
  rw [publicKey_serialize_length] at h1
  have h2 := msgField_length_le_1 3 40 (by decide) (by decide)
    (rc.chainKey.map encChainKey)
    (fun b hb => by
      rcases Option.mem_map.mp hb with ⟨ck, _, rfl⟩
      exact encChainKey_length_le ck)
  have h3 := flatten_map_length_le (fun mkg => lenField 4 (encMessageKey mkg)) 42 rc.messageKeys
    (fun mkg hmk => by
      have hmk_len : (encMessageKey mkg).length ≤ 40 := by
        unfold encMessageKey
        rw [List.length_append]
        have hc := uint32Field_length_le_6 1 (by decide) mkg.counter
        have hs := hseed mkg hmk
        have hb := bytesField_length_le_1 5 (by decide) mkg.seed (by omega)
        omega
      have hl := lenField_length_le_of_lt 4 1 (by decide) (by decide) (by decide) (by decide)
        (encMessageKey mkg) (by omega)
      omega)
  omega

/-- Structural size bounds for protocol-reachable `SessionRecord` states. -/
structure ReachableSessionRecordBounds (E : Party → RecordExtras) (g : GhostState Bytes) : Prop where
  receiverChains_le : g.session.receiverChains.length ≤ 5
  messageKeys_le : ∀ rc ∈ g.session.receiverChains, rc.messageKeys.length ≤ 2000
  messageKeySeed_le : ∀ rc ∈ g.session.receiverChains, ∀ mkg ∈ rc.messageKeys, mkg.seed.length ≤ 32
  aliceBaseKey_le : (E g.party).aliceBaseKey.length ≤ 33
  kyberCt_le : ∀ k ∈ (E g.party).kyber, k.ciphertext.length ≤ 1569
  pqRatchetState_le : g.session.pqRatchetState.length ≤ 286196

theorem encodeRecordUnderExtras_length_le_708531 (E : Party → RecordExtras)
    (g : GhostState Bytes) (h : ReachableSessionRecordBounds E g) :
    (encodeRecordUnderExtras E g).length ≤ 708531 := by
  have hst : (encStateUnderExtras (E g.party) g.session).length ≤ 708527 := by
    unfold encStateUnderExtras
    simp only [List.length_append]
    have f1 := uint32Field_length_le_6 1 (by decide) g.session.sessionVersion
    have f2 := bytesField_length_le_1 2 (by decide) g.session.localIdentity.serialize
      (by rw [identityKey_serialize_length]; decide)
    rw [identityKey_serialize_length] at f2
    have hrem : ((g.session.remoteIdentity.map IdentityKey.serialize).getD []).length ≤ 33 := by
      cases g.session.remoteIdentity with
      | none => simp
      | some idR => simp [identityKey_serialize_length]
    have f3 := bytesField_length_le_1 3 (by decide)
      ((g.session.remoteIdentity.map IdentityKey.serialize).getD []) (by omega)
    have f4 := bytesField_length_le_1 4 (by decide) (keyToBytes32 g.session.rootKey)
      (by rw [length_keyToBytes32]; decide)
    rw [length_keyToBytes32] at f4
    have f5 := uint32Field_length_le_6 5 (by decide) g.session.previousCounter
    have f6 := msgField_length_le_1 6 111 (by decide) (by decide)
      (g.session.senderChain.map encSenderChain)
      (fun b hb => by
        rcases Option.mem_map.mp hb with ⟨sc, _, rfl⟩
        exact encSenderChain_length_le sc)
    have f7 := flatten_map_length_le (fun c => lenField 7 (encReceiverChain c)) 84081
      g.session.receiverChains
      (fun rc hrc => by
        have hrc_len := encReceiverChain_length_le rc (h.messageKeys_le rc hrc)
          (h.messageKeySeed_le rc hrc)
        have hl := lenField_length_le_of_lt 7 3 (by decide) (by decide) (by decide) (by decide)
          (encReceiverChain rc) (by omega)
        omega)
    have hpend_len : (encPendingPreKeyX (E g.party).pending).length ≤ 63 := by
      unfold encPendingPreKeyX
      simp only [List.length_append]
      have p1 := optUint32FieldX_length_le_6 1 (by decide) (E g.party).pending.preKeyId
      have p2 := bytesField_length_le_1 2 (by decide) (E g.party).pending.baseKey.serialize
        (by rw [publicKey_serialize_length]; decide)
      rw [publicKey_serialize_length] at p2
      have p3 := int32FieldX_length_le_11 3 (by decide) (E g.party).pending.signedPreKeyId
      have p4 := uint64FieldX_length_le_11 4 (by decide) (E g.party).pending.timestamp
      omega
    have f9 := msgField_length_le_1 9 63 (by decide) (by decide)
      (if g.session.pendingPreKey then some (encPendingPreKeyX (E g.party).pending) else none)
      (fun b hb => by
        split_ifs at hb
        · simp only [Option.mem_def, Option.some.injEq] at hb
          subst hb
          exact hpend_len
        · cases hb)
    have f10 := uint32Field_length_le_6 10 (by decide) (E g.party).remoteRegistrationId
    have f11 := uint32Field_length_le_6 11 (by decide) (E g.party).localRegistrationId
    have hab := h.aliceBaseKey_le
    have f13 := bytesField_length_le_1 13 (by decide) (E g.party).aliceBaseKey (by omega)
    have f14 := msgField_length_le_2 14 1578 (by decide) (by decide)
      (if g.session.pendingPreKey then (E g.party).kyber.map encPendingKyberX else none)
      (fun b hb => by
        split_ifs at hb
        · rcases Option.mem_map.mp hb with ⟨k, hk, rfl⟩
          unfold encPendingKyberX
          rw [List.length_append]
          have k1 := uint32Field_length_le_6 1 (by decide) k.preKeyId
          have hct := h.kyberCt_le k hk
          have k2 := bytesField_length_le_2 2 (by decide) k.ciphertext (by omega)
          omega
        · cases hb)
    have hpq := h.pqRatchetState_le
    have f15 := bytesField_length_le_3 15 (by decide) g.session.pqRatchetState (by omega)
    have hrc5 := h.receiverChains_le
    omega
  unfold encodeRecordUnderExtras
  exact msgField_length_le_3 1 708527 (by decide) (by decide)
    (some (encStateUnderExtras (E g.party) g.session))
    (fun _ hb => by cases hb; exact hst)

/-- Under reachable session and SPQR V1 size bounds, `e2eEncodeSessionRecord` does not truncate. -/
theorem e2eEncodeSessionRecord_lossless {ℓ : ℕ}
    (regIdA regIdB bobRemoteRegId : BitVec 32)
    (hdrV0 : (hdrT (ℓ := ℓ)).denote)
    (g : GhostState Bytes)
    (hrc : g.session.receiverChains.length ≤ 5)
    (hmk : ∀ rc ∈ g.session.receiverChains, rc.messageKeys.length ≤ 2000)
    (hseed : ∀ rc ∈ g.session.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length ≤ 32)
    (hpq : g.session.pqRatchetState.length ≤ 286196) :
    e2eEncodeSessionRecord (ℓ := ℓ) ((regIdA, (regIdB, (bobRemoteRegId, hdrV0))), g) =
      binStateOfUnderExtras (e2eRecordExtras regIdA regIdB bobRemoteRegId (hdrOfV hdrV0)) g := by
  let E := e2eRecordExtras regIdA regIdB bobRemoteRegId (hdrOfV hdrV0)
  have hbounds : ReachableSessionRecordBounds E g :=
    { receiverChains_le := hrc
      messageKeys_le := hmk
      messageKeySeed_le := hseed
      aliceBaseKey_le := by
        cases g.party <;> simp [E, e2eRecordExtras, publicKey_serialize_length]
      kyberCt_le := by
        cases g.party with
        | A =>
          intro k hk
          simp only [E, e2eRecordExtras, Option.mem_def, Option.some.injEq] at hk
          subst hk
          simp [kyberKey]
        | B =>
          intro k hk
          simp [E, e2eRecordExtras] at hk
      pqRatchetState_le := hpq }
  have hlen := encodeRecordUnderExtras_length_le_708531 E g hbounds
  unfold e2eEncodeSessionRecord binStateOfUnderExtras
  dsimp only
  rw [List.take_of_length_le (Nat.le_trans hlen (by decide))]

/-! ## Cryptographic nominal-length clamps -/

private theorem sigVerify_length_eq_64 {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {pk msg sig : SignalPqxdh.Bytes}
    (hv : P.sigVerify pk msg sig = true) : sig.length = 64 := by
  rw [hP.sigVerify_eq_xeddsaVerifyRef] at hv
  unfold SignalPqxdh.xeddsaVerifyRef at hv
  simp only [Bool.and_eq_true, beq_iff_eq] at hv
  split_ifs at hv with hif
  exact hif.1.2

private theorem sigSign_length_eq_64 {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) (sk msg rnd : SignalPqxdh.Bytes) :
    (P.sigSign sk msg rnd).length = 64 :=
  sigVerify_length_eq_64 hP (hP.sig_corr sk msg rnd)

theorem e2eCryptoOps_eval_x25519_lossless (ℓ : ℕ) {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) (C : Crypto) (K : MlKem)
    (sk pk : SignalPqxdh.Bytes) :
    (e2eCryptoOps ℓ P C K).eval .x25519 (sk, pk) = P.x25519 sk pk :=
  List.take_of_length_le (Nat.le_of_eq (hP.x25519_len sk pk))

theorem e2eCryptoOps_eval_x25519Base_lossless (ℓ : ℕ) {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) (C : Crypto) (K : MlKem)
    (sk : SignalPqxdh.Bytes) :
    (e2eCryptoOps ℓ P C K).eval .x25519Base sk = P.x25519Base sk :=
  List.take_of_length_le (Nat.le_of_eq (hP.x25519Base_len sk))

theorem e2eCryptoOps_eval_pow8_lossless (ℓ : ℕ) {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) (C : Crypto) (K : MlKem)
    (pk : SignalPqxdh.Bytes) :
    (e2eCryptoOps ℓ P C K).eval .pow8 pk = P.pow8 pk :=
  List.take_of_length_le (Nat.le_of_eq (hP.pow8_len pk))

theorem e2eCryptoOps_eval_sigSign_lossless (ℓ : ℕ) {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) (C : Crypto) (K : MlKem)
    (sk msg rnd : SignalPqxdh.Bytes) :
    (e2eCryptoOps ℓ P C K).eval .sigSign (sk, (msg, rnd)) = P.sigSign sk msg rnd :=
  List.take_of_length_le (Nat.le_of_eq (sigSign_length_eq_64 hP sk msg rnd))

theorem e2eCryptoOps_eval_kemKeyGen_lossless (ℓ : ℕ) {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) (C : Crypto) (K : MlKem)
    (seed : SignalPqxdh.Bytes) :
    (e2eCryptoOps ℓ P C K).eval .kemKeyGen seed = P.kemKeyGen seed := by
  obtain ⟨hpk, hsk⟩ := hP.kemKeyGen_valid seed
  change ((P.kemKeyGen seed).1.take 1568, (P.kemKeyGen seed).2.take 3168) = P.kemKeyGen seed
  rcases hgen : P.kemKeyGen seed with ⟨pk, sk⟩
  rw [hgen] at hpk hsk
  dsimp only [SignalPqxdh.kyberPkLen] at hpk hsk ⊢
  rw [List.take_of_length_le (Nat.le_of_eq hpk), List.take_of_length_le (Nat.le_of_eq hsk)]

theorem e2eCryptoOps_eval_kemEncaps_lossless (ℓ : ℕ) {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) (C : Crypto) (K : MlKem)
    (pk coins : SignalPqxdh.Bytes) :
    (e2eCryptoOps ℓ P C K).eval .kemEncaps (pk, coins) = P.kemEncaps pk coins := by
  change (P.kemEncaps pk coins).map (fun sc => (sc.1.take 32, sc.2.take 1568)) = P.kemEncaps pk coins
  rcases henc : P.kemEncaps pk coins with _ | ⟨ss, ct⟩
  · rfl
  · obtain ⟨hss, hct⟩ := hP.kemEncaps_len pk coins ss ct henc
    dsimp only [Option.map]
    rw [List.take_of_length_le (Nat.le_of_eq hss), List.take_of_length_le (Nat.le_of_eq hct)]

theorem e2eCryptoOps_eval_kemDecaps_lossless (ℓ : ℕ) {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) (C : Crypto) (K : MlKem)
    (sk ct : SignalPqxdh.Bytes) :
    (e2eCryptoOps ℓ P C K).eval .kemDecaps (sk, ct) = P.kemDecaps sk ct := by
  dsimp only [e2eCryptoOps, CryptoVerification.E2E.Costed.E2ECryptoOp.eval]
  rcases hdec : P.kemDecaps sk ct with _ | ss
  · rfl
  · have hss := hP.kemDecaps_len sk ct ss hdec
    dsimp only [Option.map]
    rw [List.take_of_length_le (Nat.le_of_eq hss)]

theorem e2eCryptoOps_eval_hkdfDerive96_lossless (ℓ : ℕ) {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) (C : Crypto) (K : MlKem)
    (ikm : SignalPqxdh.Bytes) :
    (e2eCryptoOps ℓ P C K).eval .hkdfDerive96 ikm =
      let dk := P.hkdfDerive96 ikm
      (dk.rootKey, (dk.chainKey, dk.pqrKey)) := by
  have hlen :
      (P.hkdfDerive96 ikm).rootKey.length = 32 ∧
      (P.hkdfDerive96 ikm).chainKey.length = 32 ∧
      (P.hkdfDerive96 ikm).pqrKey.length = 32 := by
    rw [hP.hkdfDerive96_eq_ref]
    simp [SignalPqxdh.hkdfDerive96Ref, SignalPqxdh.hkdfExpand96Ref,
      SignalPqxdh.hmacSha256Ref, SignalPqxdh.sha256Ref, SignalPqxdh.fitBytesRef_length]
  obtain ⟨hrk, hck, hpq⟩ := hlen
  dsimp only [e2eCryptoOps, CryptoVerification.E2E.Costed.E2ECryptoOp.eval]
  rw [List.take_of_length_le (Nat.le_of_eq hrk),
    List.take_of_length_le (Nat.le_of_eq hck),
    List.take_of_length_le (Nat.le_of_eq hpq)]

/-! ## Session wire and ciphertext clamps -/

private theorem preKeyMessageFields_inner_length_lt (m : PreKeyMessageFields) :
    m.inner.length < (wirePrekey :: m.bytes).length := by
  simp only [PreKeyMessageFields.bytes, ProtoPreKeySignalMessage.encode,
    CryptoGames.LibsignalSessionApi.Prost.bytesField, List.length_cons, List.length_append]
  omega

theorem e2eDecodePreKeyMsg_inner_take {c : Bytes} {m : PreKeyMessageFields}
    (h : e2eDecodePreKeyMsg c = some m) :
    m.inner.take c.length = m.inner := by
  unfold e2eDecodePreKeyMsg at h
  cases hraw : e2eDecodePreKeyRaw c with
  | none => rw [hraw] at h; cases h
  | some m' =>
    rw [hraw] at h
    dsimp only at h
    split at h
    · next heq =>
      injection h with hm
      subst hm
      have hc : c = wirePrekey :: m'.bytes := beq_iff_eq.mp heq
      rw [hc]
      exact List.take_of_length_le (Nat.le_of_lt (preKeyMessageFields_inner_length_lt m'))
    · cases h

theorem e2eWireInnerBytes_lossless (c : Bytes) :
    e2eWireInnerBytes c =
      match e2eDecodePreKeyMsg c with
      | some m => some m.inner
      | none =>
        match c with
        | t :: body => if t == wireWhisper then some body else none
        | [] => none := by
  unfold e2eWireInnerBytes
  cases h : e2eDecodePreKeyMsg c with
  | none => rfl
  | some m => simp [e2eDecodePreKeyMsg_inner_take h]

theorem e2ePartneredInnerBytes_lossless (bobAccepted : Bool) (regIdA : BitVec 32)
    (sessionHdr : SignalPqxdh.HandshakeHdr) (c : Bytes) :
    e2ePartneredInnerBytes bobAccepted regIdA sessionHdr c =
      if !bobAccepted then
        match e2eDecodePreKeyMsg c with
        | some m =>
          if c == wirePrekey :: (e2eExpectedPreKeyMsg regIdA sessionHdr m.inner).bytes then
            some m.inner
          else none
        | none => none
      else
        match e2eDecodePreKeyMsg c with
        | some m =>
          if e2eHdrOfPreKeyMsg m == sessionHdr then some m.inner else none
        | none =>
          match c with
          | t :: body => if t == wireWhisper then some body else none
          | [] => none := by
  unfold e2ePartneredInnerBytes
  cases bobAccepted <;>
  · cases h : e2eDecodePreKeyMsg c with
    | none => rfl
    | some m => simp [e2eDecodePreKeyMsg_inner_take h]

theorem e2ePureOps_eval_parsePreKeyWire_lossless (ℓ : ℕ) (c : Bytes) :
    (e2ePureOps ℓ).eval .parsePreKeyWire c =
      (e2eDecodePreKeyMsg c).map fun m => (m.regId, (hdrV (e2eHdrOfPreKeyMsg m), m.inner)) := by
  dsimp only [e2ePureOps, E2EPureOp.eval]
  cases h : e2eDecodePreKeyMsg c with
  | none => rfl
  | some m => simp [e2eDecodePreKeyMsg_inner_take h]

private theorem spqrDecodeVarintLoop_length_le (i : ℕ) (out : BitVec 64) (bs : Bytes)
    {val : BitVec 64} {rest : Bytes}
    (h : decodeVarintLoop i out bs = some (val, rest)) :
    rest.length ≤ bs.length := by
  induction bs generalizing i out with
  | nil => simp [decodeVarintLoop] at h
  | cons b tail ih =>
    simp only [decodeVarintLoop] at h
    split at h
    · injection h with hpair
      injection hpair with _ hr
      subst hr
      exact Nat.le_succ _
    · split at h
      · cases h
      · exact Nat.le_trans (ih _ _ h) (Nat.le_succ _)

theorem e2ePureOps_eval_spqrParsePreamble_lossless (ℓ : ℕ) (msg : Bytes) :
    (e2ePureOps ℓ).eval .spqrParsePreamble msg =
      match msgPreamble msg with
      | .ok p => some (p.version, (p.epoch, (p.index, p.remaining)))
      | .error _ => none := by
  dsimp only [e2ePureOps, E2EPureOp.eval]
  rcases hp : msgPreamble msg with _ | p
  · rfl
  · dsimp only
    have hrem : p.remaining.length ≤ msg.length := by
      unfold msgPreamble msg_preamble at hp
      cases msg with
      | nil =>
        injection hp with hp'
        subst hp'
        simp
      | cons ver rest0 =>
        dsimp only [Bind.bind, Except.bind, decode_varint] at hp
        cases hd1 : decodeVarintLoop 0 0#64 rest0 with
        | none => rw [hd1] at hp; cases hp
        | some er1 =>
          rcases er1 with ⟨ep, rest1⟩
          rw [hd1] at hp
          dsimp only at hp
          split at hp
          · cases hp
          · cases hd2 : decodeVarintLoop 0 0#64 rest1 with
            | none => rw [hd2] at hp; cases hp
            | some ir2 =>
              rcases ir2 with ⟨idx64, rest2⟩
              rw [hd2] at hp
              dsimp only at hp
              split at hp
              · injection hp with hp'
                subst hp'
                have h1 := spqrDecodeVarintLoop_length_le 0 0#64 rest0 hd1
                have h2 := spqrDecodeVarintLoop_length_le 0 0#64 rest1 hd2
                dsimp only
                simp only [List.length_cons]
                omega
              · cases hp
    rw [List.take_of_length_le hrem]

private theorem prostDecodeVarintAux_length_le (i : ℕ) (acc : BitVec 64) (bs : Bytes)
    {v : BitVec 64} {rest : Bytes}
    (h : decodeVarintAux i acc bs = some (v, rest)) :
    rest.length ≤ bs.length := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b tail ih =>
    simp only [decodeVarintAux] at h
    split at h
    · split at h
      · cases h
      · injection h with hp
        injection hp with _ hr
        subst hr
        exact Nat.le_succ _
    · split at h
      · cases h
      · exact Nat.le_trans (ih _ _ h) (Nat.le_succ _)

private theorem prostDecodeVarint_length_le (bs : Bytes) {v : BitVec 64} {rest : Bytes}
    (h : decodeVarint bs = some (v, rest)) :
    rest.length ≤ bs.length :=
  prostDecodeVarintAux_length_le 0 0 bs h

private theorem prostDecodeKey_length_le (bs : Bytes) {kw : ℕ × WireType} {rest : Bytes}
    (h : decodeKey bs = some (kw, rest)) :
    rest.length ≤ bs.length := by
  unfold decodeKey at h
  cases hd : decodeVarint bs with
  | none => rw [hd] at h; cases h
  | some kr =>
    rcases kr with ⟨key, r0⟩
    have hr0 := prostDecodeVarint_length_le bs hd
    rw [hd] at h
    dsimp only at h
    split at h
    · cases h
    · cases hw : WireType.ofNat? (key.toNat % 8) with
      | none => rw [hw] at h; cases h
      | some wt =>
        rw [hw] at h
        dsimp only at h
        split at h
        · cases h
        · injection h with hp
          injection hp with _ hr
          subst hr
          exact hr0

private theorem prostSkipBytes_length_le (n : ℕ) (bs : Bytes) {rest : Bytes}
    (h : skipBytes n bs = some rest) :
    rest.length ≤ bs.length := by
  unfold skipBytes at h
  split at h
  · cases h
  · injection h with hr
    subst hr
    simp

private theorem prostSkipScalar_length_le (wt : WireType) (bs : Bytes) {rest : Bytes}
    (h : skipScalar wt bs = some rest) :
    rest.length ≤ bs.length := by
  unfold skipScalar at h
  cases wt with
  | varint =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hd, rfl⟩
    exact prostDecodeVarint_length_le bs hd
  | thirtyTwoBit => exact prostSkipBytes_length_le 4 bs h
  | sixtyFourBit => exact prostSkipBytes_length_le 8 bs h
  | lengthDelimited =>
    cases hd : decodeVarint bs with
    | none => rw [hd] at h; cases h
    | some lr =>
      rcases lr with ⟨len, r0⟩
      rw [hd] at h
      dsimp only at h
      exact Nat.le_trans (prostSkipBytes_length_le len.toNat r0 h)
        (prostDecodeVarint_length_le bs hd)
  | startGroup => cases h
  | endGroup => cases h

private theorem prostSkipField_group_length_le :
    ∀ fuel : ℕ,
      (∀ depth tag wt bs rest, skipField fuel depth tag wt bs = some rest →
        rest.length ≤ bs.length) ∧
      (∀ depth tag bs rest, skipGroup fuel depth tag bs = some rest →
        rest.length ≤ bs.length)
  | 0 => ⟨(fun _ _ _ _ _ h => by simp [skipField] at h),
          (fun _ _ _ _ h => by simp [skipGroup] at h)⟩
  | fuel + 1 => by
    obtain ⟨ihF, ihG⟩ := prostSkipField_group_length_le fuel
    refine ⟨?_, ?_⟩
    · intro depth tag wt bs rest h
      unfold skipField at h
      split at h
      · cases h
      · cases wt with
        | endGroup => cases h
        | startGroup => exact ihG depth tag bs rest h
        | varint => exact prostSkipScalar_length_le .varint bs h
        | sixtyFourBit => exact prostSkipScalar_length_le .sixtyFourBit bs h
        | lengthDelimited => exact prostSkipScalar_length_le .lengthDelimited bs h
        | thirtyTwoBit => exact prostSkipScalar_length_le .thirtyTwoBit bs h
    · intro depth tag bs rest h
      unfold skipGroup at h
      cases hk : decodeKey bs with
      | none => rw [hk] at h; cases h
      | some kw =>
        rcases kw with ⟨⟨itag, iwt⟩, r0⟩
        have hr0 := prostDecodeKey_length_le bs hk
        rw [hk] at h
        cases iwt with
        | endGroup =>
          dsimp only at h
          split at h
          · injection h with hr
            subst hr
            exact hr0
          · cases h
        | varint =>
          dsimp only at h
          cases hf : skipField fuel (depth - 1) itag .varint r0 with
          | none => rw [hf] at h; cases h
          | some r1 =>
            rw [hf] at h; dsimp only at h
            exact Nat.le_trans (ihG depth tag r1 rest h) (Nat.le_trans (ihF _ _ _ r0 r1 hf) hr0)
        | sixtyFourBit =>
          dsimp only at h
          cases hf : skipField fuel (depth - 1) itag .sixtyFourBit r0 with
          | none => rw [hf] at h; cases h
          | some r1 =>
            rw [hf] at h; dsimp only at h
            exact Nat.le_trans (ihG depth tag r1 rest h) (Nat.le_trans (ihF _ _ _ r0 r1 hf) hr0)
        | lengthDelimited =>
          dsimp only at h
          cases hf : skipField fuel (depth - 1) itag .lengthDelimited r0 with
          | none => rw [hf] at h; cases h
          | some r1 =>
            rw [hf] at h; dsimp only at h
            exact Nat.le_trans (ihG depth tag r1 rest h) (Nat.le_trans (ihF _ _ _ r0 r1 hf) hr0)
        | startGroup =>
          dsimp only at h
          cases hf : skipField fuel (depth - 1) itag .startGroup r0 with
          | none => rw [hf] at h; cases h
          | some r1 =>
            rw [hf] at h; dsimp only at h
            exact Nat.le_trans (ihG depth tag r1 rest h) (Nat.le_trans (ihF _ _ _ r0 r1 hf) hr0)
        | thirtyTwoBit =>
          dsimp only at h
          cases hf : skipField fuel (depth - 1) itag .thirtyTwoBit r0 with
          | none => rw [hf] at h; cases h
          | some r1 =>
            rw [hf] at h; dsimp only at h
            exact Nat.le_trans (ihG depth tag r1 rest h) (Nat.le_trans (ihF _ _ _ r0 r1 hf) hr0)

private theorem prostMergeBytes_length_le (wt : WireType) (bs : Bytes) {v rest : Bytes}
    (h : mergeBytes wt bs = some (v, rest)) :
    v.length ≤ bs.length ∧ rest.length ≤ bs.length := by
  unfold mergeBytes at h
  split at h
  · cases h
  · cases hd : decodeVarint bs with
    | none => rw [hd] at h; cases h
    | some lr =>
      rcases lr with ⟨len, r0⟩
      have hr0 := prostDecodeVarint_length_le bs hd
      rw [hd] at h
      dsimp only at h
      split at h
      · cases h
      · injection h with hp
        injection hp with hv hr
        subst hv hr
        exact ⟨Nat.le_trans (List.length_take_le' _ _) hr0, by simp; omega⟩

private theorem prostMergeUint32_length_le (wt : WireType) (bs : Bytes)
    {v : BitVec 32} {rest : Bytes}
    (h : mergeUint32 wt bs = some (v, rest)) :
    rest.length ≤ bs.length := by
  unfold mergeUint32 at h
  split at h
  · cases h
  · cases hd : decodeVarint bs with
    | none => rw [hd] at h; cases h
    | some vr =>
      rcases vr with ⟨v0, r0⟩
      rw [hd] at h
      dsimp only at h
      injection h with hp
      injection hp with _ hr
      subst hr
      exact prostDecodeVarint_length_le bs hd

private def ProtoSignalFieldsLe (N : ℕ) (p : ProtoSignalMessage) : Prop :=
  (∀ v ∈ p.ciphertext, v.length ≤ N) ∧
  (∀ v ∈ p.pqRatchet, v.length ≤ N) ∧
  (∀ v ∈ p.addresses, v.length ≤ N)

private theorem prostMergeField_preserves {N : ℕ} {p p' : ProtoSignalMessage}
    {tag : ℕ} {wt : WireType} {bs rest : Bytes}
    (hp : ProtoSignalFieldsLe N p) (hbs : bs.length ≤ N)
    (h : mergeField p tag wt bs = some (p', rest)) :
    ProtoSignalFieldsLe N p' ∧ rest.length ≤ bs.length := by
  unfold mergeField at h
  match tag with
  | 1 =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq
    subst hp_eq hr_eq
    exact ⟨hp, (prostMergeBytes_length_le wt bs hm).2⟩
  | 2 =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq
    subst hp_eq hr_eq
    exact ⟨hp, prostMergeUint32_length_le wt bs hm⟩
  | 3 =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq
    subst hp_eq hr_eq
    exact ⟨hp, prostMergeUint32_length_le wt bs hm⟩
  | 4 =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq
    subst hp_eq hr_eq
    obtain ⟨hv, hr⟩ := prostMergeBytes_length_le wt bs hm
    refine ⟨⟨?_, hp.2.1, hp.2.2⟩, hr⟩
    intro w hw
    simp only [Option.mem_def, Option.some.injEq] at hw
    subst hw
    exact Nat.le_trans hv hbs
  | 5 =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq
    subst hp_eq hr_eq
    obtain ⟨hv, hr⟩ := prostMergeBytes_length_le wt bs hm
    refine ⟨⟨hp.1, ?_, hp.2.2⟩, hr⟩
    intro w hw
    simp only [Option.mem_def, Option.some.injEq] at hw
    subst hw
    exact Nat.le_trans hv hbs
  | 6 =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq
    subst hp_eq hr_eq
    obtain ⟨hv, hr⟩ := prostMergeBytes_length_le wt bs hm
    refine ⟨⟨hp.1, hp.2.1, ?_⟩, hr⟩
    intro w hw
    simp only [Option.mem_def, Option.some.injEq] at hw
    subst hw
    exact Nat.le_trans hv hbs
  | 0 | _ + 7 =>
    rcases Option.mem_map.mp h with ⟨r, hs, hp'⟩
    injection hp' with hp_eq hr_eq
    subst hp_eq hr_eq
    exact ⟨hp, (prostSkipField_group_length_le (2 * bs.length + 2)).1 _ _ _ bs r hs⟩

private theorem prostDecodeLoop_preserves (fuel N : ℕ) (p : ProtoSignalMessage) (bs : Bytes)
    {p' : ProtoSignalMessage}
    (hp : ProtoSignalFieldsLe N p) (hbs : bs.length ≤ N)
    (h : decodeLoop fuel p bs = some p') :
    ProtoSignalFieldsLe N p' := by
  induction fuel generalizing p bs with
  | zero =>
    cases bs with
    | nil =>
      simp only [decodeLoop, Option.some.injEq] at h
      subst h
      exact hp
    | cons _ _ => simp [decodeLoop] at h
  | succ fuel ih =>
    cases bs with
    | nil =>
      simp only [decodeLoop, Option.some.injEq] at h
      subst h
      exact hp
    | cons b tail =>
      simp only [decodeLoop] at h
      cases hk : decodeKey (b :: tail) with
      | none => rw [hk] at h; cases h
      | some kw =>
        rcases kw with ⟨⟨tag, wt⟩, rest⟩
        have hrest := Nat.le_trans (prostDecodeKey_length_le (b :: tail) hk) hbs
        rw [hk] at h
        dsimp only at h
        cases hm : mergeField p tag wt rest with
        | none => rw [hm] at h; cases h
        | some pr =>
          rcases pr with ⟨p1, rest'⟩
          obtain ⟨hp1, hrest'⟩ := prostMergeField_preserves hp hrest hm
          rw [hm] at h
          dsimp only at h
          exact ih p1 rest' hp1 (Nat.le_trans hrest' hrest) h

theorem e2ePureOps_eval_signalMsgParse_lossless (ℓ : ℕ) (body : Bytes) :
    (e2ePureOps ℓ).eval .signalMsgParse body =
      match SignalMessage.tryFrom protoSignalCodec body with
      | .ok m =>
        some ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
              (m.ciphertext, (m.pqRatchet, m.addresses)))
      | .error _ => none := by
  dsimp only [e2ePureOps, E2EPureOp.eval]
  rcases hm : SignalMessage.tryFrom protoSignalCodec body with _ | m
  · rfl
  · dsimp only
    have hfields :
        m.ciphertext.length ≤ body.length ∧
        m.pqRatchet.length ≤ body.length ∧
        (∀ a ∈ m.addresses, a.length ≤ body.length) := by
      unfold SignalMessage.tryFrom at hm
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hm
      split at hm
      · cases hm
      · split at hm
        · cases hm
        · split at hm
          · cases hm
          · cases hdec : protoSignalCodec.decode ((body.take (body.length - macLength)).drop 1) with
            | none => rw [hdec] at hm; cases hm
            | some p =>
              rw [hdec] at hm
              dsimp only at hm
              cases hrk : p.ratchetKey with
              | none => rw [hrk] at hm; cases hm
              | some rk =>
                rw [hrk] at hm
                dsimp only at hm
                cases hdes : PublicKey.deserialize rk with
                | error _ => rw [hdes] at hm; cases hm
                | ok srk =>
                  rw [hdes] at hm
                  dsimp only at hm
                  cases hctr : p.counter with
                  | none => rw [hctr] at hm; cases hm
                  | some ctr =>
                    rw [hctr] at hm
                    dsimp only at hm
                    cases hct : p.ciphertext with
                    | none => rw [hct] at hm; cases hm
                    | some ct =>
                      rw [hct] at hm
                      dsimp only at hm
                      injection hm with hm'
                      subst hm'
                      have hbuf : ((body.take (body.length - macLength)).drop 1).length ≤ body.length := by
                        have := List.length_take_le (body.length - macLength) body
                        simp only [List.length_drop]
                        omega
                      have hemp : ProtoSignalFieldsLe body.length emptyProtoSignalMessage :=
                        ⟨by simp [emptyProtoSignalMessage],
                         by simp [emptyProtoSignalMessage],
                         by simp [emptyProtoSignalMessage]⟩
                      have hp := prostDecodeLoop_preserves _ body.length emptyProtoSignalMessage _
                        hemp hbuf hdec
                      refine ⟨hp.1 ct hct, ?_, hp.2.2⟩
                      cases hpq : p.pqRatchet with
                      | none => simp
                      | some pq => exact hp.2.1 pq hpq
    obtain ⟨hct, hpq, haddr⟩ := hfields
    have hmap : m.addresses.map (·.take body.length) = m.addresses := by
      cases ha : m.addresses with
      | none => rfl
      | some a =>
        dsimp only [Option.map]
        rw [List.take_of_length_le (haddr a ha)]
    rw [List.take_of_length_le hct, List.take_of_length_le hpq, hmap]

private theorem flatMap_blockToBytesLE_length :
    ∀ l : List Block, (l.flatMap blockToBytesLE).length = 16 * l.length
  | [] => rfl
  | b :: bs => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, blockToBytesLE,
      List.length_ofFn, flatMap_blockToBytesLE_length bs]
    omega

theorem aesCbcEncrypt_length_eq {ℓ : ℕ} (E : BitVec 256 → Block → Block)
    (k : BitVec 256) (iv : Block) (pt : Plain ℓ) :
    (aesCbcEncrypt E k iv pt.toList).length = 16 * (ℓ / 16 + 1) := by
  unfold aesCbcEncrypt
  rw [flatMap_blockToBytesLE_length, List.Vector.toList_length, nBlocks, pt.toList_length]

theorem e2eCryptoOps_eval_aes256CbcEnc_lossless (ℓ : ℕ) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (k : BitVec 256) (iv : Block) (pt : Plain ℓ) :
    (e2eCryptoOps ℓ P C K).eval .aes256CbcEnc (k, (iv, pt)) =
      aesCbcEncrypt C.E k iv pt.toList := by
  dsimp only [e2eCryptoOps, E2ECryptoOp.eval]
  have hlen := aesCbcEncrypt_length_eq C.E k iv pt
  exact List.take_of_length_le (by omega)

private theorem prostEncodeVarintAux_length_le :
    ∀ (k : ℕ) (v : BitVec 64), (encodeVarintAux k v).length ≤ k
  | 0, _ => by simp [encodeVarintAux]
  | k + 1, v => by
    simp only [encodeVarintAux]
    split
    · simp
    · simp only [List.length_cons]
      have ih := prostEncodeVarintAux_length_le k (v >>> 7)
      omega

private theorem prostEncodeBytesField_length_le (tag : ℕ) (opt : Option Bytes) (N : ℕ)
    (h : ∀ b ∈ opt, b.length ≤ N) :
    (encodeBytesField tag opt).length ≤ 20 + N := by
  cases opt with
  | none => simp [encodeBytesField]
  | some b =>
    simp only [encodeBytesField, List.length_append]
    have h1 := prostEncodeVarintAux_length_le 10 (BitVec.ofNat 64 (tag * 8 + WireType.lengthDelimited.toNat))
    have h2 := prostEncodeVarintAux_length_le 10 (BitVec.ofNat 64 b.length)
    have h3 := h b rfl
    unfold encodeKey encodeVarint
    omega

private theorem prostEncodeUint32Field_length_le (tag : ℕ) (opt : Option (BitVec 32)) :
    (encodeUint32Field tag opt).length ≤ 20 := by
  cases opt with
  | none => simp [encodeUint32Field]
  | some v =>
    simp only [encodeUint32Field, List.length_append]
    have h1 := prostEncodeVarintAux_length_le 10 (BitVec.ofNat 64 (tag * 8 + WireType.varint.toNat))
    have h2 := prostEncodeVarintAux_length_le 10 (v.zeroExtend 64)
    unfold encodeKey encodeVarint
    omega

theorem signalMsgNew_serialized_length_le {ℓ : ℕ} (F : ShaCompress)
    (msgVer : BitVec 8) (macKey : BitVec 256) (addr? : Option Bytes) (senderRk : PublicKey)
    (ctr prevCtr : BitVec 32) (ct : Bytes) (idS idR : IdentityKey) (pqMsg : Bytes)
    (hct : ct.length ≤ 32 * (ℓ / 32 + 2))
    (hpq : pqMsg.length ≤ 96)
    (haddr : ∀ a ∈ addr?, a.length ≤ 128) :
    (SignalMessage.new F protoSignalCodec msgVer macKey addr? senderRk ctr prevCtr ct
      idS idR pqMsg).serialized.length ≤ 32 * (ℓ / 32) + 450 := by
  have hmac : (hmacSha256Trunc8 F (keyToBytes32 macKey)
      ((CryptoGames.LibsignalSession.macIds idS idR).toList ++
        serializeContent protoSignalCodec msgVer senderRk ctr prevCtr ct pqMsg addr?)).length ≤ 8 :=
    List.length_take_le 8 _
  dsimp only [SignalMessage.new, computeMac]
  rw [List.length_append]
  have hser : (serializeContent protoSignalCodec msgVer senderRk ctr prevCtr ct pqMsg addr?).length ≤
      32 * (ℓ / 32) + 442 := by
    dsimp only [serializeContent, protoSignalCodec, encode]
    simp only [List.length_cons, List.length_append]
    have f1 := prostEncodeBytesField_length_le 1 (some senderRk.serialize) 33
      (fun b hb => by
        simp only [Option.mem_def, Option.some.injEq] at hb
        subst hb
        rw [publicKey_serialize_length])
    have f2 := prostEncodeUint32Field_length_le 2 (some ctr)
    have f3 := prostEncodeUint32Field_length_le 3 (some prevCtr)
    have f4 := prostEncodeBytesField_length_le 4 (some ct) (32 * (ℓ / 32 + 2))
      (fun b hb => by
        simp only [Option.mem_def, Option.some.injEq] at hb
        subst hb
        exact hct)
    have f5 := prostEncodeBytesField_length_le 5 (if pqMsg.isEmpty then none else some pqMsg) 96
      (fun b hb => by
        split at hb
        · cases hb
        · simp only [Option.mem_def, Option.some.injEq] at hb
          subst hb
          exact hpq)
    have f6 := prostEncodeBytesField_length_le 6 addr? 128 haddr
    omega
  omega

/-- Under reachable ciphertext, SPQR payload, and address bounds, `E2ECryptoOp.signalMsgEncode` does not truncate. -/
theorem e2eCryptoOps_eval_signalMsgEncode_lossless (ℓ : ℕ) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem)
    (msgVer : BitVec 8) (senderRk : PublicKey) (ctr prevCtr : BitVec 32)
    (ct pqMsg : Bytes) (addr? : Option Bytes) (idS idR : IdentityKey) (macKey : BitVec 256)
    (hct : ct.length ≤ 32 * (ℓ / 32 + 2))
    (hpq : pqMsg.length ≤ 96)
    (haddr : ∀ a ∈ addr?, a.length ≤ 128) :
    (e2eCryptoOps ℓ P C K).eval .signalMsgEncode
      ((msgVer, (senderRk, (ctr, prevCtr))), (ct, (pqMsg, (addr?, (idS, (idR, macKey)))))) =
      (SignalMessage.new C.F protoSignalCodec msgVer macKey addr? senderRk ctr prevCtr ct
        idS idR pqMsg).serialized := by
  dsimp only [e2eCryptoOps, E2ECryptoOp.eval]
  have hlen := signalMsgNew_serialized_length_le C.F msgVer macKey addr? senderRk ctr prevCtr
    ct idS idR pqMsg hct hpq haddr
  exact List.take_of_length_le (by omega)

theorem e2ePureOps_eval_wrapWhisperWire_lossless (ℓ : ℕ) (ct : Bytes)
    (hct : ct.length < 32 * (2 * (ℓ / 32) + 26)) :
    (e2ePureOps ℓ).eval .wrapWhisperWire ct =
      if ct.isEmpty then [] else wireWhisper :: ct := by
  dsimp only [e2ePureOps, E2EPureOp.eval]
  split
  · rfl
  · exact List.take_of_length_le (by simp; omega)

private theorem prostNatVarint_length_le_div64 (n : ℕ) :
    (CryptoGames.LibsignalSessionApi.Prost.varint n).length ≤ n / 64 + 1 := by
  induction n using CryptoGames.LibsignalSessionApi.Prost.varint.induct with
  | case1 n hn =>
    rw [CryptoGames.LibsignalSessionApi.Prost.varint.eq_1]
    simp [hn]
  | case2 n hn ih =>
    rw [CryptoGames.LibsignalSessionApi.Prost.varint.eq_1]
    simp only [hn, ↓reduceDIte, List.length_cons]
    omega

private theorem prostNatVarint_length_le_k :
    ∀ (k n : ℕ), n < 128 ^ (k + 1) →
      (CryptoGames.LibsignalSessionApi.Prost.varint n).length ≤ k + 1
  | 0, n, hn => by
    rw [CryptoGames.LibsignalSessionApi.Prost.varint.eq_1]
    have hn' : n < 128 := by simpa using hn
    simp [hn']
  | k + 1, n, hn => by
    rw [CryptoGames.LibsignalSessionApi.Prost.varint.eq_1]
    by_cases h128 : n < 128
    · simp [h128]
    · simp only [h128, ↓reduceDIte, List.length_cons]
      have hdiv : n / 128 < 128 ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        simpa [Nat.pow_succ] using hn
      have ih := prostNatVarint_length_le_k k (n / 128) hdiv
      omega

private theorem prostNatVarint_length_le_5_of_u32 (v : BitVec 32) :
    (CryptoGames.LibsignalSessionApi.Prost.varint v.toNat).length ≤ 5 :=
  prostNatVarint_length_le_k 4 v.toNat (lt_trans v.isLt (by decide))

private theorem prostUint32Field_length_le_6 (tag : ℕ) (htag : tag < 16)
    (opt : Option (BitVec 32)) :
    (CryptoGames.LibsignalSessionApi.Prost.uint32Field tag opt).length ≤ 6 := by
  cases opt with
  | none => simp [CryptoGames.LibsignalSessionApi.Prost.uint32Field]
  | some v =>
    simp only [CryptoGames.LibsignalSessionApi.Prost.uint32Field,
      CryptoGames.LibsignalSessionApi.Prost.key, List.length_append]
    have hk := prostNatVarint_length_le_k 0 (8 * tag + 0) (by omega)
    have hv := prostNatVarint_length_le_5_of_u32 v
    omega

private theorem prostBytesField_fixed_length_le (tag : ℕ) (htag : tag < 16) (b : Bytes) :
    (CryptoGames.LibsignalSessionApi.Prost.bytesField tag (some b)).length ≤
      1 + (CryptoGames.LibsignalSessionApi.Prost.varint b.length).length + b.length := by
  simp only [CryptoGames.LibsignalSessionApi.Prost.bytesField,
    CryptoGames.LibsignalSessionApi.Prost.key, List.length_append]
  have hk := prostNatVarint_length_le_k 0 (8 * tag + 2) (by omega)
  omega

theorem e2ePureOps_eval_wrapPreKeyWire_lossless (ℓ : ℕ) (regIdA : BitVec 32)
    (hdr : (hdrT (ℓ := ℓ)).denote) (inner : Bytes)
    (hinner : inner.length ≤ 32 * (ℓ / 32) + 512) :
    (e2ePureOps ℓ).eval .wrapPreKeyWire (regIdA, (hdr, inner)) =
      if inner.isEmpty then []
      else wirePrekey :: (e2eExpectedPreKeyMsg regIdA (hdrOfV hdr) inner).bytes := by
  dsimp only [e2ePureOps, E2EPureOp.eval]
  split
  · rfl
  · apply List.take_of_length_le
    let m := e2eExpectedPreKeyMsg regIdA (hdrOfV hdr) inner
    change (wirePrekey :: m.bytes).length ≤ 32 * (2 * (ℓ / 32) + 84)
    simp only [PreKeyMessageFields.bytes, ProtoPreKeySignalMessage.encode, List.length_cons,
      List.length_append]
    have f1 := prostUint32Field_length_le_6 1 (by decide) m.opkId
    have f2 := prostBytesField_fixed_length_le 2 (by decide) (djbKey m.baseKey)
    have hdjb2 : (djbKey m.baseKey).length = 33 := by simp [djbKey]
    have hv33 := prostNatVarint_length_le_k 0 33 (by decide)
    rw [hdjb2] at f2
    have f3 := prostBytesField_fixed_length_le 3 (by decide) (djbKey m.idPub)
    have hdjb3 : (djbKey m.idPub).length = 33 := by simp [djbKey]
    rw [hdjb3] at f3
    have f4 := prostBytesField_fixed_length_le 4 (by decide) m.inner
    have f5 := prostUint32Field_length_le_6 5 (by decide) (some m.regId)
    have f6 := prostUint32Field_length_le_6 6 (by decide) (some m.spkId)
    have f7 := prostUint32Field_length_le_6 7 (by decide) (some m.kpkId)
    have f8 := prostBytesField_fixed_length_le 8 (by decide) (kyberKey m.kyberCt)
    have hkyb : (kyberKey m.kyberCt).length = 1569 := by simp [kyberKey]
    have hv1569 := prostNatVarint_length_le_k 1 1569 (by decide)
    rw [hkyb] at f8
    have hm_len : m.inner.length = inner.length := rfl
    have hvin := prostNatVarint_length_le_div64 m.inner.length
    omega

end Computational.Proofs.E2E.Dsl.ClampsLossless
