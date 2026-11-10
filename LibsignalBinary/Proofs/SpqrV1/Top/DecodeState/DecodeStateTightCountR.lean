/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChain
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TightSize
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Proof
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Field
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
import LibsignalBinary.Proofs.SpqrV1Sync.ErasureCode
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.DecoderCodec
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.EncoderCodec
import LibsignalBinary.Proofs.SpqrV1Sync.TopSize

/-!
# Tight Event Bounds, Canonical Wire Helpers, & `TopStateTight` Extraction

Proves leaf `SpqrTightEvs` bounds for zero-capacity `bytes::merge` and `RawVec<ChainEpoch>::grow_one`,
canonical wire round-trip lemmas, and `e2ar_topStateTight_encode_valid` showing every
`TopStateTight F K bs` state encodes a valid canonical `PqRatchetState`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateTightCountR

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint encodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalSpqrV1 hiding WireType decodeVarint encodeVarint
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState)
open CryptoVerification.SpqrV1.Prost.BytesMerge (protoWireTypeToCodec)
open CryptoVerification.SpqrV1.Prost.MessageMerge (ChainParamsMergeGhost codecWireTypeToProto)
open CryptoVerification.SpqrV1Sync.Braid
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoVerification.SpqrV1Sync.Erasure
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.TopSync
open CryptoVerification.SpqrV1Sync.Codec
  (LoopsTo decodeKey_encodeKey loopsTo_chain loopsTo_chainEpoch loopsTo_chainParams
   loopsTo_epochDirection loopsTo_pqRatchetState loopsTo_v1State loopsTo_versionNegotiation
   mergeBytes_encode mergeMessage_encode proto_decodeVarint_encodeVarint proto_encodeVarint_length)
open CryptoVerification.SpqrV1Sync.SendTotal
  (AuthOk BOk BOkTight DecTightOnly DecWF DecWFTight EncWF RecvSmallTight)
open LibsignalBinary.Heap (AllocEvent rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (SpqrTightEvs spqrAllocTightCost)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_ValidAuthPB tlb_ValidChainEpochPB tlb_ValidChainPB tlb_ValidChunkedCt1AcknowledgedPB
   tlb_ValidChunkedCt1ReceivedPB tlb_ValidChunkedCt1SampledPB tlb_ValidChunkedCt2SampledPB
   tlb_ValidChunkedEkReceivedCt1SampledPB tlb_ValidChunkedEkSentCt1ReceivedPB
   tlb_ValidChunkedHeaderReceivedPB tlb_ValidChunkedHeaderSentPB tlb_ValidChunkedKeysSampledPB
   tlb_ValidChunkedKeysUnsampledPB tlb_ValidChunkedNoHeaderReceivedPB tlb_ValidEpochDirPB
   tlb_ValidInnerStatePB tlb_ValidOptAuthPB tlb_ValidPolyDecoderPB tlb_ValidPolyEncoderPB
   tlb_ValidPqRatchetStatePB tlb_ValidUcCt1SentEkReceivedPB tlb_ValidUcCt1SentPB
   tlb_ValidUcCt2SentPB tlb_ValidUcEkSentCt1ReceivedPB tlb_ValidUcEkSentPB
   tlb_ValidUcHeaderReceivedPB tlb_ValidUcHeaderSentPB tlb_ValidUcKeysUnsampledPB
   tlb_ValidUcNoHeaderReceivedPB tlb_ValidV1StatePB tlb_ValidVersionNegotiationPB tlb_lenPrefixed)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight TopStateTightW topStateTightW_length_le topStateTightW_links_le_three
   topStateTight_length_le)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget (GrowOneStrideEnv growOneStrideEvents)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget (ChainParamsMergePostEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget (BytesMerge3EnvCore)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

/-! ## 1. Tight Leaf Event Bounds (`SpqrTightEvs`) -/

theorem e2ar_reserveCap_zero_le {vLen R : Nat} (h8 : 8 ≤ R) (hv : vLen ≤ R) :
    reserveCap 0 0 vLen ≤ R := by
  unfold reserveCap
  omega

/-- On a `0#64`-capacity `Vec<u8>`, `bytesMergeEventsCore` on a succeeding `mergeBytes` with
`v.length ≤ R` (`8 ≤ R`) emits at most `2` non-free allocs (`tmp` + `reserveCap 0 0 v.length`)
plus `1` `free`, fitting `SpqrTightEvs 2 (2 * spqrAllocTightCost R) R`. -/
theorem e2ar_bytesMergeEventsCore_zero_tight {wt : WireType} {bs v rest : List (BitVec 8)}
    {R : Nat} (hm : mergeBytes wt bs = some (v, rest)) (h8 : 8 ≤ R) (hvR : v.length ≤ R) :
    SpqrTightEvs 2 (2 * spqrAllocTightCost R) R (bytesMergeEventsCore wt 0#64 bs) := by
  unfold bytesMergeEventsCore
  rw [hm]
  dsimp only
  by_cases hv0 : v.length = 0
  · simp only [hv0, ↓reduceIte]
    exact SpqrTightEvs.nil 2 (2 * spqrAllocTightCost R) R
  · have hnle : ¬ v.length ≤ 0 := by omega
    simp only [hv0, ↓reduceIte, doReserveClearEvents, BitVec.toNat_zero, hnle]
    have h1 : SpqrTightEvs 1 (spqrAllocTightCost R) R (rustAllocEvents v.length 1) :=
      SpqrTightEvs.rustAlloc hvR (by decide)
    have h2 : SpqrTightEvs 1 (spqrAllocTightCost R) R
        (rustAllocEvents (reserveCap 0 0 v.length) 1) :=
      SpqrTightEvs.rustAlloc (e2ar_reserveCap_zero_le h8 hvR) (by decide)
    have h3 : SpqrTightEvs 0 0 0 (rustDeallocEvents v.length 1) :=
      SpqrTightEvs.rustDealloc v.length 1
    exact ((h1.append h2).append h3).mono (by omega) (by omega) (by omega)

theorem e2ar_bytesMerge3_zero_tight32 {wt : WireType} {bs v rest : List (BitVec 8)}
    {evs : List AllocEvent}
    (hm : mergeBytes wt bs = some (v, rest)) (hv : v.length ≤ 32)
    (hevs : BytesMerge3EnvCore wt 0#64 bs evs) :
    SpqrTightEvs 2 1476 32 evs := by
  change evs = bytesMergeEventsCore wt 0#64 bs at hevs
  subst hevs
  exact (e2ar_bytesMergeEventsCore_zero_tight hm (by decide) hv).mono
    (Nat.le_refl 2) (by decide) (Nat.le_refl 32)

theorem e2ar_bytesMerge3_zero_tight79236 {wt : WireType} {bs v rest : List (BitVec 8)}
    {evs : List AllocEvent}
    (hm : mergeBytes wt bs = some (v, rest)) (hv : v.length ≤ 79236)
    (hevs : BytesMerge3EnvCore wt 0#64 bs evs) :
    SpqrTightEvs 2 180468 79236 evs := by
  change evs = bytesMergeEventsCore wt 0#64 bs at hevs
  subst hevs
  exact (e2ar_bytesMergeEventsCore_zero_tight hm (by decide) hv).mono
    (Nat.le_refl 2) (by decide) (Nat.le_refl 79236)

/-- `RawVec<ChainEpoch>::grow_one` from `cap = 0#64` allocates `4 * 112 = 448` bytes (`align = 8`),
fitting `SpqrTightEvs 1 9789 448`. -/
theorem e2ar_growOneChainEpoch_zero_tight {evs : List AllocEvent}
    (h : GrowOneStrideEnv 0#64 112 8 evs) :
    SpqrTightEvs 1 9789 448 evs := by
  unfold GrowOneStrideEnv growOneStrideEvents at h
  simp only [↓reduceIte] at h
  subst h
  exact SpqrTightEvs.rustAlloc (Nat.le_refl 448) (by decide)

theorem e2ar_chainParamsMergePostEnv_ok_nil {x : ChainParamsMergeGhost}
    {p : ChainParamsPB × List (BitVec 8)} {evs : List AllocEvent}
    (hok : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
        ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some p)
    (h : ChainParamsMergePostEnv x evs) :
    evs = [] := by
  unfold ChainParamsMergePostEnv at h
  rw [hok] at h
  exact h

theorem e2ar_decodeVarint2Env_some_nil {bs : List (BitVec 8)}
    {p : BitVec 64 × List (BitVec 8)} {evs : List AllocEvent}
    (hdv : decodeVarint bs = some p) (h : DecodeVarint2Env bs evs) :
    evs = [] := by
  change DecodeVarintSliceEnv bs evs at h
  unfold DecodeVarintSliceEnv decodeVarintSliceEvents at h
  rw [hdv] at h
  exact h

/-! ## 2. Canonical Wire, Key, & Length-Prefix Round-Trip Lemmas -/

theorem e2ar_tlb_lenPrefixed_eq_proto (raw rest : Bytes) :
    tlb_lenPrefixed raw rest =
      CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 raw.length) ++
        (raw ++ rest) := by
  unfold tlb_lenPrefixed
  rw [CryptoVerification.SpqrV1.Auth.protoEncodeVarint_eq_codec, List.append_assoc]

theorem e2ar_decodeVarint_encodeVarint_codec (v : BitVec 64) (rest : Bytes) :
    decodeVarint (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v ++ rest) =
      some (v, rest) := by
  rw [← CryptoVerification.SpqrV1.Prost.BytesMerge.proto_decodeVarint_toOption,
    proto_decodeVarint_encodeVarint]
  rfl

theorem e2ar_decodeVarint_lenPrefixed (raw rest : Bytes) :
    decodeVarint (tlb_lenPrefixed raw rest) =
      some (BitVec.ofNat 64 raw.length, raw ++ rest) := by
  rw [e2ar_tlb_lenPrefixed_eq_proto]
  exact e2ar_decodeVarint_encodeVarint_codec (BitVec.ofNat 64 raw.length) (raw ++ rest)

theorem e2ar_decodeVarint_encodeKey (tag : BitVec 32)
    (wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType) (rest : Bytes)
    (h2 : tag.toNat < 2 ^ 29) :
    ∃ key : BitVec 64,
      decodeVarint (CryptoVerification.LibsignalSpqrV1.Proto.encodeKey tag wt ++ rest) =
        some (key, rest) ∧
      key.toNat = 8 * tag.toNat + wt.toU32.toNat := by
  let key : BitVec 64 := ((tag <<< 3) ||| wt.toU32).zeroExtend 64
  refine ⟨key, ?_, ?_⟩
  · unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeKey
    exact e2ar_decodeVarint_encodeVarint_codec key rest
  · have hw : wt.toU32.toNat < 8 := by cases wt <;> decide
    have hor := Nat.two_pow_add_eq_or_of_lt (i := 3) (b := wt.toU32.toNat) hw tag.toNat
    simp only [Nat.reducePow] at hor
    dsimp only [key]
    rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    simp only [Nat.reducePow]
    rw [show tag.toNat * 8 % 4294967296 = 8 * tag.toNat by omega, ← hor]
    omega

theorem e2ar_mergeBytes_lenPrefixed (v rest : Bytes) (hv : v.length < 2 ^ 64) :
    mergeBytes .lengthDelimited (tlb_lenPrefixed v rest) = some (v, rest) := by
  have hproto := mergeBytes_encode v rest hv
  have hopt := CryptoVerification.SpqrV1.Prost.BytesMerge.proto_mergeBytes_toOption
    .lengthDelimited (tlb_lenPrefixed v rest)
  rw [← e2ar_tlb_lenPrefixed_eq_proto] at hproto
  rw [hproto] at hopt
  exact hopt.symm

theorem e2ar_mergeMessage_lenPrefixed {N : Type}
    (mfN : CryptoVerification.SpqrV1Sync.Codec.MergeFieldFn N)
    (dN : Nat) (encodeRaw : N → Bytes) (n₀ n : N) (depth : Nat) (rest : Bytes)
    (hsub : LoopsTo mfN dN n₀ (encodeRaw n) n)
    (hlen : (encodeRaw n).length < 2 ^ 64) (hd : dN < depth) :
    (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      mfN .lengthDelimited n₀ (tlb_lenPrefixed (encodeRaw n) rest) depth).toOption =
        some (n, rest) := by
  rw [e2ar_tlb_lenPrefixed_eq_proto, mergeMessage_encode mfN dN encodeRaw n₀ n depth rest hsub hlen hd]
  rfl

theorem e2ar_raw_lt_of_lenPrefixed_lt {raw rest : Bytes}
    (hlt : (tlb_lenPrefixed raw rest).length < 2 ^ 63) :
    raw.length < 2 ^ 64 := by
  unfold tlb_lenPrefixed at hlt
  simp only [List.length_append] at hlt
  omega

theorem e2ar_encodeBytesUncond_eq_key_lenPrefixed (tag : BitVec 32) (v rest : Bytes) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond tag v ++ rest =
      CryptoVerification.LibsignalSpqrV1.Proto.encodeKey tag .lengthDelimited ++
        tlb_lenPrefixed v rest := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond tlb_lenPrefixed
  simp [List.append_assoc]

theorem e2ar_encodeMessage_eq_key_lenPrefixed {N : Type} (encodeRaw : N → Bytes)
    (tag : BitVec 32) (n : N) (rest : Bytes) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage encodeRaw tag n ++ rest =
      CryptoVerification.LibsignalSpqrV1.Proto.encodeKey tag .lengthDelimited ++
        tlb_lenPrefixed (encodeRaw n) rest := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage tlb_lenPrefixed
  simp [List.append_assoc]

theorem e2ar_mergeMessage_chainParams_lenPrefixed (m : ChainParamsPB) (rest : Bytes)
    (depth : Nat) (hd : 0 < depth)
    (hlt : (tlb_lenPrefixed (ChainParamsPB.encodeRaw m) rest).length < 2 ^ 63) :
    (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      ChainParamsPB.mergeField .lengthDelimited default
      (tlb_lenPrefixed (ChainParamsPB.encodeRaw m) rest) depth).toOption =
        some (m, rest) := by
  have hlen := e2ar_raw_lt_of_lenPrefixed_lt hlt
  exact e2ar_mergeMessage_lenPrefixed ChainParamsPB.mergeField 0 ChainParamsPB.encodeRaw
    default m depth rest (loopsTo_chainParams m) hlen hd

theorem e2ar_mergeMessage_epochDirection_lenPrefixed (m : CryptoVerification.LibsignalSpqrV1.EpochDirectionPB)
    (rest : Bytes) (depth : Nat) (hd : 0 < depth)
    (hlt : (tlb_lenPrefixed (CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.encodeRaw m) rest).length < 2 ^ 63) :
    (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField .lengthDelimited default
      (tlb_lenPrefixed (CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.encodeRaw m) rest) depth).toOption =
        some (m, rest) := by
  have hlen := e2ar_raw_lt_of_lenPrefixed_lt hlt
  exact e2ar_mergeMessage_lenPrefixed
    CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField 0
    CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.encodeRaw
    default m depth rest (loopsTo_epochDirection m hlen) hlen hd

theorem e2ar_mergeMessage_chainEpoch_lenPrefixed (m : ChainEpochPB) (rest : Bytes)
    (depth : Nat) (hd : 1 < depth)
    (hlt : (tlb_lenPrefixed (ChainEpochPB.encodeRaw m) rest).length < 2 ^ 63) :
    (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      ChainEpochPB.mergeField .lengthDelimited default
      (tlb_lenPrefixed (ChainEpochPB.encodeRaw m) rest) depth).toOption =
        some (m, rest) := by
  have hlen := e2ar_raw_lt_of_lenPrefixed_lt hlt
  exact e2ar_mergeMessage_lenPrefixed ChainEpochPB.mergeField 1 ChainEpochPB.encodeRaw
    default m depth rest (loopsTo_chainEpoch m hlen) hlen hd

theorem e2ar_mergeMessage_chain_lenPrefixed (m : ChainPB) (rest : Bytes)
    (depth : Nat) (hd : 2 < depth)
    (hlt : (tlb_lenPrefixed (ChainPB.encodeRaw m) rest).length < 2 ^ 63) :
    (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      ChainPB.mergeField .lengthDelimited default
      (tlb_lenPrefixed (ChainPB.encodeRaw m) rest) depth).toOption =
        some (m, rest) := by
  have hlen := e2ar_raw_lt_of_lenPrefixed_lt hlt
  exact e2ar_mergeMessage_lenPrefixed ChainPB.mergeField 2 ChainPB.encodeRaw
    default m depth rest (loopsTo_chain m hlen) hlen hd

theorem e2ar_mergeMessage_versionNegotiation_lenPrefixed (m : VersionNegotiationPB) (rest : Bytes)
    (depth : Nat) (hd : 1 < depth)
    (hlt : (tlb_lenPrefixed (VersionNegotiationPB.encodeRaw m) rest).length < 2 ^ 63) :
    (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      VersionNegotiationPB.mergeField .lengthDelimited default
      (tlb_lenPrefixed (VersionNegotiationPB.encodeRaw m) rest) depth).toOption =
        some (m, rest) := by
  have hlen := e2ar_raw_lt_of_lenPrefixed_lt hlt
  exact e2ar_mergeMessage_lenPrefixed VersionNegotiationPB.mergeField 1 VersionNegotiationPB.encodeRaw
    default m depth rest (loopsTo_versionNegotiation m hlen) hlen hd

theorem e2ar_mergeMessage_v1State_lenPrefixed (m : V1State) (rest : Bytes)
    (depth : Nat) (hd : 3 < depth)
    (hlt : (tlb_lenPrefixed (V1State.encodeRaw m) rest).length < 2 ^ 63) :
    (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      V1State.mergeField .lengthDelimited default
      (tlb_lenPrefixed (V1State.encodeRaw m) rest) depth).toOption =
        some (m, rest) := by
  have hlen := e2ar_raw_lt_of_lenPrefixed_lt hlt
  exact e2ar_mergeMessage_lenPrefixed V1State.mergeField 3 V1State.encodeRaw
    default m depth rest (loopsTo_v1State m hlen) hlen hd

/-! ## 3. `TopStateTight` → `tlb_ValidPqRatchetStatePB` Extraction -/

private theorem e2ar_needed_le {len : Nat} (hlen : len ≤ 1152) (j : Nat) :
    needed len j ≤ 1200 := by
  unfold needed
  split <;> omega

private theorem e2ar_sortedSetPt_tight_length_le {n : Nat} {d : PolyDecoder}
    (hd : DecWFTight n d) (hn : n ≤ 576) (j : Nat) (hj : j < d.pts.length) :
    d.pts[j].vec.length ≤ 72 := by
  let S := (d.pts[j].vec.map fun pt => pt.x.value.toNat).toFinset
  have hnec : d.necessaryPoints j ≤ 36 := by
    unfold PolyDecoder.necessaryPoints
    rw [hd.1.1]
    dsimp only
    split_ifs <;> omega
  have hsub_union : S ⊆ S.filter (· < d.necessaryPoints j) ∪ S.filter (d.necessaryPoints j ≤ ·) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hlt : x < d.necessaryPoints j
    · exact Or.inl ⟨hx, hlt⟩
    · exact Or.inr ⟨hx, by omega⟩
  have hsub_range : S.filter (· < d.necessaryPoints j) ⊆ Finset.range (d.necessaryPoints j) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact hx.2
  have hlt_card : (S.filter (· < d.necessaryPoints j)).card ≤ d.necessaryPoints j := by
    have hc := Finset.card_le_card hsub_range
    rwa [Finset.card_range] at hc
  have hge_card : (S.filter (d.necessaryPoints j ≤ ·)).card ≤ d.necessaryPoints j := hd.2 j hj
  have htot_card : S.card ≤
      (S.filter (· < d.necessaryPoints j)).card + (S.filter (d.necessaryPoints j ≤ ·)).card :=
    (Finset.card_le_card hsub_union).trans (Finset.card_union_le _ _)
  have hnd : (d.pts[j].vec.map fun pt => pt.x.value.toNat).Nodup := (hd.1.2.2 j hj).imp ne_of_lt
  have hlen : d.pts[j].vec.length = S.card := by
    dsimp [S]
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  omega

theorem e2ar_validOptAuthPB_of_authOk (F : ShaCompress) {a : Authenticator}
    (ha : AuthOk a) :
    tlb_ValidOptAuthPB (some ((spqrAuthApi F).into_pb a)) := by
  intro v hv
  cases hv
  rcases ha with ⟨hrk, hck⟩
  simp [tlb_ValidAuthPB, spqrAuthApi, Authenticator.intoPb, hrk, hck]

theorem e2ar_validPolyEncoderPB_of_encWF {len : Nat} {enc : PolyEncoder}
    (henc : EncWF len enc) (hlen : len ≤ 1152) :
    tlb_ValidPolyEncoderPB (spqrPolyApi.encoder_into_pb enc) := by
  rcases henc with ⟨msg, henc, rfl⟩
  rcases enc with ⟨idx, s⟩
  rcases henc with hpts | ⟨polys, hpolys, hlen16, hcoeff⟩
  · simp only at hpts
    subst hpts
    dsimp only [spqrPolyApi, protoPolyEncoderToPb, PolyEncoder.intoPb, tlb_ValidPolyEncoderPB]
    refine ⟨Or.inr rfl, ?_, ?_, fun _ hs => nomatch hs⟩
    · simp [EncoderCodec.msgPoints_length]
    · intro b hb
      rcases List.mem_map.1 hb with ⟨pt, hpt, rfl⟩
      rcases List.mem_map.1 hpt with ⟨j, -, rfl⟩
      rw [EncoderCodec.flatMap_u16ToBeBytes_length, List.length_map, List.length_range]
      have := e2ar_needed_le hlen j
      omega
  · simp only at hpolys
    subst hpolys
    dsimp only [spqrPolyApi, protoPolyEncoderToPb, PolyEncoder.intoPb, tlb_ValidPolyEncoderPB]
    refine ⟨Or.inl rfl, by simp [hlen16], by simp, ?_⟩
    intro b hb
    rcases List.mem_map.1 hb with ⟨p, hp, rfl⟩
    rcases List.getElem_of_mem hp with ⟨j, hj, rfl⟩
    have hcj := (hcoeff j hj).1
    have hser : (Poly.serialize polys[j]).length = 2 * polys[j].coefficients.length :=
      EncoderCodec.flatMap_u16ToBeBytes_length polys[j].coefficients
    have := e2ar_needed_le hlen j
    omega

theorem e2ar_validPolyDecoderPB_of_decWFTight {n : Nat} {dec : PolyDecoder}
    (hdec : DecWFTight n dec) (hn : n ≤ 576) :
    tlb_ValidPolyDecoderPB (spqrPolyApi.decoder_into_pb dec) := by
  simp only [spqrPolyApi, protoPolyDecoderToPb, PolyDecoder.intoPb, tlb_ValidPolyDecoderPB]
  refine ⟨?_, ?_⟩
  · rw [List.length_map, hdec.1.2.1]
  · intro b hb
    rcases List.mem_map.1 hb with ⟨s, hs, rfl⟩
    rcases List.getElem_of_mem hs with ⟨j, hj, rfl⟩
    have hlen := e2ar_sortedSetPt_tight_length_le hdec hn j hj
    have hser := DecoderCodec.length_flatMap_serialize dec.pts[j].vec
    omega

theorem e2ar_validV1StatePB_of_bokTight (F : ShaCompress) (st : St F) (h : BOkTight st) :
    tlb_ValidV1StatePB st.into_pb := by
  rcases h with ⟨hbok, htight⟩
  intro is his
  cases st with
  | keysUnsampled s =>
    simp only [States.into_pb, Option.some.injEq] at his; subst his
    simp only [tlb_ValidInnerStatePB, tlb_ValidChunkedKeysUnsampledPB,
      Chunked.SendEk.KeysUnsampled.into_pb, Option.some.injEq]
    rintro u rfl; exact e2ar_validOptAuthPB_of_authOk F hbok
  | keysSampled s =>
    rcases hbok with ⟨ha, ⟨hdk, hek⟩, henc⟩
    simp only [States.into_pb, Option.some.injEq] at his; subst his
    simp only [tlb_ValidInnerStatePB, tlb_ValidChunkedKeysSampledPB,
      Chunked.SendEk.KeysSampled.into_pb, Option.some.injEq]
    refine ⟨fun u hu => ?_, by rintro e rfl; exact e2ar_validPolyEncoderPB_of_encWF henc (by decide)⟩
    subst hu; refine ⟨e2ar_validOptAuthPB_of_authOk F ha, ?_, ?_⟩
    · simp only [Unchunked.SendEk.HeaderSent.into_pb, hek, ENCAPSULATION_KEY_SIZE]; decide
    · simp only [Unchunked.SendEk.HeaderSent.into_pb, hdk, DECAPSULATION_KEY_SIZE]; decide
  | headerSent s =>
    rcases hbok with ⟨ha, hdk, henc, _⟩
    have hdk' : s.uc.dk.length = DECAPSULATION_KEY_SIZE := hdk
    simp only [States.into_pb, Option.some.injEq] at his; subst his
    simp only [tlb_ValidInnerStatePB, tlb_ValidChunkedHeaderSentPB,
      Chunked.SendEk.HeaderSent.into_pb, Option.some.injEq]
    refine ⟨fun u hu => ?_, by rintro e rfl; exact e2ar_validPolyEncoderPB_of_encWF henc (by decide),
      by rintro d rfl; exact e2ar_validPolyDecoderPB_of_decWFTight htight (by decide)⟩
    subst hu; refine ⟨e2ar_validOptAuthPB_of_authOk F ha, ?_⟩
    simp only [Unchunked.SendEk.EkSent.into_pb, hdk', DECAPSULATION_KEY_SIZE]; decide
  | ct1Received s =>
    rcases hbok with ⟨ha, ⟨hdk, hct1⟩, henc⟩
    simp only [States.into_pb, Option.some.injEq] at his; subst his
    simp only [tlb_ValidInnerStatePB, tlb_ValidChunkedCt1ReceivedPB,
      Chunked.SendEk.Ct1Received.into_pb, Option.some.injEq]
    refine ⟨fun u hu => ?_, by rintro e rfl; exact e2ar_validPolyEncoderPB_of_encWF henc (by decide)⟩
    subst hu; refine ⟨e2ar_validOptAuthPB_of_authOk F ha, ?_, ?_⟩
    · simp only [Unchunked.SendEk.EkSentCt1Received.into_pb, hdk, DECAPSULATION_KEY_SIZE]; decide
    · simp only [Unchunked.SendEk.EkSentCt1Received.into_pb, hct1, CIPHERTEXT1_SIZE]; decide
  | ekSentCt1Received s =>
    rcases hbok with ⟨ha, ⟨hdk, hct1⟩, _⟩
    simp only [States.into_pb, Option.some.injEq] at his; subst his
    simp only [tlb_ValidInnerStatePB, tlb_ValidChunkedEkSentCt1ReceivedPB,
      Chunked.SendEk.EkSentCt1Received.into_pb, Option.some.injEq]
    refine ⟨fun u hu => ?_, by rintro d rfl; exact e2ar_validPolyDecoderPB_of_decWFTight htight (by decide)⟩
    subst hu; refine ⟨e2ar_validOptAuthPB_of_authOk F ha, ?_, ?_⟩
    · simp only [Unchunked.SendEk.EkSentCt1Received.into_pb, hdk, DECAPSULATION_KEY_SIZE]; decide
    · simp only [Unchunked.SendEk.EkSentCt1Received.into_pb, hct1, CIPHERTEXT1_SIZE]; decide
  | noHeaderReceived s =>
    rcases hbok with ⟨ha, _⟩
    simp only [States.into_pb, Option.some.injEq] at his; subst his
    simp only [tlb_ValidInnerStatePB, tlb_ValidChunkedNoHeaderReceivedPB,
      Chunked.SendCt.NoHeaderReceived.into_pb, Option.some.injEq]
    exact ⟨by rintro u rfl; exact e2ar_validOptAuthPB_of_authOk F ha,
      by rintro d rfl; exact e2ar_validPolyDecoderPB_of_decWFTight htight (by decide)⟩
  | headerReceived s =>
    rcases hbok with ⟨ha, hhdr, _⟩
    have hhdr' : s.uc.hdr.length = HEADER_SIZE := hhdr
    simp only [States.into_pb, Option.some.injEq] at his; subst his
    simp only [tlb_ValidInnerStatePB, tlb_ValidChunkedHeaderReceivedPB,
      Chunked.SendCt.HeaderReceived.into_pb, Option.some.injEq]
    refine ⟨fun u hu => ?_, by rintro d rfl; exact e2ar_validPolyDecoderPB_of_decWFTight htight (by decide)⟩
    subst hu; refine ⟨e2ar_validOptAuthPB_of_authOk F ha, ?_⟩
    simp only [Unchunked.SendCt.HeaderReceived.into_pb, hhdr', HEADER_SIZE]; decide
  | ct1Sampled s =>
    rcases hbok with ⟨ha, ⟨hhdr, hes, hct1⟩, henc, _⟩
    simp only [States.into_pb, Option.some.injEq] at his; subst his
    simp only [tlb_ValidInnerStatePB, tlb_ValidChunkedCt1SampledPB,
      Chunked.SendCt.Ct1Sampled.into_pb, Option.some.injEq]
    refine ⟨fun u hu => ?_, by rintro e rfl; exact e2ar_validPolyEncoderPB_of_encWF henc (by decide),
      by rintro d rfl; exact e2ar_validPolyDecoderPB_of_decWFTight htight (by decide)⟩
    subst hu; refine ⟨e2ar_validOptAuthPB_of_authOk F ha, ?_, ?_, ?_⟩
    · simp only [Unchunked.SendCt.Ct1Sent.into_pb, hhdr, HEADER_SIZE]; decide
    · simp only [Unchunked.SendCt.Ct1Sent.into_pb, hes, ENCAPSULATION_STATE_SIZE]; decide
    · simp only [Unchunked.SendCt.Ct1Sent.into_pb, hct1, CIPHERTEXT1_SIZE]; decide
  | ekReceivedCt1Sampled s =>
    rcases hbok with ⟨ha, ⟨hes, hct1, hek⟩, henc⟩
    simp only [States.into_pb, Option.some.injEq] at his; subst his
    simp only [tlb_ValidInnerStatePB, tlb_ValidChunkedEkReceivedCt1SampledPB,
      Chunked.SendCt.EkReceivedCt1Sampled.into_pb, Option.some.injEq]
    refine ⟨fun u hu => ?_, by rintro e rfl; exact e2ar_validPolyEncoderPB_of_encWF henc (by decide)⟩
    subst hu; refine ⟨e2ar_validOptAuthPB_of_authOk F ha, ?_, ?_, ?_⟩
    · simp only [Unchunked.SendCt.Ct1SentEkReceived.into_pb, hes, ENCAPSULATION_STATE_SIZE]; decide
    · simp only [Unchunked.SendCt.Ct1SentEkReceived.into_pb, hek, ENCAPSULATION_KEY_SIZE]; decide
    · simp only [Unchunked.SendCt.Ct1SentEkReceived.into_pb, hct1, CIPHERTEXT1_SIZE]; decide
  | ct1Acknowledged s =>
    rcases hbok with ⟨ha, ⟨hhdr, hes, hct1⟩, _⟩
    simp only [States.into_pb, Option.some.injEq] at his; subst his
    simp only [tlb_ValidInnerStatePB, tlb_ValidChunkedCt1AcknowledgedPB,
      Chunked.SendCt.Ct1Acknowledged.into_pb, Option.some.injEq]
    refine ⟨fun u hu => ?_, by rintro d rfl; exact e2ar_validPolyDecoderPB_of_decWFTight htight (by decide)⟩
    subst hu; refine ⟨e2ar_validOptAuthPB_of_authOk F ha, ?_, ?_, ?_⟩
    · simp only [Unchunked.SendCt.Ct1Sent.into_pb, hhdr, HEADER_SIZE]; decide
    · simp only [Unchunked.SendCt.Ct1Sent.into_pb, hes, ENCAPSULATION_STATE_SIZE]; decide
    · simp only [Unchunked.SendCt.Ct1Sent.into_pb, hct1, CIPHERTEXT1_SIZE]; decide
  | ct2Sampled s =>
    rcases hbok with ⟨ha, henc⟩
    simp only [States.into_pb, Option.some.injEq] at his; subst his
    simp only [tlb_ValidInnerStatePB, tlb_ValidChunkedCt2SampledPB,
      Chunked.SendCt.Ct2Sampled.into_pb, Option.some.injEq]
    exact ⟨by rintro u rfl; exact e2ar_validOptAuthPB_of_authOk F ha,
      by rintro e rfl; exact e2ar_validPolyEncoderPB_of_encWF henc (by decide)⟩

theorem e2ar_validChainPB_of_chainOk (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : Nat → Bytes) (sendCtr : Nat → Nat) (recvSet : Nat → Finset Nat) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch)
    (hsp : SendPrevNil ch) (hsmall : RecvSmallTight ch)
    (hlinks_le : ch.links.length ≤ 3) :
    tlb_ValidChainPB ch.intoPb := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Chain.intoPb] using hlinks_le
  · have hroot : ch.nextRoot.length = 32 := by
      rw [h.hroot]
      simp
    simp [Chain.intoPb, hroot]
  · intro ep hep
    simp only [Chain.intoPb, List.mem_map] at hep
    rcases hep with ⟨l, hmem, rfl⟩
    obtain ⟨i, hl⟩ := List.mem_iff_getElem?.mp hmem
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hl
    have hlen := h.hlen
    have hsle := h.hsend_le
    have he : ch.sendEpoch.toNat - 1 + i ≤ ch.currentEpoch.toNat := by omega
    have hidx : ch.sendEpoch.toNat - 1 + i - (ch.sendEpoch.toNat - 1) = i := by omega
    obtain ⟨l', hl', hrd⟩ := h.hrecvDir (ch.sendEpoch.toNat - 1 + i) (by omega) he
    rw [hidx, hl] at hl'
    obtain rfl := Option.some.inj hl'
    have hrn : l.recv.next.length = 32 := by
      rw [hrd.hnext]
      exact length_nextAt F _ (length_seedAt _ _ _ _ _) _
    have hrp : l.recv.prev.data.length ≤ 79236 := hsmall l hmem
    have hsn : l.send.next.length ≤ 32 := by
      by_cases hse : ch.sendEpoch.toNat ≤ ch.sendEpoch.toNat - 1 + i
      · obtain ⟨l'', hl'', hsd⟩ := h.hsendDir (ch.sendEpoch.toNat - 1 + i) hse he
        rw [hidx, hl] at hl''
        obtain rfl := Option.some.inj hl''
        rw [hsd.hnext, length_nextAt F _ (length_seedAt _ _ _ _ _) _]
      · have hi0 : i = 0 := by omega
        subst hi0
        rw [h.hsendOld l (by omega) hl]
        simp
    have hsp' : l.send.prev.data = [] := hsp l hmem
    simp only [tlb_ValidChainEpochPB, Option.some.injEq]
    refine ⟨?_, ?_⟩
    · rintro d rfl
      refine ⟨hsn, ?_⟩
      simp [ChainEpochDirection.intoPb, hsp']
    · rintro d rfl
      refine ⟨?_, hrp⟩
      simp [ChainEpochDirection.intoPb, hrn]

/-- Every `TopStateTight F K bs` state encodes a canonical `PqRatchetState`
(`bs = encodeState pb`) satisfying `tlb_ValidPqRatchetStatePB pb`. -/
theorem e2ar_topStateTight_encode_valid {F : ShaCompress} {K : MlKem} {bs : Bytes}
    (hTop : TopStateTight F K bs) :
    ∃ pb : PqRatchetState, bs = encodeState pb ∧ tlb_ValidPqRatchetStatePB pb := by
  obtain ⟨authKey, dir, secret, st, sendEp, sendCtr, recvSet, vn?, ch?, chE, hw⟩ := hTop
  refine ⟨pbToPqRatchetState (topPb st vn? ch?), hw.htop.hbytes, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro vn hvn
    rcases hw.htop.hvn with rfl | rfl
    · simp [pbToPqRatchetState, topPb] at hvn
    · simp only [pbToPqRatchetState, topPb, Option.some.injEq] at hvn
      subst hvn
      simp only [tlb_ValidVersionNegotiationPB, vnOf, hw.hauth]
      exact Nat.le_refl 32
  · intro ch hch
    rcases hw.htop.hch with rfl | ⟨rfl, -, -⟩
    · simp only [pbToPqRatchetState, topPb, Option.map, Option.some.injEq] at hch
      subst hch
      exact e2ar_validChainPB_of_chainOk F authKey dir secret sendCtr recvSet chE
        hw.htop.hok hw.htop.hsendPrev hw.hsmall (topStateTightW_links_le_three hw)
    · simp [pbToPqRatchetState, topPb] at hch
  · intro v1 hv1
    simp only [pbToPqRatchetState, topPb, Option.map] at hv1
    injection hv1 with hv1
    injection hv1 with hv1
    subst hv1
    exact e2ar_validV1StatePB_of_bokTight F st hw.hbok

theorem e2ar_topStateTight_encode_valid_with_len {F : ShaCompress} {K : MlKem} {bs : Bytes}
    (hTop : TopStateTight F K bs) :
    ∃ pb : PqRatchetState,
      bs = encodeState pb ∧
      tlb_ValidPqRatchetStatePB pb ∧
      (encodeState pb).length ≤ spqrStateTightCapBytes := by
  obtain ⟨pb, rfl, hvalid⟩ := e2ar_topStateTight_encode_valid hTop
  exact ⟨pb, rfl, hvalid, topStateTight_length_le hTop⟩

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateTightCountR
