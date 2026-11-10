/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Proof
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Field
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget

/-!
# Zero-Capacity Tight Event Envelopes and Canonical Wire Round-Trip Lemmas

Tight `SpqrTightEvs` bounds for `bytesMergeEventsCore .lengthDelimited 0#64` and
`GrowOneStrideEnv 0#64 112 8`, together with canonical wire round-trip bridges from
`LibsignalSpqrV1.Proto` (`encodeKey`, `encodeVarint`, `encodeBytesField`, `encodeUint32Field`,
`encodeUint64Field`, `encodeInt32Field`) to `LibsignalProtoCodec`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.E2aTightBytesZeroAux

open CryptoVerification.LibsignalProtoCodec (decodeVarint mergeBytes)
open CryptoVerification.LibsignalSpqrV1 (Bytes)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeBytesUncond encodeInt32Field encodeKey encodeUint32Field
   encodeUint64Field encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.SpqrV1.Prost.BytesMerge
  (protoWireTypeToCodec proto_decodeVarint_toOption proto_mergeBytes_toOption)
open CryptoVerification.SpqrV1Sync.Codec
  (encodeBytesField_of_ne encodeInt32Field_of_ne encodeUint32Field_of_ne encodeUint64Field_of_ne
   mergeBytes_encode proto_decodeVarint_encodeVarint proto_encodeVarint_length)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents fitsEvents_append
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget (GrowOneStrideEnv growOneStrideEvents)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

/-! ## 1. Tight Event Envelopes at `cap = 0#64` -/

theorem e2a_bytesMergeEventsCore_zero_tight_32 {bs v rest : Bytes}
    (hm : mergeBytes .lengthDelimited bs = some (v, rest))
    (hlen : v.length ≤ 32) :
    SpqrTightEvs 2 1476 32 (bytesMergeEventsCore .lengthDelimited 0#64 bs) := by
  unfold bytesMergeEventsCore
  rw [hm]
  dsimp only
  by_cases hv0 : v.length = 0
  · simp [hv0, SpqrTightEvs.nil]
  · have hnot_le : ¬ v.length ≤ 0 := by omega
    simp only [hv0, ↓reduceIte, doReserveClearEvents,
      show (0#64 : BitVec 64).toNat = 0 from rfl, hnot_le, reserveCap]
    have ha1 : SpqrTightEvs 1 738 32 (rustAllocEvents v.length 1) :=
      SpqrTightEvs.rustAlloc hlen (by decide)
    have hmax : max (max (0 + v.length) (2 * 0)) 8 ≤ 32 := by omega
    have ha2 : SpqrTightEvs 1 738 32 (rustAllocEvents (max (max (0 + v.length) (2 * 0)) 8) 1) :=
      SpqrTightEvs.rustAlloc hmax (by decide)
    have hd : SpqrTightEvs 0 0 0 (rustDeallocEvents v.length 1) :=
      SpqrTightEvs.rustDealloc v.length 1
    exact ((ha1.append ha2).append hd).mono (by decide) (by decide) (by decide)

theorem e2a_bytesMergeEventsCore_zero_tight_79236 {bs v rest : Bytes}
    (hm : mergeBytes .lengthDelimited bs = some (v, rest))
    (hlen : v.length ≤ 79236) :
    SpqrTightEvs 2 180468 79236 (bytesMergeEventsCore .lengthDelimited 0#64 bs) := by
  unfold bytesMergeEventsCore
  rw [hm]
  dsimp only
  by_cases hv0 : v.length = 0
  · simp [hv0, SpqrTightEvs.nil]
  · have hnot_le : ¬ v.length ≤ 0 := by omega
    simp only [hv0, ↓reduceIte, doReserveClearEvents,
      show (0#64 : BitVec 64).toNat = 0 from rfl, hnot_le, reserveCap]
    have ha1 : SpqrTightEvs 1 90234 79236 (rustAllocEvents v.length 1) :=
      SpqrTightEvs.rustAlloc hlen (by decide)
    have hmax : max (max (0 + v.length) (2 * 0)) 8 ≤ 79236 := by omega
    have ha2 : SpqrTightEvs 1 90234 79236 (rustAllocEvents (max (max (0 + v.length) (2 * 0)) 8) 1) :=
      SpqrTightEvs.rustAlloc hmax (by decide)
    have hd : SpqrTightEvs 0 0 0 (rustDeallocEvents v.length 1) :=
      SpqrTightEvs.rustDealloc v.length 1
    exact ((ha1.append ha2).append hd).mono (by decide) (by decide) (by decide)

theorem e2a_growOneChainEpoch_zero_tight {evs : List AllocEvent}
    (h : GrowOneStrideEnv 0#64 112 8 evs) :
    SpqrTightEvs 1 9789 448 evs := by
  rw [h]
  unfold growOneStrideEvents
  simp only [↓reduceIte]
  exact SpqrTightEvs.rustAlloc (Nat.le_refl 448) (by decide)

theorem e2a_decodeVarint2Env_eq_nil {bs rest : Bytes} {v : BitVec 64} {evs : List AllocEvent}
    (hd : decodeVarint bs = some (v, rest)) (hdv : DecodeVarint2Env bs evs) :
    evs = [] := by
  change DecodeVarintSliceEnv bs evs at hdv
  simpa [DecodeVarintSliceEnv, decodeVarintSliceEvents, hd] using hdv

theorem e2a_fitsEnv_decodeVarint2_of_some {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {bs rest : Bytes} {v : BitVec 64} {maxOps cumCap maxReq : Nat}
    (hd : decodeVarint bs = some (v, rest))
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq)) :
    FitsEnv M lim st (DecodeVarint2Env bs) := by
  intro evs hdv
  rw [e2a_decodeVarint2Env_eq_nil hd hdv]
  exact hFit [] (SpqrTightEvs.nil maxOps cumCap maxReq)

theorem e2a_fitsEnv_tight_split {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {n₁ n₂ c₁ c₂ r₁ r₂ : Nat} {evs₁ : List AllocEvent}
    (h₁ : SpqrTightEvs n₁ c₁ r₁ evs₁)
    (hFit : FitsEnv M lim st (SpqrTightEvs (n₁ + n₂) (c₁ + c₂) (max r₁ r₂))) :
    FitsEnv M lim (M.stepEvents evs₁ st) (SpqrTightEvs n₂ c₂ r₂) :=
  fun evs₂ h₂ =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp (hFit (evs₁ ++ evs₂) (h₁.append h₂))).2

/-! ## 2. Canonical Wire Round-Trip Helpers -/

theorem e2a_decodeVarint_encodeVarint (v : BitVec 64) (rest : Bytes) :
    decodeVarint (encodeVarint v ++ rest) = some (v, rest) := by
  rw [← proto_decodeVarint_toOption, proto_decodeVarint_encodeVarint]
  rfl

/-- Canonical length-prefixed payload `encodeVarint (BitVec.ofNat 64 raw.length) ++ raw ++ rest`
(definitionally equal to `tlb_lenPrefixed raw rest`). -/
abbrev e2a_lenPrefixed (raw rest : Bytes) : Bytes :=
  encodeVarint (BitVec.ofNat 64 raw.length) ++ raw ++ rest

theorem e2a_decodeVarint_lenPrefixed {raw rest : Bytes} (h : raw.length < 2 ^ 64) :
    decodeVarint (e2a_lenPrefixed raw rest) =
      some (BitVec.ofNat 64 raw.length, raw ++ rest) ∧
    (BitVec.ofNat 64 raw.length).toNat = raw.length := by
  refine ⟨?_, ?_⟩
  · unfold e2a_lenPrefixed
    rw [List.append_assoc]
    exact e2a_decodeVarint_encodeVarint (BitVec.ofNat 64 raw.length) (raw ++ rest)
  · rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h

theorem e2a_mergeBytes_encode_assoc {v rest : Bytes} (h : v.length < 2 ^ 64) :
    mergeBytes .lengthDelimited
        (encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) =
      some (v, rest) := by
  change mergeBytes (protoWireTypeToCodec .lengthDelimited) _ = _
  rw [← proto_mergeBytes_toOption, mergeBytes_encode v rest h]
  rfl

theorem e2a_mergeBytes_encode {v rest : Bytes} (h : v.length < 2 ^ 64) :
    mergeBytes .lengthDelimited
        (encodeVarint (BitVec.ofNat 64 v.length) ++ v ++ rest) =
      some (v, rest) := by
  rw [List.append_assoc]
  exact e2a_mergeBytes_encode_assoc h

private theorem e2a_wt_toNat_lt (wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType) :
    wt.toU32.toNat < 8 := by
  cases wt <;> decide

private theorem e2a_wt_ofNat_toU32 (wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType) :
    CryptoVerification.LibsignalProtoCodec.WireType.ofNat? wt.toU32.toNat =
      some (protoWireTypeToCodec wt) := by
  cases wt <;> decide

/-- Canonical field-key decoding on `encodeKey tag wt ++ rest` (`1 ≤ tag.toNat < 2 ^ 29`). -/
theorem e2a_decodeKey_encodeKey (tag : BitVec 32)
    (wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType) (rest : Bytes)
    (h1 : 1 ≤ tag.toNat) (h2 : tag.toNat < 2 ^ 29) :
    let key : BitVec 64 := ((tag <<< 3) ||| wt.toU32).zeroExtend 64
    decodeVarint (encodeKey tag wt ++ rest) = some (key, rest) ∧
    key.toNat = 8 * tag.toNat + wt.toU32.toNat ∧
    ¬ 2 ^ 32 ≤ key.toNat ∧
    CryptoVerification.LibsignalProtoCodec.WireType.ofNat? (key.toNat % 8) =
      some (protoWireTypeToCodec wt) ∧
    key.toNat / 8 = tag.toNat ∧
    ¬ key.toNat / 8 < 1 := by
  intro key
  have hw := e2a_wt_toNat_lt wt
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 3) (b := wt.toU32.toNat) (by omega) tag.toNat
  simp only [Nat.reducePow] at hor
  have hkey : key.toNat = 8 * tag.toNat + wt.toU32.toNat := by
    dsimp only [key]
    rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    simp only [Nat.reducePow]
    rw [show tag.toNat * 8 % 4294967296 = 8 * tag.toNat by omega, ← hor]
    omega
  refine ⟨?_, hkey, by omega, ?_, by omega, by omega⟩
  · unfold encodeKey
    exact e2a_decodeVarint_encodeVarint key rest
  · rw [show key.toNat % 8 = wt.toU32.toNat by omega]
    exact e2a_wt_ofNat_toU32 wt

theorem e2a_encodeBytesField_append_of_ne (tag : BitVec 32) {v : Bytes} (hv : v ≠ [])
    (rest : Bytes) :
    encodeBytesField tag v ++ rest =
      encodeKey tag .lengthDelimited ++
        (encodeVarint (BitVec.ofNat 64 v.length) ++ v ++ rest) := by
  rw [encodeBytesField_of_ne tag v hv, encodeBytesUncond]
  simp only [List.append_assoc]

theorem e2a_encodeBytesField_of_nil (tag : BitVec 32) :
    encodeBytesField tag [] = [] :=
  rfl

theorem e2a_encodeUint32Field_append_of_ne (tag v : BitVec 32) (hv : v ≠ 0#32) (rest : Bytes) :
    encodeUint32Field tag v ++ rest =
      encodeKey tag .varint ++ (encodeVarint (v.zeroExtend 64) ++ rest) := by
  rw [encodeUint32Field_of_ne tag v hv, List.append_assoc]

theorem e2a_encodeUint32Field_of_zero (tag : BitVec 32) :
    encodeUint32Field tag 0#32 = [] :=
  rfl

theorem e2a_encodeUint64Field_append_of_ne (tag : BitVec 32) (v : BitVec 64) (hv : v ≠ 0#64)
    (rest : Bytes) :
    encodeUint64Field tag v ++ rest =
      encodeKey tag .varint ++ (encodeVarint v ++ rest) := by
  rw [encodeUint64Field_of_ne tag v hv, List.append_assoc]

theorem e2a_encodeUint64Field_of_zero (tag : BitVec 32) :
    encodeUint64Field tag 0#64 = [] :=
  rfl

theorem e2a_encodeInt32Field_append_of_ne (tag v : BitVec 32) (hv : v ≠ 0#32) (rest : Bytes) :
    encodeInt32Field tag v ++ rest =
      encodeKey tag .varint ++ (encodeVarint (v.signExtend 64) ++ rest) := by
  rw [encodeInt32Field_of_ne tag v hv, List.append_assoc]

theorem e2a_encodeInt32Field_of_zero (tag : BitVec 32) :
    encodeInt32Field tag 0#32 = [] :=
  rfl

theorem e2a_encodeVarint_len_le_10 (v : BitVec 64) :
    (encodeVarint v).length ≤ 10 :=
  (proto_encodeVarint_length v).2

end LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.E2aTightBytesZeroAux
