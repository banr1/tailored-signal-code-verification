/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Grow.Defs
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecv.HelpersA
import Symbolic.Proofs.Swarm.SHARED.SpqrX.Prost.MessageMerge.AppendX
import Symbolic.Proofs.Swarm.SHARED.StateSizePure

/-!
# SPQR V1 Send-Path Wire Weight and Chain Growth Bounds

Proves chain weight growth under `Chain.sendKey` and protobuf wire-decode weight bounds for
`V1State` and `PqRatchetState` across `decodeState`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF

open Symbolic.Swarm.CREF (SpqrOooBounded)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Top.StateSize.SymP3
open Symbolic.Swarm.TRREF.SpqrSemOf
open Symbolic.Swarm.TRREF.GrowthRecv

theorem spqrOooBounded_nil : SpqrOooBounded [] := by
  intro st hdec
  have hdec0 : PqRatchetState.decode [] = .ok { versionNegotiation := none, chain := none, inner := none } := rfl
  rw [hdec0] at hdec; injection hdec with hst; subst hst
  exact ⟨(by intro c hc; cases hc), (by intro v hv; cases hv)⟩

theorem spqr_send_inner_none_growth (st : Bytes) :
    SpqrOooBounded ([] : Bytes) ∧ ([] : Bytes).length ≤ st.length + 2^14 :=
  ⟨spqrOooBounded_nil, Nat.zero_le _⟩

/-! ## Chain Send-Key Weight Bounds -/

theorem mergeBytes_length_le' {wt : Proto.WireType} {bs rest v : Bytes}
    (h : Proto.mergeBytes wt bs = .ok (v, rest)) : v.length + 1 + rest.length ≤ bs.length ∧ v.length < 2 ^ 64 := by
  unfold Proto.mergeBytes Proto.checkWireType at h; split at h; · contradiction
  dsimp only [Bind.bind, Except.bind] at h; rcases except_bind_eq_ok h with ⟨⟨len, rest0⟩, hdv, h⟩
  dsimp only at h; have hlt := CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3.decodeVarint_length_lt hdv; rcases takeExact_length_eq h with ⟨hvlen, hsum⟩
  exact ⟨by omega, by rw [hvlen]; exact len.isLt⟩

theorem ite_ok_cases {ε α : Type} {c : Prop} [Decidable c] {t e : Except ε α} {x : α}
    (h : (if c then t else e) = .ok x) : t = .ok x ∨ e = .ok x := by
  by_cases hc : c <;> simp [hc] at h <;> [exact Or.inl h; exact Or.inr h]

theorem encodeRaw_le_encodeMessage {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32) (m : M) :
    (encodeRaw m).length ≤ (Proto.encodeMessage encodeRaw tag m).length := by
  unfold Proto.encodeMessage; simp only [List.length_append]; omega

theorem encodeRepeatedMessage_drop_le {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32) :
    ∀ (k : Nat) (ms : List M), (Proto.encodeRepeatedMessage encodeRaw tag (ms.drop k)).length ≤ (Proto.encodeRepeatedMessage encodeRaw tag ms).length
  | 0, ms => by simp
  | _ + 1, [] => by simp
  | k + 1, m :: ms => by
    simp only [List.drop_succ_cons, encodeRepeatedMessage_cons, List.length_append]
    have ih := encodeRepeatedMessage_drop_le encodeRaw tag k ms; omega

theorem encodeRepeatedMessage_set_le {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32) (K : Nat) :
    ∀ (xs : List M) (i : Nat) (x x' : M), xs[i]? = some x →
      (Proto.encodeMessage encodeRaw tag x').length ≤ (Proto.encodeMessage encodeRaw tag x).length + K →
      (Proto.encodeRepeatedMessage encodeRaw tag (xs.set i x')).length ≤ (Proto.encodeRepeatedMessage encodeRaw tag xs).length + K
  | [], _, _, _, hget, _ => by simp at hget
  | a :: xs, 0, x, x', hget, hle => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget; subst hget
    simp only [List.set_cons_zero, encodeRepeatedMessage_cons, List.length_append]; omega
  | a :: xs, i + 1, x, x', hget, hle => by
    simp only [List.getElem?_cons_succ] at hget; simp only [List.set_cons_succ, encodeRepeatedMessage_cons, List.length_append]
    have ih := encodeRepeatedMessage_set_le encodeRaw tag K xs i x x' hget hle; omega

theorem linkToPb_modify_send_le (link : ChainEpoch) (send' : ChainEpochDirection) (K : Nat)
    (h : (EpochDirectionPB.encodeRaw send'.intoPb).length ≤ (EpochDirectionPB.encodeRaw link.send.intoPb).length + K) :
    (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 (linkToPb { link with send := send' })).length ≤
      (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 (linkToPb link)).length + K + 44 := by
  have hm' := encodeMessage_length_le ChainEpochPB.encodeRaw 3#32 (linkToPb { link with send := send' })
  have hm := encodeRaw_le_encodeMessage ChainEpochPB.encodeRaw 3#32 (linkToPb link)
  simp only [ChainEpochPB.encodeRaw, linkToPb, Proto.encodeOptMessage, List.length_append] at hm' hm ⊢
  have hs' := encodeMessage_length_le EpochDirectionPB.encodeRaw 1#32 send'.intoPb
  have hs := encodeRaw_le_encodeMessage EpochDirectionPB.encodeRaw 1#32 link.send.intoPb; omega

theorem clearSendNextPrefix_le1_weight_le {n : Nat} (hn : n ≤ 1) (links : List ChainEpoch) :
    (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ((Chain.clearSendNextPrefix n links).map linkToPb)).length ≤
    (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (links.map linkToPb)).length + 44 := by
  have hcases : n = 0 ∨ n = 1 := by omega
  rcases hcases with rfl | rfl
  · simp [Chain.clearSendNextPrefix]
  · cases links with
    | nil => simp [Chain.clearSendNextPrefix]
    | cons x xs =>
      simp only [Chain.clearSendNextPrefix, List.map, encodeRepeatedMessage_cons, List.length_append]
      have hclear : (EpochDirectionPB.encodeRaw x.send.clearNext.intoPb).length ≤ (EpochDirectionPB.encodeRaw x.send.intoPb).length + 0 := by
        simp only [ChainEpochDirection.clearNext, ChainEpochDirection.intoPb, EpochDirectionPB.encodeRaw, List.length_append]
        have hempty : Proto.encodeBytesField 2#32 [] = [] := rfl
        rw [hempty, List.length_nil]; omega
      have hlink := linkToPb_modify_send_le x x.send.clearNext 0 hclear; dsimp only [linkToPb] at hlink ⊢; omega

theorem nextKey_encodeRaw_le {hkdf : HkdfFn} {ced ced' : ChainEpochDirection} {out : BitVec 32 × Bytes}
    (h : ced.nextKey hkdf = .ok (ced', out)) :
    (EpochDirectionPB.encodeRaw ced'.intoPb).length ≤ (EpochDirectionPB.encodeRaw ced.intoPb).length + 76 := by
  unfold ChainEpochDirection.nextKey ChainEpochDirection.nextKeyInternal at h
  rcases except_bind_eq_ok h with ⟨⟨next', ctr', out0⟩, hnk, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, _⟩
  split at hnk; · contradiction
  split at hnk; · contradiction
  injection hnk with htriple; injection htriple with hnext' _; subst hnext'
  simp only [ChainEpochDirection.intoPb, EpochDirectionPB.encodeRaw, List.length_append]
  have h1 := encodeUint32Field_length_le 1#32 ctr'
  have h2 := encodeBytesField_length_le 2#32
    ((hkdf (List.replicate 32 0#8) ced.next (CryptoGames.HMAC.toBEBytes 4 (ced.ctr + 1#32) ++ chainNextInfo) 64).take 32)
  have htake : ((hkdf (List.replicate 32 0#8) ced.next (CryptoGames.HMAC.toBEBytes 4 (ced.ctr + 1#32) ++ chainNextInfo) 64).take 32).length ≤ 32 := by
    simp [List.length_take]
  omega

theorem chain_sendKey_weight_le {hkdf : HkdfFn} {c1 c2 : Chain} {ep : Epoch} {out : BitVec 32 × Bytes}
    (h : c1.sendKey hkdf ep = .ok (c2, out)) : chainWeight c2.intoPb ≤ chainWeight c1.intoPb + 164 := by
  unfold Chain.sendKey at h; split at h; · contradiction
  rcases except_bind_eq_ok h with ⟨epochIndex0, _, h⟩; dsimp only at h
  generalize hself1 :
    (if (c1.sendEpoch != ep) = true then
      let dropCount := epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
      let epochIndex' := epochIndex0 - dropCount
      let links1 := c1.links.drop dropCount
      let links2 := Chain.clearSendNextPrefix epochIndex' links1
      ({ c1 with sendEpoch := ep, links := links2 }, epochIndex')
    else (c1, epochIndex0)) = pair1 at h
  rcases pair1 with ⟨self1, epochIndex⟩
  have hself1_le :
      (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (self1.links.map linkToPb)).length ≤
      (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (c1.links.map linkToPb)).length + 44 ∧
      self1.nextRoot = c1.nextRoot := by
    split at hself1
    · rcases Prod.mk.inj hself1 with ⟨rfl, _⟩; refine ⟨?_, rfl⟩
      have hle1 : epochIndex0 - (epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH) ≤ 1 := by simp only [EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH]; omega
      have hc := clearSendNextPrefix_le1_weight_le hle1 (c1.links.drop (epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH))
      have hd := encodeRepeatedMessage_drop_le ChainEpochPB.encodeRaw 3#32 (epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH) (c1.links.map linkToPb)
      rw [← List.map_drop] at hd; dsimp only at hc hd ⊢; omega
    · rcases Prod.mk.inj hself1 with ⟨rfl, _⟩; exact ⟨by omega, rfl⟩
  dsimp only at h; cases hget : self1.links[epochIndex]? with
  | none => simp [hget] at h
  | some link =>
    rw [hget] at h; dsimp only [Bind.bind, Except.bind] at h
    rcases except_bind_eq_ok h with ⟨⟨send', out'⟩, hnk, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, _⟩
    cases hnk_inner : link.send.nextKey hkdf with
    | error _ => simp [ChainResult.ofPanic, hnk_inner] at hnk
    | ok res =>
      rw [hnk_inner] at hnk; injection hnk with hres; subst hres
      have hnk_len := nextKey_encodeRaw_le hnk_inner; have hmod := linkToPb_modify_send_le link send' 76 hnk_len
      have hget_map : (self1.links.map linkToPb)[epochIndex]? = some (linkToPb link) := by rw [List.getElem?_map, hget]; rfl
      have hset := encodeRepeatedMessage_set_le ChainEpochPB.encodeRaw 3#32 120
        (self1.links.map linkToPb) epochIndex (linkToPb link) (linkToPb { link with send := send' }) hget_map (by omega)
      have hmap_set : (self1.links.set epochIndex { link with send := send' }).map linkToPb =
          (self1.links.map linkToPb).set epochIndex (linkToPb { link with send := send' }) := by rw [List.map_set]
      rcases hself1_le with ⟨hlinks_le, hroot_eq⟩
      change (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32
        ((self1.links.set epochIndex { link with send := send' }).map linkToPb)).length + self1.nextRoot.length ≤
        (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (c1.links.map linkToPb)).length + c1.nextRoot.length + 164
      rw [hmap_set, hroot_eq]; omega

/-! ## `V1State` and `PqRatchetState` Wire Weight Bounds -/

def bytesSum (xs : List Bytes) : Nat := (xs.map List.length).sum

@[scoped simp] theorem bytesSum_nil : bytesSum [] = 0 := rfl

@[scoped simp] theorem bytesSum_cons (b : Bytes) (bs : List Bytes) : bytesSum (b :: bs) = b.length + bytesSum bs := by simp [bytesSum]

@[scoped simp] theorem bytesSum_append (xs ys : List Bytes) : bytesSum (xs ++ ys) = bytesSum xs + bytesSum ys := by simp [bytesSum, List.sum_append]

theorem mergeRepeatedBytes_bytesSum_le {wt : Proto.WireType} {xs xs' : List Bytes} {rest rest' : Bytes}
    (h : Proto.mergeRepeatedBytes wt xs rest = .ok (xs', rest')) : bytesSum xs' + rest'.length ≤ bytesSum xs + rest.length + 1 := by
  unfold Proto.mergeRepeatedBytes at h
  rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
  rcases mergeBytes_length_le' hm with ⟨h1, _⟩; simp only [bytesSum_append, bytesSum_cons, bytesSum_nil]; omega

def encWeight (m : PolynomialEncoder) : Nat := bytesSum m.pts + bytesSum m.polys

def optEncWeight : Option PolynomialEncoder → Nat := optWeight encWeight

def decWeight (m : PolynomialDecoder) : Nat := bytesSum m.pts

def optDecWeight : Option PolynomialDecoder → Nat := optWeight decWeight

def authWeight (m : ProtoAuthenticator) : Nat := m.rootKey.length + m.macKey.length

def optAuthWeight : Option ProtoAuthenticator → Nat := optWeight authWeight

theorem polyEnc_mergeField_weight_le (d : Nat) (m : PolynomialEncoder) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (m' : PolynomialEncoder) (rest' : Bytes)
    (h : PolynomialEncoder.mergeField m tag wt rest d = .ok (m', rest')) :
    encWeight m' + rest'.length ≤ encWeight m + rest.length + 1 := by
  unfold PolynomialEncoder.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint32_length_lt hm; simp only [encWeight]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeRepeatedBytes_bytesSum_le hm; simp only [encWeight]; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := mergeRepeatedBytes_bytesSum_le hm; simp only [encWeight]; omega
      · rcases except_bind_eq_ok h with ⟨bs', hskip, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := GrowthRecv.skipField_length_le hskip; simp only [encWeight]; omega

theorem polyDec_mergeField_weight_le (d : Nat) (m : PolynomialDecoder) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (m' : PolynomialDecoder) (rest' : Bytes)
    (h : PolynomialDecoder.mergeField m tag wt rest d = .ok (m', rest')) :
    decWeight m' + rest'.length ≤ decWeight m + rest.length + 1 := by
  unfold PolynomialDecoder.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint32_length_lt hm; simp only [decWeight]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeUint32_length_lt hm; simp only [decWeight]; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := mergeRepeatedBytes_bytesSum_le hm; simp only [decWeight]; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have := mergeBool_length_lt hm; simp only [decWeight]; omega
        · rcases except_bind_eq_ok h with ⟨bs', hskip, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have := GrowthRecv.skipField_length_le hskip; simp only [decWeight]; omega

theorem auth_mergeField_weight_le (d : Nat) (m : ProtoAuthenticator) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (m' : ProtoAuthenticator) (rest' : Bytes)
    (h : ProtoAuthenticator.mergeField m tag wt rest d = .ok (m', rest')) :
    authWeight m' + rest'.length ≤ authWeight m + rest.length + 1 := by
  unfold ProtoAuthenticator.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    rcases mergeBytes_length_le' hm with ⟨h1, _⟩; simp only [authWeight]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      rcases mergeBytes_length_le' hm with ⟨h1, _⟩; simp only [authWeight]; omega
    · rcases except_bind_eq_ok h with ⟨bs', hskip, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := GrowthRecv.skipField_length_le hskip; simp only [authWeight]; omega

theorem ucKeysUnsampled_mergeField_le (d : Nat) (m : V1State.Unchunked.KeysUnsampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.KeysUnsampled) (rest' : Bytes)
    (h : V1State.Unchunked.KeysUnsampled.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.KeysUnsampled.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := GrowthRecv.skipField_length_le hs; omega

theorem ucHeaderSent_mergeField_le (d : Nat) (m : V1State.Unchunked.HeaderSent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.HeaderSent) (rest' : Bytes)
    (h : V1State.Unchunked.HeaderSent.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.HeaderSent.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le' hm with ⟨h1, _⟩; dsimp only; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le' hm with ⟨h1, _⟩; dsimp only; omega
        · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have := GrowthRecv.skipField_length_le hs; omega

theorem ucEkSent_mergeField_le (d : Nat) (m : V1State.Unchunked.EkSent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.EkSent) (rest' : Bytes)
    (h : V1State.Unchunked.EkSent.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.EkSent.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le' hm with ⟨h1, _⟩; dsimp only; omega
      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := GrowthRecv.skipField_length_le hs; omega

theorem ucEkSentCt1Received_mergeField_le (d : Nat) (m : V1State.Unchunked.EkSentCt1Received) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.EkSentCt1Received) (rest' : Bytes)
    (h : V1State.Unchunked.EkSentCt1Received.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.EkSentCt1Received.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le' hm with ⟨h1, _⟩; dsimp only; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le' hm with ⟨h1, _⟩; dsimp only; omega
        · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have := GrowthRecv.skipField_length_le hs; omega

theorem ucNoHeaderReceived_mergeField_le (d : Nat) (m : V1State.Unchunked.NoHeaderReceived) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.NoHeaderReceived) (rest' : Bytes)
    (h : V1State.Unchunked.NoHeaderReceived.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.NoHeaderReceived.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := GrowthRecv.skipField_length_le hs; omega

theorem ucHeaderReceived_mergeField_le (d : Nat) (m : V1State.Unchunked.HeaderReceived) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.HeaderReceived) (rest' : Bytes)
    (h : V1State.Unchunked.HeaderReceived.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.HeaderReceived.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le' hm with ⟨h1, _⟩; dsimp only; omega
      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := GrowthRecv.skipField_length_le hs; omega

theorem ucCt1Sent_mergeField_le (d : Nat) (m : V1State.Unchunked.Ct1Sent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.Ct1Sent) (rest' : Bytes)
    (h : V1State.Unchunked.Ct1Sent.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.Ct1Sent.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le' hm with ⟨h1, _⟩; dsimp only; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le' hm with ⟨h1, _⟩; dsimp only; omega
        · split at h
          · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            rcases mergeBytes_length_le' hm with ⟨h1, _⟩; dsimp only; omega
          · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            have := GrowthRecv.skipField_length_le hs; omega

theorem ucCt1SentEkReceived_mergeField_le (d : Nat) (m : V1State.Unchunked.Ct1SentEkReceived) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.Ct1SentEkReceived) (rest' : Bytes)
    (h : V1State.Unchunked.Ct1SentEkReceived.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.Ct1SentEkReceived.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le' hm with ⟨h1, _⟩; dsimp only; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le' hm with ⟨h1, _⟩; dsimp only; omega
        · split at h
          · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            rcases mergeBytes_length_le' hm with ⟨h1, _⟩; dsimp only; omega
          · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            have := GrowthRecv.skipField_length_le hs; omega

theorem ucCt2Sent_mergeField_le (d : Nat) (m : V1State.Unchunked.Ct2Sent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.Ct2Sent) (rest' : Bytes)
    (h : V1State.Unchunked.Ct2Sent.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.Ct2Sent.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := GrowthRecv.skipField_length_le hs; omega

def ckKeysUnsampledW (m : V1State.Chunked.KeysUnsampled) : Nat := optWeight (fun u => optAuthWeight u.auth) m.uc

def ckKeysSampledW (m : V1State.Chunked.KeysSampled) : Nat := optWeight (fun u => optAuthWeight u.auth) m.uc + optEncWeight m.sendingHdr

def ckHeaderSentW (m : V1State.Chunked.HeaderSent) : Nat := optWeight (fun u => optAuthWeight u.auth) m.uc + optEncWeight m.sendingEk + optDecWeight m.receivingCt1

def ckCt1ReceivedW (m : V1State.Chunked.Ct1Received) : Nat := optWeight (fun u => optAuthWeight u.auth) m.uc + optEncWeight m.sendingEk

def ckEkSentCt1ReceivedW (m : V1State.Chunked.EkSentCt1Received) : Nat := optWeight (fun u => optAuthWeight u.auth) m.uc + optDecWeight m.receivingCt2

def ckNoHeaderReceivedW (m : V1State.Chunked.NoHeaderReceived) : Nat := optWeight (fun u => optAuthWeight u.auth) m.uc + optDecWeight m.receivingHdr

def ckHeaderReceivedW (m : V1State.Chunked.HeaderReceived) : Nat := optWeight (fun u => optAuthWeight u.auth) m.uc + optDecWeight m.receivingEk

def ckCt1SampledW (m : V1State.Chunked.Ct1Sampled) : Nat := optWeight (fun u => optAuthWeight u.auth) m.uc + optEncWeight m.sendingCt1 + optDecWeight m.receivingEk

def ckEkReceivedCt1SampledW (m : V1State.Chunked.EkReceivedCt1Sampled) : Nat := optWeight (fun u => optAuthWeight u.auth) m.uc + optEncWeight m.sendingCt1

def ckCt1AcknowledgedW (m : V1State.Chunked.Ct1Acknowledged) : Nat := optWeight (fun u => optAuthWeight u.auth) m.uc + optDecWeight m.receivingEk

def ckCt2SampledW (m : V1State.Chunked.Ct2Sampled) : Nat := optWeight (fun u => optAuthWeight u.auth) m.uc + optEncWeight m.sendingCt2

theorem ckKeysUnsampled_mergeField_le (d : Nat) (m : V1State.Chunked.KeysUnsampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.KeysUnsampled) (rest' : Bytes)
    (h : V1State.Chunked.KeysUnsampled.mergeField m tag wt rest d = .ok (m', rest')) :
    ckKeysUnsampledW m' + rest'.length ≤ ckKeysUnsampledW m + rest.length + 1 := by
  unfold V1State.Chunked.KeysUnsampled.mergeField at h; rcases ite_ok_cases h with h | h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le _ _ rfl d ucKeysUnsampled_mergeField_le wt m.uc v rest bs' hm
    simp only [ckKeysUnsampledW] at this ⊢; omega
  · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := GrowthRecv.skipField_length_le hs; simp only [ckKeysUnsampledW]; omega

theorem ckKeysSampled_mergeField_le (d : Nat) (m : V1State.Chunked.KeysSampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.KeysSampled) (rest' : Bytes)
    (h : V1State.Chunked.KeysSampled.mergeField m tag wt rest d = .ok (m', rest')) :
    ckKeysSampledW m' + rest'.length ≤ ckKeysSampledW m + rest.length + 1 := by
  unfold V1State.Chunked.KeysSampled.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le V1State.Unchunked.HeaderSent.mergeField (fun u => optAuthWeight u.auth) rfl d ucHeaderSent_mergeField_le wt m.uc v rest bs' hm
    simp only [ckKeysSampledW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le PolynomialEncoder.mergeField encWeight rfl d polyEnc_mergeField_weight_le wt m.sendingHdr v rest bs' hm
      simp only [ckKeysSampledW, optEncWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := GrowthRecv.skipField_length_le hs; omega

theorem ckHeaderSent_mergeField_le (d : Nat) (m : V1State.Chunked.HeaderSent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.HeaderSent) (rest' : Bytes)
    (h : V1State.Chunked.HeaderSent.mergeField m tag wt rest d = .ok (m', rest')) :
    ckHeaderSentW m' + rest'.length ≤ ckHeaderSentW m + rest.length + 1 := by
  unfold V1State.Chunked.HeaderSent.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le V1State.Unchunked.EkSent.mergeField (fun u => optAuthWeight u.auth) rfl d ucEkSent_mergeField_le wt m.uc v rest bs' hm
    simp only [ckHeaderSentW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le PolynomialEncoder.mergeField encWeight rfl d polyEnc_mergeField_weight_le wt m.sendingEk v rest bs' hm
      simp only [ckHeaderSentW, optEncWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := mergeOptMessage_weight_le PolynomialDecoder.mergeField decWeight rfl d polyDec_mergeField_weight_le wt m.receivingCt1 v rest bs' hm
        simp only [ckHeaderSentW, optDecWeight] at this ⊢; omega
      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := GrowthRecv.skipField_length_le hs; omega

theorem ckCt1Received_mergeField_le (d : Nat) (m : V1State.Chunked.Ct1Received) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.Ct1Received) (rest' : Bytes)
    (h : V1State.Chunked.Ct1Received.mergeField m tag wt rest d = .ok (m', rest')) :
    ckCt1ReceivedW m' + rest'.length ≤ ckCt1ReceivedW m + rest.length + 1 := by
  unfold V1State.Chunked.Ct1Received.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le V1State.Unchunked.EkSentCt1Received.mergeField (fun u => optAuthWeight u.auth) rfl d ucEkSentCt1Received_mergeField_le wt m.uc v rest bs' hm
    simp only [ckCt1ReceivedW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le PolynomialEncoder.mergeField encWeight rfl d polyEnc_mergeField_weight_le wt m.sendingEk v rest bs' hm
      simp only [ckCt1ReceivedW, optEncWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := GrowthRecv.skipField_length_le hs; omega

theorem ckEkSentCt1Received_mergeField_le (d : Nat) (m : V1State.Chunked.EkSentCt1Received) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.EkSentCt1Received) (rest' : Bytes)
    (h : V1State.Chunked.EkSentCt1Received.mergeField m tag wt rest d = .ok (m', rest')) :
    ckEkSentCt1ReceivedW m' + rest'.length ≤ ckEkSentCt1ReceivedW m + rest.length + 1 := by
  unfold V1State.Chunked.EkSentCt1Received.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le V1State.Unchunked.EkSentCt1Received.mergeField (fun u => optAuthWeight u.auth) rfl d ucEkSentCt1Received_mergeField_le wt m.uc v rest bs' hm
    simp only [ckEkSentCt1ReceivedW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le PolynomialDecoder.mergeField decWeight rfl d polyDec_mergeField_weight_le wt m.receivingCt2 v rest bs' hm
      simp only [ckEkSentCt1ReceivedW, optDecWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := GrowthRecv.skipField_length_le hs; omega

theorem ckNoHeaderReceived_mergeField_le (d : Nat) (m : V1State.Chunked.NoHeaderReceived) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.NoHeaderReceived) (rest' : Bytes)
    (h : V1State.Chunked.NoHeaderReceived.mergeField m tag wt rest d = .ok (m', rest')) :
    ckNoHeaderReceivedW m' + rest'.length ≤ ckNoHeaderReceivedW m + rest.length + 1 := by
  unfold V1State.Chunked.NoHeaderReceived.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le V1State.Unchunked.NoHeaderReceived.mergeField (fun u => optAuthWeight u.auth) rfl d ucNoHeaderReceived_mergeField_le wt m.uc v rest bs' hm
    simp only [ckNoHeaderReceivedW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le PolynomialDecoder.mergeField decWeight rfl d polyDec_mergeField_weight_le wt m.receivingHdr v rest bs' hm
      simp only [ckNoHeaderReceivedW, optDecWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := GrowthRecv.skipField_length_le hs; omega

theorem ckHeaderReceived_mergeField_le (d : Nat) (m : V1State.Chunked.HeaderReceived) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.HeaderReceived) (rest' : Bytes)
    (h : V1State.Chunked.HeaderReceived.mergeField m tag wt rest d = .ok (m', rest')) :
    ckHeaderReceivedW m' + rest'.length ≤ ckHeaderReceivedW m + rest.length + 1 := by
  unfold V1State.Chunked.HeaderReceived.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le V1State.Unchunked.HeaderReceived.mergeField (fun u => optAuthWeight u.auth) rfl d ucHeaderReceived_mergeField_le wt m.uc v rest bs' hm
    simp only [ckHeaderReceivedW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le PolynomialDecoder.mergeField decWeight rfl d polyDec_mergeField_weight_le wt m.receivingEk v rest bs' hm
      simp only [ckHeaderReceivedW, optDecWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := GrowthRecv.skipField_length_le hs; omega

theorem ckCt1Sampled_mergeField_le (d : Nat) (m : V1State.Chunked.Ct1Sampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.Ct1Sampled) (rest' : Bytes)
    (h : V1State.Chunked.Ct1Sampled.mergeField m tag wt rest d = .ok (m', rest')) :
    ckCt1SampledW m' + rest'.length ≤ ckCt1SampledW m + rest.length + 1 := by
  unfold V1State.Chunked.Ct1Sampled.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le V1State.Unchunked.Ct1Sent.mergeField (fun u => optAuthWeight u.auth) rfl d ucCt1Sent_mergeField_le wt m.uc v rest bs' hm
    simp only [ckCt1SampledW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le PolynomialEncoder.mergeField encWeight rfl d polyEnc_mergeField_weight_le wt m.sendingCt1 v rest bs' hm
      simp only [ckCt1SampledW, optEncWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := mergeOptMessage_weight_le PolynomialDecoder.mergeField decWeight rfl d polyDec_mergeField_weight_le wt m.receivingEk v rest bs' hm
        simp only [ckCt1SampledW, optDecWeight] at this ⊢; omega
      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := GrowthRecv.skipField_length_le hs; omega

theorem ckEkReceivedCt1Sampled_mergeField_le (d : Nat) (m : V1State.Chunked.EkReceivedCt1Sampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.EkReceivedCt1Sampled) (rest' : Bytes)
    (h : V1State.Chunked.EkReceivedCt1Sampled.mergeField m tag wt rest d = .ok (m', rest')) :
    ckEkReceivedCt1SampledW m' + rest'.length ≤ ckEkReceivedCt1SampledW m + rest.length + 1 := by
  unfold V1State.Chunked.EkReceivedCt1Sampled.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le V1State.Unchunked.Ct1SentEkReceived.mergeField (fun u => optAuthWeight u.auth) rfl d ucCt1SentEkReceived_mergeField_le wt m.uc v rest bs' hm
    simp only [ckEkReceivedCt1SampledW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le PolynomialEncoder.mergeField encWeight rfl d polyEnc_mergeField_weight_le wt m.sendingCt1 v rest bs' hm
      simp only [ckEkReceivedCt1SampledW, optEncWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := GrowthRecv.skipField_length_le hs; omega

theorem ckCt1Acknowledged_mergeField_le (d : Nat) (m : V1State.Chunked.Ct1Acknowledged) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.Ct1Acknowledged) (rest' : Bytes)
    (h : V1State.Chunked.Ct1Acknowledged.mergeField m tag wt rest d = .ok (m', rest')) :
    ckCt1AcknowledgedW m' + rest'.length ≤ ckCt1AcknowledgedW m + rest.length + 1 := by
  unfold V1State.Chunked.Ct1Acknowledged.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le V1State.Unchunked.Ct1Sent.mergeField (fun u => optAuthWeight u.auth) rfl d ucCt1Sent_mergeField_le wt m.uc v rest bs' hm
    simp only [ckCt1AcknowledgedW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le PolynomialDecoder.mergeField decWeight rfl d polyDec_mergeField_weight_le wt m.receivingEk v rest bs' hm
      simp only [ckCt1AcknowledgedW, optDecWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := GrowthRecv.skipField_length_le hs; omega

theorem ckCt2Sampled_mergeField_le (d : Nat) (m : V1State.Chunked.Ct2Sampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.Ct2Sampled) (rest' : Bytes)
    (h : V1State.Chunked.Ct2Sampled.mergeField m tag wt rest d = .ok (m', rest')) :
    ckCt2SampledW m' + rest'.length ≤ ckCt2SampledW m + rest.length + 1 := by
  unfold V1State.Chunked.Ct2Sampled.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le V1State.Unchunked.Ct2Sent.mergeField (fun u => optAuthWeight u.auth) rfl d ucCt2Sent_mergeField_le wt m.uc v rest bs' hm
    simp only [ckCt2SampledW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le PolynomialEncoder.mergeField encWeight rfl d polyEnc_mergeField_weight_le wt m.sendingCt2 v rest bs' hm
      simp only [ckCt2SampledW, optEncWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := GrowthRecv.skipField_length_le hs; omega

def innerStateW : Option V1State.InnerState → Nat
  | none => 0
  | some (.keysUnsampled v) => ckKeysUnsampledW v | some (.keysSampled v) => ckKeysSampledW v
  | some (.headerSent v) => ckHeaderSentW v | some (.ct1Received v) => ckCt1ReceivedW v
  | some (.ekSentCt1Received v) => ckEkSentCt1ReceivedW v | some (.noHeaderReceived v) => ckNoHeaderReceivedW v
  | some (.headerReceived v) => ckHeaderReceivedW v | some (.ct1Sampled v) => ckCt1SampledW v
  | some (.ekReceivedCt1Sampled v) => ckEkReceivedCt1SampledW v | some (.ct1Acknowledged v) => ckCt1AcknowledgedW v
  | some (.ct2Sampled v) => ckCt2SampledW v

def v1Weight (m : V1State) : Nat := innerStateW m.innerState

theorem innerState_merge_le (d : Nat) (cur cur' : Option V1State.InnerState) (tag : BitVec 32)
    (wt : Proto.WireType) (rest rest' : Bytes)
    (h : V1State.InnerState.merge cur tag wt rest d = .ok (cur', rest')) :
    innerStateW cur' + rest'.length ≤ innerStateW cur + rest.length := by
  unfold V1State.InnerState.merge at h
  rcases ite_ok_cases h with h | h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    refine Nat.le_trans (mergeMessage_weight_le V1State.Chunked.KeysUnsampled.mergeField ckKeysUnsampledW d ckKeysUnsampled_mergeField_le wt _ v rest bs' hm) (Nat.add_le_add_right ?_ _)
    cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _
  · rcases ite_ok_cases h with h | h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      refine Nat.le_trans (mergeMessage_weight_le V1State.Chunked.KeysSampled.mergeField ckKeysSampledW d ckKeysSampled_mergeField_le wt _ v rest bs' hm) (Nat.add_le_add_right ?_ _)
      cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _
    · rcases ite_ok_cases h with h | h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        refine Nat.le_trans (mergeMessage_weight_le V1State.Chunked.HeaderSent.mergeField ckHeaderSentW d ckHeaderSent_mergeField_le wt _ v rest bs' hm) (Nat.add_le_add_right ?_ _)
        cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _
      · rcases ite_ok_cases h with h | h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          refine Nat.le_trans (mergeMessage_weight_le V1State.Chunked.Ct1Received.mergeField ckCt1ReceivedW d ckCt1Received_mergeField_le wt _ v rest bs' hm) (Nat.add_le_add_right ?_ _)
          cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _
        · rcases ite_ok_cases h with h | h
          · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            refine Nat.le_trans (mergeMessage_weight_le V1State.Chunked.EkSentCt1Received.mergeField ckEkSentCt1ReceivedW d ckEkSentCt1Received_mergeField_le wt _ v rest bs' hm) (Nat.add_le_add_right ?_ _)
            cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _
          · rcases ite_ok_cases h with h | h
            · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
              refine Nat.le_trans (mergeMessage_weight_le V1State.Chunked.NoHeaderReceived.mergeField ckNoHeaderReceivedW d ckNoHeaderReceived_mergeField_le wt _ v rest bs' hm) (Nat.add_le_add_right ?_ _)
              cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _
            · rcases ite_ok_cases h with h | h
              · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
                refine Nat.le_trans (mergeMessage_weight_le V1State.Chunked.HeaderReceived.mergeField ckHeaderReceivedW d ckHeaderReceived_mergeField_le wt _ v rest bs' hm) (Nat.add_le_add_right ?_ _)
                cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _
              · rcases ite_ok_cases h with h | h
                · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
                  refine Nat.le_trans (mergeMessage_weight_le V1State.Chunked.Ct1Sampled.mergeField ckCt1SampledW d ckCt1Sampled_mergeField_le wt _ v rest bs' hm) (Nat.add_le_add_right ?_ _)
                  cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _
                · rcases ite_ok_cases h with h | h
                  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
                    refine Nat.le_trans (mergeMessage_weight_le V1State.Chunked.EkReceivedCt1Sampled.mergeField ckEkReceivedCt1SampledW d ckEkReceivedCt1Sampled_mergeField_le wt _ v rest bs' hm) (Nat.add_le_add_right ?_ _)
                    cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _
                  · rcases ite_ok_cases h with h | h
                    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
                      refine Nat.le_trans (mergeMessage_weight_le V1State.Chunked.Ct1Acknowledged.mergeField ckCt1AcknowledgedW d ckCt1Acknowledged_mergeField_le wt _ v rest bs' hm) (Nat.add_le_add_right ?_ _)
                      cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _
                    · rcases ite_ok_cases h with h | h
                      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
                        refine Nat.le_trans (mergeMessage_weight_le V1State.Chunked.Ct2Sampled.mergeField ckCt2SampledW d ckCt2Sampled_mergeField_le wt _ v rest bs' hm) (Nat.add_le_add_right ?_ _)
                        cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _
                      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
                        have := GrowthRecv.skipField_length_le hs; omega

theorem v1State_mergeField_le (d : Nat) (m : V1State) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State) (rest' : Bytes)
    (h : V1State.mergeField m tag wt rest d = .ok (m', rest')) : v1Weight m' + rest'.length ≤ v1Weight m + rest.length + 1 := by
  unfold V1State.mergeField at h; rcases ite_ok_cases h with h | h
  · rcases except_bind_eq_ok h with ⟨⟨is', bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := innerState_merge_le d m.innerState is' tag wt rest bs' hm; dsimp only [v1Weight]; omega
  · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := GrowthRecv.skipField_length_le hs; dsimp only [v1Weight]; omega

def pqInnerW : Option PqRatchetState.Inner → Nat | none => 0 | some (.v1 v) => v1Weight v

def stateWeight (m : PqRatchetState) : Nat := optVnWeight m.versionNegotiation + optChainWeight m.chain + pqInnerW m.inner

theorem pqRatchetState_mergeField_le (d : Nat) (m : PqRatchetState) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : PqRatchetState) (rest' : Bytes)
    (h : PqRatchetState.mergeField m tag wt rest d = .ok (m', rest')) :
    stateWeight m' + rest'.length ≤ stateWeight m + rest.length + 1 := by
  unfold PqRatchetState.mergeField at h
  rcases ite_ok_cases h with h | h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le VersionNegotiationPB.mergeField vnWeight rfl d vnPB_mergeField_weight_le wt m.versionNegotiation v rest bs' hm
    simp only [stateWeight, optVnWeight] at this ⊢; omega
  · rcases ite_ok_cases h with h | h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ChainPB.mergeField chainWeight rfl d chainPB_mergeField_weight_le wt m.chain v rest bs' hm
      simp only [stateWeight, optChainWeight] at this ⊢; omega
    · rcases ite_ok_cases h with h | h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        unfold PqRatchetState.Inner.merge at hm; rcases ite_ok_cases hm with hm | hm
        · rcases except_bind_eq_ok hm with ⟨⟨v1, bs1⟩, hm1, hm⟩; dsimp only at hm; rcases Prod.mk.inj (Except.ok.inj hm) with ⟨rfl, rfl⟩
          have h1 : v1Weight v1 + bs1.length ≤ pqInnerW m.inner + rest.length :=
            Nat.le_trans (mergeMessage_weight_le V1State.mergeField v1Weight d v1State_mergeField_le wt _ v1 rest bs1 hm1)
              (Nat.add_le_add_right (by cases m.inner with | none => exact Nat.zero_le _ | some i => cases i; exact Nat.le_refl _) _)
          change (optVnWeight m.versionNegotiation + optChainWeight m.chain + v1Weight v1) + bs1.length ≤
            (optVnWeight m.versionNegotiation + optChainWeight m.chain + pqInnerW m.inner) + rest.length + 1
          omega
        · rcases except_bind_eq_ok hm with ⟨bs1, hs, hm⟩; rcases Prod.mk.inj (Except.ok.inj hm) with ⟨rfl, rfl⟩
          have := GrowthRecv.skipField_length_le hs; dsimp only [stateWeight]; omega
      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := GrowthRecv.skipField_length_le hs; dsimp only [stateWeight]; omega

theorem decodeState_weight_le (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st : Bytes) (statePb : PqRatchetStatePB V1State) (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok statePb) :
    optVnWeight statePb.versionNegotiation + optChainWeight statePb.chain +
      (match statePb.inner with | none => 0 | some v => v1Weight v) ≤ st.length := by
  unfold decodeState at hdec; split at hdec
  · injection hdec with hst; subst hst; simp [optVnWeight, optChainWeight, optWeight]
  · dsimp only [spqrDepsWithMac] at hdec; cases hp : Proto.decodeState st with
    | error _ => simp [hp] at hdec
    | ok rawSt =>
      rw [hp] at hdec; dsimp only at hdec; injection hdec with hst; subst hst
      have htop := mergeFieldsLoop_weight_le PqRatchetState.mergeField stateWeight Proto.RECURSION_LIMIT
        (pqRatchetState_mergeField_le Proto.RECURSION_LIMIT) st.length default rawSt st hp
      have hdef : stateWeight default = 0 := rfl
      rw [hdef, Nat.zero_add] at htop; unfold pqRatchetStateToPb stateWeight at *
      cases hinner : rawSt.inner with
      | none => simp only [hinner, pqInnerW, Option.map] at htop ⊢; omega
      | some i => cases i; simp only [hinner, pqInnerW, Option.map] at htop ⊢; omega

end Symbolic.Swarm.TRREF
