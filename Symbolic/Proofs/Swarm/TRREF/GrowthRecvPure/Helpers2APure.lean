/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.Helpers1BPure
public import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.ProofHubsPure
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.Helpers1APure

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthRecvPureB

open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Top.StateSize CryptoVerification.SpqrV1.Top.StateSize.SymP3
open CryptoVerification.SpqrV1.ProtoRepr

theorem ced_fromPb_intoPb {pb : EpochDirectionPB} {ced : ChainEpochDirection}
    (h : ChainEpochDirection.fromPb pb = .ok ced) :
    ced.intoPb = pb := by
  unfold ChainEpochDirection.fromPb at h
  split at h
  · contradiction
  · injection h with hced; subst hced; cases pb; rfl

theorem chain_linksFromPb_map_eq :
    ∀ (pbs : List ChainEpochPB) (links : List ChainEpoch),
      Chain.linksFromPb pbs = .ok links →
      links.map linkToPb = pbs
  | [], links, h => by simp [Chain.linksFromPb] at h; subst h; rfl
  | link :: rest, links, h => by
    unfold Chain.linksFromPb at h
    cases hs : link.send with
    | none => simp [hs, Bind.bind, Except.bind] at h
    | some sendPb =>
      rw [hs] at h; dsimp only [Bind.bind, Except.bind] at h
      rcases except_bind_eq_ok h with ⟨send, hsend, h⟩
      cases hr : link.recv with
      | none => simp [hr] at h
      | some recvPb =>
        rw [hr] at h; dsimp only [Bind.bind, Except.bind] at h
        rcases except_bind_eq_ok h with ⟨recv, hrecv, h⟩
        rcases except_bind_eq_ok h with ⟨tail, htail, h⟩
        injection h with hlinks; subst hlinks
        have hs_eq := ced_fromPb_intoPb hsend
        have hr_eq := ced_fromPb_intoPb hrecv
        have ih := chain_linksFromPb_map_eq rest tail htail
        cases link; simp only at hs hr; subst hs; subst hr
        simp [linkToPb, hs_eq, hr_eq, ih]

theorem chain_fromPb_weight_eq {pb : ChainPB} {c : Chain}
    (h : Chain.fromPb pb = .ok c) :
    chainWeight c.intoPb = chainWeight pb := by
  unfold Chain.fromPb at h
  cases hd : Direction.fromI32? pb.direction with
  | none => simp [hd, Bind.bind, Except.bind] at h
  | some dir =>
    cases hl : Chain.linksFromPb pb.links with
    | error _ => simp [hd, hl, Bind.bind, Except.bind] at h
    | ok links =>
      cases hp : pb.params with
      | none => simp [hd, hl, hp, Bind.bind, Except.bind] at h
      | some params =>
        simp only [hd, hl, hp, Bind.bind, Except.bind] at h
        injection h with hc; subst hc
        have hmap := chain_linksFromPb_map_eq pb.links links hl
        simp only [Chain.intoPb, chainWeight]; rw [hmap]

theorem cedForDirection_encodeRaw_le (genr8r : Bytes) (dir : Direction) :
    (EpochDirectionPB.encodeRaw (Chain.cedForDirection genr8r dir).intoPb).length ≤ 54 := by
  cases dir
  · unfold Chain.cedForDirection ChainEpochDirection.new ChainEpochDirection.intoPb
      KeyHistory.new EpochDirectionPB.encodeRaw
    dsimp only
    have h0 : Proto.encodeUint32Field 1#32 0#32 = [] := rfl
    have h3 : Proto.encodeBytesField 3#32 [] = [] := rfl
    rw [h0, h3, List.nil_append, List.append_nil]
    have h2 := encodeBytesField_length_le 2#32 ((genr8r.drop 32).take 32)
    have htake : ((genr8r.drop 32).take 32).length ≤ 32 := by simp [List.length_take]
    omega
  · unfold Chain.cedForDirection ChainEpochDirection.new ChainEpochDirection.intoPb
      KeyHistory.new EpochDirectionPB.encodeRaw
    dsimp only
    have h0 : Proto.encodeUint32Field 1#32 0#32 = [] := rfl
    have h3 : Proto.encodeBytesField 3#32 [] = [] := rfl
    rw [h0, h3, List.nil_append, List.append_nil]
    have h2 := encodeBytesField_length_le 2#32 ((genr8r.drop 64).take 32)
    have htake : ((genr8r.drop 64).take 32).length ≤ 32 := by simp [List.length_take]
    omega

theorem newLink_encodeMessage_le (genr8r : Bytes) (dir : Direction) :
    (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32
      (linkToPb { send := Chain.cedForDirection genr8r dir, recv := Chain.cedForDirection genr8r dir.switch })).length ≤ 174 := by
  have hm := encodeMessage_length_le ChainEpochPB.encodeRaw 3#32
    (linkToPb { send := Chain.cedForDirection genr8r dir, recv := Chain.cedForDirection genr8r dir.switch })
  simp only [ChainEpochPB.encodeRaw, linkToPb, Proto.encodeOptMessage, List.length_append] at hm ⊢
  have hs := encodeMessage_length_le EpochDirectionPB.encodeRaw 1#32 (Chain.cedForDirection genr8r dir).intoPb
  have hr := encodeMessage_length_le EpochDirectionPB.encodeRaw 2#32 (Chain.cedForDirection genr8r dir.switch).intoPb
  have hs0 := cedForDirection_encodeRaw_le genr8r dir
  have hr0 := cedForDirection_encodeRaw_le genr8r dir.switch
  omega

theorem chain_new_weight_le {hkdf : HkdfFn} {k : Bytes} {dir : Direction} {params : ChainParamsPB} {c : Chain}
    (h : Chain.new hkdf k dir params = .ok c) :
    chainWeight c.intoPb ≤ 206 := by
  unfold Chain.new at h
  injection h with hc
  subst hc
  simp only [Chain.intoPb, chainWeight, List.map, Proto.encodeRepeatedMessage, List.foldr, List.append_nil]
  have hlink := newLink_encodeMessage_le (hkdf (List.replicate 32 0#8) k chainStartInfo 96) dir
  dsimp only [linkToPb] at hlink
  have hroot : ((hkdf (List.replicate 32 0#8) k chainStartInfo 96).take 32).length ≤ 32 := by
    simp [List.length_take]
  omega

theorem chain_addEpoch_weight_le {hkdf : HkdfFn} {c0 c1 : Chain} {es : EpochSecret}
    (h : c0.addEpoch hkdf es = .ok c1) :
    chainWeight c1.intoPb ≤ chainWeight c0.intoPb + 206 := by
  unfold Chain.addEpoch at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · injection h with hc1
      subst hc1
      simp only [Chain.intoPb, chainWeight, List.map_append, List.map]
      rw [encodeRepeatedMessage_append, List.length_append]
      have hlink := newLink_encodeMessage_le (hkdf c0.nextRoot es.secret chainAddEpochInfo 96) c0.dir
      dsimp only [linkToPb] at hlink
      have hroot : ((hkdf c0.nextRoot es.secret chainAddEpochInfo 96).take 32).length ≤ 32 := by
        simp [List.length_take]
      omega

theorem encodeRaw_le_encodeMessage {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32) (m : M) :
    (encodeRaw m).length ≤ (Proto.encodeMessage encodeRaw tag m).length := by
  unfold Proto.encodeMessage
  simp only [List.length_append]
  omega

theorem encodeRepeatedMessage_set_le {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32) (K : Nat) :
    ∀ (xs : List M) (i : Nat) (x x' : M),
      xs[i]? = some x →
      (Proto.encodeMessage encodeRaw tag x').length ≤ (Proto.encodeMessage encodeRaw tag x).length + K →
      (Proto.encodeRepeatedMessage encodeRaw tag (xs.set i x')).length ≤
        (Proto.encodeRepeatedMessage encodeRaw tag xs).length + K
  | [], _, _, _, hget, _ => by simp at hget
  | a :: xs, 0, x, x', hget, hle => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget
    simp only [List.set_cons_zero, encodeRepeatedMessage_cons, List.length_append]
    omega
  | a :: xs, i + 1, x, x', hget, hle => by
    simp only [List.getElem?_cons_succ] at hget
    simp only [List.set_cons_succ, encodeRepeatedMessage_cons, List.length_append]
    have ih := encodeRepeatedMessage_set_le encodeRaw tag K xs i x x' hget hle
    omega

def bytesSum (xs : List Bytes) : Nat := (xs.map List.length).sum

@[scoped simp]
theorem bytesSum_nil : bytesSum [] = 0 := rfl

@[scoped simp]
theorem bytesSum_cons (x : Bytes) (xs : List Bytes) :
    bytesSum (x :: xs) = x.length + bytesSum xs := by
  simp [bytesSum]

theorem bytesSum_append (xs : List Bytes) (v : Bytes) :
    bytesSum (xs ++ [v]) = bytesSum xs + v.length := by
  simp [bytesSum]

theorem mergeRepeatedBytes_bytesSum_le {wt : Proto.WireType} {xs xs' : List Bytes} {bs rest : Bytes}
    (h : Proto.mergeRepeatedBytes wt xs bs = .ok (xs', rest)) :
    bytesSum xs' + rest.length ≤ bytesSum xs + bs.length := by
  unfold Proto.mergeRepeatedBytes at h
  rcases except_bind_eq_ok h with ⟨⟨v, rest'⟩, hm, h⟩
  rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
  rcases mergeBytes_length_le hm with ⟨h1, _⟩
  rw [bytesSum_append]; omega

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
  unfold PolynomialEncoder.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have h1 := mergeUint32_length_lt hm; simp only [encWeight]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have h1 := mergeRepeatedBytes_bytesSum_le hm; simp only [encWeight]; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
        rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have h1 := mergeRepeatedBytes_bytesSum_le hm; simp only [encWeight]; omega
      · rcases except_bind_eq_ok h with ⟨bs', hskip, h⟩
        rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have hs := skipField_length_le hskip; simp only [encWeight]; omega

theorem polyDec_mergeField_weight_le (d : Nat) (m : PolynomialDecoder) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (m' : PolynomialDecoder) (rest' : Bytes)
    (h : PolynomialDecoder.mergeField m tag wt rest d = .ok (m', rest')) :
    decWeight m' + rest'.length ≤ decWeight m + rest.length + 1 := by
  unfold PolynomialDecoder.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have h1 := mergeUint32_length_lt hm; simp only [decWeight]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have h1 := mergeUint32_length_lt hm; simp only [decWeight]; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
        rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have h1 := mergeRepeatedBytes_bytesSum_le hm; simp only [decWeight]; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
          rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have h1 := mergeBool_length_lt hm; simp only [decWeight]; omega
        · rcases except_bind_eq_ok h with ⟨bs', hskip, h⟩
          rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have hs := skipField_length_le hskip; simp only [decWeight]; omega

theorem auth_mergeField_weight_le (d : Nat) (m : ProtoAuthenticator) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (m' : ProtoAuthenticator) (rest' : Bytes)
    (h : ProtoAuthenticator.mergeField m tag wt rest d = .ok (m', rest')) :
    authWeight m' + rest'.length ≤ authWeight m + rest.length + 1 := by
  unfold ProtoAuthenticator.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [authWeight]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [authWeight]; omega
    · rcases except_bind_eq_ok h with ⟨bs', hskip, h⟩
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have hs := skipField_length_le hskip; simp only [authWeight]; omega

theorem ucKeysUnsampled_mergeField_le (d : Nat) (m : V1State.Unchunked.KeysUnsampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.KeysUnsampled) (rest' : Bytes)
    (h : V1State.Unchunked.KeysUnsampled.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.KeysUnsampled.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

theorem ucHeaderSent_mergeField_le (d : Nat) (m : V1State.Unchunked.HeaderSent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.HeaderSent) (rest' : Bytes)
    (h : V1State.Unchunked.HeaderSent.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.HeaderSent.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le hm with ⟨h1, _⟩; dsimp only; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le hm with ⟨h1, _⟩; dsimp only; omega
        · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have := skipField_length_le hs; omega

theorem ucEkSent_mergeField_le (d : Nat) (m : V1State.Unchunked.EkSent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.EkSent) (rest' : Bytes)
    (h : V1State.Unchunked.EkSent.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.EkSent.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le hm with ⟨h1, _⟩; dsimp only; omega
      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := skipField_length_le hs; omega

theorem ucEkSentCt1Received_mergeField_le (d : Nat) (m : V1State.Unchunked.EkSentCt1Received) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.EkSentCt1Received) (rest' : Bytes)
    (h : V1State.Unchunked.EkSentCt1Received.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.EkSentCt1Received.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le hm with ⟨h1, _⟩; dsimp only; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le hm with ⟨h1, _⟩; dsimp only; omega
        · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have := skipField_length_le hs; omega

theorem ucNoHeaderReceived_mergeField_le (d : Nat) (m : V1State.Unchunked.NoHeaderReceived) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.NoHeaderReceived) (rest' : Bytes)
    (h : V1State.Unchunked.NoHeaderReceived.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.NoHeaderReceived.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

theorem ucHeaderReceived_mergeField_le (d : Nat) (m : V1State.Unchunked.HeaderReceived) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.HeaderReceived) (rest' : Bytes)
    (h : V1State.Unchunked.HeaderReceived.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.HeaderReceived.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le hm with ⟨h1, _⟩; dsimp only; omega
      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := skipField_length_le hs; omega

theorem ucCt1Sent_mergeField_le (d : Nat) (m : V1State.Unchunked.Ct1Sent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.Ct1Sent) (rest' : Bytes)
    (h : V1State.Unchunked.Ct1Sent.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.Ct1Sent.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le hm with ⟨h1, _⟩; dsimp only; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le hm with ⟨h1, _⟩; dsimp only; omega
        · split at h
          · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            rcases mergeBytes_length_le hm with ⟨h1, _⟩; dsimp only; omega
          · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            have := skipField_length_le hs; omega

theorem ucCt1SentEkReceived_mergeField_le (d : Nat) (m : V1State.Unchunked.Ct1SentEkReceived) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.Ct1SentEkReceived) (rest' : Bytes)
    (h : V1State.Unchunked.Ct1SentEkReceived.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.Ct1SentEkReceived.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le hm with ⟨h1, _⟩; dsimp only; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le hm with ⟨h1, _⟩; dsimp only; omega
        · split at h
          · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            rcases mergeBytes_length_le hm with ⟨h1, _⟩; dsimp only; omega
          · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            have := skipField_length_le hs; omega

theorem ucCt2Sent_mergeField_le (d : Nat) (m : V1State.Unchunked.Ct2Sent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.Ct2Sent) (rest' : Bytes)
    (h : V1State.Unchunked.Ct2Sent.mergeField m tag wt rest d = .ok (m', rest')) :
    optAuthWeight m'.auth + rest'.length ≤ optAuthWeight m.auth + rest.length + 1 := by
  unfold V1State.Unchunked.Ct2Sent.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; dsimp only; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField authWeight rfl d auth_mergeField_weight_le wt m.auth v rest bs' hm
      simp only [optAuthWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

theorem mergeMessage_weight_le {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (w : M → Nat) (depth : Nat)
    (hstep : ∀ d m tag wt rest m' rest',
      mergeField m tag wt rest d = .ok (m', rest') →
      w m' + rest'.length ≤ w m + rest.length + 1)
    (wt : Proto.WireType) (prev m' : M) (bs after : Bytes)
    (h : Proto.mergeMessage mergeField wt prev bs depth = .ok (m', after)) :
    w m' + after.length ≤ w prev + bs.length := by
  unfold Proto.mergeMessage Proto.checkWireType at h
  split at h
  · contradiction
  · dsimp only [Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i depth'
      rcases except_bind_eq_ok h with ⟨⟨len, rest0⟩, hdv, h⟩
      rcases except_bind_eq_ok h with ⟨⟨sub, after1⟩, htake, h⟩
      rcases except_bind_eq_ok h with ⟨m1, hloop, h⟩
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      dsimp only at htake hloop ⊢
      have hdv_lt := decodeVarint_length_lt hdv
      rcases takeExact_length_eq htake with ⟨_, htake_sum⟩
      have hm1 := mergeFieldsLoop_weight_le mergeField w depth' (hstep depth') sub.length prev m1 sub hloop
      omega

def ckKeysUnsampledW (m : V1State.Chunked.KeysUnsampled) : Nat :=
  optWeight (fun u => optAuthWeight u.auth) m.uc
def ckKeysSampledW (m : V1State.Chunked.KeysSampled) : Nat :=
  optWeight (fun u => optAuthWeight u.auth) m.uc + optEncWeight m.sendingHdr
def ckHeaderSentW (m : V1State.Chunked.HeaderSent) : Nat :=
  optWeight (fun u => optAuthWeight u.auth) m.uc + optEncWeight m.sendingEk + optDecWeight m.receivingCt1
def ckCt1ReceivedW (m : V1State.Chunked.Ct1Received) : Nat :=
  optWeight (fun u => optAuthWeight u.auth) m.uc + optEncWeight m.sendingEk
def ckEkSentCt1ReceivedW (m : V1State.Chunked.EkSentCt1Received) : Nat :=
  optWeight (fun u => optAuthWeight u.auth) m.uc + optDecWeight m.receivingCt2
def ckNoHeaderReceivedW (m : V1State.Chunked.NoHeaderReceived) : Nat :=
  optWeight (fun u => optAuthWeight u.auth) m.uc + optDecWeight m.receivingHdr
def ckHeaderReceivedW (m : V1State.Chunked.HeaderReceived) : Nat :=
  optWeight (fun u => optAuthWeight u.auth) m.uc + optDecWeight m.receivingEk
def ckCt1SampledW (m : V1State.Chunked.Ct1Sampled) : Nat :=
  optWeight (fun u => optAuthWeight u.auth) m.uc + optEncWeight m.sendingCt1 + optDecWeight m.receivingEk
def ckEkReceivedCt1SampledW (m : V1State.Chunked.EkReceivedCt1Sampled) : Nat :=
  optWeight (fun u => optAuthWeight u.auth) m.uc + optEncWeight m.sendingCt1
def ckCt1AcknowledgedW (m : V1State.Chunked.Ct1Acknowledged) : Nat :=
  optWeight (fun u => optAuthWeight u.auth) m.uc + optDecWeight m.receivingEk
def ckCt2SampledW (m : V1State.Chunked.Ct2Sampled) : Nat :=
  optWeight (fun u => optAuthWeight u.auth) m.uc + optEncWeight m.sendingCt2

end Symbolic.Swarm.TRREF.GrowthRecvPureB
