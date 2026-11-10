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
public import Symbolic.Proofs.SpecLemmas.ProofHubsPure
import Symbolic.Proofs.Swarm.SHARED.StateSizePure

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthRecv

open Symbolic.Swarm.CREF (SpqrOooBounded)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open Symbolic.Swarm.TRREF.SpqrSemOf
open CryptoVerification.SpqrV1.Top.StateSize.SymP3

theorem encodeRaw_le_encodeMessage {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32) (m : M) :
    (encodeRaw m).length ≤ (Proto.encodeMessage encodeRaw tag m).length := by
  unfold Proto.encodeMessage; simp only [List.length_append]; omega

theorem encodeRepeatedMessage_set_le {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32) (K : Nat) :
    ∀ (xs : List M) (i : Nat) (x x' : M),
      xs[i]? = some x →
      (Proto.encodeMessage encodeRaw tag x').length ≤ (Proto.encodeMessage encodeRaw tag x).length + K →
      (Proto.encodeRepeatedMessage encodeRaw tag (xs.set i x')).length ≤
        (Proto.encodeRepeatedMessage encodeRaw tag xs).length + K
  | [], _, _, _, hget, _ => by simp at hget
  | a :: xs, 0, x, x', hget, hle => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget; subst hget
    simp only [List.set_cons_zero, encodeRepeatedMessage_cons, List.length_append]; omega
  | a :: xs, i + 1, x, x', hget, hle => by
    simp only [List.getElem?_cons_succ] at hget
    simp only [List.set_cons_succ, encodeRepeatedMessage_cons, List.length_append]
    have ih := encodeRepeatedMessage_set_le encodeRaw tag K xs i x x' hget hle; omega

theorem linkToPb_modify_recv_le (link : ChainEpoch) (recv' : ChainEpochDirection) (K : Nat)
    (h : (EpochDirectionPB.encodeRaw recv'.intoPb).length ≤
         (EpochDirectionPB.encodeRaw link.recv.intoPb).length + K) :
    (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 (linkToPb { link with recv := recv' })).length ≤
      (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 (linkToPb link)).length + K + 44 := by
  have hm' := encodeMessage_length_le ChainEpochPB.encodeRaw 3#32 (linkToPb { link with recv := recv' })
  have hm := encodeRaw_le_encodeMessage ChainEpochPB.encodeRaw 3#32 (linkToPb link)
  simp only [ChainEpochPB.encodeRaw, linkToPb, Proto.encodeOptMessage, List.length_append] at hm' hm ⊢
  have hr' := encodeMessage_length_le EpochDirectionPB.encodeRaw 2#32 recv'.intoPb
  have hr := encodeRaw_le_encodeMessage EpochDirectionPB.encodeRaw 2#32 link.recv.intoPb
  omega

theorem chain_recvKey_weight_le {hkdf : HkdfFn} {c1 c2 : Chain} {ep : Epoch} {idx : BitVec 32} {out : Bytes}
    (hooo : c1.params.maxOooKeysOrDefault.toNat ≤ 2000)
    (h : c1.recvKey hkdf ep idx = .ok (c2, out)) :
    chainWeight c2.intoPb ≤ chainWeight c1.intoPb + 72156 := by
  unfold Chain.recvKey at h; split at h
  · injection h with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩; omega
  · rcases except_bind_eq_ok h with ⟨epochIndex, _, h⟩; dsimp only at h
    cases hget : c1.links[epochIndex]? with
    | none => simp [hget] at h
    | some link =>
      rw [hget] at h; dsimp only [Bind.bind, Except.bind] at h
      rcases except_bind_eq_ok h with ⟨⟨recv', out'⟩, hkey, h⟩
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have hkey_len := key_ooo_encodeRaw_le hkdf link.recv idx c1.params hooo hkey
      have hmod := linkToPb_modify_recv_le link recv' 72112 hkey_len
      have hget_map : (c1.links.map linkToPb)[epochIndex]? = some (linkToPb link) := by
        rw [List.getElem?_map, hget]; rfl
      have hset := encodeRepeatedMessage_set_le ChainEpochPB.encodeRaw 3#32 72156
        (c1.links.map linkToPb) epochIndex (linkToPb link) (linkToPb { link with recv := recv' })
        hget_map (by omega)
      change (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32
        ((c1.links.set epochIndex { link with recv := recv' }).map linkToPb)).length +
        c1.nextRoot.length ≤
        (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (c1.links.map linkToPb)).length +
        c1.nextRoot.length + 72156
      rw [List.map_set]; omega

def StatePbOooBounded {V1StatePB : Type} (statePb : PqRatchetStatePB V1StatePB) : Prop :=
  (∀ c ∈ statePb.chain, ∀ p ∈ c.params, p.maxOooKeysOrDefault.toNat ≤ 2000) ∧
  (∀ v ∈ statePb.versionNegotiation, ∀ p ∈ v.chainParams, p.maxOooKeysOrDefault.toNat ≤ 2000)

theorem statePbOooBounded_of_decodeState
    (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st : Bytes) (statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok statePb) :
    StatePbOooBounded statePb := by
  unfold decodeState at hdec; split at hdec
  · injection hdec with hst; subst hst; exact ⟨(by intro c hc; cases hc), (by intro v hv; cases hv)⟩
  · dsimp only [spqrDepsWithMac] at hdec
    cases hp : Proto.decodeState st with
    | error _ => simp [hp] at hdec
    | ok rawSt =>
      rw [hp] at hdec; dsimp only at hdec; injection hdec with hst; subst hst
      exact hb rawSt hp

theorem chainFrom_weight_and_ooo {hkdf : HkdfFn} {chainPb : Option ChainPB}
    {vnPb : Option VersionNegotiationPB} {c : Chain}
    (hc_ooo : ∀ ch ∈ chainPb, ∀ p ∈ ch.params, p.maxOooKeysOrDefault.toNat ≤ 2000)
    (hvn_ooo : ∀ v ∈ vnPb, ∀ p ∈ v.chainParams, p.maxOooKeysOrDefault.toNat ≤ 2000)
    (hcf : chainFrom hkdf chainPb vnPb = .ok c) :
    chainWeight c.intoPb ≤ optChainWeight chainPb + 206 ∧
      c.params.maxOooKeysOrDefault.toNat ≤ 2000 := by
  unfold chainFrom at hcf
  cases chainPb with
  | some pb =>
    dsimp only at hcf
    have hw := chain_fromPb_weight_eq hcf
    unfold Chain.fromPb at hcf
    cases hd : Direction.fromI32? pb.direction with
    | none => simp [hd, Bind.bind, Except.bind] at hcf
    | some dir =>
      cases hl : Chain.linksFromPb pb.links with
      | error _ => simp [hd, hl, Bind.bind, Except.bind] at hcf
      | ok links =>
        cases hp : pb.params with
        | none => simp [hd, hl, hp, Bind.bind, Except.bind] at hcf
        | some params =>
          simp only [hd, hl, hp, Bind.bind, Except.bind] at hcf
          injection hcf with hc; subst hc
          exact ⟨by simp [optChainWeight, hw], hc_ooo pb rfl params hp⟩
  | none =>
    cases vnPb with
    | none => contradiction
    | some vn =>
      dsimp only [chainFromVersionNegotiation] at hcf
      cases hd : Direction.fromI32? vn.direction with
      | none => simp [hd, Bind.bind, Except.bind] at hcf
      | some dir =>
        cases hp : vn.chainParams with
        | none => simp [hd, hp, Bind.bind, Except.bind] at hcf
        | some params =>
          simp only [hd, hp, Bind.bind, Except.bind] at hcf
          have hw := chain_new_weight_le hcf
          have hparams : c.params = params := by
            unfold Chain.new at hcf; injection hcf with hc; subst hc; rfl
          exact ⟨by simp [optChainWeight]; omega, by rw [hparams]; exact hvn_ooo vn rfl params hp⟩

@[scoped simp] theorem encodeRepeatedBytes_cons (tag : BitVec 32) (x : Bytes) (xs : List Bytes) :
    Proto.encodeRepeatedBytes tag (x :: xs) =
      Proto.encodeBytesUncond tag x ++ Proto.encodeRepeatedBytes tag xs := rfl

theorem encodeRepeatedBytes_append (tag : BitVec 32) (xs : List Bytes) (x : Bytes) :
    Proto.encodeRepeatedBytes tag (xs ++ [x]) =
      Proto.encodeRepeatedBytes tag xs ++ Proto.encodeBytesUncond tag x := by
  induction xs with
  | nil => simp [Proto.encodeRepeatedBytes]
  | cons a xs ih => simp only [List.cons_append, encodeRepeatedBytes_cons, ih, List.append_assoc]

theorem mergeRepeatedBytes_encodeRepeatedBytes_length_le (tag : BitVec 32) {wt : Proto.WireType}
    {xs xs' : List Bytes} {bs rest : Bytes}
    (htag : (Proto.encodeKey tag .lengthDelimited).length = 1)
    (h : Proto.mergeRepeatedBytes wt xs bs = .ok (xs', rest)) :
    (Proto.encodeRepeatedBytes tag xs').length + rest.length ≤
      (Proto.encodeRepeatedBytes tag xs).length + bs.length + 1 := by
  unfold Proto.mergeRepeatedBytes at h
  rcases except_bind_eq_ok h with ⟨⟨v, rest'⟩, hm, h⟩
  rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
  have h1 := mergeBytes_encodeBytesUncond_length_le tag htag hm
  rw [encodeRepeatedBytes_append, List.length_append]; omega

def encFullW (m : PolynomialEncoder) : Nat :=
  (Proto.encodeRepeatedBytes 2#32 m.pts).length + (Proto.encodeRepeatedBytes 3#32 m.polys).length
def decFullW (m : PolynomialDecoder) : Nat :=
  (Proto.encodeRepeatedBytes 3#32 m.pts).length

theorem polyEnc_mergeField_full_le (d : Nat) (m : PolynomialEncoder) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (m' : PolynomialEncoder) (rest' : Bytes)
    (h : PolynomialEncoder.mergeField m tag wt rest d = .ok (m', rest')) :
    encFullW m' + rest'.length ≤ encFullW m + rest.length + 1 := by
  unfold PolynomialEncoder.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint32_length_lt hm; simp only [encFullW]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeRepeatedBytes_encodeRepeatedBytes_length_le 2#32 rfl hm; simp only [encFullW]; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := mergeRepeatedBytes_encodeRepeatedBytes_length_le 3#32 rfl hm; simp only [encFullW]; omega
      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := skipField_length_le hs; simp only [encFullW]; omega

theorem polyDec_mergeField_full_le (d : Nat) (m : PolynomialDecoder) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (m' : PolynomialDecoder) (rest' : Bytes)
    (h : PolynomialDecoder.mergeField m tag wt rest d = .ok (m', rest')) :
    decFullW m' + rest'.length ≤ decFullW m + rest.length + 1 := by
  unfold PolynomialDecoder.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint32_length_lt hm; simp only [decFullW]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeUint32_length_lt hm; simp only [decFullW]; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := mergeRepeatedBytes_encodeRepeatedBytes_length_le 3#32 rfl hm; simp only [decFullW]; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have := mergeBool_length_lt hm; simp only [decFullW]; omega
        · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have := skipField_length_le hs; simp only [decFullW]; omega

theorem auth_mergeField_raw_le (d : Nat) (m : ProtoAuthenticator) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (m' : ProtoAuthenticator) (rest' : Bytes)
    (h : ProtoAuthenticator.mergeField m tag wt rest d = .ok (m', rest')) :
    rawAuth m' + rest'.length ≤ rawAuth m + rest.length + 1 := by
  unfold ProtoAuthenticator.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawAuth]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawAuth]; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; simp only [rawAuth]; omega

@[scoped simp] theorem optRaw_eq_optWeight {M : Type} (w : M → Nat) (o : Option M) :
    optRaw w o = optWeight w o := by cases o <;> rfl

theorem ucKeysUnsampled_mergeField_raw_le (d : Nat) (m : V1State.Unchunked.KeysUnsampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.KeysUnsampled) (rest' : Bytes)
    (h : V1State.Unchunked.KeysUnsampled.mergeField m tag wt rest d = .ok (m', rest')) :
    rawUcKeysUnsampled m' + rest'.length ≤ rawUcKeysUnsampled m + rest.length + 1 := by
  unfold V1State.Unchunked.KeysUnsampled.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; simp only [rawUcKeysUnsampled]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField rawAuth rfl d auth_mergeField_raw_le wt m.auth v rest bs' hm
      simp only [rawUcKeysUnsampled, optRaw_eq_optWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

theorem ucHeaderSent_mergeField_raw_le (d : Nat) (m : V1State.Unchunked.HeaderSent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.HeaderSent) (rest' : Bytes)
    (h : V1State.Unchunked.HeaderSent.mergeField m tag wt rest d = .ok (m', rest')) :
    rawUcHeaderSent m' + rest'.length ≤ rawUcHeaderSent m + rest.length + 1 := by
  unfold V1State.Unchunked.HeaderSent.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; simp only [rawUcHeaderSent]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField rawAuth rfl d auth_mergeField_raw_le wt m.auth v rest bs' hm
      simp only [rawUcHeaderSent, optRaw_eq_optWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawUcHeaderSent]; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawUcHeaderSent]; omega
        · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have := skipField_length_le hs; omega

theorem ucEkSent_mergeField_raw_le (d : Nat) (m : V1State.Unchunked.EkSent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.EkSent) (rest' : Bytes)
    (h : V1State.Unchunked.EkSent.mergeField m tag wt rest d = .ok (m', rest')) :
    rawUcEkSent m' + rest'.length ≤ rawUcEkSent m + rest.length + 1 := by
  unfold V1State.Unchunked.EkSent.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; simp only [rawUcEkSent]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField rawAuth rfl d auth_mergeField_raw_le wt m.auth v rest bs' hm
      simp only [rawUcEkSent, optRaw_eq_optWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawUcEkSent]; omega
      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := skipField_length_le hs; omega

theorem ucEkSentCt1Received_mergeField_raw_le (d : Nat) (m : V1State.Unchunked.EkSentCt1Received) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.EkSentCt1Received) (rest' : Bytes)
    (h : V1State.Unchunked.EkSentCt1Received.mergeField m tag wt rest d = .ok (m', rest')) :
    rawUcEkSentCt1Received m' + rest'.length ≤ rawUcEkSentCt1Received m + rest.length + 1 := by
  unfold V1State.Unchunked.EkSentCt1Received.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; simp only [rawUcEkSentCt1Received]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField rawAuth rfl d auth_mergeField_raw_le wt m.auth v rest bs' hm
      simp only [rawUcEkSentCt1Received, optRaw_eq_optWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawUcEkSentCt1Received]; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawUcEkSentCt1Received]; omega
        · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have := skipField_length_le hs; omega

theorem ucNoHeaderReceived_mergeField_raw_le (d : Nat) (m : V1State.Unchunked.NoHeaderReceived) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.NoHeaderReceived) (rest' : Bytes)
    (h : V1State.Unchunked.NoHeaderReceived.mergeField m tag wt rest d = .ok (m', rest')) :
    rawUcNoHeaderReceived m' + rest'.length ≤ rawUcNoHeaderReceived m + rest.length + 1 := by
  unfold V1State.Unchunked.NoHeaderReceived.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; simp only [rawUcNoHeaderReceived]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField rawAuth rfl d auth_mergeField_raw_le wt m.auth v rest bs' hm
      simp only [rawUcNoHeaderReceived, optRaw_eq_optWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

theorem ucHeaderReceived_mergeField_raw_le (d : Nat) (m : V1State.Unchunked.HeaderReceived) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.HeaderReceived) (rest' : Bytes)
    (h : V1State.Unchunked.HeaderReceived.mergeField m tag wt rest d = .ok (m', rest')) :
    rawUcHeaderReceived m' + rest'.length ≤ rawUcHeaderReceived m + rest.length + 1 := by
  unfold V1State.Unchunked.HeaderReceived.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; simp only [rawUcHeaderReceived]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField rawAuth rfl d auth_mergeField_raw_le wt m.auth v rest bs' hm
      simp only [rawUcHeaderReceived, optRaw_eq_optWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawUcHeaderReceived]; omega
      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := skipField_length_le hs; omega

theorem ucCt1Sent_mergeField_raw_le (d : Nat) (m : V1State.Unchunked.Ct1Sent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.Ct1Sent) (rest' : Bytes)
    (h : V1State.Unchunked.Ct1Sent.mergeField m tag wt rest d = .ok (m', rest')) :
    rawUcCt1Sent m' + rest'.length ≤ rawUcCt1Sent m + rest.length + 1 := by
  unfold V1State.Unchunked.Ct1Sent.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; simp only [rawUcCt1Sent]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField rawAuth rfl d auth_mergeField_raw_le wt m.auth v rest bs' hm
      simp only [rawUcCt1Sent, optRaw_eq_optWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawUcCt1Sent]; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawUcCt1Sent]; omega
        · split at h
          · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawUcCt1Sent]; omega
          · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            have := skipField_length_le hs; omega

theorem ucCt1SentEkReceived_mergeField_raw_le (d : Nat) (m : V1State.Unchunked.Ct1SentEkReceived) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.Ct1SentEkReceived) (rest' : Bytes)
    (h : V1State.Unchunked.Ct1SentEkReceived.mergeField m tag wt rest d = .ok (m', rest')) :
    rawUcCt1SentEkReceived m' + rest'.length ≤ rawUcCt1SentEkReceived m + rest.length + 1 := by
  unfold V1State.Unchunked.Ct1SentEkReceived.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; simp only [rawUcCt1SentEkReceived]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField rawAuth rfl d auth_mergeField_raw_le wt m.auth v rest bs' hm
      simp only [rawUcCt1SentEkReceived, optRaw_eq_optWeight] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawUcCt1SentEkReceived]; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawUcCt1SentEkReceived]; omega
        · split at h
          · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [rawUcCt1SentEkReceived]; omega
          · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            have := skipField_length_le hs; omega

theorem ucCt2Sent_mergeField_raw_le (d : Nat) (m : V1State.Unchunked.Ct2Sent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Unchunked.Ct2Sent) (rest' : Bytes)
    (h : V1State.Unchunked.Ct2Sent.mergeField m tag wt rest d = .ok (m', rest')) :
    rawUcCt2Sent m' + rest'.length ≤ rawUcCt2Sent m + rest.length + 1 := by
  unfold V1State.Unchunked.Ct2Sent.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeUint64_length_lt hm; simp only [rawUcCt2Sent]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le ProtoAuthenticator.mergeField rawAuth rfl d auth_mergeField_raw_le wt m.auth v rest bs' hm
      simp only [rawUcCt2Sent, optRaw_eq_optWeight] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

def ckKeysUnsampledFullW (m : V1State.Chunked.KeysUnsampled) : Nat := optWeight rawUcKeysUnsampled m.uc
def ckKeysSampledFullW (m : V1State.Chunked.KeysSampled) : Nat :=
  optWeight rawUcHeaderSent m.uc + optWeight encFullW m.sendingHdr
def ckHeaderSentFullW (m : V1State.Chunked.HeaderSent) : Nat :=
  optWeight rawUcEkSent m.uc + optWeight encFullW m.sendingEk + optWeight decFullW m.receivingCt1
def ckCt1ReceivedFullW (m : V1State.Chunked.Ct1Received) : Nat :=
  optWeight rawUcEkSentCt1Received m.uc + optWeight encFullW m.sendingEk
def ckEkSentCt1ReceivedFullW (m : V1State.Chunked.EkSentCt1Received) : Nat :=
  optWeight rawUcEkSentCt1Received m.uc + optWeight decFullW m.receivingCt2
def ckNoHeaderReceivedFullW (m : V1State.Chunked.NoHeaderReceived) : Nat :=
  optWeight rawUcNoHeaderReceived m.uc + optWeight decFullW m.receivingHdr
def ckHeaderReceivedFullW (m : V1State.Chunked.HeaderReceived) : Nat :=
  optWeight rawUcHeaderReceived m.uc + optWeight decFullW m.receivingEk
def ckCt1SampledFullW (m : V1State.Chunked.Ct1Sampled) : Nat :=
  optWeight rawUcCt1Sent m.uc + optWeight encFullW m.sendingCt1 + optWeight decFullW m.receivingEk
def ckEkReceivedCt1SampledFullW (m : V1State.Chunked.EkReceivedCt1Sampled) : Nat :=
  optWeight rawUcCt1SentEkReceived m.uc + optWeight encFullW m.sendingCt1
def ckCt1AcknowledgedFullW (m : V1State.Chunked.Ct1Acknowledged) : Nat :=
  optWeight rawUcCt1Sent m.uc + optWeight decFullW m.receivingEk
def ckCt2SampledFullW (m : V1State.Chunked.Ct2Sampled) : Nat :=
  optWeight rawUcCt2Sent m.uc + optWeight encFullW m.sendingCt2

theorem ckKeysUnsampled_mergeField_full_le (d : Nat) (m : V1State.Chunked.KeysUnsampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.KeysUnsampled) (rest' : Bytes)
    (h : V1State.Chunked.KeysUnsampled.mergeField m tag wt rest d = .ok (m', rest')) :
    ckKeysUnsampledFullW m' + rest'.length ≤ ckKeysUnsampledFullW m + rest.length + 1 := by
  unfold V1State.Chunked.KeysUnsampled.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le _ rawUcKeysUnsampled rfl d ucKeysUnsampled_mergeField_raw_le wt m.uc v rest bs' hm
    simp only [ckKeysUnsampledFullW] at this ⊢; omega
  · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := skipField_length_le hs; omega

theorem ckKeysSampled_mergeField_full_le (d : Nat) (m : V1State.Chunked.KeysSampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.KeysSampled) (rest' : Bytes)
    (h : V1State.Chunked.KeysSampled.mergeField m tag wt rest d = .ok (m', rest')) :
    ckKeysSampledFullW m' + rest'.length ≤ ckKeysSampledFullW m + rest.length + 1 := by
  unfold V1State.Chunked.KeysSampled.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le _ rawUcHeaderSent rfl d ucHeaderSent_mergeField_raw_le wt m.uc v rest bs' hm
    simp only [ckKeysSampledFullW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le _ encFullW rfl d polyEnc_mergeField_full_le wt m.sendingHdr v rest bs' hm
      simp only [ckKeysSampledFullW] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

theorem ckHeaderSent_mergeField_full_le (d : Nat) (m : V1State.Chunked.HeaderSent) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.HeaderSent) (rest' : Bytes)
    (h : V1State.Chunked.HeaderSent.mergeField m tag wt rest d = .ok (m', rest')) :
    ckHeaderSentFullW m' + rest'.length ≤ ckHeaderSentFullW m + rest.length + 1 := by
  unfold V1State.Chunked.HeaderSent.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le _ rawUcEkSent rfl d ucEkSent_mergeField_raw_le wt m.uc v rest bs' hm
    simp only [ckHeaderSentFullW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le _ encFullW rfl d polyEnc_mergeField_full_le wt m.sendingEk v rest bs' hm
      simp only [ckHeaderSentFullW] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := mergeOptMessage_weight_le _ decFullW rfl d polyDec_mergeField_full_le wt m.receivingCt1 v rest bs' hm
        simp only [ckHeaderSentFullW] at this ⊢; omega
      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := skipField_length_le hs; omega

theorem ckCt1Received_mergeField_full_le (d : Nat) (m : V1State.Chunked.Ct1Received) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.Ct1Received) (rest' : Bytes)
    (h : V1State.Chunked.Ct1Received.mergeField m tag wt rest d = .ok (m', rest')) :
    ckCt1ReceivedFullW m' + rest'.length ≤ ckCt1ReceivedFullW m + rest.length + 1 := by
  unfold V1State.Chunked.Ct1Received.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le _ rawUcEkSentCt1Received rfl d ucEkSentCt1Received_mergeField_raw_le wt m.uc v rest bs' hm
    simp only [ckCt1ReceivedFullW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le _ encFullW rfl d polyEnc_mergeField_full_le wt m.sendingEk v rest bs' hm
      simp only [ckCt1ReceivedFullW] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

theorem ckEkSentCt1Received_mergeField_full_le (d : Nat) (m : V1State.Chunked.EkSentCt1Received) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.EkSentCt1Received) (rest' : Bytes)
    (h : V1State.Chunked.EkSentCt1Received.mergeField m tag wt rest d = .ok (m', rest')) :
    ckEkSentCt1ReceivedFullW m' + rest'.length ≤ ckEkSentCt1ReceivedFullW m + rest.length + 1 := by
  unfold V1State.Chunked.EkSentCt1Received.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le _ rawUcEkSentCt1Received rfl d ucEkSentCt1Received_mergeField_raw_le wt m.uc v rest bs' hm
    simp only [ckEkSentCt1ReceivedFullW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le _ decFullW rfl d polyDec_mergeField_full_le wt m.receivingCt2 v rest bs' hm
      simp only [ckEkSentCt1ReceivedFullW] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

theorem ckNoHeaderReceived_mergeField_full_le (d : Nat) (m : V1State.Chunked.NoHeaderReceived) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.NoHeaderReceived) (rest' : Bytes)
    (h : V1State.Chunked.NoHeaderReceived.mergeField m tag wt rest d = .ok (m', rest')) :
    ckNoHeaderReceivedFullW m' + rest'.length ≤ ckNoHeaderReceivedFullW m + rest.length + 1 := by
  unfold V1State.Chunked.NoHeaderReceived.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le _ rawUcNoHeaderReceived rfl d ucNoHeaderReceived_mergeField_raw_le wt m.uc v rest bs' hm
    simp only [ckNoHeaderReceivedFullW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le _ decFullW rfl d polyDec_mergeField_full_le wt m.receivingHdr v rest bs' hm
      simp only [ckNoHeaderReceivedFullW] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

theorem ckHeaderReceived_mergeField_full_le (d : Nat) (m : V1State.Chunked.HeaderReceived) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.HeaderReceived) (rest' : Bytes)
    (h : V1State.Chunked.HeaderReceived.mergeField m tag wt rest d = .ok (m', rest')) :
    ckHeaderReceivedFullW m' + rest'.length ≤ ckHeaderReceivedFullW m + rest.length + 1 := by
  unfold V1State.Chunked.HeaderReceived.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le _ rawUcHeaderReceived rfl d ucHeaderReceived_mergeField_raw_le wt m.uc v rest bs' hm
    simp only [ckHeaderReceivedFullW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le _ decFullW rfl d polyDec_mergeField_full_le wt m.receivingEk v rest bs' hm
      simp only [ckHeaderReceivedFullW] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

theorem ckCt1Sampled_mergeField_full_le (d : Nat) (m : V1State.Chunked.Ct1Sampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.Ct1Sampled) (rest' : Bytes)
    (h : V1State.Chunked.Ct1Sampled.mergeField m tag wt rest d = .ok (m', rest')) :
    ckCt1SampledFullW m' + rest'.length ≤ ckCt1SampledFullW m + rest.length + 1 := by
  unfold V1State.Chunked.Ct1Sampled.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le _ rawUcCt1Sent rfl d ucCt1Sent_mergeField_raw_le wt m.uc v rest bs' hm
    simp only [ckCt1SampledFullW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le _ encFullW rfl d polyEnc_mergeField_full_le wt m.sendingCt1 v rest bs' hm
      simp only [ckCt1SampledFullW] at this ⊢; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := mergeOptMessage_weight_le _ decFullW rfl d polyDec_mergeField_full_le wt m.receivingEk v rest bs' hm
        simp only [ckCt1SampledFullW] at this ⊢; omega
      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := skipField_length_le hs; omega

theorem ckEkReceivedCt1Sampled_mergeField_full_le (d : Nat) (m : V1State.Chunked.EkReceivedCt1Sampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.EkReceivedCt1Sampled) (rest' : Bytes)
    (h : V1State.Chunked.EkReceivedCt1Sampled.mergeField m tag wt rest d = .ok (m', rest')) :
    ckEkReceivedCt1SampledFullW m' + rest'.length ≤ ckEkReceivedCt1SampledFullW m + rest.length + 1 := by
  unfold V1State.Chunked.EkReceivedCt1Sampled.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le _ rawUcCt1SentEkReceived rfl d ucCt1SentEkReceived_mergeField_raw_le wt m.uc v rest bs' hm
    simp only [ckEkReceivedCt1SampledFullW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le _ encFullW rfl d polyEnc_mergeField_full_le wt m.sendingCt1 v rest bs' hm
      simp only [ckEkReceivedCt1SampledFullW] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

theorem ckCt1Acknowledged_mergeField_full_le (d : Nat) (m : V1State.Chunked.Ct1Acknowledged) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.Ct1Acknowledged) (rest' : Bytes)
    (h : V1State.Chunked.Ct1Acknowledged.mergeField m tag wt rest d = .ok (m', rest')) :
    ckCt1AcknowledgedFullW m' + rest'.length ≤ ckCt1AcknowledgedFullW m + rest.length + 1 := by
  unfold V1State.Chunked.Ct1Acknowledged.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le _ rawUcCt1Sent rfl d ucCt1Sent_mergeField_raw_le wt m.uc v rest bs' hm
    simp only [ckCt1AcknowledgedFullW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le _ decFullW rfl d polyDec_mergeField_full_le wt m.receivingEk v rest bs' hm
      simp only [ckCt1AcknowledgedFullW] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

theorem ckCt2Sampled_mergeField_full_le (d : Nat) (m : V1State.Chunked.Ct2Sampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.Ct2Sampled) (rest' : Bytes)
    (h : V1State.Chunked.Ct2Sampled.mergeField m tag wt rest d = .ok (m', rest')) :
    ckCt2SampledFullW m' + rest'.length ≤ ckCt2SampledFullW m + rest.length + 1 := by
  unfold V1State.Chunked.Ct2Sampled.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le _ rawUcCt2Sent rfl d ucCt2Sent_mergeField_raw_le wt m.uc v rest bs' hm
    simp only [ckCt2SampledFullW] at this ⊢; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeOptMessage_weight_le _ encFullW rfl d polyEnc_mergeField_full_le wt m.sendingCt2 v rest bs' hm
      simp only [ckCt2SampledFullW] at this ⊢; omega
    · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; omega

def innerStateFullW : Option V1State.InnerState → Nat
  | none => 0
  | some (.keysUnsampled v) => ckKeysUnsampledFullW v
  | some (.keysSampled v) => ckKeysSampledFullW v
  | some (.headerSent v) => ckHeaderSentFullW v
  | some (.ct1Received v) => ckCt1ReceivedFullW v
  | some (.ekSentCt1Received v) => ckEkSentCt1ReceivedFullW v
  | some (.noHeaderReceived v) => ckNoHeaderReceivedFullW v
  | some (.headerReceived v) => ckHeaderReceivedFullW v
  | some (.ct1Sampled v) => ckCt1SampledFullW v
  | some (.ekReceivedCt1Sampled v) => ckEkReceivedCt1SampledFullW v
  | some (.ct1Acknowledged v) => ckCt1AcknowledgedFullW v
  | some (.ct2Sampled v) => ckCt2SampledFullW v

def v1FullWeight (m : V1State) : Nat := innerStateFullW m.innerState

private theorem ite_ok_cases {ε α : Type} {c : Prop} [Decidable c] {t e : Except ε α} {x : α}
    (h : (if c then t else e) = .ok x) : t = .ok x ∨ e = .ok x := by
  by_cases hc : c <;> simp [hc] at h <;> [exact Or.inl h; exact Or.inr h]

private theorem branch_oneof_weight {M I : Type} (mf : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (w : M → Nat) (iw : Option I → Nat) (ctor : M → I)
    (d : Nat)
    (hmf : ∀ d m tag wt rest m' rest', mf m tag wt rest d = .ok (m', rest') → w m' + rest'.length ≤ w m + rest.length + 1)
    {wt : Proto.WireType} {prev : M} {cur cur' : Option I} {rest rest' : Bytes}
    (hprev : w prev ≤ iw cur)
    (hctor : ∀ v, iw (some (ctor v)) = w v)
    (h : (do let (v, bs') ← Proto.mergeMessage mf wt prev rest d; pure (some (ctor v), bs')) = .ok (cur', rest')) :
    iw cur' + rest'.length ≤ iw cur + rest.length := by
  rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
  dsimp only [Pure.pure, Except.pure] at h
  rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
  have h1 := mergeMessage_weight_le mf w d hmf wt prev v rest bs' hm
  rw [hctor]; omega

theorem innerState_merge_full_le (d : Nat) (cur cur' : Option V1State.InnerState) (tag : BitVec 32)
    (wt : Proto.WireType) (rest rest' : Bytes)
    (h : V1State.InnerState.merge cur tag wt rest d = .ok (cur', rest')) :
    innerStateFullW cur' + rest'.length ≤ innerStateFullW cur + rest.length := by
  unfold V1State.InnerState.merge at h
  rcases ite_ok_cases h with h | h
  · exact branch_oneof_weight _ ckKeysUnsampledFullW innerStateFullW V1State.InnerState.keysUnsampled d
      ckKeysUnsampled_mergeField_full_le
      (by cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _)
      (fun _ => rfl) h
  rcases ite_ok_cases h with h | h
  · exact branch_oneof_weight _ ckKeysSampledFullW innerStateFullW V1State.InnerState.keysSampled d
      ckKeysSampled_mergeField_full_le
      (by cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _)
      (fun _ => rfl) h
  rcases ite_ok_cases h with h | h
  · exact branch_oneof_weight _ ckHeaderSentFullW innerStateFullW V1State.InnerState.headerSent d
      ckHeaderSent_mergeField_full_le
      (by cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _)
      (fun _ => rfl) h
  rcases ite_ok_cases h with h | h
  · exact branch_oneof_weight _ ckCt1ReceivedFullW innerStateFullW V1State.InnerState.ct1Received d
      ckCt1Received_mergeField_full_le
      (by cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _)
      (fun _ => rfl) h
  rcases ite_ok_cases h with h | h
  · exact branch_oneof_weight _ ckEkSentCt1ReceivedFullW innerStateFullW V1State.InnerState.ekSentCt1Received d
      ckEkSentCt1Received_mergeField_full_le
      (by cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _)
      (fun _ => rfl) h
  rcases ite_ok_cases h with h | h
  · exact branch_oneof_weight _ ckNoHeaderReceivedFullW innerStateFullW V1State.InnerState.noHeaderReceived d
      ckNoHeaderReceived_mergeField_full_le
      (by cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _)
      (fun _ => rfl) h
  rcases ite_ok_cases h with h | h
  · exact branch_oneof_weight _ ckHeaderReceivedFullW innerStateFullW V1State.InnerState.headerReceived d
      ckHeaderReceived_mergeField_full_le
      (by cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _)
      (fun _ => rfl) h
  rcases ite_ok_cases h with h | h
  · exact branch_oneof_weight _ ckCt1SampledFullW innerStateFullW V1State.InnerState.ct1Sampled d
      ckCt1Sampled_mergeField_full_le
      (by cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _)
      (fun _ => rfl) h
  rcases ite_ok_cases h with h | h
  · exact branch_oneof_weight _ ckEkReceivedCt1SampledFullW innerStateFullW V1State.InnerState.ekReceivedCt1Sampled d
      ckEkReceivedCt1Sampled_mergeField_full_le
      (by cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _)
      (fun _ => rfl) h
  rcases ite_ok_cases h with h | h
  · exact branch_oneof_weight _ ckCt1AcknowledgedFullW innerStateFullW V1State.InnerState.ct1Acknowledged d
      ckCt1Acknowledged_mergeField_full_le
      (by cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _)
      (fun _ => rfl) h
  rcases ite_ok_cases h with h | h
  · exact branch_oneof_weight _ ckCt2SampledFullW innerStateFullW V1State.InnerState.ct2Sampled d
      ckCt2Sampled_mergeField_full_le
      (by cases cur with | none => exact Nat.zero_le _ | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _)
      (fun _ => rfl) h
  · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := skipField_length_le hs; omega

theorem v1State_mergeField_full_le (d : Nat) (m : V1State) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State) (rest' : Bytes)
    (h : V1State.mergeField m tag wt rest d = .ok (m', rest')) :
    v1FullWeight m' + rest'.length ≤ v1FullWeight m + rest.length + 1 := by
  unfold V1State.mergeField at h; rcases ite_ok_cases h with h | h
  · rcases except_bind_eq_ok h with ⟨⟨is', bs'⟩, hm, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := innerState_merge_full_le d m.innerState is' tag wt rest bs' hm
    dsimp only [v1FullWeight]; omega
  · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := skipField_length_le hs; dsimp only [v1FullWeight]; omega

def pqInnerFullW : Option PqRatchetState.Inner → Nat
  | none => 0
  | some (.v1 v) => v1FullWeight v

def stateFullWeight (m : PqRatchetState) : Nat :=
  optVnWeight m.versionNegotiation + optChainWeight m.chain + pqInnerFullW m.inner

theorem pqRatchetState_mergeField_full_le (d : Nat) (m : PqRatchetState) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : PqRatchetState) (rest' : Bytes)
    (h : PqRatchetState.mergeField m tag wt rest d = .ok (m', rest')) :
    stateFullWeight m' + rest'.length ≤ stateFullWeight m + rest.length + 1 := by
  unfold PqRatchetState.mergeField at h
  rcases ite_ok_cases h with h | h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le VersionNegotiationPB.mergeField vnWeight rfl d vnPB_mergeField_weight_le wt m.versionNegotiation v rest bs' hm
    simp only [stateFullWeight, optVnWeight] at this ⊢; omega
  rcases ite_ok_cases h with h | h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le ChainPB.mergeField chainWeight rfl d chainPB_mergeField_weight_le wt m.chain v rest bs' hm
    simp only [stateFullWeight, optChainWeight] at this ⊢; omega
  rcases ite_ok_cases h with h | h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    unfold PqRatchetState.Inner.merge at hm; rcases ite_ok_cases hm with hm | hm
    · rcases except_bind_eq_ok hm with ⟨⟨v1, bs1⟩, hm1, hm⟩
      dsimp only [Pure.pure, Except.pure] at hm
      rcases Prod.mk.inj (Except.ok.inj hm) with ⟨rfl, rfl⟩
      have h1 : v1FullWeight v1 + bs1.length ≤ pqInnerFullW m.inner + rest.length :=
        Nat.le_trans (mergeMessage_weight_le V1State.mergeField v1FullWeight d v1State_mergeField_full_le wt _ v1 rest bs1 hm1)
          (Nat.add_le_add_right (by cases m.inner with | none => exact Nat.zero_le _ | some i => cases i; exact Nat.le_refl _) _)
      change (optVnWeight m.versionNegotiation + optChainWeight m.chain + v1FullWeight v1) + bs1.length ≤
        (optVnWeight m.versionNegotiation + optChainWeight m.chain + pqInnerFullW m.inner) + rest.length + 1
      omega
    · rcases except_bind_eq_ok hm with ⟨bs1, hs, hm⟩
      rcases Prod.mk.inj (Except.ok.inj hm) with ⟨rfl, rfl⟩
      have := skipField_length_le hs; dsimp only [stateFullWeight]; omega
  · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := skipField_length_le hs; dsimp only [stateFullWeight]; omega

theorem decodeState_fullWeight_le (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st : Bytes) (statePb : PqRatchetStatePB V1State)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok statePb) :
    optVnWeight statePb.versionNegotiation + optChainWeight statePb.chain +
      optWeight v1FullWeight statePb.inner ≤ st.length := by
  unfold decodeState at hdec; split at hdec
  · injection hdec with hst; subst hst; simp [optVnWeight, optChainWeight, optWeight]
  · dsimp only [spqrDepsWithMac] at hdec
    cases hp : Proto.decodeState st with
    | error _ => simp [hp] at hdec
    | ok rawSt =>
      rw [hp] at hdec; dsimp only at hdec; injection hdec with hst; subst hst
      have htop := mergeFieldsLoop_weight_le PqRatchetState.mergeField stateFullWeight Proto.RECURSION_LIMIT
        (pqRatchetState_mergeField_full_le Proto.RECURSION_LIMIT) st.length default rawSt st hp
      have hdef : stateFullWeight default = 0 := rfl
      rw [hdef, Nat.zero_add] at htop
      unfold pqRatchetStateToPb stateFullWeight at *
      cases hinner : rawSt.inner with
      | none => simp only [hinner, pqInnerFullW, Option.map, optWeight] at htop ⊢; omega
      | some i => cases i; simp only [hinner, pqInnerFullW, Option.map, optWeight] at htop ⊢; omega

theorem polynomialEncoder_encodeRaw_le_fullW (m : PolynomialEncoder) :
    (PolynomialEncoder.encodeRaw m).length ≤ encFullW m + 22 := by
  unfold PolynomialEncoder.encodeRaw encFullW
  simp only [List.length_append]
  have h1 := encodeUint32Field_length_le 1#32 m.idx; omega

theorem polynomialDecoder_encodeRaw_le_fullW (m : PolynomialDecoder) :
    (PolynomialDecoder.encodeRaw m).length ≤ decFullW m + 56 := by
  unfold PolynomialDecoder.encodeRaw decFullW
  simp only [List.length_append]
  have h1 := encodeUint32Field_length_le 1#32 m.ptsNeeded
  have h2 := encodeUint32Field_length_le 2#32 m.polys
  have h4 := encodeBoolField_length_le 4#32 m.isComplete; omega

private theorem encodeOptMessage_length_le_w {M : Type} (encodeRaw : M → Bytes) (w : M → Nat) (c : Nat)
    (h : ∀ m, (encodeRaw m).length ≤ w m + c) (tag : BitVec 32) (o : Option M) :
    (Proto.encodeOptMessage encodeRaw tag o).length ≤ optWeight w o + c + 22 := by
  cases o with
  | none => simp [Proto.encodeOptMessage, optWeight]
  | some m =>
    simp only [Proto.encodeOptMessage, optWeight]
    have hm := encodeMessage_length_le encodeRaw tag m
    have hw := h m; omega

theorem v1State_encodeRaw_le_fullWeight (m : V1State) :
    (V1State.encodeRaw m).length ≤ v1FullWeight m + 400 := by
  unfold V1State.encodeRaw v1FullWeight
  cases h : m.innerState with
  | none => simp [innerStateFullW]
  | some is =>
    dsimp only [V1State.InnerState.encode, innerStateFullW]
    cases is with
    | keysUnsampled v =>
      have hm := encodeMessage_length_le V1State.Chunked.KeysUnsampled.encodeRaw 1#32 v
      have h1 := encodeOptMessage_length_le_w V1State.Unchunked.KeysUnsampled.encodeRaw rawUcKeysUnsampled 88 ucKeysUnsampled_encodeRaw_length_le 1#32 v.uc
      simp only [V1State.Chunked.KeysUnsampled.encodeRaw, ckKeysUnsampledFullW] at hm h1 ⊢; omega
    | keysSampled v =>
      have hm := encodeMessage_length_le V1State.Chunked.KeysSampled.encodeRaw 2#32 v
      have h1 := encodeOptMessage_length_le_w V1State.Unchunked.HeaderSent.encodeRaw rawUcHeaderSent 132 ucHeaderSent_encodeRaw_length_le 1#32 v.uc
      have h2 := encodeOptMessage_length_le_w PolynomialEncoder.encodeRaw encFullW 22 polynomialEncoder_encodeRaw_le_fullW 2#32 v.sendingHdr
      simp only [V1State.Chunked.KeysSampled.encodeRaw, List.length_append, ckKeysSampledFullW] at hm h1 h2 ⊢; omega
    | headerSent v =>
      have hm := encodeMessage_length_le V1State.Chunked.HeaderSent.encodeRaw 3#32 v
      have h1 := encodeOptMessage_length_le_w V1State.Unchunked.EkSent.encodeRaw rawUcEkSent 110 ucEkSent_encodeRaw_length_le 1#32 v.uc
      have h2 := encodeOptMessage_length_le_w PolynomialEncoder.encodeRaw encFullW 22 polynomialEncoder_encodeRaw_le_fullW 2#32 v.sendingEk
      have h3 := encodeOptMessage_length_le_w PolynomialDecoder.encodeRaw decFullW 56 polynomialDecoder_encodeRaw_le_fullW 3#32 v.receivingCt1
      simp only [V1State.Chunked.HeaderSent.encodeRaw, List.length_append, ckHeaderSentFullW] at hm h1 h2 h3 ⊢; omega
    | ct1Received v =>
      have hm := encodeMessage_length_le V1State.Chunked.Ct1Received.encodeRaw 4#32 v
      have h1 := encodeOptMessage_length_le_w V1State.Unchunked.EkSentCt1Received.encodeRaw rawUcEkSentCt1Received 132 ucEkSentCt1Received_encodeRaw_length_le 1#32 v.uc
      have h2 := encodeOptMessage_length_le_w PolynomialEncoder.encodeRaw encFullW 22 polynomialEncoder_encodeRaw_le_fullW 2#32 v.sendingEk
      simp only [V1State.Chunked.Ct1Received.encodeRaw, List.length_append, ckCt1ReceivedFullW] at hm h1 h2 ⊢; omega
    | ekSentCt1Received v =>
      have hm := encodeMessage_length_le V1State.Chunked.EkSentCt1Received.encodeRaw 5#32 v
      have h1 := encodeOptMessage_length_le_w V1State.Unchunked.EkSentCt1Received.encodeRaw rawUcEkSentCt1Received 132 ucEkSentCt1Received_encodeRaw_length_le 1#32 v.uc
      have h2 := encodeOptMessage_length_le_w PolynomialDecoder.encodeRaw decFullW 56 polynomialDecoder_encodeRaw_le_fullW 3#32 v.receivingCt2
      simp only [V1State.Chunked.EkSentCt1Received.encodeRaw, List.length_append, ckEkSentCt1ReceivedFullW] at hm h1 h2 ⊢; omega
    | noHeaderReceived v =>
      have hm := encodeMessage_length_le V1State.Chunked.NoHeaderReceived.encodeRaw 6#32 v
      have h1 := encodeOptMessage_length_le_w V1State.Unchunked.NoHeaderReceived.encodeRaw rawUcNoHeaderReceived 88 ucNoHeaderReceived_encodeRaw_length_le 1#32 v.uc
      have h2 := encodeOptMessage_length_le_w PolynomialDecoder.encodeRaw decFullW 56 polynomialDecoder_encodeRaw_le_fullW 2#32 v.receivingHdr
      simp only [V1State.Chunked.NoHeaderReceived.encodeRaw, List.length_append, ckNoHeaderReceivedFullW] at hm h1 h2 ⊢; omega
    | headerReceived v =>
      have hm := encodeMessage_length_le V1State.Chunked.HeaderReceived.encodeRaw 7#32 v
      have h1 := encodeOptMessage_length_le_w V1State.Unchunked.HeaderReceived.encodeRaw rawUcHeaderReceived 110 ucHeaderReceived_encodeRaw_length_le 1#32 v.uc
      have h2 := encodeOptMessage_length_le_w PolynomialDecoder.encodeRaw decFullW 56 polynomialDecoder_encodeRaw_le_fullW 2#32 v.receivingEk
      simp only [V1State.Chunked.HeaderReceived.encodeRaw, List.length_append, ckHeaderReceivedFullW] at hm h1 h2 ⊢; omega
    | ct1Sampled v =>
      have hm := encodeMessage_length_le V1State.Chunked.Ct1Sampled.encodeRaw 8#32 v
      have h1 := encodeOptMessage_length_le_w V1State.Unchunked.Ct1Sent.encodeRaw rawUcCt1Sent 154 ucCt1Sent_encodeRaw_length_le 1#32 v.uc
      have h2 := encodeOptMessage_length_le_w PolynomialEncoder.encodeRaw encFullW 22 polynomialEncoder_encodeRaw_le_fullW 2#32 v.sendingCt1
      have h3 := encodeOptMessage_length_le_w PolynomialDecoder.encodeRaw decFullW 56 polynomialDecoder_encodeRaw_le_fullW 3#32 v.receivingEk
      simp only [V1State.Chunked.Ct1Sampled.encodeRaw, List.length_append, ckCt1SampledFullW] at hm h1 h2 h3 ⊢; omega
    | ekReceivedCt1Sampled v =>
      have hm := encodeMessage_length_le V1State.Chunked.EkReceivedCt1Sampled.encodeRaw 9#32 v
      have h1 := encodeOptMessage_length_le_w V1State.Unchunked.Ct1SentEkReceived.encodeRaw rawUcCt1SentEkReceived 154 ucCt1SentEkReceived_encodeRaw_length_le 1#32 v.uc
      have h2 := encodeOptMessage_length_le_w PolynomialEncoder.encodeRaw encFullW 22 polynomialEncoder_encodeRaw_le_fullW 2#32 v.sendingCt1
      simp only [V1State.Chunked.EkReceivedCt1Sampled.encodeRaw, List.length_append, ckEkReceivedCt1SampledFullW] at hm h1 h2 ⊢; omega
    | ct1Acknowledged v =>
      have hm := encodeMessage_length_le V1State.Chunked.Ct1Acknowledged.encodeRaw 10#32 v
      have h1 := encodeOptMessage_length_le_w V1State.Unchunked.Ct1Sent.encodeRaw rawUcCt1Sent 154 ucCt1Sent_encodeRaw_length_le 1#32 v.uc
      have h2 := encodeOptMessage_length_le_w PolynomialDecoder.encodeRaw decFullW 56 polynomialDecoder_encodeRaw_le_fullW 2#32 v.receivingEk
      simp only [V1State.Chunked.Ct1Acknowledged.encodeRaw, List.length_append, ckCt1AcknowledgedFullW] at hm h1 h2 ⊢; omega
    | ct2Sampled v =>
      have hm := encodeMessage_length_le V1State.Chunked.Ct2Sampled.encodeRaw 11#32 v
      have h1 := encodeOptMessage_length_le_w V1State.Unchunked.Ct2Sent.encodeRaw rawUcCt2Sent 88 ucCt2Sent_encodeRaw_length_le 1#32 v.uc
      have h2 := encodeOptMessage_length_le_w PolynomialEncoder.encodeRaw encFullW 22 polynomialEncoder_encodeRaw_le_fullW 2#32 v.sendingCt2
      simp only [V1State.Chunked.Ct2Sampled.encodeRaw, List.length_append, ckCt2SampledFullW] at hm h1 h2 ⊢; omega

end Symbolic.Swarm.TRREF.GrowthRecv
