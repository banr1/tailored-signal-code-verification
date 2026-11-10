/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.Helpers2APure
public import Symbolic.Proofs.SpecLemmas.ProofHubsPure
public import Symbolic.Proofs.Swarm.CREF.Grow.Defs
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
import Symbolic.Proofs.Swarm.SHARED.StateSizePure
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.Helpers1APure

/-!
# SPQR V1 Chunked State Weight Bounds and `StatePbOooBounded`

Proves protobuf field-merge weight bounds for the 11 chunked V1 inner states and `PqRatchetState`,
lifts `SpqrOooBounded` to `StatePbOooBounded` across `decodeState`, and relates raw polynomial
encoder/decoder sizes to their decoded weights.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthRecvPureB

open Symbolic.Swarm.CREF (SpqrOooBounded)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open Symbolic.Swarm.TRREF.SpqrSemOf
open CryptoVerification.SpqrV1.Top.StateSize.SymP3
open CryptoVerification.SpqrV1.ProtoRepr

theorem ckKeysUnsampled_mergeField_le (d : Nat) (m : V1State.Chunked.KeysUnsampled) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State.Chunked.KeysUnsampled) (rest' : Bytes)
    (h : V1State.Chunked.KeysUnsampled.mergeField m tag wt rest d = .ok (m', rest')) :
    ckKeysUnsampledW m' + rest'.length ≤ ckKeysUnsampledW m + rest.length + 1 := by
  unfold V1State.Chunked.KeysUnsampled.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeOptMessage_weight_le V1State.Unchunked.KeysUnsampled.mergeField (fun u => optAuthWeight u.auth) rfl d ucKeysUnsampled_mergeField_le wt m.uc v rest bs' hm
    simp only [ckKeysUnsampledW] at this ⊢; omega
  · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := skipField_length_le hs; omega

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
      have := skipField_length_le hs; omega

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
        have := skipField_length_le hs; omega

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
      have := skipField_length_le hs; omega

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
      have := skipField_length_le hs; omega

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
      have := skipField_length_le hs; omega

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
      have := skipField_length_le hs; omega

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
        have := skipField_length_le hs; omega

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
      have := skipField_length_le hs; omega

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
      have := skipField_length_le hs; omega

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
      have := skipField_length_le hs; omega

def innerStateW : Option V1State.InnerState → Nat
  | none => 0
  | some (.keysUnsampled v) => ckKeysUnsampledW v
  | some (.keysSampled v) => ckKeysSampledW v
  | some (.headerSent v) => ckHeaderSentW v
  | some (.ct1Received v) => ckCt1ReceivedW v
  | some (.ekSentCt1Received v) => ckEkSentCt1ReceivedW v
  | some (.noHeaderReceived v) => ckNoHeaderReceivedW v
  | some (.headerReceived v) => ckHeaderReceivedW v
  | some (.ct1Sampled v) => ckCt1SampledW v
  | some (.ekReceivedCt1Sampled v) => ckEkReceivedCt1SampledW v
  | some (.ct1Acknowledged v) => ckCt1AcknowledgedW v
  | some (.ct2Sampled v) => ckCt2SampledW v

def v1Weight (m : V1State) : Nat := innerStateW m.innerState

theorem ite_ok_cases {ε α : Type} {c : Prop} [Decidable c] {t e : Except ε α} {x : α}
    (h : (if c then t else e) = .ok x) : t = .ok x ∨ e = .ok x := by
  by_cases hc : c <;> simp [hc] at h <;> [exact Or.inl h; exact Or.inr h]

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
                        have := skipField_length_le hs; omega

theorem v1State_mergeField_le (d : Nat) (m : V1State) (tag : BitVec 32)
    (wt : Proto.WireType) (rest : Bytes) (m' : V1State) (rest' : Bytes)
    (h : V1State.mergeField m tag wt rest d = .ok (m', rest')) :
    v1Weight m' + rest'.length ≤ v1Weight m + rest.length + 1 := by
  unfold V1State.mergeField at h; rcases ite_ok_cases h with h | h
  · rcases except_bind_eq_ok h with ⟨⟨is', bs'⟩, hm, h⟩; dsimp only at h; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := innerState_merge_le d m.innerState is' tag wt rest bs' hm
    dsimp only [v1Weight]; omega
  · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := skipField_length_le hs; dsimp only [v1Weight]; omega

def pqInnerW : Option PqRatchetState.Inner → Nat
  | none => 0
  | some (.v1 v) => v1Weight v

def stateWeight (m : PqRatchetState) : Nat :=
  optVnWeight m.versionNegotiation + optChainWeight m.chain + pqInnerW m.inner

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
          have := skipField_length_le hs; dsimp only [stateWeight]; omega
      · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := skipField_length_le hs; dsimp only [stateWeight]; omega

theorem decodeState_weight_le (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st : Bytes) (statePb : PqRatchetStatePB V1State)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok statePb) :
    optVnWeight statePb.versionNegotiation + optChainWeight statePb.chain +
      (match statePb.inner with | none => 0 | some v => v1Weight v) ≤ st.length := by
  unfold decodeState at hdec
  split at hdec
  · injection hdec with hst; subst hst; simp [optVnWeight, optChainWeight, optWeight]
  · dsimp only [spqrDepsWithMac] at hdec
    cases hp : Proto.decodeState st with
    | error _ => simp [hp] at hdec
    | ok rawSt =>
      rw [hp] at hdec; dsimp only at hdec; injection hdec with hst; subst hst
      have htop := mergeFieldsLoop_weight_le PqRatchetState.mergeField stateWeight Proto.RECURSION_LIMIT
        (pqRatchetState_mergeField_le Proto.RECURSION_LIMIT) st.length default rawSt st hp
      have hdef : stateWeight default = 0 := rfl
      rw [hdef, Nat.zero_add] at htop
      unfold pqRatchetStateToPb stateWeight at *
      cases hinner : rawSt.inner with
      | none => simp only [hinner, pqInnerW, Option.map] at htop ⊢; omega
      | some i => cases i; simp only [hinner, pqInnerW, Option.map] at htop ⊢; omega

/-! ## `StatePbOooBounded` and Polynomial Codec Weight Bounds -/

/-- `SpqrOooBounded` lifted to decoded `PqRatchetStatePB`. -/
def StatePbOooBounded {V1StatePB : Type} (statePb : PqRatchetStatePB V1StatePB) : Prop :=
  (∀ c ∈ statePb.chain, ∀ p ∈ c.params, p.maxOooKeysOrDefault.toNat ≤ 2000) ∧
  (∀ v ∈ statePb.versionNegotiation, ∀ p ∈ v.chainParams, p.maxOooKeysOrDefault.toNat ≤ 2000)

theorem statePbOooBounded_of_decodeState
    (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st : Bytes) (statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok statePb) :
    StatePbOooBounded statePb := by
  unfold decodeState at hdec
  split at hdec
  · injection hdec with hst
    subst hst
    exact ⟨(by intro c hc; cases hc), (by intro v hv; cases hv)⟩
  · dsimp only [spqrDepsWithMac] at hdec
    cases hp : Proto.decodeState st with
    | error _ => simp [hp] at hdec
    | ok rawSt =>
      rw [hp] at hdec
      dsimp only at hdec
      injection hdec with hst
      subst hst
      exact hb rawSt hp

theorem chain_new_params (hkdf : HkdfFn) (k : Bytes) (dir : Direction) (params : ChainParamsPB) (c : Chain)
    (h : Chain.new hkdf k dir params = .ok c) :
    c.params = params := by
  unfold Chain.new at h
  injection h with hc
  subst hc
  rfl

theorem chainFromVersionNegotiation_params (hkdf : HkdfFn) (vn : VersionNegotiationPB) (c : Chain)
    (h : chainFromVersionNegotiation hkdf vn = .ok c) :
    vn.chainParams = some c.params := by
  unfold chainFromVersionNegotiation at h
  cases hd : Direction.fromI32? vn.direction with
  | none => simp [hd, Bind.bind, Except.bind] at h
  | some dir =>
    cases hp : vn.chainParams with
    | none => simp [hd, hp, Bind.bind, Except.bind] at h
    | some params =>
      simp only [hd, hp, Bind.bind, Except.bind] at h
      have hnew := chain_new_params hkdf vn.authKey dir params c h
      rw [hnew]

theorem chain_fromPb_params (pb : ChainPB) (c : Chain)
    (h : Chain.fromPb pb = .ok c) :
    pb.params = some c.params := by
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
        injection h with hc
        subst hc
        rfl

theorem chain_addEpoch_params (hkdf : HkdfFn) (c0 : Chain) (es : EpochSecret) (c1 : Chain)
    (h : c0.addEpoch hkdf es = .ok c1) :
    c1.params = c0.params := by
  unfold Chain.addEpoch at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · injection h with hc
      subst hc
      rfl

@[scoped simp]
theorem chain_intoPb_params (c : Chain) :
    c.intoPb.params = some c.params := rfl

open CryptoVerification.SpqrV1.Top.StateSize.SymP3

@[scoped simp] theorem pure_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (pure x >>= f) = f x := rfl
@[scoped simp] theorem ok_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl
@[scoped simp] theorem except_mapError_eq_ok_iff {ε ε' α : Type} {f : ε → ε'}
    {m : Except ε α} {a : α} : m.mapError f = .ok a ↔ m = .ok a := by cases m <;> simp [Except.mapError]
@[scoped simp] theorem liftSpqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    liftSpqrPanic r = .ok v ↔ r = .ok v := by cases r <;> simp [liftSpqrPanic]
@[scoped simp] theorem statesResult_ofPanic_eq_ok {ε α : Type} [ToStatesPanic ε]
    {r : Except ε α} {v : α} : StatesResult.ofPanic r = .ok v ↔ r = .ok v := by
  cases r <;> simp [StatesResult.ofPanic]

theorem rawOptAuth_eq_optAuthWeight : ∀ (o : Option ProtoAuthenticator), optRaw rawAuth o = optAuthWeight o
  | none => rfl
  | some _ => rfl

theorem sum_map_add_const (xs : List Bytes) (c : Nat) :
    (xs.map (fun b => b.length + c)).sum = bytesSum xs + c * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, bytesSum_cons, List.length_cons, Nat.mul_succ, ih]
    omega

theorem polyEncoder_fromPb_raw_le_weight {pb : PolynomialEncoder} {enc : PolyEncoder}
    (h : PolyEncoder.fromPb (pbToProtoPolyEncoder pb) = .ok (.ok enc)) :
    rawPolyEnc pb ≤ encWeight pb + 352 := by
  unfold PolyEncoder.fromPb at h; split at h
  · split at h
    · simp [pure, Except.pure] at h
    · split at h
      · simp [pure, Except.pure] at h
      · rename_i h1 h2 h3
        have hpts : pb.pts.length = 16 := by simpa [pbToProtoPolyEncoder, NUM_POLYS, CHUNK_SIZE, bne_iff_ne] using h3
        have hpolys : pb.polys.length = 0 := by
          cases hpol : pb.polys with
          | nil => rfl
          | cons _ _ => simp [pbToProtoPolyEncoder, hpol] at h2
        simp only [rawPolyEnc, encWeight, sum_map_add_const, hpts, hpolys]; omega
  · split at h
    · rename_i h1 h2
      have hpts : pb.pts.length = 0 := by
        cases hpt : pb.pts with
        | nil => rfl
        | cons _ _ => simp [pbToProtoPolyEncoder, hpt] at h1
      have hpolys : pb.polys.length = 16 := by simpa [pbToProtoPolyEncoder, NUM_POLYS, CHUNK_SIZE, beq_iff_eq] using h2
      simp only [rawPolyEnc, encWeight, sum_map_add_const, hpts, hpolys]; omega
    · simp [pure, Except.pure] at h

theorem encoderFromPbStateDecode_raw_le_weight {pb? : Option PolynomialEncoder} {enc : PolyEncoder}
    (h : encoderFromPbStateDecode spqrPolyApi pb? = .ok enc) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ optEncWeight pb? + 352 := by
  have hraw := encoderFromPbStateDecode_raw_le h
  unfold encoderFromPbStateDecode spqrPolyApi at h
  cases pb? with
  | none => contradiction
  | some pb =>
    dsimp only [] at h
    rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    have h1' := except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h1)
    cases res with
    | error _ => contradiction
    | ok enc' =>
      have hinj := Except.ok.inj h2; subst hinj
      have hpb := polyEncoder_fromPb_raw_le_weight h1'
      simp only [optRaw_some, optEncWeight, optWeight] at hraw ⊢
      omega

theorem polyDecoder_fromPb_raw_le_weight {pb : PolynomialDecoder} {dec : PolyDecoder}
    (h : PolyDecoder.fromPb (pbToProtoPolyDecoder pb) = .ok (.ok dec)) :
    rawPolyDec pb ≤ decWeight pb + 352 := by
  unfold PolyDecoder.fromPb at h; split at h
  · simp [pure, Except.pure] at h
  · rename_i h1
    have hpts : pb.pts.length = 16 := by simpa [pbToProtoPolyDecoder, NUM_POLYS, CHUNK_SIZE, bne_iff_ne] using h1
    simp only [rawPolyDec, decWeight, sum_map_add_const, hpts]; omega

theorem decoderFromPbStateDecode_raw_le_weight {pb? : Option PolynomialDecoder} {dec : PolyDecoder}
    (h : decoderFromPbStateDecode spqrPolyApi pb? = .ok dec) :
    rawPolyDec (protoPolyDecoderToPb dec.intoPb) ≤ optDecWeight pb? + 352 := by
  have hraw := (decoderFromPbStateDecode_raw_le h).1
  unfold decoderFromPbStateDecode spqrPolyApi at h
  cases pb? with
  | none => contradiction
  | some pb =>
    dsimp only [] at h
    rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    have h1' := except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h1)
    cases res with
    | error _ => contradiction
    | ok dec' =>
      have hinj := Except.ok.inj h2; subst hinj
      have hpb := polyDecoder_fromPb_raw_le_weight h1'
      simp only [optRaw_some, optDecWeight, optWeight] at hraw ⊢
      omega

end Symbolic.Swarm.TRREF.GrowthRecvPureB
