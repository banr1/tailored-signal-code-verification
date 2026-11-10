/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
import DY.Bytes.Basic
import Symbolic.Specifications.Model.EquationalTheory.Kem
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Init.Data.String
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc

/-!
# Composed Term Algebra

Injectivity, destructor characterization, and KDF domain-separation lemmas on
`DY.Libsignal.Composed.Bytes`, together with X25519 agreement inversion and the
`bobAgreement`/`aliceAgreement` key-equality bridges.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.TermAlgebra

open DY DY.Comparse DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed

/-! ## Concatenation, literals, and serialization -/

theorem concat_inj {a₁ b₁ a₂ b₂ : Bytes}
    (h : Concat.concat a₁ b₁ = Concat.concat a₂ b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have hv := congrArg (fun x : Bytes => x.view? Concat.Concat.SubF) h
  simp only [Concat.concat, Concat.CanConcat.concat, BytesView.view_pack,
    Option.some.injEq, Concat.Concat.SubF.mk.injEq] at hv
  exact hv

theorem litByte_inj {b₁ b₂ : UInt8} (h : litByte b₁ = litByte b₂) : b₁ = b₂ := by
  have hm := congrArg bytesToLiteral h
  simp only [litByte, bytesToLiteral_literalToBytes, Option.some.injEq] at hm
  have hd : (#[b₁] : Array UInt8)[0]? = (#[b₂] : Array UInt8)[0]? :=
    congrArg (fun a : ByteArray => a.data[0]?) hm
  simpa using hd

theorem encodeEC_inj {pk₁ pk₂ : Bytes} (h : encodeEC pk₁ = encodeEC pk₂) : pk₁ = pk₂ :=
  (concat_inj h).2

theorem encodeKEM_inj {pk₁ pk₂ : Bytes} (h : encodeKEM pk₁ = encodeKEM pk₂) : pk₁ = pk₂ :=
  (concat_inj h).2

theorem serializedIk_inj {ik₁ ik₂ : Bytes} (h : serializedIk ik₁ = serializedIk ik₂) : ik₁ = ik₂ :=
  encodeEC_inj h

theorem encodeEC_ne_encodeKEM (pk₁ pk₂ : Bytes) : encodeEC pk₁ ≠ encodeKEM pk₂ := by
  intro h
  have hb := litByte_inj (concat_inj h).1
  revert hb; decide

/-! ## KDF extract, HKDF blocks, and PQXDH KDF -/

theorem kdfExtract_inj {s₁ m₁ s₂ m₂ : Bytes}
    (h : kdfExtract s₁ m₁ = kdfExtract s₂ m₂) : s₁ = s₂ ∧ m₁ = m₂ := by
  have hv := congrArg (fun b : Bytes => b.view? KdfExtract.KdfExtract.SubF) h
  dsimp only [KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hv
  rw [BytesView.view_pack, BytesView.view_pack] at hv
  injection hv with hv'
  cases hv'
  exact ⟨rfl, rfl⟩

theorem hmac_inj {k₁ m₁ k₂ m₂ : Bytes} (h : hmac k₁ m₁ = hmac k₂ m₂) : k₁ = k₂ ∧ m₁ = m₂ :=
  kdfExtract_inj h

theorem hkdfBlock1_inj {p₁ i₁ p₂ i₂ : Bytes}
    (h : hkdfBlock1 p₁ i₁ = hkdfBlock1 p₂ i₂) : p₁ = p₂ ∧ i₁ = i₂ := by
  obtain ⟨hp, hi⟩ := hmac_inj h
  exact ⟨hp, (concat_inj hi).1⟩

theorem hkdfBlock2_inj {p₁ i₁ p₂ i₂ : Bytes}
    (h : hkdfBlock2 p₁ i₁ = hkdfBlock2 p₂ i₂) : p₁ = p₂ ∧ i₁ = i₂ := by
  obtain ⟨hp, hi⟩ := hmac_inj h
  exact ⟨hp, (concat_inj (concat_inj hi).2).1⟩

theorem hkdfBlock3_inj {p₁ i₁ p₂ i₂ : Bytes}
    (h : hkdfBlock3 p₁ i₁ = hkdfBlock3 p₂ i₂) : p₁ = p₂ ∧ i₁ = i₂ := by
  obtain ⟨hp, hi⟩ := hmac_inj h
  exact ⟨hp, (concat_inj (concat_inj hi).2).1⟩

theorem hkdfBlock1_ne_hkdfBlock2 (p₁ i₁ p₂ i₂ : Bytes) :
    hkdfBlock1 p₁ i₁ ≠ hkdfBlock2 p₂ i₂ := by
  intro h
  have hr := (concat_inj (hmac_inj h).2).2
  dsimp only [litByte, literalToBytes, Concat.concat, Concat.CanConcat.concat] at hr
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hr

theorem hkdfBlock1_ne_hkdfBlock3 (p₁ i₁ p₂ i₂ : Bytes) :
    hkdfBlock1 p₁ i₁ ≠ hkdfBlock3 p₂ i₂ := by
  intro h
  have hr := (concat_inj (hmac_inj h).2).2
  dsimp only [litByte, literalToBytes, Concat.concat, Concat.CanConcat.concat] at hr
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hr

theorem hkdfBlock2_ne_hkdfBlock3 (p₁ i₁ p₂ i₂ : Bytes) :
    hkdfBlock2 p₁ i₁ ≠ hkdfBlock3 p₂ i₂ := by
  intro h
  have hcat := (hmac_inj h).2
  have hr := (concat_inj (concat_inj hcat).2).2
  have hb := litByte_inj hr
  revert hb; decide

theorem pqxdhKdf_rk_inj {ikm₁ ikm₂ : Bytes}
    (h : (pqxdhKdf ikm₁).rk = (pqxdhKdf ikm₂).rk) : ikm₁ = ikm₂ :=
  (hmac_inj (hkdfBlock1_inj h).1).2

theorem pqxdhKdf_ck_inj {ikm₁ ikm₂ : Bytes}
    (h : (pqxdhKdf ikm₁).ck = (pqxdhKdf ikm₂).ck) : ikm₁ = ikm₂ :=
  (hmac_inj (hkdfBlock2_inj h).1).2

theorem pqxdhKdf_pqr_inj {ikm₁ ikm₂ : Bytes}
    (h : (pqxdhKdf ikm₁).pqr = (pqxdhKdf ikm₂).pqr) : ikm₁ = ikm₂ :=
  (hmac_inj (hkdfBlock3_inj h).1).2

theorem pqxdhKdf_inj {ikm₁ ikm₂ : Bytes}
    (h : pqxdhKdf ikm₁ = pqxdhKdf ikm₂) : ikm₁ = ikm₂ :=
  pqxdhKdf_rk_inj (congrArg HandshakeKeys.rk h)

/-! ## Ratchet key schedule and domain separation -/

theorem pqxdhLabel_ne_whisperRatchet :
    (pqxdhLabel : Bytes) ≠ lit "WhisperRatchet" := by
  intro h
  have hm := congrArg bytesToLiteral h
  simp only [pqxdhLabel, lit, bytesToLiteral_literalToBytes, Option.some.injEq,
    String.toUTF8_eq_toByteArray, String.toByteArray_inj] at hm
  have hl := congrArg String.toList hm; revert hl; decide

theorem pqxdhLabel_ne_whisperMessageKeys :
    (pqxdhLabel : Bytes) ≠ lit "WhisperMessageKeys" := by
  intro h
  have hm := congrArg bytesToLiteral h
  simp only [pqxdhLabel, lit, bytesToLiteral_literalToBytes, Option.some.injEq,
    String.toUTF8_eq_toByteArray, String.toByteArray_inj] at hm
  have hl := congrArg String.toList hm; revert hl; decide

theorem lit_whisperRatchet_ne_whisperMessageKeys :
    (lit "WhisperRatchet" : Bytes) ≠ lit "WhisperMessageKeys" := by
  intro h
  have hm := congrArg bytesToLiteral h
  simp only [lit, bytesToLiteral_literalToBytes, Option.some.injEq,
    String.toUTF8_eq_toByteArray, String.toByteArray_inj] at hm
  have hl := congrArg String.toList hm; revert hl; decide

theorem kdfRk_fst_inj {rk₁ dh₁ rk₂ dh₂ : Bytes}
    (h : (kdfRk rk₁ dh₁).1 = (kdfRk rk₂ dh₂).1) : rk₁ = rk₂ ∧ dh₁ = dh₂ :=
  hmac_inj (hkdfBlock1_inj h).1

theorem kdfRk_snd_inj {rk₁ dh₁ rk₂ dh₂ : Bytes}
    (h : (kdfRk rk₁ dh₁).2 = (kdfRk rk₂ dh₂).2) : rk₁ = rk₂ ∧ dh₁ = dh₂ :=
  hmac_inj (hkdfBlock2_inj h).1

theorem createChain_fst_inj {rk₁ pk₁ sk₁ rk₂ pk₂ sk₂ : Bytes}
    (h : (createChain rk₁ pk₁ sk₁).1 = (createChain rk₂ pk₂ sk₂).1) :
    rk₁ = rk₂ ∧ agree pk₁ sk₁ = agree pk₂ sk₂ :=
  kdfRk_fst_inj h

theorem createChain_snd_inj {rk₁ pk₁ sk₁ rk₂ pk₂ sk₂ : Bytes}
    (h : (createChain rk₁ pk₁ sk₁).2 = (createChain rk₂ pk₂ sk₂).2) :
    rk₁ = rk₂ ∧ agree pk₁ sk₁ = agree pk₂ sk₂ :=
  kdfRk_snd_inj h

theorem pqxdhKdf_rk_ne_createChain_fst (ikm rk pk sk : Bytes) :
    (pqxdhKdf ikm).rk ≠ (createChain rk pk sk).1 := by
  intro h
  exact pqxdhLabel_ne_whisperRatchet (hkdfBlock1_inj h).2

theorem pqxdhKdf_ck_ne_createChain_snd (ikm rk pk sk : Bytes) :
    (pqxdhKdf ikm).ck ≠ (createChain rk pk sk).2 := by
  intro h
  exact pqxdhLabel_ne_whisperRatchet (hkdfBlock2_inj h).2

theorem kdfCk_fst_inj {ck₁ ck₂ : Bytes} (h : (kdfCk ck₁).1 = (kdfCk ck₂).1) : ck₁ = ck₂ :=
  (hmac_inj h).1

theorem kdfCk_snd_inj {ck₁ ck₂ : Bytes} (h : (kdfCk ck₁).2 = (kdfCk ck₂).2) : ck₁ = ck₂ :=
  (hmac_inj h).1

theorem kdfCk_fst_ne_snd (ck₁ ck₂ : Bytes) : (kdfCk ck₁).1 ≠ (kdfCk ck₂).2 := by
  intro h
  have hm := litByte_inj (hmac_inj h).2
  revert hm; decide

theorem hkdfBlock1_ne_kdfCk_fst (p i ck : Bytes) : hkdfBlock1 p i ≠ (kdfCk ck).1 := by
  intro h
  obtain ⟨_, hikm⟩ := hmac_inj h
  dsimp only [litByte, literalToBytes, Concat.concat, Concat.CanConcat.concat] at hikm
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hikm

theorem hkdfBlock1_ne_kdfCk_snd (p i ck : Bytes) : hkdfBlock1 p i ≠ (kdfCk ck).2 := by
  intro h
  obtain ⟨_, hikm⟩ := hmac_inj h
  dsimp only [litByte, literalToBytes, Concat.concat, Concat.CanConcat.concat] at hikm
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hikm

theorem hkdfBlock2_ne_kdfCk_fst (p i ck : Bytes) : hkdfBlock2 p i ≠ (kdfCk ck).1 := by
  intro h
  obtain ⟨_, hikm⟩ := hmac_inj h
  dsimp only [litByte, literalToBytes, Concat.concat, Concat.CanConcat.concat] at hikm
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hikm

theorem hkdfBlock2_ne_kdfCk_snd (p i ck : Bytes) : hkdfBlock2 p i ≠ (kdfCk ck).2 := by
  intro h
  obtain ⟨_, hikm⟩ := hmac_inj h
  dsimp only [litByte, literalToBytes, Concat.concat, Concat.CanConcat.concat] at hikm
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hikm

theorem hkdfBlock3_ne_kdfCk_fst (p i ck : Bytes) : hkdfBlock3 p i ≠ (kdfCk ck).1 := by
  intro h
  obtain ⟨_, hikm⟩ := hmac_inj h
  dsimp only [litByte, literalToBytes, Concat.concat, Concat.CanConcat.concat] at hikm
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hikm

theorem hkdfBlock3_ne_kdfCk_snd (p i ck : Bytes) : hkdfBlock3 p i ≠ (kdfCk ck).2 := by
  intro h
  obtain ⟨_, hikm⟩ := hmac_inj h
  dsimp only [litByte, literalToBytes, Concat.concat, Concat.CanConcat.concat] at hikm
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hikm

theorem createChain_snd_ne_kdfCk_fst (rk pk sk ck : Bytes) :
    (createChain rk pk sk).2 ≠ (kdfCk ck).1 :=
  hkdfBlock2_ne_kdfCk_fst _ _ _

theorem pqxdhKdf_ck_ne_kdfCk_fst (ikm ck : Bytes) :
    (pqxdhKdf ikm).ck ≠ (kdfCk ck).1 :=
  hkdfBlock2_ne_kdfCk_fst _ _ _

theorem chainKeyAt_add (ck : Bytes) : ∀ m n : Nat,
    chainKeyAt ck (m + n) = chainKeyAt (chainKeyAt ck m) n
  | 0, n => by simp [chainKeyAt]
  | m + 1, n => by rw [Nat.add_right_comm, Nat.add_assoc]; exact chainKeyAt_add (kdfCk ck).1 m n

theorem chainKeyAt_succ_eq_kdfCk_fst (ck : Bytes) (n : Nat) :
    chainKeyAt ck (n + 1) = (kdfCk (chainKeyAt ck n)).1 := by
  rw [chainKeyAt_add ck n 1]; rfl

theorem chainKeyAt_createChain_snd_inj {rk₁ pk₁ sk₁ rk₂ pk₂ sk₂ : Bytes} :
    ∀ {n₁ n₂ : Nat},
      chainKeyAt (createChain rk₁ pk₁ sk₁).2 n₁ = chainKeyAt (createChain rk₂ pk₂ sk₂).2 n₂ →
      (createChain rk₁ pk₁ sk₁).2 = (createChain rk₂ pk₂ sk₂).2 ∧ n₁ = n₂
  | 0, 0, h => ⟨h, rfl⟩
  | 0, n₂ + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    exact False.elim (createChain_snd_ne_kdfCk_fst _ _ _ _ h)
  | n₁ + 1, 0, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    exact False.elim (createChain_snd_ne_kdfCk_fst _ _ _ _ h.symm)
  | n₁ + 1, n₂ + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst, chainKeyAt_succ_eq_kdfCk_fst] at h
    obtain ⟨hck, rfl⟩ := chainKeyAt_createChain_snd_inj (kdfCk_fst_inj h)
    exact ⟨hck, rfl⟩

theorem chainKeyAt_pqxdhKdf_ck_inj {ikm₁ ikm₂ : Bytes} :
    ∀ {n₁ n₂ : Nat},
      chainKeyAt (pqxdhKdf ikm₁).ck n₁ = chainKeyAt (pqxdhKdf ikm₂).ck n₂ →
      (pqxdhKdf ikm₁).ck = (pqxdhKdf ikm₂).ck ∧ n₁ = n₂
  | 0, 0, h => ⟨h, rfl⟩
  | 0, n₂ + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    exact False.elim (pqxdhKdf_ck_ne_kdfCk_fst _ _ h)
  | n₁ + 1, 0, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    exact False.elim (pqxdhKdf_ck_ne_kdfCk_fst _ _ h.symm)
  | n₁ + 1, n₂ + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst, chainKeyAt_succ_eq_kdfCk_fst] at h
    obtain ⟨hck, rfl⟩ := chainKeyAt_pqxdhKdf_ck_inj (kdfCk_fst_inj h)
    exact ⟨hck, rfl⟩

theorem chainKeyAt_createChain_snd_ne_chainKeyAt_pqxdhKdf_ck
    (rk pk sk ikm : Bytes) :
    ∀ (n₁ n₂ : Nat),
      chainKeyAt (createChain rk pk sk).2 n₁ ≠ chainKeyAt (pqxdhKdf ikm).ck n₂
  | 0, 0, h => pqxdhKdf_ck_ne_createChain_snd ikm rk pk sk h.symm
  | 0, n₂ + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    exact createChain_snd_ne_kdfCk_fst _ _ _ _ h
  | n₁ + 1, 0, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    exact pqxdhKdf_ck_ne_kdfCk_fst _ _ h.symm
  | n₁ + 1, n₂ + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst, chainKeyAt_succ_eq_kdfCk_fst] at h
    exact chainKeyAt_createChain_snd_ne_chainKeyAt_pqxdhKdf_ck rk pk sk ikm n₁ n₂ (kdfCk_fst_inj h)

theorem trMsgKeys_cipherKey_inj {s₁ k₁ s₂ k₂ : Bytes}
    (h : (trMsgKeys s₁ k₁).cipherKey = (trMsgKeys s₂ k₂).cipherKey) : s₁ = s₂ ∧ k₁ = k₂ :=
  hmac_inj (hkdfBlock1_inj h).1

theorem trMsgKeys_macKey_inj {s₁ k₁ s₂ k₂ : Bytes}
    (h : (trMsgKeys s₁ k₁).macKey = (trMsgKeys s₂ k₂).macKey) : s₁ = s₂ ∧ k₁ = k₂ :=
  hmac_inj (hkdfBlock2_inj h).1

theorem trMsgKeys_iv_inj {s₁ k₁ s₂ k₂ : Bytes}
    (h : (trMsgKeys s₁ k₁).iv = (trMsgKeys s₂ k₂).iv) : s₁ = s₂ ∧ k₁ = k₂ :=
  hmac_inj (hkdfBlock3_inj h).1

theorem trMsgKeys_inj {s₁ k₁ s₂ k₂ : Bytes}
    (h : trMsgKeys s₁ k₁ = trMsgKeys s₂ k₂) : s₁ = s₂ ∧ k₁ = k₂ :=
  trMsgKeys_macKey_inj (congrArg MessageKeys.macKey h)

theorem computeMac_inj {mk₁ ikS₁ ikR₁ w₁ mk₂ ikS₂ ikR₂ w₂ : Bytes}
    (h : computeMac mk₁ ikS₁ ikR₁ w₁ = computeMac mk₂ ikS₂ ikR₂ w₂) :
    mk₁ = mk₂ ∧ ikS₁ = ikS₂ ∧ ikR₁ = ikR₂ ∧ w₁ = w₂ := by
  obtain ⟨hmk, hmsg⟩ := hmac_inj (Trunc.trunc8_inj _ _ h)
  obtain ⟨hikS, hrest⟩ := concat_inj hmsg
  obtain ⟨hikR, hw⟩ := concat_inj hrest
  exact ⟨hmk, hikS, hikR, hw⟩

/-! ## SPQR and wire-message constructors -/

theorem spqrInit_inj {k₁ p₁ k₂ p₂ : Bytes}
    (h : Spqr.spqrInit k₁ p₁ = Spqr.spqrInit k₂ p₂) : k₁ = k₂ ∧ p₁ = p₂ := by
  have hv := congrArg (fun b : Bytes => b.view? Spqr.InitState.SubF) h
  simp only [Spqr.spqrInit, BytesView.view_pack,
    Option.some.injEq, Spqr.InitState.SubF.mk.injEq] at hv
  exact hv

theorem spqrChainKey_inj {k₁ p₁ i₁ k₂ p₂ i₂ : Bytes}
    (h : Spqr.spqrChainKey k₁ p₁ i₁ = Spqr.spqrChainKey k₂ p₂ i₂) :
    k₁ = k₂ ∧ p₁ = p₂ ∧ i₁ = i₂ := by
  have hv := congrArg (fun b : Bytes => b.view? Spqr.ChainKey.SubF) h
  simp only [Spqr.spqrChainKey, BytesView.view_pack,
    Option.some.injEq, Spqr.ChainKey.SubF.mk.injEq] at hv
  exact hv

theorem spqrRecv_init_snd_cases {k msg : Bytes} {d : Spqr.Direction} {idx : UInt32}
    {st' salt : Bytes}
    (h : Spqr.spqrRecv (Spqr.spqrInit k (Spqr.encodeSpqrDirectionParams d)) msg idx = some (st', salt)) :
    (idx = 0 ∧ salt = Spqr.zeroKey) ∨
      (idx ≠ 0 ∧ salt = Spqr.spqrChainKey k (Spqr.encodeSpqrDirectionParams d.flip) (Spqr.encodeSpqrIndexTerm idx)) := by
  unfold Spqr.spqrRecv at h
  split at h
  · cases h
  · simp only [Spqr.spqrInit, BytesView.view_pack, Spqr.spqrParamsDir?_spqrParams,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hsalt⟩ := h
    by_cases hidx : idx = 0
    · simp only [hidx, ↓reduceIte] at hsalt
      exact Or.inl ⟨hidx, hsalt.symm⟩
    · simp only [hidx, ↓reduceIte] at hsalt
      exact Or.inr ⟨hidx, hsalt.symm⟩

theorem trWireMsg_inj {v₁ v₂ : UInt8} {rk₁ ct₁ pq₁ rk₂ ct₂ pq₂ : Bytes}
    {c₁ pc₁ c₂ pc₂ : UInt32} {ev₁ ev₂ : TrWire.EncodingVariation}
    (h : TrWire.trWireMsg v₁ rk₁ c₁ pc₁ ct₁ pq₁ ev₁ =
         TrWire.trWireMsg v₂ rk₂ c₂ pc₂ ct₂ pq₂ ev₂) :
    v₁ = v₂ ∧ rk₁ = rk₂ ∧ c₁ = c₂ ∧ pc₁ = pc₂ ∧ ct₁ = ct₂ ∧ pq₁ = pq₂ ∧ ev₁ = ev₂ := by
  have hv := congrArg TrWire.trWireMsgFields? h
  simp only [TrWire.trWireMsgFields?_trWireMsg, Option.some.injEq,
    TrWire.TrWireMsg.SubF.mk.injEq] at hv
  exact hv

/-! ## PQ-KEM constructors and decapsulation -/

theorem kemPk_inj {sk₁ sk₂ : Bytes} (h : kemPk sk₁ = kemPk sk₂) : sk₁ = sk₂ := by
  have hv := congrArg (fun b : Bytes => b.view? PQKem.Pk.SubF) h
  simp only [kemPk, CanPQKem.kemPk, BytesView.view_pack,
    Option.some.injEq, PQKem.Pk.SubF.mk.injEq] at hv
  exact hv

theorem kemRejKey_inj {sk₁ ct₁ sk₂ ct₂ : Bytes} :
    kemRejKey sk₁ ct₁ = kemRejKey sk₂ ct₂ ↔ sk₁ = sk₂ ∧ ct₁ = ct₂ := by
  constructor
  · intro h
    have hv := congrArg (fun b : Bytes => b.view? PQKem.RejKey.SubF) h
    simp only [kemRejKey, CanPQKem.kemRejKey, BytesView.view_pack,
      Option.some.injEq, PQKem.RejKey.SubF.mk.injEq] at hv
    exact hv
  · rintro ⟨rfl, rfl⟩; rfl

theorem kemEncap_fst_inj {pk₁ e₁ pk₂ e₂ : Bytes}
    (h : (kemEncap pk₁ e₁).1 = (kemEncap pk₂ e₂).1) : pk₁ = pk₂ ∧ e₁ = e₂ := by
  have hv := congrArg (fun b : Bytes => b.view? PQKem.Encap.SubF) h
  simp only [kemEncap, CanPQKem.kemEncap, BytesView.view_pack,
    Option.some.injEq, PQKem.Encap.SubF.mk.injEq] at hv
  exact hv

theorem kemEncap_snd_inj {pk₁ e₁ pk₂ e₂ : Bytes}
    (h : (kemEncap pk₁ e₁).2 = (kemEncap pk₂ e₂).2) : pk₁ = pk₂ ∧ e₁ = e₂ := by
  have hv := congrArg (fun b : Bytes => b.view? PQKem.SharedSecret.SubF) h
  simp only [kemEncap, CanPQKem.kemEncap, BytesView.view_pack,
    Option.some.injEq, PQKem.SharedSecret.SubF.mk.injEq] at hv
  exact hv

theorem kemEncap_inj {pk₁ e₁ pk₂ e₂ : Bytes}
    (h : kemEncap pk₁ e₁ = kemEncap pk₂ e₂) : pk₁ = pk₂ ∧ e₁ = e₂ :=
  kemEncap_fst_inj (congrArg Prod.fst h)

theorem kemDecap_kemEncap (sk e : Bytes) :
    kemDecap sk (kemEncap (kemPk sk) e).1 = some (kemEncap (kemPk sk) e).2 := by
  simp only [kemDecap, CanPQKem.kemDecap, kemEncap, CanPQKem.kemEncap, kemPk, CanPQKem.kemPk,
    BytesView.view_pack, ↓reduceIte]

theorem kemDecap_eq_some_iff {sk ct ss : Bytes} :
    kemDecap sk ct = some ss ↔
      ∃ e, ct = (kemEncap (kemPk sk) e).1 ∧ ss = (kemEncap (kemPk sk) e).2 := by
  constructor
  · intro h
    dsimp only [kemDecap, CanPQKem.kemDecap] at h
    have hct_pack := Bytes.pack_view? PQKem.Encap.SubF ct
    rcases hct : ct.view? PQKem.Encap.SubF with _ | ⟨pk, e⟩
    · rw [hct] at h; cases h
    · rw [hct] at h hct_pack
      dsimp only at h
      have hpk_pack := Bytes.pack_view? PQKem.Pk.SubF pk
      rcases hpk : pk.view? PQKem.Pk.SubF with _ | ⟨sk'⟩
      · rw [hpk] at h; cases h
      · rw [hpk] at h hpk_pack
        dsimp only at h
        split at h
        · rename_i hsk
          subst hsk
          injection h with hss
          exact ⟨e, by rw [← hct_pack, ← hpk_pack]; rfl, by rw [← hss, ← hpk_pack]; rfl⟩
        · cases h
  · rintro ⟨e, rfl, rfl⟩
    exact kemDecap_kemEncap sk e

theorem kemPkInvert_kemPk (sk : Bytes) : invertKemPublicKey (kemPk sk) = some sk := by
  simp only [invertKemPublicKey, kemPk, CanPQKem.kemPk, BytesView.view_pack]

theorem kemPkInvert_eq_some_iff {pk sk : Bytes} :
    invertKemPublicKey pk = some sk ↔ pk = kemPk sk := by
  constructor
  · intro h
    dsimp only [invertKemPublicKey] at h
    have hpack := Bytes.pack_view? PQKem.Pk.SubF pk
    rcases hpk : pk.view? PQKem.Pk.SubF with _ | ⟨sk'⟩
    · rw [hpk] at h; cases h
    · rw [hpk] at h hpack
      injection h with hsk
      subst hsk
      exact hpack.symm
  · rintro rfl
    exact kemPkInvert_kemPk sk

section ViewConcatKem
unseal Bytes

theorem view_concat_kemEncap_snd (pk e : Bytes) :
    (kemEncap pk e).2.view? Concat.Concat.SubF = none := by
  exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Concat.Concat.SubF ({ pk := pk, entropy := e } : PQKem.SharedSecret.SubF Bytes)

theorem view_concat_kemRejKey (sk ct : Bytes) :
    (kemRejKey sk ct).view? Concat.Concat.SubF = none := by
  exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Concat.Concat.SubF ({ sk := sk, cipher := ct } : PQKem.RejKey.SubF Bytes)

theorem kemRejKey_ne_sharedSecret_pack (sk ct : Bytes) (ss : PQKem.SharedSecret.SubF Bytes) :
    kemRejKey sk ct ≠ ss.pack := by
  intro h
  have hv := congrArg (fun b : Bytes => b.view? PQKem.RejKey.SubF) h
  have hnone : ss.pack.view? PQKem.RejKey.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none PQKem.RejKey.SubF ss
  simp only [kemRejKey, CanPQKem.kemRejKey, BytesView.view_pack, hnone] at hv
  cases hv

end ViewConcatKem

theorem kemRejKey_ne_kemEncap_snd (sk ct pk e : Bytes) :
    kemRejKey sk ct ≠ (kemEncap pk e).2 :=
  kemRejKey_ne_sharedSecret_pack sk ct { pk := pk, entropy := e }

theorem view_concat_bobKemShare (pqsk ct : Bytes) :
    ((errToOption (kemDecap pqsk ct)).getD (kemRejKey pqsk ct)).view? Concat.Concat.SubF = none := by
  rcases hdec : errToOption (kemDecap pqsk ct) with _ | ss
  · exact view_concat_kemRejKey pqsk ct
  · obtain ⟨e, _, rfl⟩ := kemDecap_eq_some_iff.mp hdec
    exact view_concat_kemEncap_snd (kemPk pqsk) e

theorem view_concat_of_kemDecap {sk ct ss : Bytes} (h : kemDecap sk ct = some ss) :
    ss.view? Concat.Concat.SubF = none := by
  obtain ⟨e, _, rfl⟩ := kemDecap_eq_some_iff.mp h
  exact view_concat_kemEncap_snd (kemPk sk) e

/-! ## PQXDH input key material -/

theorem pqxdhIkm_inj_parts {dh1 dh2 dh3 : Bytes} {dh4 : Option Bytes} {ss : Bytes}
    {dh1' dh2' dh3' : Bytes} {dh4' : Option Bytes} {ss' : Bytes}
    (h : pqxdhIkm dh1 dh2 dh3 dh4 ss = pqxdhIkm dh1' dh2' dh3' dh4' ss') :
    dh1 = dh1' ∧ dh2 = dh2' ∧ dh3 = dh3' ∧
      (match dh4 with | some d => Concat.concat d ss | none => ss) =
      (match dh4' with | some d' => Concat.concat d' ss' | none => ss') := by
  unfold pqxdhIkm at h
  obtain ⟨_, h1⟩ := concat_inj h
  obtain ⟨hdh1, h2⟩ := concat_inj h1
  obtain ⟨hdh2, h3⟩ := concat_inj h2
  obtain ⟨hdh3, htail⟩ := concat_inj h3
  refine ⟨hdh1, hdh2, hdh3, ?_⟩
  cases dh4 <;> cases dh4' <;> exact htail

/-- `pqxdhIkm` is injective when the KEM shares `ss` and `ss'` are not `Concat` terms,
disambiguating the optional `dh4` component. -/
theorem pqxdhIkm_inj {dh1 dh2 dh3 : Bytes} {dh4 : Option Bytes} {ss : Bytes}
    {dh1' dh2' dh3' : Bytes} {dh4' : Option Bytes} {ss' : Bytes}
    (hss : ss.view? Concat.Concat.SubF = none)
    (hss' : ss'.view? Concat.Concat.SubF = none)
    (h : pqxdhIkm dh1 dh2 dh3 dh4 ss = pqxdhIkm dh1' dh2' dh3' dh4' ss') :
    dh1 = dh1' ∧ dh2 = dh2' ∧ dh3 = dh3' ∧ dh4 = dh4' ∧ ss = ss' := by
  obtain ⟨rfl, rfl, rfl, htail⟩ := pqxdhIkm_inj_parts h
  refine ⟨rfl, rfl, rfl, ?_⟩
  cases dh4 with
  | none =>
    cases dh4' with
    | none => exact ⟨rfl, htail⟩
    | some d' =>
      dsimp only at htail
      have hv := congrArg (fun b : Bytes => b.view? Concat.Concat.SubF) htail
      simp only [Concat.concat, Concat.CanConcat.concat, BytesView.view_pack, hss] at hv
      cases hv
  | some d =>
    cases dh4' with
    | none =>
      dsimp only at htail
      have hv := congrArg (fun b : Bytes => b.view? Concat.Concat.SubF) htail
      simp only [Concat.concat, Concat.CanConcat.concat, BytesView.view_pack, hss'] at hv
      cases hv
    | some d' =>
      dsimp only at htail
      obtain ⟨rfl, rfl⟩ := concat_inj htail
      exact ⟨rfl, rfl⟩

theorem pqxdhIkm_inj_kem {dh1 dh2 dh3 : Bytes} {dh4 : Option Bytes} {pk e : Bytes}
    {dh1' dh2' dh3' : Bytes} {dh4' : Option Bytes} {pk' e' : Bytes}
    (h : pqxdhIkm dh1 dh2 dh3 dh4 (kemEncap pk e).2 =
         pqxdhIkm dh1' dh2' dh3' dh4' (kemEncap pk' e').2) :
    dh1 = dh1' ∧ dh2 = dh2' ∧ dh3 = dh3' ∧ dh4 = dh4' ∧ pk = pk' ∧ e = e' := by
  obtain ⟨rfl, rfl, rfl, rfl, hss⟩ :=
    pqxdhIkm_inj (view_concat_kemEncap_snd pk e) (view_concat_kemEncap_snd pk' e') h
  obtain ⟨rfl, rfl⟩ := kemEncap_snd_inj hss
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## X25519 agreement and signatures -/

theorem dhPk_inj {sk₁ sk₂ : Bytes} (h : dhPk sk₁ = dhPk sk₂) : sk₁ = sk₂ := by
  have hv := congrArg (fun x : Bytes => x.view? DiffieHellman.DhPk.SubF) h
  simp only [dhPk, CanDH.dhPk, BytesView.view_pack,
    Option.some.injEq, DiffieHellman.DhPk.SubF.mk.injEq] at hv
  exact hv

theorem dhSkOf_dhPk (sk : Bytes) : extractDhSecretKey (dhPk sk) = some sk := by
  simp only [extractDhSecretKey, dhPk, CanDH.dhPk, BytesView.view_pack]

theorem dhSkOf_eq_some_iff {pk sk : Bytes} : extractDhSecretKey pk = some sk ↔ pk = dhPk sk := by
  constructor
  · intro h
    dsimp only [extractDhSecretKey] at h
    have hpack := Bytes.pack_view? DiffieHellman.DhPk.SubF pk
    rcases hpk : pk.view? DiffieHellman.DhPk.SubF with _ | ⟨sk'⟩
    · rw [hpk] at h; cases h
    · rw [hpk] at h hpack
      injection h with hsk
      subst hsk
      exact hpack.symm
  · rintro rfl
    exact dhSkOf_dhPk sk

section ViewVariantDhPk
unseal Bytes

theorem view_variant_dhPk (sk : Bytes) :
    (dhPk sk).view? X25519.Variant.SubF = none := by
  exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none X25519.Variant.SubF ({ sk := sk } : DiffieHellman.DhPk.SubF Bytes)

end ViewVariantDhPk

@[simp] theorem x25519Key_dhPk (sk : Bytes) : X25519.normalizeX25519Key (dhPk sk) = dhPk sk := by
  unfold X25519.normalizeX25519Key
  rw [view_variant_dhPk]

theorem x25519Key_of_isCanonicalKey {pk : Bytes} (h : isCanonicalKey pk = true) :
    X25519.normalizeX25519Key pk = pk := by
  unfold isCanonicalKey at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  unfold X25519.normalizeX25519Key
  rw [h.1]

theorem x25519Key_idem_of_view_none {pk : Bytes}
    (h : (X25519.normalizeX25519Key pk).view? X25519.Variant.SubF = none) :
    X25519.normalizeX25519Key (X25519.normalizeX25519Key pk) = X25519.normalizeX25519Key pk := by
  unfold X25519.normalizeX25519Key at h
  unfold X25519.normalizeX25519Key
  rw [h]

theorem agree_x25519Key_of_view_none {pk : Bytes}
    (h : (X25519.normalizeX25519Key pk).view? X25519.Variant.SubF = none) (sk : Bytes) :
    agree (X25519.normalizeX25519Key pk) sk = agree pk sk := by
  simp only [agree, x25519Key_idem_of_view_none h]

theorem agree_eq_dh_of_sameDHKey_dhPk {pk a sk : Bytes} (h : SameDHKey pk (dhPk a)) :
    agree pk sk = dh (dhPk a) sk := by
  unfold SameDHKey at h
  rw [x25519Key_dhPk] at h
  simp only [agree, h]

theorem agree_of_sameDHKey {pk₁ pk₂ : Bytes} (h : SameDHKey pk₁ pk₂) (sk : Bytes) :
    agree pk₁ sk = agree pk₂ sk := by
  unfold SameDHKey at h
  simp only [agree, h]

theorem agree_comm (a b : Bytes) : agree (dhPk a) b = agree (dhPk b) a := by
  simp only [agree, x25519Key_dhPk, DiffieHellman.dh_commutes]

theorem agree_dhPk_comm {pk a b : Bytes} (h : SameDHKey pk (dhPk a)) :
    agree pk b = agree (dhPk b) a := by
  rw [agree_of_sameDHKey h b, agree_comm]

theorem SameDHKey.refl (pk : Bytes) : SameDHKey pk pk := rfl
theorem SameDHKey.symm {pk₁ pk₂ : Bytes} (h : SameDHKey pk₁ pk₂) : SameDHKey pk₂ pk₁ := h.symm
theorem SameDHKey.trans {pk₁ pk₂ pk₃ : Bytes}
    (h₁ : SameDHKey pk₁ pk₂) (h₂ : SameDHKey pk₂ pk₃) : SameDHKey pk₁ pk₃ := h₁.trans h₂

theorem SameOPK.refl (o : Option Bytes) : SameOPK o o := rfl
theorem SameOPK.symm {o₁ o₂ : Option Bytes} (h : SameOPK o₁ o₂) : SameOPK o₂ o₁ := h.symm
theorem SameOPK.trans {o₁ o₂ o₃ : Option Bytes}
    (h₁ : SameOPK o₁ o₂) (h₂ : SameOPK o₂ o₃) : SameOPK o₁ o₃ := h₁.trans h₂

@[simp] theorem sameOPK_none_left {o : Option Bytes} : SameOPK none o ↔ o = none := by
  cases o <;> simp [SameOPK]

@[simp] theorem sameOPK_none_right {o : Option Bytes} : SameOPK o none ↔ o = none := by
  cases o <;> simp [SameOPK]

@[simp] theorem sameOPK_some_some {a b : Bytes} :
    SameOPK (some a) (some b) ↔ SameDHKey a b := by
  simp [SameOPK, SameDHKey]

theorem dh_eq_dh_dhPk_cases {pk sk a b : Bytes}
    (h : dh pk sk = dh (dhPk a) b) : (pk = dhPk a ∧ sk = b) ∨ (pk = dhPk b ∧ sk = a) := by
  have hview := congrArg (fun x : Bytes => x.view? DiffieHellman.Dh.SubF) h
  dsimp only [dh, CanDH.dh, dhPk, CanDH.dhPk] at hview
  simp only [BytesView.view_pack] at hview
  have hpack := Bytes.pack_view? DiffieHellman.DhPk.SubF pk
  rcases hpk : pk.view? DiffieHellman.DhPk.SubF with _ | ⟨⟨sk2⟩⟩
  · rw [hpk] at hview hpack
    dsimp only at hview
    split at hview <;>
    · simp only [BytesView.view_pack, Option.some.injEq, DiffieHellman.Dh.SubF.mk.injEq] at hview
      rcases hview with ⟨rfl, rfl⟩
      first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩
  · rw [hpk] at hview hpack
    dsimp only at hview
    have hpk_eq : pk = dhPk sk2 := hpack.symm
    subst hpk_eq
    split at hview <;> split at hview <;>
    · simp only [BytesView.view_pack, Option.some.injEq, DiffieHellman.Dh.SubF.mk.injEq] at hview
      rcases hview with ⟨h1, h2⟩
      first
      | exact Or.inl ⟨h1, h2⟩
      | exact Or.inr ⟨h1, h2⟩
      | (obtain rfl := dhPk_inj h1; subst h2; exact Or.inl ⟨rfl, rfl⟩)
      | (obtain rfl := dhPk_inj h1; subst h2; exact Or.inr ⟨rfl, rfl⟩)

/-- `dh` equality with distinct secret exponents forces each public-key argument to be the `dhPk`
of the opposite exponent. -/
theorem dh_eq_of_sk_ne {pk₁ sk₁ pk₂ sk₂ : Bytes} (hne : sk₁ ≠ sk₂)
    (h : dh pk₁ sk₁ = dh pk₂ sk₂) : pk₁ = dhPk sk₂ ∧ pk₂ = dhPk sk₁ := by
  have hpack₂ := Bytes.pack_view? DiffieHellman.DhPk.SubF pk₂
  rcases hpk₂ : pk₂.view? DiffieHellman.DhPk.SubF with _ | ⟨⟨a⟩⟩
  · have hpack₁ := Bytes.pack_view? DiffieHellman.DhPk.SubF pk₁
    rcases hpk₁ : pk₁.view? DiffieHellman.DhPk.SubF with _ | ⟨⟨b⟩⟩
    · have hview := congrArg (fun x : Bytes => x.view? DiffieHellman.Dh.SubF) h
      dsimp only [dh, CanDH.dh] at hview
      rw [hpk₁, hpk₂] at hview
      simp only [BytesView.view_pack, Option.some.injEq, DiffieHellman.Dh.SubF.mk.injEq] at hview
      exact False.elim (hne hview.2)
    · rw [hpk₁] at hpack₁
      have hpk₁_eq : pk₁ = dhPk b := hpack₁.symm
      subst hpk₁_eq
      rcases dh_eq_dh_dhPk_cases h.symm with ⟨_, hsk⟩ | ⟨hpk₂_eq, _⟩
      · exact False.elim (hne hsk.symm)
      · rw [hpk₂_eq] at hpk₂
        simp only [dhPk, CanDH.dhPk, BytesView.view_pack] at hpk₂
        cases hpk₂
  · rw [hpk₂] at hpack₂
    have hpk₂_eq : pk₂ = dhPk a := hpack₂.symm
    subst hpk₂_eq
    rcases dh_eq_dh_dhPk_cases h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
    · exact False.elim (hne rfl)
    · exact ⟨rfl, rfl⟩

theorem agree_eq_agree_dhPk_cases {pk sk a b : Bytes}
    (h : agree pk sk = agree (dhPk a) b) :
    (SameDHKey pk (dhPk a) ∧ sk = b) ∨ (SameDHKey pk (dhPk b) ∧ sk = a) := by
  unfold agree at h
  rw [x25519Key_dhPk] at h
  rcases dh_eq_dh_dhPk_cases h with ⟨hpk, rfl⟩ | ⟨hpk, rfl⟩
  · exact Or.inl ⟨hpk.trans (x25519Key_dhPk a).symm, rfl⟩
  · exact Or.inr ⟨hpk.trans (x25519Key_dhPk b).symm, rfl⟩

/-- X25519 `agree` equality with distinct secret exponents forces `SameDHKey` against the
opposite `dhPk` keys. -/
theorem agree_eq_of_sk_ne {pk₁ sk₁ pk₂ sk₂ : Bytes} (hne : sk₁ ≠ sk₂)
    (h : agree pk₁ sk₁ = agree pk₂ sk₂) :
    SameDHKey pk₁ (dhPk sk₂) ∧ SameDHKey pk₂ (dhPk sk₁) := by
  unfold agree at h
  obtain ⟨h1, h2⟩ := dh_eq_of_sk_ne hne h
  unfold SameDHKey
  rw [x25519Key_dhPk, x25519Key_dhPk]
  exact ⟨h1, h2⟩

theorem sameDHKey_of_agree_eq {ek spk spkPk' : Bytes}
    (h : agree (dhPk ek) spk = agree spkPk' ek) :
    SameDHKey (dhPk spk) spkPk' := by
  rw [agree_comm ek spk] at h
  rcases agree_eq_agree_dhPk_cases h.symm with ⟨h1, _⟩ | ⟨h1, rfl⟩
  · exact h1.symm
  · exact h1.symm

theorem sameDHKey_of_agree_right_eq {ek ek' spk : Bytes}
    (h : agree ek spk = agree (dhPk ek') spk) :
    SameDHKey ek (dhPk ek') := by
  rcases agree_eq_agree_dhPk_cases h with ⟨h1, _⟩ | ⟨h1, rfl⟩
  · exact h1
  · exact h1

theorem sameOPK_of_map_agree_eq {ek : Bytes} {opk opkPk' : Option Bytes}
    (h : opk.map (agree (dhPk ek) ·) = opkPk'.map (agree · ek)) :
    SameOPK (opk.map dhPk) opkPk' := by
  cases opk with
  | none =>
    cases opkPk' with
    | none => rfl
    | some o' => cases h
  | some o =>
    cases opkPk' with
    | none => cases h
    | some o' =>
      dsimp only [Option.map] at h
      injection h with hagree
      exact sameOPK_some_some.mpr (sameDHKey_of_agree_eq hagree)

theorem sameDHKey_of_agree_eq_uncond {ek spk spkPk' : Bytes}
    (h : agree (dhPk ek) spk = agree spkPk' ek) :
    SameDHKey (dhPk spk) spkPk' :=
  sameDHKey_of_agree_eq h

theorem sameOPK_of_map_agree_eq_uncond {ek : Bytes} {opk opkPk' : Option Bytes}
    (h : opk.map (agree (dhPk ek) ·) = opkPk'.map (agree · ek)) :
    SameOPK (opk.map dhPk) opkPk' :=
  sameOPK_of_map_agree_eq h

theorem consumeMessageKey_seed_eq {rk pk : Bytes} {rcIdx : Nat} {counter : UInt32}
    {seed : Bytes} {c' : RecvChain}
    (h : consumeMessageKey { ratchetKey := rk, chainKey := pk, index := 0, rIdx := rcIdx } counter =
      some (seed, c')) :
    seed = (kdfCk (chainKeyAt pk counter.toNat)).2 := by
  unfold consumeMessageKey at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · injection h with hpair
        have h1 := congrArg Prod.fst hpair
        dsimp only at h1
        have hsub : counter.toNat - (0 : UInt32).toNat = counter.toNat := Nat.sub_zero counter.toNat
        rw [hsub] at h1
        exact h1.symm

theorem vk_inj {sk₁ sk₂ : Bytes} (h : Signature.vk sk₁ = Signature.vk sk₂) : sk₁ = sk₂ := by
  have hv := congrArg (fun b : Bytes => b.view? Signature.Vk.SubF) h
  simp only [Signature.vk, Signature.CanSign.vk, BytesView.view_pack,
    Option.some.injEq, Signature.Vk.SubF.mk.injEq] at hv
  exact hv

theorem sign_inj {sk₁ n₁ m₁ sk₂ n₂ m₂ : Bytes}
    (h : Signature.sign sk₁ n₁ m₁ = Signature.sign sk₂ n₂ m₂) :
    sk₁ = sk₂ ∧ n₁ = n₂ ∧ m₁ = m₂ := by
  have hv := congrArg (fun b : Bytes => b.view? Signature.Sign.SubF) h
  simp only [Signature.sign, Signature.CanSign.sign, BytesView.view_pack,
    Option.some.injEq, Signature.Sign.SubF.mk.injEq] at hv
  exact hv

theorem verify_eq_true_iff {vkPk msg sig : Bytes} :
    Signature.verify vkPk msg sig = true ↔
      ∃ sk nonce, vkPk = Signature.vk sk ∧ sig = Signature.sign sk nonce msg := by
  constructor
  · intro h
    dsimp only [Signature.verify, Signature.CanSign.verify] at h
    have hpack := Bytes.pack_view? Signature.Sign.SubF sig
    rcases hsig : sig.view? Signature.Sign.SubF with _ | ⟨sk, nonce, msg'⟩
    · rw [hsig] at h; cases h
    · rw [hsig] at h hpack
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨sk, nonce, rfl, hpack.symm⟩
  · rintro ⟨sk, nonce, rfl, rfl⟩
    exact Signature.verify_sign sk nonce msg

/-! ## PQXDH agreement bridges -/

theorem bobAgreement_eq_some (ikB spk pqsk : Bytes) (opk : Option Bytes) (ikAPk ekPk ct : Bytes) :
    bobAgreement ikB spk pqsk opk ikAPk ekPk ct =
      some (pqxdhKdf (pqxdhIkm (agree ikAPk spk) (agree ekPk ikB) (agree ekPk spk)
        (opk.map (agree ekPk ·))
        ((errToOption (kemDecap pqsk ct)).getD (kemRejKey pqsk ct)))) := rfl

theorem bobAgreement_eq_some_iff {ikB spk pqsk : Bytes} {opk : Option Bytes}
    {ikAPk ekPk ct : Bytes} {keys : HandshakeKeys} :
    bobAgreement ikB spk pqsk opk ikAPk ekPk ct = some keys ↔
      keys = pqxdhKdf (pqxdhIkm (agree ikAPk spk) (agree ekPk ikB) (agree ekPk spk)
        (opk.map (agree ekPk ·))
        ((errToOption (kemDecap pqsk ct)).getD (kemRejKey pqsk ct))) := by
  rw [bobAgreement_eq_some, Option.some.injEq, eq_comm]

/-- Matching `rk` outputs between `bobAgreement` and `aliceAgreement` rule out implicit KEM
rejection and equate all four DH shares, the KEM public key, ciphertext, and full `HandshakeKeys`. -/
theorem bobAgreement_rk_eq_aliceAgreement_rk {ikB spk pqsk : Bytes} {opk : Option Bytes}
    {ikAPk ekPk ct : Bytes} {keys : HandshakeKeys}
    {ikA' ek' ikBPk' spkPk' pqPk' : Bytes} {opkPk' : Option Bytes} {e' : Bytes}
    (hbob : bobAgreement ikB spk pqsk opk ikAPk ekPk ct = some keys)
    (hrk : keys.rk = (aliceAgreement ikA' ek' ikBPk' spkPk' pqPk' opkPk' e').2.rk) :
    agree ikAPk spk = agree spkPk' ikA' ∧
    agree ekPk ikB = agree ikBPk' ek' ∧
    agree ekPk spk = agree spkPk' ek' ∧
    opk.map (agree ekPk ·) = opkPk'.map (agree · ek') ∧
    pqPk' = kemPk pqsk ∧
    ct = (aliceAgreement ikA' ek' ikBPk' spkPk' pqPk' opkPk' e').1 ∧
    keys = (aliceAgreement ikA' ek' ikBPk' spkPk' pqPk' opkPk' e').2 := by
  rw [bobAgreement_eq_some_iff] at hbob
  subst hbob
  have hikm := pqxdhKdf_rk_inj hrk
  obtain ⟨h1, h2, h3, h4, hss⟩ :=
    pqxdhIkm_inj (view_concat_bobKemShare pqsk ct) (view_concat_kemEncap_snd pqPk' e') hikm
  rcases hdec : errToOption (kemDecap pqsk ct) with _ | ss
  · rw [hdec] at hss; exact (kemRejKey_ne_kemEncap_snd pqsk ct pqPk' e' hss).elim
  · rw [hdec] at hss; dsimp only [Option.getD] at hss
    obtain ⟨e, rfl, rfl⟩ := kemDecap_eq_some_iff.mp hdec
    obtain ⟨hpq, he⟩ := kemEncap_snd_inj hss
    subst hpq; subst he
    exact ⟨h1, h2, h3, h4, rfl, rfl,
      by dsimp only [Option.getD, aliceAgreement]; rw [h1, h2, h3, h4]⟩

/-- Analogous `bobAgreement`/`aliceAgreement` inversion from matching `pqr` outputs. -/
theorem bobAgreement_pqr_eq_aliceAgreement_pqr {ikB spk pqsk : Bytes} {opk : Option Bytes}
    {ikAPk ekPk ct : Bytes} {keys : HandshakeKeys}
    {ikA' ek' ikBPk' spkPk' pqPk' : Bytes} {opkPk' : Option Bytes} {e' : Bytes}
    (hbob : bobAgreement ikB spk pqsk opk ikAPk ekPk ct = some keys)
    (hpqr : keys.pqr = (aliceAgreement ikA' ek' ikBPk' spkPk' pqPk' opkPk' e').2.pqr) :
    agree ikAPk spk = agree spkPk' ikA' ∧
    agree ekPk ikB = agree ikBPk' ek' ∧
    agree ekPk spk = agree spkPk' ek' ∧
    opk.map (agree ekPk ·) = opkPk'.map (agree · ek') ∧
    pqPk' = kemPk pqsk ∧
    ct = (aliceAgreement ikA' ek' ikBPk' spkPk' pqPk' opkPk' e').1 ∧
    keys = (aliceAgreement ikA' ek' ikBPk' spkPk' pqPk' opkPk' e').2 := by
  rw [bobAgreement_eq_some_iff] at hbob
  subst hbob
  have hikm := pqxdhKdf_pqr_inj hpqr
  obtain ⟨h1, h2, h3, h4, hss⟩ :=
    pqxdhIkm_inj (view_concat_bobKemShare pqsk ct) (view_concat_kemEncap_snd pqPk' e') hikm
  rcases hdec : errToOption (kemDecap pqsk ct) with _ | ss
  · rw [hdec] at hss; exact (kemRejKey_ne_kemEncap_snd pqsk ct pqPk' e' hss).elim
  · rw [hdec] at hss; dsimp only [Option.getD] at hss
    obtain ⟨e, rfl, rfl⟩ := kemDecap_eq_some_iff.mp hdec
    obtain ⟨hpq, he⟩ := kemEncap_snd_inj hss
    subst hpq; subst he
    exact ⟨h1, h2, h3, h4, rfl, rfl,
      by dsimp only [Option.getD, aliceAgreement]; rw [h1, h2, h3, h4]⟩

end Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.TermAlgebra
