/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
import DY.Bytes.Basic
import Init.Data.String
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic

/-!
# Composed Post-Compromise Security Genealogy and Dual-Closure Engine

Proves post-compromise security (`PCSQuery`) for `DY.Libsignal.Composed` from step-1 anchored
key-schedule invariants, KDF domain separation along `RootDescends`, and dual structured and
witness-based attacker-knowledge closures.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompPcsEngine

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.X25519
open DY.Libsignal.TripleRatchet (SessionInfo TREvent hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 lit
  litByte kdfRk createChain kdfCk chainKeyAt DerivesMsgKey RootDescends DerivesChain zeroSalt
  trMsgKeys)
open DY.Libsignal.TripleRatchet.Cheval (StateStoredAt TRKeyKnown HandshakeRootCompromised
  CompromisedKey HonestDHKey MessageSeedUsed PCSQuery)
open DY.Libsignal.PQXDH (PQXDHEvent pqxdhKdf pqxdhLabel HandshakeKeysAt HandshakeWasCompromisedAt)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security

/-! ## Term Algebra, KDF Domain Separation, and `RootDescends` Inversion -/

abbrev mkRand (ts sz : Nat) : Bytes :=
  ({ timestamp := ts, size := sz } : Random.Random Bytes).pack

private theorem mkRand_inj {t₁ s₁ t₂ s₂ : Nat} (h : mkRand t₁ s₁ = mkRand t₂ s₂) :
    t₁ = t₂ ∧ s₁ = s₂ := by
  have hv := congrArg (fun b : Bytes => b.view? Random.Random) h
  dsimp only [mkRand] at hv; rw [BytesView.view_pack, BytesView.view_pack] at hv
  injection hv with hv'; cases hv'; exact ⟨rfl, rfl⟩

private theorem concat_inj {a₁ b₁ a₂ b₂ : Bytes}
    (h : Concat.concat a₁ b₁ = Concat.concat a₂ b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have hv := congrArg (fun x : Bytes => x.view? Concat.Concat.SubF) h
  dsimp only [Concat.concat, Concat.CanConcat.concat] at hv
  rw [BytesView.view_pack, BytesView.view_pack] at hv
  injection hv with hv'; cases hv'; exact ⟨rfl, rfl⟩

private theorem litByte_inj {b₁ b₂ : UInt8} (h : litByte b₁ = litByte b₂) : b₁ = b₂ := by
  have hm := congrArg (fun a : ByteArray => a.data.toList) (Option.some.inj
    (by simpa only [litByte, bytesToLiteral_literalToBytes] using congrArg bytesToLiteral h))
  exact (List.cons.inj hm).1

private theorem kdfExtract_inj {s₁ m₁ s₂ m₂ : Bytes}
    (h : kdfExtract s₁ m₁ = kdfExtract s₂ m₂) : s₁ = s₂ ∧ m₁ = m₂ := by
  have hv := congrArg (fun b : Bytes => b.view? KdfExtract.KdfExtract.SubF) h
  dsimp only [KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hv
  rw [BytesView.view_pack, BytesView.view_pack] at hv
  injection hv with hv'; cases hv'; exact ⟨rfl, rfl⟩

private theorem hmac_inj {k₁ m₁ k₂ m₂ : Bytes} (h : hmac k₁ m₁ = hmac k₂ m₂) :
    k₁ = k₂ ∧ m₁ = m₂ := kdfExtract_inj h

private theorem hkdfBlock1_inj {p₁ i₁ p₂ i₂ : Bytes}
    (h : hkdfBlock1 p₁ i₁ = hkdfBlock1 p₂ i₂) : p₁ = p₂ ∧ i₁ = i₂ :=
  let ⟨hp, hi⟩ := hmac_inj h; ⟨hp, (concat_inj hi).1⟩

private theorem hkdfBlock2_inj {p₁ i₁ p₂ i₂ : Bytes}
    (h : hkdfBlock2 p₁ i₁ = hkdfBlock2 p₂ i₂) : p₁ = p₂ ∧ i₁ = i₂ :=
  let ⟨hp, hi⟩ := hmac_inj h; ⟨hp, (concat_inj (concat_inj hi).2).1⟩

private theorem hkdfBlock1_ne_hkdfBlock2 (p₁ i₁ p₂ i₂ : Bytes) :
    hkdfBlock1 p₁ i₁ ≠ hkdfBlock2 p₂ i₂ := fun h => by
  have hr := (concat_inj (hmac_inj h).2).2
  dsimp only [litByte, literalToBytes, Concat.concat, Concat.CanConcat.concat] at hr
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hr

private theorem hkdfBlock1_ne_hkdfBlock3 (p₁ i₁ p₂ i₂ : Bytes) :
    hkdfBlock1 p₁ i₁ ≠ hkdfBlock3 p₂ i₂ := fun h => by
  have hr := (concat_inj (hmac_inj h).2).2
  dsimp only [litByte, literalToBytes, Concat.concat, Concat.CanConcat.concat] at hr
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hr

private theorem hkdfBlock2_ne_hkdfBlock3 (p₁ i₁ p₂ i₂ : Bytes) :
    hkdfBlock2 p₁ i₁ ≠ hkdfBlock3 p₂ i₂ := fun h => by
  have hb := litByte_inj (concat_inj (concat_inj (hmac_inj h).2).2).2
  revert hb; decide

private theorem litByte_ne_concat (x : UInt8) (a b : Bytes) :
    litByte x ≠ Concat.concat a b := fun h => by
  dsimp only [litByte, literalToBytes, Concat.concat, Concat.CanConcat.concat] at h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

private theorem hkdfBlock1_ne_kdfCk_fst (p i ck : Bytes) :
    hkdfBlock1 p i ≠ (kdfCk ck).1 := fun h => litByte_ne_concat 0x02 _ _ (hmac_inj h).2.symm

private theorem hkdfBlock1_ne_kdfCk_snd (p i ck : Bytes) :
    hkdfBlock1 p i ≠ (kdfCk ck).2 := fun h => litByte_ne_concat 0x01 _ _ (hmac_inj h).2.symm

private theorem hkdfBlock2_ne_kdfCk_snd (p i ck : Bytes) :
    hkdfBlock2 p i ≠ (kdfCk ck).2 := fun h => litByte_ne_concat 0x01 _ _ (hmac_inj h).2.symm

private theorem kdfCk_fst_ne_snd (c₁ c₂ : Bytes) : (kdfCk c₁).1 ≠ (kdfCk c₂).2 := fun h => by
  have hb := litByte_inj (hmac_inj h).2; revert hb; decide

private theorem kdfCk_fst_inj {c₁ c₂ : Bytes} (h : (kdfCk c₁).1 = (kdfCk c₂).1) : c₁ = c₂ :=
  (hmac_inj h).1

private theorem kdfCk_snd_inj {c₁ c₂ : Bytes} (h : (kdfCk c₁).2 = (kdfCk c₂).2) : c₁ = c₂ :=
  (hmac_inj h).1

private theorem kdfRk_fst_inj {r₁ d₁ r₂ d₂ : Bytes}
    (h : (kdfRk r₁ d₁).1 = (kdfRk r₂ d₂).1) : r₁ = r₂ ∧ d₁ = d₂ := hmac_inj (hkdfBlock1_inj h).1

private theorem kdfRk_snd_inj {r₁ d₁ r₂ d₂ : Bytes}
    (h : (kdfRk r₁ d₁).2 = (kdfRk r₂ d₂).2) : r₁ = r₂ ∧ d₁ = d₂ := hmac_inj (hkdfBlock2_inj h).1

private theorem createChain_fst_inj {r₁ p₁ s₁ r₂ p₂ s₂ : Bytes}
    (h : (createChain r₁ p₁ s₁).1 = (createChain r₂ p₂ s₂).1) :
    r₁ = r₂ ∧ DiffieHellman.dh (X25519.normalizeX25519Key p₁) s₁ =
      DiffieHellman.dh (X25519.normalizeX25519Key p₂) s₂ := kdfRk_fst_inj h

private theorem createChain_snd_inj {r₁ p₁ s₁ r₂ p₂ s₂ : Bytes}
    (h : (createChain r₁ p₁ s₁).2 = (createChain r₂ p₂ s₂).2) :
    r₁ = r₂ ∧ DiffieHellman.dh (X25519.normalizeX25519Key p₁) s₁ =
      DiffieHellman.dh (X25519.normalizeX25519Key p₂) s₂ := kdfRk_snd_inj h

private theorem mkRand_ne_kdfExtract (ts sz : Nat) (s m : Bytes) :
    mkRand ts sz ≠ kdfExtract s m := fun h => by
  dsimp only [mkRand, KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

private theorem dh_ne_concat (p s a b : Bytes) : DiffieHellman.dh p s ≠ Concat.concat a b := by
  intro h
  have hv := congrArg (fun x : Bytes => x.view? Concat.Concat.SubF) h
  dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh, Concat.concat, Concat.CanConcat.concat] at hv
  split at hv
  · split at hv <;> (rw [BytesView.view_pack, Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Concat.Concat.SubF] at hv; cases hv)
  · rw [BytesView.view_pack, Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Concat.Concat.SubF] at hv; cases hv

private theorem dh_ne_litByte (p s : Bytes) (x : UInt8) : DiffieHellman.dh p s ≠ litByte x := by
  intro h
  have hv := congrArg (fun y : Bytes => y.view? Literal.Literal.SubF) h
  dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh, litByte, Literal.literalToBytes] at hv
  split at hv
  · split at hv <;> (rw [BytesView.view_pack, Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Literal.Literal.SubF] at hv; cases hv)
  · rw [BytesView.view_pack, Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Literal.Literal.SubF] at hv; cases hv

private theorem whisperRatchet_ne_whisperMessageKeys :
    lit "WhisperRatchet" ≠ lit "WhisperMessageKeys" := by
  intro h
  have hm := congrArg bytesToLiteral h
  simp only [lit, bytesToLiteral_literalToBytes, Option.some.injEq,
    String.toUTF8_eq_toByteArray, String.toByteArray_inj] at hm
  have hl := congrArg String.toList hm; revert hl; decide

private theorem whisperRatchet_ne_pqxdhLabel : lit "WhisperRatchet" ≠ pqxdhLabel := by
  intro h
  have hm := congrArg bytesToLiteral h
  dsimp only [pqxdhLabel] at hm
  simp only [lit, bytesToLiteral_literalToBytes, Option.some.injEq,
    String.toUTF8_eq_toByteArray, String.toByteArray_inj] at hm
  have hl := congrArg String.toList hm; revert hl; decide

@[simp] theorem x25519Key_dhPk (sk : Bytes) :
    X25519.normalizeX25519Key (DiffieHellman.dhPk sk) = DiffieHellman.dhPk sk := by
  dsimp only [X25519.normalizeX25519Key, DiffieHellman.dhPk, DiffieHellman.instCanDHBytes]
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none X25519.Variant.SubF]

theorem pqxdhKdf_rk_ne_createChain_fst (ikm rk pk sk : Bytes) :
    (pqxdhKdf ikm).rk ≠ (createChain rk pk sk).1 :=
  fun h => whisperRatchet_ne_pqxdhLabel (hkdfBlock1_inj h).2.symm

theorem chainKeyAt_succ_eq_kdfCk_fst (ck : Bytes) :
    ∀ n : Nat, chainKeyAt ck (n + 1) = (kdfCk (chainKeyAt ck n)).1
  | 0 => rfl
  | n + 1 => chainKeyAt_succ_eq_kdfCk_fst (kdfCk ck).1 n

theorem chainKeyAt_add (ck : Bytes) :
    ∀ a b : Nat, chainKeyAt ck (a + b) = chainKeyAt (chainKeyAt ck a) b
  | 0, b => by simp [chainKeyAt]
  | a + 1, b => by rw [Nat.succ_add]; exact chainKeyAt_add (kdfCk ck).1 a b

theorem derivesMsgKey_of_chainKeyAt_le {ck₀ mk : Bytes} {j n : Nat}
    (hj : j ≤ n) (hmk : mk = (kdfCk (chainKeyAt ck₀ n)).2) :
    DerivesMsgKey (chainKeyAt ck₀ j) mk :=
  ⟨n - j, by rw [hmk, ← chainKeyAt_add, Nat.add_sub_of_le hj]⟩

/-- A chain root `ck₀` is never equal to `(kdfCk x).1`. -/
def IsChainRoot (ck₀ : Bytes) : Prop := ∀ x : Bytes, ck₀ ≠ (kdfCk x).1

private theorem isChainRoot_hkdfBlock2 (prk info : Bytes) :
    IsChainRoot (hkdfBlock2 prk info) :=
  fun _ h => litByte_ne_concat 0x02 _ _ (hmac_inj h).2.symm

theorem chainKeyAt_root_inj {ck₁ ck₂ : Bytes} (h₁ : IsChainRoot ck₁) (h₂ : IsChainRoot ck₂) :
    ∀ {n₁ n₂ : Nat}, chainKeyAt ck₁ n₁ = chainKeyAt ck₂ n₂ → ck₁ = ck₂ ∧ n₁ = n₂
  | 0, 0, h => ⟨h, rfl⟩
  | 0, n₂ + 1, h => by rw [chainKeyAt_succ_eq_kdfCk_fst] at h; exact False.elim (h₁ _ h)
  | n₁ + 1, 0, h => by rw [chainKeyAt_succ_eq_kdfCk_fst] at h; exact False.elim (h₂ _ h.symm)
  | n₁ + 1, n₂ + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst, chainKeyAt_succ_eq_kdfCk_fst] at h
    obtain ⟨rfl, rfl⟩ := chainKeyAt_root_inj h₁ h₂ (kdfCk_fst_inj h)
    exact ⟨rfl, rfl⟩

theorem rootDescends_of_pqxdhKdf_rk_createChain_fst {ikm rk_prev pk sk : Bytes}
    (h : RootDescends (pqxdhKdf ikm).rk (createChain rk_prev pk sk).1) :
    RootDescends (pqxdhKdf ikm).rk rk_prev := by
  generalize htarget : (createChain rk_prev pk sk).1 = target at h
  cases h with
  | refl => exact False.elim (pqxdhKdf_rk_ne_createChain_fst ikm rk_prev pk sk htarget.symm)
  | step hprev => obtain ⟨rfl, _⟩ := createChain_fst_inj htarget; exact hprev

/-- If `r₂` descends from both `r₁` and `(pqxdhKdf ikm).rk`, then `r₁` descends from
`(pqxdhKdf ikm).rk`. -/
theorem rootDescends_pqxdhKdf_rk_of_right {ikm r₁ r₂ : Bytes}
    (h₁ : RootDescends r₁ r₂) (h₂ : RootDescends (pqxdhKdf ikm).rk r₂) :
    RootDescends (pqxdhKdf ikm).rk r₁ := by
  induction h₁ with
  | refl => exact h₂
  | step _ ih => exact ih (rootDescends_of_pqxdhKdf_rk_createChain_fst h₂)

theorem rootDescends_exists_hkdfBlock1_of_pqxdhKdf_rk {ikm rk : Bytes}
    (h : RootDescends (pqxdhKdf ikm).rk rk) : ∃ p i, rk = hkdfBlock1 p i := by
  cases h <;> exact ⟨_, _, rfl⟩

theorem rootDescends_exists_createChain_fst {r p s rk : Bytes}
    (h : RootDescends (createChain r p s).1 rk) : ∃ r' p' s', rk = (createChain r' p' s').1 := by
  cases h <;> exact ⟨_, _, _, rfl⟩

/-! ## Step-1 Anchored Schedule and PCS Genealogy Bridges -/

/-- Step-1 anchored root-key derivation `CompRkSteps dh₁ d rk₀ rk`. -/
inductive CompRkSteps (dh₁ : Bytes) : Nat → Bytes → Bytes → Prop
  | zero (rk₀ : Bytes) : CompRkSteps dh₁ 0 rk₀ rk₀
  | step_one (rk₀ : Bytes) : CompRkSteps dh₁ 1 rk₀ (kdfRk rk₀ dh₁).1
  | step_succ {k : Nat} {rk₀ rk₁ pk sk : Bytes} :
      CompRkSteps dh₁ (k + 1) rk₀ rk₁ → CompRkSteps dh₁ (k + 2) rk₀ (createChain rk₁ pk sk).1

theorem CompRkSteps.to_rootDescends {dh₁ rk₀ rk : Bytes} {d : Nat}
    (hd : ∃ p sk, dh₁ = DiffieHellman.dh (X25519.normalizeX25519Key p) sk)
    (hrk : CompRkSteps dh₁ d rk₀ rk) : RootDescends rk₀ rk := by
  induction hrk with
  | zero => exact .refl
  | step_one _ => obtain ⟨p, sk, rfl⟩ := hd; exact .step (theirPk := p) (ourSk := sk) .refl
  | @step_succ _ _ _ pk' sk' _ ih => exact .step (theirPk := pk') (ourSk := sk') ih

/-- Step-1 anchored chain-root derivation `CompChainRootFrom1 dh₁ ikm m ck₀`. -/
def CompChainRootFrom1 (dh₁ ikm : Bytes) (m : Nat) (ck₀ : Bytes) : Prop :=
  match m with
  | 0 => ck₀ = (pqxdhKdf ikm).ck
  | 1 => ck₀ = (kdfRk (pqxdhKdf ikm).rk dh₁).2
  | k + 2 =>
    ∃ rk pk sk, CompRkSteps dh₁ (k + 1) (pqxdhKdf ikm).rk rk ∧ ck₀ = (createChain rk pk sk).2

theorem CompChainRootFrom1.isChainRoot {dh₁ ikm : Bytes} {m : Nat} {ck₀ : Bytes}
    (h : CompChainRootFrom1 dh₁ ikm m ck₀) : IsChainRoot ck₀ := by
  rcases m with _ | _ | k
  · subst h; exact isChainRoot_hkdfBlock2 _ _
  · subst h; exact isChainRoot_hkdfBlock2 _ _
  · obtain ⟨_, _, _, _, rfl⟩ := h; exact isChainRoot_hkdfBlock2 _ _

private theorem CompChainRootFrom1.exists_hkdfBlock2 {dh₁ ikm ck₀ : Bytes} {m : Nat}
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀) : ∃ p i, ck₀ = hkdfBlock2 p i := by
  rcases m with _ | _ | k
  · rw [hroot]; exact ⟨_, _, rfl⟩
  · rw [hroot]; exact ⟨_, _, rfl⟩
  · obtain ⟨_, _, _, _, rfl⟩ := hroot; exact ⟨_, _, rfl⟩

/-- If a composed schedule chain root `ck₀` equals `(createChain rk_prev pk sk).2`, then
`rk_prev` descends from `(pqxdhKdf ikm).rk`. -/
theorem CompChainRootFrom1.rootDescends_of_eq_createChain_snd {dh₁ ikm ck₀ rk_prev pk sk : Bytes}
    {m : Nat} (hd : ∃ p₀ sk₀, dh₁ = DiffieHellman.dh (X25519.normalizeX25519Key p₀) sk₀)
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀)
    (heq : ck₀ = (createChain rk_prev pk sk).2) :
    RootDescends (pqxdhKdf ikm).rk rk_prev := by
  rcases m with _ | _ | k
  · dsimp [CompChainRootFrom1] at hroot
    exact False.elim (whisperRatchet_ne_pqxdhLabel (hkdfBlock2_inj (heq.symm.trans hroot)).2)
  · dsimp [CompChainRootFrom1] at hroot
    obtain ⟨hrk, _⟩ := kdfRk_snd_inj (hroot.symm.trans heq)
    exact hrk ▸ .refl
  · obtain ⟨rk₁, _, _, hrk₁, hck₁⟩ := hroot
    obtain ⟨hrk, _⟩ := createChain_snd_inj (hck₁.symm.trans heq)
    exact hrk ▸ hrk₁.to_rootDescends hd

/-- If `(createChain rk_prev pk sk).1` derives a composed schedule chain root `ck₀`, then both
`(createChain rk_prev pk sk).1` and `rk_prev` descend from `(pqxdhKdf ikm).rk`. -/
theorem CompChainRootFrom1.rootDescends_of_derivesChain_heal {dh₁ ikm ck₀ rk_prev pk sk : Bytes}
    {m : Nat} (hd : ∃ p₀ sk₀, dh₁ = DiffieHellman.dh (X25519.normalizeX25519Key p₀) sk₀)
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀)
    (hdc : DerivesChain (createChain rk_prev pk sk).1 ck₀) :
    RootDescends (pqxdhKdf ikm).rk (createChain rk_prev pk sk).1 ∧
    RootDescends (pqxdhKdf ikm).rk rk_prev := by
  obtain ⟨rk_end, pk_end, sk_end, hdesc_heal, hck_end⟩ := hdc
  have hrk_end : RootDescends (pqxdhKdf ikm).rk rk_end :=
    hroot.rootDescends_of_eq_createChain_snd hd hck_end
  have hrk_heal : RootDescends (pqxdhKdf ikm).rk (createChain rk_prev pk sk).1 :=
    rootDescends_pqxdhKdf_rk_of_right hdesc_heal hrk_end
  exact ⟨hrk_heal, rootDescends_of_pqxdhKdf_rk_createChain_fst hrk_heal⟩

/-! ## Witness Closure and Heal-Share Compromise -/

/-- Syntactic shape of keys exposed by Triple Ratchet `exposeKey` / `exposeSkipped` transitions. -/
def IsScheduleKey (k : Bytes) : Prop :=
  (∃ r p sk, k = (createChain r p sk).1) ∨
  (∃ r p sk, k = (createChain r p sk).2) ∨
  (∃ ikm, k = (pqxdhKdf ikm).ck) ∨
  (∃ c, k = (kdfCk c).1) ∨
  (∃ c, k = (kdfCk c).2)

/-- Honest ephemeral DH secret predicate matching `HonestDHKey tr`. -/
def IsHonestDH (tr : ExecTrace) (d : Bytes) : Prop :=
  (∃ s i, tr.EventLogged (TREvent.HonestDH s d i)) ∨
  (∃ me st idx, StateStoredAt me st idx tr ∧ st.dhs = d)

/-- Witness exposure set (`CompPcsWitnessExposureFor MsgEncWitness tr`): excludes unexposed honest
ratchet secrets from `.rand` unless `ExposedDHs` or `BrokenDH` holds. -/
inductive CompPcsWitnessExposureFor (MsgEncWitness : Bytes → Prop) (tr : ExecTrace) : Bytes → Prop
  | rand {ts sz : Nat} :
      ((mkRand ts sz).AttackerKnows tr ∨ MsgEncWitness (mkRand ts sz)) →
      (IsHonestDH tr (mkRand ts sz) →
        (∃ s i, tr.EventLogged (TREvent.ExposedDHs s (mkRand ts sz) i)) ∨
        tr.EventLogged PQXDHEvent.BrokenDH) →
      CompPcsWitnessExposureFor MsgEncWitness tr (mkRand ts sz)
  | exposedDHs {s : SessionInfo} {dhs : Bytes} {rIdx : Nat} :
      tr.EventLogged (TREvent.ExposedDHs s dhs rIdx) →
      CompPcsWitnessExposureFor MsgEncWitness tr dhs
  | brokenDH {dhs : Bytes} :
      IsHonestDH tr dhs →
      tr.EventLogged PQXDHEvent.BrokenDH →
      CompPcsWitnessExposureFor MsgEncWitness tr dhs
  | pqr {ikm : Bytes} :
      CompPcsWitnessExposureFor MsgEncWitness tr (pqxdhKdf ikm).pqr
  | exposedRK {s : SessionInfo} {rk : Bytes} {rIdx : Nat} :
      (∃ r p sk, rk = (createChain r p sk).1) →
      tr.EventLogged (TREvent.ExposedRK s rk rIdx) →
      CompPcsWitnessExposureFor MsgEncWitness tr rk
  | exposedCKs {s : SessionInfo} {cks : Bytes} {n : UInt32} {rIdx : Nat} :
      IsScheduleKey cks →
      tr.EventLogged (TREvent.ExposedCKs s cks n rIdx) →
      CompPcsWitnessExposureFor MsgEncWitness tr cks
  | exposedCKr {s : SessionInfo} {ckr : Bytes} {n : UInt32} {rIdx : Nat} :
      IsScheduleKey ckr →
      tr.EventLogged (TREvent.ExposedCKr s ckr n rIdx) →
      CompPcsWitnessExposureFor MsgEncWitness tr ckr
  | exposedMK {s : SessionInfo} {seed : Bytes} {n : UInt32} {rIdx : Nat} :
      (∃ c, seed = (kdfCk c).2) →
      tr.EventLogged (TREvent.ExposedMK s seed n rIdx) →
      CompPcsWitnessExposureFor MsgEncWitness tr seed

/-- Inversion interface satisfied by `CompTrClosed (CompPcsWitnessExposureFor MsgEncWitness tr)`. -/
structure PcsWitnessClosureInv (EW ClosedW : Bytes → Prop) : Prop where
  inv_trKeyKnown :
    (∀ p c, ¬ EW (trMsgKeys p (kdfCk c).2).cipherKey) →
    (∀ p c, ¬ EW (hmac p (kdfCk c).2)) →
    ∀ {c pqSalt : Bytes}, TRKeyKnown ClosedW (kdfCk c).2 pqSalt → ClosedW (kdfCk c).2
  inv_kdfCk_snd_chainKeyAt :
    ∀ {ck₀ : Bytes} {n : Nat}, ClosedW (kdfCk (chainKeyAt ck₀ n)).2 →
      EW (kdfCk (chainKeyAt ck₀ n)).2 ∨ (∃ j ≤ n, EW (chainKeyAt ck₀ j)) ∨ ClosedW ck₀
  inv_kdfExtract :
    ∀ {s m : Bytes}, ClosedW (kdfExtract s m) → EW (kdfExtract s m) ∨ (ClosedW s ∧ ClosedW m)
  inv_dh_dhPk :
    ∀ {a b : Bytes}, (∃ t₁, a = mkRand t₁ 32) → (∃ t₂, b = mkRand t₂ 32) →
      ClosedW (DiffieHellman.dh (DiffieHellman.dhPk a) b) → ClosedW a ∨ ClosedW b
  inv_mkRand :
    ∀ {ts sz : Nat}, ClosedW (mkRand ts sz) → EW (mkRand ts sz)

/-- Witness closure of an honest DH share `d` yields `CompromisedKey tr d`. -/
theorem ratchetSecret_compromised_of_witnessClosure {MsgEncWitness ClosedW : Bytes → Prop}
    {tr : ExecTrace}
    (hW : PcsWitnessClosureInv (CompPcsWitnessExposureFor MsgEncWitness tr) ClosedW)
    (hdhs : ∀ d, IsHonestDH tr d → ∃ ts, d = mkRand ts 32)
    {d : Bytes} (hhon : HonestDHKey tr d) (hcl : ClosedW d) :
    CompromisedKey tr d := by
  obtain ⟨ts, rfl⟩ := hdhs d hhon
  have hexp := hW.inv_mkRand hcl
  generalize hq : mkRand ts 32 = q at hexp
  cases hexp with
  | rand _ hguard =>
    obtain ⟨rfl, rfl⟩ := mkRand_inj hq
    rcases hguard hhon with ⟨s, i, hev⟩ | hbdh
    · exact .inr (.inl ⟨s, i, hev⟩)
    · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨hhon, hbdh⟩)))))
  | @exposedDHs s _ i hev => subst hq; exact .inr (.inl ⟨s, i, hev⟩)
  | brokenDH _ hbdh => subst hq; exact .inr (.inr (.inr (.inr (.inr (.inr ⟨hhon, hbdh⟩)))))
  | pqr => exact False.elim (mkRand_ne_kdfExtract ts 32 _ _ hq)
  | exposedRK hrk _ =>
    obtain ⟨_, _, _, hrk⟩ := hrk; exact False.elim (mkRand_ne_kdfExtract ts 32 _ _ (hq.trans hrk))
  | exposedCKs hsk _ | exposedCKr hsk _ =>
    rcases hsk with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;>
      exact False.elim (mkRand_ne_kdfExtract ts 32 _ _ (hq.trans h))
  | exposedMK hm _ =>
    obtain ⟨_, hm⟩ := hm; exact False.elim (mkRand_ne_kdfExtract ts 32 _ _ (hq.trans hm))

/-- If `dh (dhPk peerSk) ownSk` lies in `ClosedW` and both shares satisfy `HonestDHKey tr`, then
one of them is compromised. -/
theorem healShare_compromised_of_witnessClosure {MsgEncWitness ClosedW : Bytes → Prop}
    {tr : ExecTrace} (hW : PcsWitnessClosureInv (CompPcsWitnessExposureFor MsgEncWitness tr) ClosedW)
    (hdhs : ∀ d, IsHonestDH tr d → ∃ ts, d = mkRand ts 32) {ownSk peerSk : Bytes}
    (hOwn : HonestDHKey tr ownSk) (hPeer : HonestDHKey tr peerSk)
    (hcl : ClosedW (DiffieHellman.dh (DiffieHellman.dhPk peerSk) ownSk)) :
    CompromisedKey tr ownSk ∨ CompromisedKey tr peerSk := by
  rcases hW.inv_dh_dhPk (hdhs peerSk hPeer) (hdhs ownSk hOwn) hcl with hPeerCl | hOwnCl
  · exact .inr (ratchetSecret_compromised_of_witnessClosure hW hdhs hPeer hPeerCl)
  · exact .inl (ratchetSecret_compromised_of_witnessClosure hW hdhs hOwn hOwnCl)

/-! ## Structured Exposure, `RootDescends` Closure Inversion, and `PCSQuery` -/

/-- Composed structured exposure set. -/
inductive CompStructuredExposureFor (MsgEncRand : Bytes → Prop) (tr : ExecTrace) : Bytes → Prop
  | rand {ts sz : Nat} :
      (mkRand ts sz).AttackerKnows tr ∨ MsgEncRand (mkRand ts sz) →
      CompStructuredExposureFor MsgEncRand tr (mkRand ts sz)
  | pqr {ikm : Bytes} : CompStructuredExposureFor MsgEncRand tr (pqxdhKdf ikm).pqr
  | exposedRK {s : SessionInfo} {rk : Bytes} {rIdx : Nat} :
      (∃ r p sk, rk = (createChain r p sk).1) → tr.EventLogged (TREvent.ExposedRK s rk rIdx) →
      CompStructuredExposureFor MsgEncRand tr rk
  | exposedCKs {s : SessionInfo} {cks : Bytes} {n : UInt32} {rIdx : Nat} :
      IsScheduleKey cks → tr.EventLogged (TREvent.ExposedCKs s cks n rIdx) →
      CompStructuredExposureFor MsgEncRand tr cks
  | exposedCKr {s : SessionInfo} {ckr : Bytes} {n : UInt32} {rIdx : Nat} :
      IsScheduleKey ckr → tr.EventLogged (TREvent.ExposedCKr s ckr n rIdx) →
      CompStructuredExposureFor MsgEncRand tr ckr
  | exposedMK {s : SessionInfo} {seed : Bytes} {n : UInt32} {rIdx : Nat} :
      (∃ c, seed = (kdfCk c).2) → tr.EventLogged (TREvent.ExposedMK s seed n rIdx) →
      CompStructuredExposureFor MsgEncRand tr seed

/-- On any non-`mkRand` term `b`, `CompPcsWitnessExposureFor` embeds into
`CompStructuredExposureFor` once honest/exposed DH shares are known to be `mkRand _ 32`. -/
theorem compStructuredExposure_of_witnessExposure_nonRand {MsgEncWitness MsgEncRand : Bytes → Prop}
    {tr : ExecTrace} {b : Bytes} (hdhs : ∀ d, IsHonestDH tr d → ∃ ts, d = mkRand ts 32)
    (hexpDH : ∀ s d i, tr.EventLogged (TREvent.ExposedDHs s d i) → ∃ ts, d = mkRand ts 32)
    (hnr : ∀ ts sz, b ≠ mkRand ts sz) (h : CompPcsWitnessExposureFor MsgEncWitness tr b) :
    CompStructuredExposureFor MsgEncRand tr b := by
  cases h with
  | rand _ _ => exact False.elim (hnr _ _ rfl)
  | exposedDHs hev => obtain ⟨ts, hts⟩ := hexpDH _ _ _ hev; exact False.elim (hnr ts 32 hts)
  | brokenDH hhon _ => obtain ⟨ts, hts⟩ := hdhs _ hhon; exact False.elim (hnr ts 32 hts)
  | pqr => exact .pqr
  | exposedRK hrk hev => exact .exposedRK hrk hev
  | exposedCKs hc hev => exact .exposedCKs hc hev
  | exposedCKr hc hev => exact .exposedCKr hc hev
  | exposedMK hm hev => exact .exposedMK hm hev

private theorem not_compStructuredExposure_of {MsgEncRand : Bytes → Prop} {tr : ExecTrace} {b : Bytes}
    (hrand : ∀ ts sz, b ≠ mkRand ts sz) (hpqr : ∀ ikm, b ≠ (pqxdhKdf ikm).pqr)
    (hsk : ¬ IsScheduleKey b) : ¬ CompStructuredExposureFor MsgEncRand tr b := by
  rintro (hr | _ | ⟨hrk, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨hm, _⟩)
  · exact hrand _ _ rfl
  · exact hpqr _ rfl
  · exact hsk (.inl hrk)
  · exact hsk hc
  · exact hsk hc
  · exact hsk (.inr (.inr (.inr (.inr hm))))

theorem not_compStructuredExposure_trMsgKeys_cipherKey (MsgEncRand : Bytes → Prop)
    (tr : ExecTrace) (pqSalt c : Bytes) :
    ¬ CompStructuredExposureFor MsgEncRand tr (trMsgKeys pqSalt (kdfCk c).2).cipherKey := by
  refine not_compStructuredExposure_of (fun ts sz h => mkRand_ne_kdfExtract ts sz _ _ h.symm)
    (fun _ h => hkdfBlock1_ne_hkdfBlock3 _ _ _ _ h) ?_
  rintro (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩)
  · exact whisperRatchet_ne_whisperMessageKeys (hkdfBlock1_inj h).2.symm
  · exact hkdfBlock1_ne_hkdfBlock2 _ _ _ _ h
  · exact hkdfBlock1_ne_hkdfBlock2 _ _ _ _ h
  · exact hkdfBlock1_ne_kdfCk_fst _ _ _ h
  · exact hkdfBlock1_ne_kdfCk_snd _ _ _ h

theorem not_compStructuredExposure_hmac_kdfCk_snd (MsgEncRand : Bytes → Prop)
    (tr : ExecTrace) (pqSalt c : Bytes) :
    ¬ CompStructuredExposureFor MsgEncRand tr (hmac pqSalt (kdfCk c).2) := by
  refine not_compStructuredExposure_of (fun ts sz h => mkRand_ne_kdfExtract ts sz _ _ h.symm)
    (fun _ h => by
      have hm := (hmac_inj h).2
      dsimp only [kdfCk, hmac, pqxdhKdf, hkdfBlock3, KdfExtract.kdfExtract,
        KdfExtract.CanKdfExtract.kdfExtract, Concat.concat, Concat.CanConcat.concat] at hm
      exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm) ?_
  rintro (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩)
  · have hm := (hmac_inj h).2
    dsimp only [kdfCk, hmac, createChain, kdfRk, hkdfBlock1, KdfExtract.kdfExtract,
      KdfExtract.CanKdfExtract.kdfExtract, Concat.concat, Concat.CanConcat.concat] at hm
    exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm
  · have hm := (hmac_inj h).2
    dsimp only [kdfCk, hmac, createChain, kdfRk, hkdfBlock2, KdfExtract.kdfExtract,
      KdfExtract.CanKdfExtract.kdfExtract, Concat.concat, Concat.CanConcat.concat] at hm
    exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm
  · have hm := (hmac_inj h).2
    dsimp only [kdfCk, hmac, pqxdhKdf, hkdfBlock2, KdfExtract.kdfExtract,
      KdfExtract.CanKdfExtract.kdfExtract, Concat.concat, Concat.CanConcat.concat] at hm
    exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm
  · have hm := (hmac_inj h).2
    dsimp only [kdfCk, hmac, KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract,
      litByte, literalToBytes] at hm
    exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm
  · have hm := (hmac_inj h).2
    dsimp only [kdfCk, hmac, KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract,
      litByte, literalToBytes] at hm
    exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm

theorem not_compStructuredExposure_kdfExtract_dh (MsgEncRand : Bytes → Prop)
    (tr : ExecTrace) (r p s : Bytes) :
    ¬ CompStructuredExposureFor MsgEncRand tr (kdfExtract r (DiffieHellman.dh p s)) := by
  refine not_compStructuredExposure_of (fun ts sz h => mkRand_ne_kdfExtract ts sz _ _ h.symm)
    (fun _ h => dh_ne_concat p s _ _ (kdfExtract_inj h).2) ?_
  rintro (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩)
  · exact dh_ne_concat p s _ _ (kdfExtract_inj h).2
  · exact dh_ne_concat p s _ _ (kdfExtract_inj h).2
  · exact dh_ne_concat p s _ _ (kdfExtract_inj h).2
  · exact dh_ne_litByte p s 0x02 (kdfExtract_inj h).2
  · exact dh_ne_litByte p s 0x01 (kdfExtract_inj h).2

theorem not_compStructuredExposure_pqxdhKdf_rk (MsgEncRand : Bytes → Prop)
    (tr : ExecTrace) (ikm : Bytes) :
    ¬ CompStructuredExposureFor MsgEncRand tr (pqxdhKdf ikm).rk := by
  refine not_compStructuredExposure_of (fun ts sz h => mkRand_ne_kdfExtract ts sz _ _ h.symm)
    (fun _ h => hkdfBlock1_ne_hkdfBlock3 _ _ _ _ h) ?_
  rintro (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩)
  · exact whisperRatchet_ne_pqxdhLabel (hkdfBlock1_inj h).2.symm
  · exact hkdfBlock1_ne_hkdfBlock2 _ _ _ _ h
  · exact hkdfBlock1_ne_hkdfBlock2 _ _ _ _ h
  · exact hkdfBlock1_ne_kdfCk_fst _ _ _ h
  · exact hkdfBlock1_ne_kdfCk_snd _ _ _ h

theorem not_compPcsWitnessExposure_trMsgKeys_cipherKey (MsgEncWitness : Bytes → Prop)
    (tr : ExecTrace) (pqSalt c : Bytes) (hdhs : ∀ d, IsHonestDH tr d → ∃ ts, d = mkRand ts 32)
    (hexpDH : ∀ s d i, tr.EventLogged (TREvent.ExposedDHs s d i) → ∃ ts, d = mkRand ts 32) :
    ¬ CompPcsWitnessExposureFor MsgEncWitness tr (trMsgKeys pqSalt (kdfCk c).2).cipherKey :=
  fun h => not_compStructuredExposure_trMsgKeys_cipherKey (fun _ => False) tr pqSalt c
    (compStructuredExposure_of_witnessExposure_nonRand hdhs hexpDH
      (fun ts sz h' => mkRand_ne_kdfExtract ts sz _ _ h'.symm) h)

theorem not_compPcsWitnessExposure_hmac_kdfCk_snd (MsgEncWitness : Bytes → Prop)
    (tr : ExecTrace) (pqSalt c : Bytes) (hdhs : ∀ d, IsHonestDH tr d → ∃ ts, d = mkRand ts 32)
    (hexpDH : ∀ s d i, tr.EventLogged (TREvent.ExposedDHs s d i) → ∃ ts, d = mkRand ts 32) :
    ¬ CompPcsWitnessExposureFor MsgEncWitness tr (hmac pqSalt (kdfCk c).2) :=
  fun h => not_compStructuredExposure_hmac_kdfCk_snd (fun _ => False) tr pqSalt c
    (compStructuredExposure_of_witnessExposure_nonRand hdhs hexpDH
      (fun ts sz h' => mkRand_ne_kdfExtract ts sz _ _ h'.symm) h)

theorem not_compPcsWitnessExposure_kdfExtract_dh (MsgEncWitness : Bytes → Prop)
    (tr : ExecTrace) (r p s : Bytes) (hdhs : ∀ d, IsHonestDH tr d → ∃ ts, d = mkRand ts 32)
    (hexpDH : ∀ s' d i, tr.EventLogged (TREvent.ExposedDHs s' d i) → ∃ ts, d = mkRand ts 32) :
    ¬ CompPcsWitnessExposureFor MsgEncWitness tr (kdfExtract r (DiffieHellman.dh p s)) :=
  fun h => not_compStructuredExposure_kdfExtract_dh (fun _ => False) tr r p s
    (compStructuredExposure_of_witnessExposure_nonRand hdhs hexpDH
      (fun ts sz h' => mkRand_ne_kdfExtract ts sz _ _ h'.symm) h)

/-- KDF-inversion interface satisfied by `CompTrClosed E`. -/
structure PcsKdfClosureInv (E Closed : Bytes → Prop) : Prop where
  inv_trKeyKnown :
    (∀ p c, ¬ E (trMsgKeys p (kdfCk c).2).cipherKey) →
    (∀ p c, ¬ E (hmac p (kdfCk c).2)) →
    ∀ {c pqSalt : Bytes}, TRKeyKnown Closed (kdfCk c).2 pqSalt → Closed (kdfCk c).2
  inv_kdfCk_snd_chainKeyAt :
    ∀ {ck₀ : Bytes} {n : Nat}, Closed (kdfCk (chainKeyAt ck₀ n)).2 →
      E (kdfCk (chainKeyAt ck₀ n)).2 ∨ (∃ j ≤ n, E (chainKeyAt ck₀ j)) ∨ Closed ck₀
  inv_kdfExtract_salt :
    ∀ {s m : Bytes}, Closed (kdfExtract s m) → E (kdfExtract s m) ∨ Closed s

theorem PcsKdfClosureInv.inv_createChain_fst {E Closed : Bytes → Prop}
    (hKdf : PcsKdfClosureInv E Closed)
    (hprk : ∀ r p s, ¬ E (kdfExtract r (DiffieHellman.dh p s)))
    {rk pk sk : Bytes} (h : Closed (createChain rk pk sk).1) :
    E (createChain rk pk sk).1 ∨ Closed rk := by
  rcases hKdf.inv_kdfExtract_salt h with hexp | hprk_c
  · exact .inl hexp
  · exact (hKdf.inv_kdfExtract_salt hprk_c).elim (fun e => False.elim (hprk _ _ _ e)) .inr

theorem PcsKdfClosureInv.inv_createChain_snd {E Closed : Bytes → Prop}
    (hKdf : PcsKdfClosureInv E Closed)
    (hprk : ∀ r p s, ¬ E (kdfExtract r (DiffieHellman.dh p s)))
    {rk pk sk : Bytes} (h : Closed (createChain rk pk sk).2) :
    E (createChain rk pk sk).2 ∨ Closed rk := by
  rcases hKdf.inv_kdfExtract_salt h with hexp | hprk_c
  · exact .inl hexp
  · exact (hKdf.inv_kdfExtract_salt hprk_c).elim (fun e => False.elim (hprk _ _ _ e)) .inr

/-- Backward KDF-closure walk along `RootDescends r₀ r`. -/
theorem PcsKdfClosureInv.inv_rootDescends {E Closed : Bytes → Prop}
    (hKdf : PcsKdfClosureInv E Closed)
    (hprk : ∀ r p s, ¬ E (kdfExtract r (DiffieHellman.dh p s)))
    {r₀ r : Bytes} (hdesc : RootDescends r₀ r) (hcl : Closed r) :
    (∃ r_mid, RootDescends r₀ r_mid ∧ RootDescends r_mid r ∧ E r_mid) ∨ Closed r₀ := by
  induction hdesc with
  | refl => exact .inr hcl
  | @step rk' theirPk ourSk hprev ih =>
    rcases hKdf.inv_createChain_fst hprk hcl with hexp | hprev_c
    · exact .inl ⟨(createChain rk' theirPk ourSk).1, .step hprev, .refl, hexp⟩
    · exact (ih hprev_c).elim
        (fun ⟨r_mid, h₀_mid, h_mid_rk', hexp⟩ =>
          .inl ⟨r_mid, h₀_mid, .step h_mid_rk', hexp⟩)
        .inr

/-- Witness-closure propagation along `RootDescends` down to the heal DH shared secret. -/
theorem PcsWitnessClosureInv.inv_rootDescends_to_heal_dh {EW ClosedW : Bytes → Prop}
    (hW : PcsWitnessClosureInv EW ClosedW)
    (hprk : ∀ r p s, ¬ EW (kdfExtract r (DiffieHellman.dh p s)))
    {rk_prev ownSk peerSk r : Bytes}
    (hdesc : RootDescends (createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk).1 r)
    (hcl : ClosedW r) :
    (∃ r_mid, RootDescends (createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk).1 r_mid ∧
      RootDescends r_mid r ∧ EW r_mid) ∨
    ClosedW (DiffieHellman.dh (DiffieHellman.dhPk peerSk) ownSk) := by
  induction hdesc with
  | refl =>
    rcases hW.inv_kdfExtract hcl with hexp | ⟨hprk_w, _⟩
    · exact .inl ⟨_, .refl, .refl, hexp⟩
    · dsimp only [DY.X25519.agree] at hprk_w
      rw [x25519Key_dhPk] at hprk_w
      rcases hW.inv_kdfExtract hprk_w with hexp_prk | ⟨_, hdh_w⟩
      · exact False.elim (hprk _ _ _ hexp_prk)
      · exact .inr hdh_w
  | @step rk' theirPk ourSk hprev ih =>
    rcases hW.inv_kdfExtract hcl with hexp | ⟨hprk_w, _⟩
    · exact .inl ⟨(createChain rk' theirPk ourSk).1, .step hprev, .refl, hexp⟩
    · rcases hW.inv_kdfExtract hprk_w with hexp_prk | ⟨hrk'_w, _⟩
      · exact False.elim (hprk _ _ _ hexp_prk)
      · exact (ih hrk'_w).elim
          (fun ⟨r_mid, h₁, h₂, hexp⟩ => .inl ⟨r_mid, h₁, .step h₂, hexp⟩)
          .inr

/-- Per-event schedule invariant on `TREvent`. -/
def CompEventScheduleOKFor (SessionAt : SessionInfo → Nat → Bytes → Bytes → Prop)
    (_tr : ExecTrace) : TREvent → Prop
  | .MessageKey s .receiver seed _ n rIdx _ =>
    1 ≤ rIdx ∧
    ∃ doneIdx ikm dh₁ ck₀, SessionAt s doneIdx ikm dh₁ ∧
      CompChainRootFrom1 dh₁ ikm (rIdx - 1) ck₀ ∧ seed = (kdfCk (chainKeyAt ck₀ n.toNat)).2
  | .MessageKey s .sender seed _ n rIdx _ =>
    1 ≤ rIdx ∧
    ∃ doneIdx ikm dh₁ ck₀, SessionAt s doneIdx ikm dh₁ ∧
      CompChainRootFrom1 dh₁ ikm rIdx ck₀ ∧ seed = (kdfCk (chainKeyAt ck₀ n.toNat)).2
  | .ExposedRK s rk rIdx =>
    1 ≤ rIdx ∧ (∃ r p sk, rk = (createChain r p sk).1) ∧
    ∃ doneIdx ikm dh₁, SessionAt s doneIdx ikm dh₁ ∧ CompRkSteps dh₁ rIdx (pqxdhKdf ikm).rk rk
  | .ExposedCKs s ck ns rIdx =>
    1 ≤ rIdx ∧
    ∃ doneIdx ikm dh₁ ck₀, SessionAt s doneIdx ikm dh₁ ∧
      CompChainRootFrom1 dh₁ ikm rIdx ck₀ ∧ ck = chainKeyAt ck₀ ns.toNat
  | .ExposedCKr s ck nr rIdx =>
    1 ≤ rIdx ∧
    ∃ doneIdx ikm dh₁ ck₀, SessionAt s doneIdx ikm dh₁ ∧
      CompChainRootFrom1 dh₁ ikm (rIdx - 1) ck₀ ∧ ck = chainKeyAt ck₀ nr.toNat
  | .ExposedMK s seed n rIdx =>
    1 ≤ rIdx ∧
    ∃ doneIdx ikm dh₁ ck₀, SessionAt s doneIdx ikm dh₁ ∧
      CompChainRootFrom1 dh₁ ikm (rIdx - 1) ck₀ ∧ seed = (kdfCk (chainKeyAt ck₀ n.toNat)).2
  | _ => True

private theorem compChainRootFrom1_chainKeyAt_ne_model_mkRand {dh₁ ikm ck₀ : Bytes} {m j : Nat}
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀) (ts sz : Nat) :
    chainKeyAt ck₀ j ≠ mkRand ts sz := by
  intro h
  cases j with
  | zero =>
    obtain ⟨_, _, rfl⟩ := hroot.exists_hkdfBlock2
    exact mkRand_ne_kdfExtract ts sz _ _ h.symm
  | succ _ =>
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    exact mkRand_ne_kdfExtract ts sz _ _ h.symm

private theorem compChainRootFrom1_chainKeyAt_ne_kdfCk_snd {dh₁ ikm ck₀ ck : Bytes} {m : Nat}
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀) (j : Nat) :
    chainKeyAt ck₀ j ≠ (kdfCk ck).2 := by
  cases j with
  | zero =>
    obtain ⟨p, i, rfl⟩ := hroot.exists_hkdfBlock2
    exact hkdfBlock2_ne_kdfCk_snd p i ck
  | succ _ =>
    rw [chainKeyAt_succ_eq_kdfCk_fst]
    exact kdfCk_fst_ne_snd _ _

private theorem hkdfBlock1_ne_compChainRootFrom1_chainKeyAt {dh₁ ikm ck₀ p i : Bytes} {m j : Nat}
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀) :
    hkdfBlock1 p i ≠ chainKeyAt ck₀ j := by
  cases j with
  | zero =>
    obtain ⟨p₂, i₂, rfl⟩ := hroot.exists_hkdfBlock2
    exact hkdfBlock1_ne_hkdfBlock2 p i p₂ i₂
  | succ _ =>
    rw [chainKeyAt_succ_eq_kdfCk_fst]
    exact hkdfBlock1_ne_kdfCk_fst p i _

theorem inv_compStructuredExposure_kdfCk_snd {MsgEncRand : Bytes → Prop} {tr : ExecTrace}
    {SessionAt : SessionInfo → Nat → Bytes → Bytes → Prop}
    (hevOK : ∀ ev, tr.EventLogged ev → CompEventScheduleOKFor SessionAt tr ev)
    (ck : Bytes)
    (hexp : CompStructuredExposureFor MsgEncRand tr (kdfCk ck).2) :
    CompromisedKey tr (kdfCk ck).2 := by
  generalize hq : (kdfCk ck).2 = q at hexp
  cases hexp with
  | rand _ => exact False.elim (mkRand_ne_kdfExtract _ _ _ _ hq.symm)
  | pqr => exact False.elim (litByte_ne_concat _ _ _ (hmac_inj hq).2)
  | exposedRK hrk _ =>
    obtain ⟨_, _, _, hrk⟩ := hrk
    exact False.elim (hkdfBlock1_ne_kdfCk_snd _ _ ck (hq.trans hrk).symm)
  | exposedCKs _ hev =>
    obtain ⟨_, _, _, _, _, _, hroot', hck⟩ := hevOK _ hev
    exact False.elim (compChainRootFrom1_chainKeyAt_ne_kdfCk_snd hroot' _ (hck.symm.trans hq.symm))
  | exposedCKr _ hev =>
    obtain ⟨_, _, _, _, _, _, hroot', hck⟩ := hevOK _ hev
    exact False.elim (compChainRootFrom1_chainKeyAt_ne_kdfCk_snd hroot' _ (hck.symm.trans hq.symm))
  | @exposedMK s' _ n' rIdx' _ hev =>
    exact .inr (.inr (.inr (.inr (.inl ⟨s', n', rIdx', hev⟩))))

theorem inv_compStructuredExposure_chainKeyAt {MsgEncRand : Bytes → Prop} {tr : ExecTrace}
    {dh₁ ikm ck₀ : Bytes} {m j : Nat}
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀)
    (hexp : CompStructuredExposureFor MsgEncRand tr (chainKeyAt ck₀ j)) :
    CompromisedKey tr (chainKeyAt ck₀ j) := by
  generalize hq : chainKeyAt ck₀ j = q at hexp
  cases hexp with
  | rand _ =>
    exact False.elim (compChainRootFrom1_chainKeyAt_ne_model_mkRand hroot _ _ hq)
  | pqr =>
    cases j with
    | zero =>
      obtain ⟨p, i, rfl⟩ := hroot.exists_hkdfBlock2
      exact False.elim (hkdfBlock2_ne_hkdfBlock3 p i _ _ hq)
    | succ _ =>
      rw [chainKeyAt_succ_eq_kdfCk_fst] at hq
      exact False.elim (litByte_ne_concat _ _ _ (hmac_inj hq).2)
  | exposedRK hrk _ =>
    obtain ⟨_, _, _, hrk⟩ := hrk
    exact False.elim (hkdfBlock1_ne_compChainRootFrom1_chainKeyAt hroot (hq.trans hrk).symm)
  | exposedMK hseed _ =>
    obtain ⟨_, rfl⟩ := hseed
    exact False.elim (compChainRootFrom1_chainKeyAt_ne_kdfCk_snd hroot j hq)
  | @exposedCKs s' _ ns rIdx' _ hev =>
    exact .inr (.inr (.inl ⟨s', ns, rIdx', hev⟩))
  | @exposedCKr s' _ nr rIdx' _ hev =>
    exact .inr (.inr (.inr (.inl ⟨s', nr, rIdx', hev⟩)))

theorem inv_compStructuredExposure_hkdfBlock1 {MsgEncRand : Bytes → Prop} {tr : ExecTrace}
    {SessionAt : SessionInfo → Nat → Bytes → Bytes → Prop}
    (hevOK : ∀ ev, tr.EventLogged ev → CompEventScheduleOKFor SessionAt tr ev)
    {rk : Bytes} (hb1 : ∃ p i, rk = hkdfBlock1 p i)
    (hexp : CompStructuredExposureFor MsgEncRand tr rk) :
    CompromisedKey tr rk := by
  obtain ⟨p, i, hrk_eq⟩ := hb1
  generalize hq : rk = q at hexp
  cases hexp with
  | rand _ => exact False.elim (mkRand_ne_kdfExtract _ _ _ _ (hrk_eq.symm.trans hq).symm)
  | pqr => exact False.elim (hkdfBlock1_ne_hkdfBlock3 p i _ _ (hrk_eq.symm.trans hq))
  | exposedCKs _ hev =>
    obtain ⟨_, _, _, _, _, _, hroot', hck⟩ := hevOK _ hev
    exact False.elim (hkdfBlock1_ne_compChainRootFrom1_chainKeyAt hroot' (hrk_eq.symm.trans (hq.trans hck)))
  | exposedCKr _ hev =>
    obtain ⟨_, _, _, _, _, _, hroot', hck⟩ := hevOK _ hev
    exact False.elim (hkdfBlock1_ne_compChainRootFrom1_chainKeyAt hroot' (hrk_eq.symm.trans (hq.trans hck)))
  | exposedMK hseed _ =>
    obtain ⟨_, rfl⟩ := hseed
    exact False.elim (hkdfBlock1_ne_kdfCk_snd p i _ (hrk_eq.symm.trans hq))
  | @exposedRK s' _ rIdx' _ hev =>
    exact .inl ⟨s', rIdx', hev⟩

theorem inv_compPcsWitnessExposure_kdfCk_snd {MsgEncWitness : Bytes → Prop} {tr : ExecTrace}
    {SessionAt : SessionInfo → Nat → Bytes → Bytes → Prop}
    (hevOK : ∀ ev, tr.EventLogged ev → CompEventScheduleOKFor SessionAt tr ev)
    (hdhs : ∀ d, IsHonestDH tr d → ∃ ts, d = mkRand ts 32)
    (hexpDH : ∀ s d i, tr.EventLogged (TREvent.ExposedDHs s d i) → ∃ ts, d = mkRand ts 32)
    (ck : Bytes)
    (hexp : CompPcsWitnessExposureFor MsgEncWitness tr (kdfCk ck).2) :
    CompromisedKey tr (kdfCk ck).2 :=
  inv_compStructuredExposure_kdfCk_snd (MsgEncRand := fun _ => False) hevOK ck
    (compStructuredExposure_of_witnessExposure_nonRand hdhs hexpDH
      (fun ts sz h => mkRand_ne_kdfExtract ts sz _ _ h.symm) hexp)

theorem inv_compPcsWitnessExposure_chainKeyAt {MsgEncWitness : Bytes → Prop} {tr : ExecTrace}
    (hdhs : ∀ d, IsHonestDH tr d → ∃ ts, d = mkRand ts 32)
    (hexpDH : ∀ s d i, tr.EventLogged (TREvent.ExposedDHs s d i) → ∃ ts, d = mkRand ts 32)
    {dh₁ ikm ck₀ : Bytes} {m j : Nat}
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀)
    (hexp : CompPcsWitnessExposureFor MsgEncWitness tr (chainKeyAt ck₀ j)) :
    CompromisedKey tr (chainKeyAt ck₀ j) :=
  inv_compStructuredExposure_chainKeyAt (MsgEncRand := fun _ => False) hroot
    (compStructuredExposure_of_witnessExposure_nonRand hdhs hexpDH
      (compChainRootFrom1_chainKeyAt_ne_model_mkRand hroot) hexp)

theorem inv_compPcsWitnessExposure_hkdfBlock1 {MsgEncWitness : Bytes → Prop} {tr : ExecTrace}
    {SessionAt : SessionInfo → Nat → Bytes → Bytes → Prop}
    (hevOK : ∀ ev, tr.EventLogged ev → CompEventScheduleOKFor SessionAt tr ev)
    (hdhs : ∀ d, IsHonestDH tr d → ∃ ts, d = mkRand ts 32)
    (hexpDH : ∀ s d i, tr.EventLogged (TREvent.ExposedDHs s d i) → ∃ ts, d = mkRand ts 32)
    {rk : Bytes} (hb1 : ∃ p i, rk = hkdfBlock1 p i)
    (hexp : CompPcsWitnessExposureFor MsgEncWitness tr rk) :
    CompromisedKey tr rk :=
  inv_compStructuredExposure_hkdfBlock1 (MsgEncRand := fun _ => False) hevOK hb1
    (compStructuredExposure_of_witnessExposure_nonRand hdhs hexpDH
      (fun ts sz h => by obtain ⟨_, _, hr⟩ := hb1; exact mkRand_ne_kdfExtract ts sz _ _ (hr.symm.trans h).symm)
      hexp)

/-- If `RootDescends (pqxdhKdf ikm).rk rk_prev` and `Closed rk_prev`, then some ancestor `rk`
of `rk_prev` satisfies `CompromisedKey tr rk`. -/
theorem exists_compromised_ancestor_of_closed {MsgEncRand Closed : Bytes → Prop} {tr : ExecTrace}
    {SessionAt : SessionInfo → Nat → Bytes → Bytes → Prop}
    (hevOK : ∀ ev, tr.EventLogged ev → CompEventScheduleOKFor SessionAt tr ev)
    (hKdf : PcsKdfClosureInv (CompStructuredExposureFor MsgEncRand tr) Closed)
    (hHsExc : ∀ {doneIdx : Nat} {ikm : Bytes},
      HandshakeKeysAt tr doneIdx (pqxdhKdf ikm) →
      Closed (hmac zeroSalt ikm) → HandshakeRootCompromised tr (pqxdhKdf ikm).rk)
    {doneIdx : Nat} {ikm rk_prev : Bytes}
    (hhk : HandshakeKeysAt tr doneIdx (pqxdhKdf ikm))
    (hdesc : RootDescends (pqxdhKdf ikm).rk rk_prev)
    (hcl : Closed rk_prev) :
    ∃ rk, RootDescends rk rk_prev ∧ CompromisedKey tr rk := by
  rcases hKdf.inv_rootDescends (not_compStructuredExposure_kdfExtract_dh MsgEncRand tr) hdesc hcl with
      ⟨r_mid, h₀_mid, h_mid_prev, hexp⟩ | hrk₀
  · exact ⟨r_mid, h_mid_prev,
      inv_compStructuredExposure_hkdfBlock1 hevOK
        (rootDescends_exists_hkdfBlock1_of_pqxdhKdf_rk h₀_mid) hexp⟩
  · rcases hKdf.inv_kdfExtract_salt hrk₀ with hexp | hprk
    · exact False.elim (not_compStructuredExposure_pqxdhKdf_rk MsgEncRand tr ikm hexp)
    · exact ⟨(pqxdhKdf ikm).rk, hdesc,
        .inr (.inr (.inr (.inr (.inr (.inl (hHsExc hhk hprk))))))⟩

theorem pcsQuery_conclusion_of_compClosure {MsgEncRand MsgEncWitness Closed ClosedW : Bytes → Prop}
    {tr : ExecTrace} {SessionAt : SessionInfo → Nat → Bytes → Bytes → Prop}
    (hevOK : ∀ ev, tr.EventLogged ev → CompEventScheduleOKFor SessionAt tr ev)
    (hdhs : ∀ d, IsHonestDH tr d → ∃ ts, d = mkRand ts 32)
    (hexpDH : ∀ s d i, tr.EventLogged (TREvent.ExposedDHs s d i) → ∃ ts, d = mkRand ts 32)
    (hKdf : PcsKdfClosureInv (CompStructuredExposureFor MsgEncRand tr) Closed)
    (hHsExc : ∀ {doneIdx : Nat} {ikm : Bytes},
      HandshakeKeysAt tr doneIdx (pqxdhKdf ikm) →
      Closed (hmac zeroSalt ikm) → HandshakeRootCompromised tr (pqxdhKdf ikm).rk)
    (hW : PcsWitnessClosureInv (CompPcsWitnessExposureFor MsgEncWitness tr) ClosedW)
    {doneIdx epoch : Nat} {dh₁ ikm ck₀ mk pqSalt rk_prev ownSk peerSk : Bytes} {n : UInt32}
    (hhk : HandshakeKeysAt tr doneIdx (pqxdhKdf ikm))
    (hd : ∃ p sk, dh₁ = DiffieHellman.dh (X25519.normalizeX25519Key p) sk)
    (hroot : CompChainRootFrom1 dh₁ ikm epoch ck₀)
    (hmk : mk = (kdfCk (chainKeyAt ck₀ n.toNat)).2)
    (hknown : TRKeyKnown Closed mk pqSalt)
    (hknownW : TRKeyKnown ClosedW mk pqSalt)
    (hOwn : HonestDHKey tr ownSk)
    (hPeer : HonestDHKey tr peerSk)
    (hGen :
      let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
      DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) :
    let (rk_heal, _) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    CompromisedKey tr mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ CompromisedKey tr ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧
      CompromisedKey tr rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ CompromisedKey tr rk) ∧
     (CompromisedKey tr ownSk ∨ CompromisedKey tr peerSk)) := by
  subst hmk
  dsimp only at hGen ⊢
  have hseed := hKdf.inv_trKeyKnown
    (not_compStructuredExposure_trMsgKeys_cipherKey MsgEncRand tr)
    (not_compStructuredExposure_hmac_kdfCk_snd MsgEncRand tr) hknown
  have hseedW := hW.inv_trKeyKnown
    (not_compPcsWitnessExposure_trMsgKeys_cipherKey MsgEncWitness tr · · hdhs hexpDH)
    (not_compPcsWitnessExposure_hmac_kdfCk_snd MsgEncWitness tr · · hdhs hexpDH) hknownW
  have hdm₀ : DerivesMsgKey ck₀ (kdfCk (chainKeyAt ck₀ n.toNat)).2 := ⟨n.toNat, rfl⟩
  rcases hKdf.inv_kdfCk_snd_chainKeyAt hseed with hexp_mk | ⟨j, hj, hexp_ck⟩ | hck₀
  · exact .inl (inv_compStructuredExposure_kdfCk_snd hevOK _ hexp_mk)
  · exact .inr (.inl ⟨chainKeyAt ck₀ j, derivesMsgKey_of_chainKeyAt_le hj rfl,
      inv_compStructuredExposure_chainKeyAt hroot hexp_ck⟩)
  · rcases hW.inv_kdfCk_snd_chainKeyAt hseedW with hexpW_mk | ⟨j, hj, hexpW_ck⟩ | hck₀W
    · exact .inl (inv_compPcsWitnessExposure_kdfCk_snd hevOK hdhs hexpDH _ hexpW_mk)
    · exact .inr (.inl ⟨chainKeyAt ck₀ j, derivesMsgKey_of_chainKeyAt_le hj rfl,
        inv_compPcsWitnessExposure_chainKeyAt hdhs hexpDH hroot hexpW_ck⟩)
    · rcases hGen with ⟨steps, hmk_eq⟩ | ⟨ck, hdc_heal, ⟨steps, hmk_eq⟩⟩
      · have hck_eq : ck₀ = (createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk).2 :=
          (chainKeyAt_root_inj hroot.isChainRoot
            (isChainRoot_hkdfBlock2 _ _) (kdfCk_snd_inj hmk_eq)).1
        have hdesc_prev : RootDescends (pqxdhKdf ikm).rk rk_prev :=
          hroot.rootDescends_of_eq_createChain_snd hd hck_eq
        have hck₀_cc : Closed (createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk).2 :=
          hck_eq ▸ hck₀
        have hck₀W_cc : ClosedW (createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk).2 :=
          hck_eq ▸ hck₀W
        rcases hKdf.inv_createChain_snd (not_compStructuredExposure_kdfExtract_dh MsgEncRand tr) hck₀_cc with
            hexp_ck₀ | hrk_prev_c
        · have hexp₀ : CompStructuredExposureFor MsgEncRand tr (chainKeyAt ck₀ 0) :=
            hck_eq.symm ▸ hexp_ck₀
          exact .inr (.inl ⟨ck₀, hdm₀, inv_compStructuredExposure_chainKeyAt hroot hexp₀⟩)
        · rcases hW.inv_kdfExtract hck₀W_cc with hexpW_ck₀ | ⟨hprkW, _⟩
          · have hexpW₀ : CompPcsWitnessExposureFor MsgEncWitness tr (chainKeyAt ck₀ 0) :=
              hck_eq.symm ▸ hexpW_ck₀
            exact .inr (.inl ⟨ck₀, hdm₀,
              inv_compPcsWitnessExposure_chainKeyAt hdhs hexpDH hroot hexpW₀⟩)
          · dsimp only [DY.X25519.agree] at hprkW
            rw [x25519Key_dhPk] at hprkW
            rcases hW.inv_kdfExtract hprkW with hexpW_prk | ⟨_, hdhW⟩
            · exact False.elim (not_compPcsWitnessExposure_kdfExtract_dh MsgEncWitness tr _ _ _
                hdhs hexpDH hexpW_prk)
            · exact .inr (.inr (.inr
                ⟨exists_compromised_ancestor_of_closed hevOK hKdf hHsExc hhk hdesc_prev hrk_prev_c,
                 healShare_compromised_of_witnessClosure hW hdhs hOwn hPeer hdhW⟩))
      · obtain ⟨rk_end, pk_end, sk_end, hdesc_heal, hck_end⟩ := hdc_heal
        have hck_root : IsChainRoot ck := hck_end ▸ isChainRoot_hkdfBlock2 _ _
        obtain ⟨hck_eq, _⟩ := chainKeyAt_root_inj hroot.isChainRoot hck_root (kdfCk_snd_inj hmk_eq)
        have hck₀_end : ck₀ = (createChain rk_end pk_end sk_end).2 := hck_eq.trans hck_end
        have hdc₀ : DerivesChain (createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk).1 ck₀ :=
          ⟨rk_end, pk_end, sk_end, hdesc_heal, hck₀_end⟩
        obtain ⟨hdesc_rk_heal, hdesc_prev⟩ :=
          hroot.rootDescends_of_derivesChain_heal hd hdc₀
        have hck₀_cc : Closed (createChain rk_end pk_end sk_end).2 := hck₀_end ▸ hck₀
        have hck₀W_cc : ClosedW (createChain rk_end pk_end sk_end).2 := hck₀_end ▸ hck₀W
        rcases hKdf.inv_createChain_snd (not_compStructuredExposure_kdfExtract_dh MsgEncRand tr) hck₀_cc with
            hexp_ck₀ | hrk_end_c
        · have hexp₀ : CompStructuredExposureFor MsgEncRand tr (chainKeyAt ck₀ 0) :=
            hck₀_end.symm ▸ hexp_ck₀
          exact .inr (.inl ⟨ck₀, hdm₀, inv_compStructuredExposure_chainKeyAt hroot hexp₀⟩)
        · rcases hKdf.inv_rootDescends (not_compStructuredExposure_kdfExtract_dh MsgEncRand tr)
              hdesc_heal hrk_end_c with ⟨r_mid, h_heal_mid, h_mid_end, hexp_mid⟩ | hrk_heal_c
          · have hb1_mid : ∃ p i, r_mid = hkdfBlock1 p i := by
              obtain ⟨_, _, _, hr⟩ := rootDescends_exists_createChain_fst h_heal_mid
              exact ⟨_, _, hr⟩
            exact .inr (.inr (.inl ⟨r_mid, ck₀, h_heal_mid,
              ⟨rk_end, pk_end, sk_end, h_mid_end, hck₀_end⟩, hdm₀,
              inv_compStructuredExposure_hkdfBlock1 hevOK hb1_mid hexp_mid⟩))
          · rcases hKdf.inv_createChain_fst (not_compStructuredExposure_kdfExtract_dh MsgEncRand tr)
                hrk_heal_c with hexp_heal | hrk_prev_c
            · exact .inr (.inr (.inl ⟨(createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk).1,
                ck₀, .refl, hdc₀, hdm₀,
                inv_compStructuredExposure_hkdfBlock1 hevOK
                  (rootDescends_exists_hkdfBlock1_of_pqxdhKdf_rk hdesc_rk_heal) hexp_heal⟩))
            · rcases hW.inv_kdfExtract hck₀W_cc with hexpW_ck₀ | ⟨hprkW_end, _⟩
              · have hexpW₀ : CompPcsWitnessExposureFor MsgEncWitness tr (chainKeyAt ck₀ 0) :=
                  hck₀_end.symm ▸ hexpW_ck₀
                exact .inr (.inl ⟨ck₀, hdm₀,
                  inv_compPcsWitnessExposure_chainKeyAt hdhs hexpDH hroot hexpW₀⟩)
              · rcases hW.inv_kdfExtract hprkW_end with hexpW_prk | ⟨hrk_end_w, _⟩
                · exact False.elim (not_compPcsWitnessExposure_kdfExtract_dh MsgEncWitness tr _ _ _
                    hdhs hexpDH hexpW_prk)
                · rcases hW.inv_rootDescends_to_heal_dh
                      (not_compPcsWitnessExposure_kdfExtract_dh MsgEncWitness tr · · · hdhs hexpDH)
                      hdesc_heal hrk_end_w with ⟨r_mid, h_heal_mid, h_mid_end, hexpW_mid⟩ | hdhW
                  · have hb1_mid : ∃ p i, r_mid = hkdfBlock1 p i := by
                      obtain ⟨_, _, _, hr⟩ := rootDescends_exists_createChain_fst h_heal_mid
                      exact ⟨_, _, hr⟩
                    exact .inr (.inr (.inl ⟨r_mid, ck₀, h_heal_mid,
                      ⟨rk_end, pk_end, sk_end, h_mid_end, hck₀_end⟩, hdm₀,
                      inv_compPcsWitnessExposure_hkdfBlock1 hevOK hdhs hexpDH hb1_mid hexpW_mid⟩))
                  · exact .inr (.inr (.inr
                      ⟨exists_compromised_ancestor_of_closed hevOK hKdf hHsExc hhk hdesc_prev hrk_prev_c,
                       healShare_compromised_of_witnessClosure hW hdhs hOwn hPeer hdhW⟩))

/-- Proves `PCSQuery tr` from the schedule invariant, structured and witness attacker-knowledge
closures, DH-origin invariant, and handshake-excuse bridge. -/
theorem pcsQuery_of_compClosure {MsgEncRand MsgEncWitness Closed ClosedW : Bytes → Prop}
    {tr : ExecTrace} {SessionAt : SessionInfo → Nat → Bytes → Bytes → Prop}
    (hS : ∀ {s doneIdx ikm dh₁}, SessionAt s doneIdx ikm dh₁ →
      HandshakeKeysAt tr doneIdx (pqxdhKdf ikm) ∧
      ∃ p sk, dh₁ = DiffieHellman.dh (X25519.normalizeX25519Key p) sk)
    (hevOK : ∀ ev, tr.EventLogged ev → CompEventScheduleOKFor SessionAt tr ev)
    (hdhs : ∀ d, IsHonestDH tr d → ∃ ts, d = mkRand ts 32)
    (hexpDH : ∀ s d i, tr.EventLogged (TREvent.ExposedDHs s d i) → ∃ ts, d = mkRand ts 32)
    (hKdf : PcsKdfClosureInv (CompStructuredExposureFor MsgEncRand tr) Closed)
    (hKnows : ∀ t : Bytes, t.AttackerKnows tr → Closed t)
    (hHsExc : ∀ {doneIdx : Nat} {ikm : Bytes},
      HandshakeKeysAt tr doneIdx (pqxdhKdf ikm) →
      Closed (hmac zeroSalt ikm) → HandshakeRootCompromised tr (pqxdhKdf ikm).rk)
    (hW : PcsWitnessClosureInv (CompPcsWitnessExposureFor MsgEncWitness tr) ClosedW)
    (hKnowsW : ∀ t : Bytes, t.AttackerKnows tr → ClosedW t) :
    PCSQuery tr := by
  intro mk pqSalt rk_prev ownSk peerSk hmk htrkn hOwn hPeer hGen
  obtain ⟨s, dir, n, i, parIdx, hev⟩ := hmk
  have hknown : TRKeyKnown Closed mk pqSalt := htrkn.imp (hKnows _) (hKnows _)
  have hknownW : TRKeyKnown ClosedW mk pqSalt := htrkn.imp (hKnowsW _) (hKnowsW _)
  cases dir <;> {
    obtain ⟨_, doneIdx, ikm, dh₁, ck₀, hs, hroot, hseed⟩ := hevOK _ hev
    obtain ⟨hhk, hd⟩ := hS hs
    exact pcsQuery_conclusion_of_compClosure hevOK hdhs hexpDH hKdf hHsExc hW
      hhk hd hroot hseed hknown hknownW hOwn hPeer hGen }

/-! ## Reachable Invariant Bundle and Post-Compromise Security -/

/-- Bundled invariants on a reachable composed trace `tr` sufficient for `PCSQuery tr`. -/
def ReachableCompPCSBundle (tr : ExecTrace) : Prop :=
  ∃ (SessionAt : SessionInfo → Nat → Bytes → Bytes → Prop)
    (MsgEncRand MsgEncWitness Closed ClosedW : Bytes → Prop),
    (∀ {s doneIdx ikm dh₁}, SessionAt s doneIdx ikm dh₁ →
      HandshakeKeysAt tr doneIdx (pqxdhKdf ikm) ∧
      ∃ p sk, dh₁ = DiffieHellman.dh (X25519.normalizeX25519Key p) sk) ∧
    (∀ ev, tr.EventLogged ev → CompEventScheduleOKFor SessionAt tr ev) ∧
    (∀ d, IsHonestDH tr d → ∃ ts, d = mkRand ts 32) ∧
    (∀ s d i, tr.EventLogged (TREvent.ExposedDHs s d i) → ∃ ts, d = mkRand ts 32) ∧
    PcsKdfClosureInv (CompStructuredExposureFor MsgEncRand tr) Closed ∧
    (∀ t : Bytes, t.AttackerKnows tr → Closed t) ∧
    (∀ {doneIdx : Nat} {ikm : Bytes},
      HandshakeKeysAt tr doneIdx (pqxdhKdf ikm) →
      Closed (hmac zeroSalt ikm) → HandshakeRootCompromised tr (pqxdhKdf ikm).rk) ∧
    PcsWitnessClosureInv (CompPcsWitnessExposureFor MsgEncWitness tr) ClosedW ∧
    (∀ t : Bytes, t.AttackerKnows tr → ClosedW t)

/-- Reduces `DY.Libsignal.Composed.Security.PostCompromiseSecurity` to `ReachableCompPCSBundle`
on reachable traces. -/
theorem post_compromise_security_of_compInvariants
    (hInv : ∀ tr : ExecTrace, tr.Reachable DY.Libsignal.Composed.reachability →
      ReachableCompPCSBundle tr) :
    Security.PostCompromiseSecurity := by
  intro tr hreach
  obtain ⟨SessionAt, MsgEncRand, MsgEncWitness, Closed, ClosedW,
    hS, hevOK, hdhs, hexpDH, hKdf, hKnows, hHsExc, hW, hKnowsW⟩ := hInv tr hreach
  exact pcsQuery_of_compClosure hS hevOK hdhs hexpDH hKdf hKnows hHsExc hW hKnowsW

end Symbolic.Swarm.COMPOSED.CompPcsEngine
