/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.Composed.Adversary
import Init.Data.String.Defs
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Bytes.AttackerKnowledge
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

@[expose] public section

set_option autoImplicit false

/-!
# Shared Triple Ratchet Tightness Helpers

Provides the symbolic KDF-depth measure (`saltDepth`), schedule injectivity and key-shape
distinctness lemmas, chain-root and root-ancestry characterization (`IsChainRoot`, `RootDescends`),
and no-compromise reductions to `ExposedKey` for Triple Ratchet specification-tightness tests.
-/

namespace Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon

open Symbolic.Proofs.Tests.Shared.Composed.Adversary (isAnyTRExposure not_tr_logged trEvIdx)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (dhsA dhsA2 dhsB1 evIdx ikA ikB
  isCompromise keys1 noCompromise_of_evIdx pqskB spkB stA0 stA1 stA2 stA4 stB00 stB1 stB2 stB3 t4)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (EvT NetE aliceOutOpt encSt encTr rnd)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.Comparse DY.DiffieHellman DY.KdfExtract DY.Concat DY.Literal DY.SymEnc DY.Trunc
open DY.X25519 DY.Spqr DY.TrWire
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Cheval
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys pqxdhKdf pqxdhIkm pqxdhLabel agree
  AliceHandshakeWasCompromised BobHandshakeWasCompromised NoCompromise HandshakeKeysAt HandshakeWasCompromisedAt)

/-! ## Symbolic KDF-depth measure (`saltDepth`) -/

section SizeOfPos
unseal Bytes
attribute [local instance_reducible] Bytes
private theorem bytes_sizeOf_pos (b : Bytes) : 1 ≤ sizeOf b := by
  cases b with
  | mk val prop =>
    change 1 ≤ sizeOf (Subtype.mk val prop)
    rw [Subtype.mk.sizeOf_spec val prop]
    omega
end SizeOfPos

set_option linter.unusedVariables false in
/-- Number of `kdfExtract` (`hmac`) applications along the left (`salt`) spine of a symbolic term. -/
def saltDepth (b : Bytes) : Nat :=
  match h : b.view? KdfExtract.KdfExtract.SubF with
  | some v => saltDepth v.salt + 1
  | none => 0
termination_by sizeOf b
decreasing_by
  have hsz := Bytes.sizeOf_view KdfExtract.KdfExtract.SubF b; rw [h] at hsz
  have hpos : 1 ≤ sizeOf v.ikm := bytes_sizeOf_pos v.ikm
  change sizeOf v.salt + sizeOf v.ikm ≤ sizeOf b at hsz; omega

@[simp] theorem saltDepth_kdfExtract (salt ikm : Bytes) :
    saltDepth (kdfExtract salt ikm) = saltDepth salt + 1 := by
  conv => lhs; unfold saltDepth
  split
  · next v hv =>
    change (BytesView.pack ({ salt, ikm } : KdfExtract.KdfExtract.SubF Bytes)).view? KdfExtract.KdfExtract.SubF = some v at hv
    rw [BytesView.view_pack] at hv
    cases hv; rfl
  · next hv =>
    change (BytesView.pack ({ salt, ikm } : KdfExtract.KdfExtract.SubF Bytes)).view? KdfExtract.KdfExtract.SubF = none at hv
    rw [BytesView.view_pack] at hv
    cases hv

@[simp] theorem saltDepth_hmac (k m : Bytes) : saltDepth (hmac k m) = saltDepth k + 1 :=
  saltDepth_kdfExtract k m

@[simp] theorem saltDepth_hkdfBlock1 (prk info : Bytes) :
    saltDepth (hkdfBlock1 prk info) = saltDepth prk + 1 := saltDepth_kdfExtract prk _

@[simp] theorem saltDepth_hkdfBlock2 (prk info : Bytes) :
    saltDepth (hkdfBlock2 prk info) = saltDepth prk + 1 := saltDepth_kdfExtract prk _

@[simp] theorem saltDepth_hkdfBlock3 (prk info : Bytes) :
    saltDepth (hkdfBlock3 prk info) = saltDepth prk + 1 := saltDepth_kdfExtract prk _

@[simp] theorem saltDepth_kdfRk_fst (rk dhOut : Bytes) :
    saltDepth (kdfRk rk dhOut).1 = saltDepth rk + 2 := by simp [kdfRk]

@[simp] theorem saltDepth_kdfRk_snd (rk dhOut : Bytes) :
    saltDepth (kdfRk rk dhOut).2 = saltDepth rk + 2 := by simp [kdfRk]

@[simp] theorem saltDepth_createChain_fst (rk pk sk : Bytes) :
    saltDepth (createChain rk pk sk).1 = saltDepth rk + 2 := by simp [createChain, DY.X25519.agree]

@[simp] theorem saltDepth_createChain_snd (rk pk sk : Bytes) :
    saltDepth (createChain rk pk sk).2 = saltDepth rk + 2 := by simp [createChain, DY.X25519.agree]

@[simp] theorem saltDepth_kdfCk_fst (ck : Bytes) :
    saltDepth (kdfCk ck).1 = saltDepth ck + 1 := by simp [kdfCk]

@[simp] theorem saltDepth_kdfCk_snd (ck : Bytes) :
    saltDepth (kdfCk ck).2 = saltDepth ck + 1 := by simp [kdfCk]

@[simp] theorem saltDepth_chainKeyAt (ck : Bytes) : ∀ n : Nat,
    saltDepth (chainKeyAt ck n) = saltDepth ck + n
  | 0 => by simp [chainKeyAt]
  | n + 1 => by simp only [chainKeyAt, saltDepth_chainKeyAt _ n, saltDepth_kdfCk_fst]; omega

@[simp] theorem saltDepth_trMsgKeys_cipherKey (pqSalt seed : Bytes) :
    saltDepth (trMsgKeys pqSalt seed).cipherKey = saltDepth pqSalt + 2 := by simp [trMsgKeys]

@[simp] theorem saltDepth_trMsgKeys_macKey (pqSalt seed : Bytes) :
    saltDepth (trMsgKeys pqSalt seed).macKey = saltDepth pqSalt + 2 := by simp [trMsgKeys]

@[simp] theorem saltDepth_rnd (t n : Nat) : saltDepth (rnd t n) = 0 := by
  unfold saltDepth
  split
  · next v hv =>
    dsimp only [rnd] at hv
    rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hv
    cases hv
  · rfl

@[simp] theorem saltDepth_literalToBytes (b : ByteArray) :
    saltDepth (literalToBytes b) = 0 := by
  unfold saltDepth
  split
  · next v hv =>
    change (BytesView.pack ({ lit := b } : Literal.Literal.SubF Bytes)).view? KdfExtract.KdfExtract.SubF = some v at hv
    rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hv
    cases hv
  · rfl

@[simp] theorem saltDepth_lit (s : String) : saltDepth (lit s) = 0 :=
  saltDepth_literalToBytes _

@[simp] theorem saltDepth_litByte (b : UInt8) : saltDepth (litByte b) = 0 :=
  saltDepth_literalToBytes _

@[simp] theorem saltDepth_zeroSalt : saltDepth zeroSalt = 0 :=
  saltDepth_literalToBytes _

@[simp] theorem saltDepth_pqxdhKdf_rk (ikm : Bytes) :
    saltDepth (pqxdhKdf ikm).rk = 2 := by simp [pqxdhKdf]

@[simp] theorem saltDepth_pqxdhKdf_ck (ikm : Bytes) :
    saltDepth (pqxdhKdf ikm).ck = 2 := by simp [pqxdhKdf]

@[simp] theorem saltDepth_pqxdhKdf_pqr (ikm : Bytes) :
    saltDepth (pqxdhKdf ikm).pqr = 2 := by simp [pqxdhKdf]

theorem aliceOutOpt_keys_eq_pqxdhKdf (tr : ExecTrace) (ikA ikBPk spkPk pqPk : Bytes)
    (opkPk : Option Bytes) :
    ∃ ikm, (aliceOutOpt tr ikA ikBPk spkPk pqPk opkPk).keys = pqxdhKdf ikm :=
  ⟨_, rfl⟩

theorem keys1_eq_pqxdhKdf : ∃ ikm, keys1 = pqxdhKdf ikm :=
  aliceOutOpt_keys_eq_pqxdhKdf t4 ikA (dhPk ikB) (dhPk spkB) ( DY.PQKem.kemPk pqskB ) none

@[simp] theorem saltDepth_keys1_rk : saltDepth keys1.rk = 2 := by
  obtain ⟨ikm, h⟩ := keys1_eq_pqxdhKdf; rw [h]; exact saltDepth_pqxdhKdf_rk ikm

@[simp] theorem saltDepth_keys1_ck : saltDepth keys1.ck = 2 := by
  obtain ⟨ikm, h⟩ := keys1_eq_pqxdhKdf; rw [h]; exact saltDepth_pqxdhKdf_ck ikm

@[simp] theorem saltDepth_keys1_pqr : saltDepth keys1.pqr = 2 := by
  obtain ⟨ikm, h⟩ := keys1_eq_pqxdhKdf; rw [h]; exact saltDepth_pqxdhKdf_pqr ikm

@[simp] theorem saltDepth_stA0_rk : saltDepth stA0.rk = 4 := by
  change saltDepth (createChain keys1.rk (dhPk spkB) dhsA).1 = 4; simp

@[simp] theorem saltDepth_stA0_cks : saltDepth stA0.cks = 4 := by
  change saltDepth (createChain keys1.rk (dhPk spkB) dhsA).2 = 4; simp

@[simp] theorem saltDepth_stA1_rk : saltDepth stA1.rk = 4 := saltDepth_stA0_rk

@[simp] theorem saltDepth_stA1_cks : saltDepth stA1.cks = 5 := by
  change saltDepth (kdfCk stA0.cks).1 = 5; simp

@[simp] theorem saltDepth_stA2_rk : saltDepth stA2.rk = 4 := saltDepth_stA0_rk

@[simp] theorem saltDepth_stA2_cks : saltDepth stA2.cks = 6 := by
  change saltDepth (kdfCk stA1.cks).1 = 6; simp

@[simp] theorem saltDepth_stB00_rk : saltDepth stB00.rk = 2 := saltDepth_keys1_rk

@[simp] theorem saltDepth_stB00_cks : saltDepth stB00.cks = 2 := saltDepth_keys1_ck

@[simp] theorem saltDepth_stB1_rk : saltDepth stB1.rk = 6 := by
  change saltDepth (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).1 = 6
  simp

@[simp] theorem saltDepth_stB1_cks : saltDepth stB1.cks = 6 := by
  change saltDepth (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).2 = 6
  simp

private theorem trState_with_recv_spqr_rk (s : TRState) (recv : List RecvChain) (spqr : Bytes) :
    ({ s with recv, spqr } : TRState).rk = s.rk := by rfl

private theorem trState_with_recv_spqr_cks (s : TRState) (recv : List RecvChain) (spqr : Bytes) :
    ({ s with recv, spqr } : TRState).cks = s.cks := by rfl

private theorem encSt_rk (s : TRState) (coins : Bytes) : (encSt s coins).rk = s.rk := by rfl

@[simp] theorem saltDepth_stB2_rk : saltDepth stB2.rk = 6 := by
  unfold stB2; rw [trState_with_recv_spqr_rk]; exact saltDepth_stB1_rk

@[simp] theorem saltDepth_stB2_cks : saltDepth stB2.cks = 6 := by
  unfold stB2; rw [trState_with_recv_spqr_cks]; exact saltDepth_stB1_cks

@[simp] theorem saltDepth_stB3_rk : saltDepth stB3.rk = 6 := by
  unfold stB3; rw [encSt_rk]; exact saltDepth_stB2_rk

@[simp] theorem saltDepth_stB3_cks : saltDepth stB3.cks = 7 := by
  change saltDepth (kdfCk stB2.cks).1 = 7; simp

@[simp] theorem saltDepth_stA4_rk : saltDepth stA4.rk = 8 := by
  change saltDepth (createChain (createChain stA2.rk (dhPk dhsB1) dhsA).1 (dhPk dhsB1) dhsA2).1 = 8
  simp

@[simp] theorem saltDepth_stA4_cks : saltDepth stA4.cks = 8 := by
  change saltDepth (createChain (createChain stA2.rk (dhPk dhsB1) dhsA).1 (dhPk dhsB1) dhsA2).2 = 8
  simp

theorem saltDepth_le_of_rootDescends {rk₁ rk₂ : Bytes} (h : RootDescends rk₁ rk₂) :
    saltDepth rk₁ ≤ saltDepth rk₂ := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [saltDepth_createChain_fst]; omega

theorem eq_of_rootDescends_of_saltDepth_zero {rk₁ rk₂ : Bytes}
    (h : RootDescends rk₁ rk₂) (h0 : saltDepth rk₂ = 0) : rk₁ = rk₂ := by
  cases h with
  | refl => rfl
  | step _ => rw [saltDepth_createChain_fst] at h0; omega

theorem saltDepth_lt_of_rootDescends_ne {rk₁ rk₂ : Bytes}
    (h : RootDescends rk₁ rk₂) (hne : rk₂ ≠ rk₁) : saltDepth rk₁ + 2 ≤ saltDepth rk₂ := by
  cases h with
  | refl => exact False.elim (hne rfl)
  | step h' => have := saltDepth_le_of_rootDescends h'; rw [saltDepth_createChain_fst]; omega

theorem saltDepth_lt_of_derivesChain {rk ck : Bytes} (h : DerivesChain rk ck) :
    saltDepth rk + 2 ≤ saltDepth ck := by
  rcases h with ⟨rk', pk, sk, hdesc, rfl⟩
  have := saltDepth_le_of_rootDescends hdesc; rw [saltDepth_createChain_snd]; omega

theorem saltDepth_lt_of_derivesMsgKey {ck mk : Bytes} (h : DerivesMsgKey ck mk) :
    saltDepth ck + 1 ≤ saltDepth mk := by
  rcases h with ⟨steps, rfl⟩; rw [saltDepth_kdfCk_snd, saltDepth_chainKeyAt]; omega

def RkStep (rk rk' : Bytes) : Prop := ∃ pk sk, rk' = (createChain rk pk sk).1

inductive RkSteps : Nat → Bytes → Bytes → Prop
  | zero (rk : Bytes) : RkSteps 0 rk rk
  | succ {k : Nat} {rk₀ rk₁ rk₂ : Bytes} :
      RkSteps k rk₀ rk₁ → RkStep rk₁ rk₂ → RkSteps (k + 1) rk₀ rk₂

theorem RkSteps.step_one {rk₁ rk₂ : Bytes} (h : RkStep rk₁ rk₂) : RkSteps 1 rk₁ rk₂ :=
  RkSteps.succ (RkSteps.zero rk₁) h

theorem RkSteps.trans {k₁ k₂ : Nat} {rk₀ rk₁ rk₂ : Bytes}
    (h₁ : RkSteps k₁ rk₀ rk₁) (h₂ : RkSteps k₂ rk₁ rk₂) : RkSteps (k₁ + k₂) rk₀ rk₂ := by
  induction h₂ with
  | zero => simp [h₁]
  | succ _ hstep ih => rw [← Nat.add_assoc]; exact RkSteps.succ (ih h₁) hstep

theorem RkSteps.saltDepth_eq {k : Nat} {rk₀ rk : Bytes} (h : RkSteps k rk₀ rk) :
    saltDepth rk = saltDepth rk₀ + 2 * k := by
  induction h with
  | zero => simp
  | succ _ hstep ih =>
    rcases hstep with ⟨pk, sk, rfl⟩; simp only [saltDepth_createChain_fst, ih]; omega

theorem RkSteps.depth_unique {k₁ k₂ : Nat} {rk₀ rk : Bytes}
    (h₁ : RkSteps k₁ rk₀ rk) (h₂ : RkSteps k₂ rk₀ rk) : k₁ = k₂ := by
  have hd₁ := h₁.saltDepth_eq; have hd₂ := h₂.saltDepth_eq; omega

/-! ## Schedule injectivity -/

theorem kdfExtract_inj {s₁ m₁ s₂ m₂ : Bytes}
    (h : kdfExtract s₁ m₁ = kdfExtract s₂ m₂) : s₁ = s₂ ∧ m₁ = m₂ := by
  have hv := congrArg (fun b : Bytes => b.view? KdfExtract.KdfExtract.SubF) h
  dsimp only [KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hv
  rw [BytesView.view_pack, BytesView.view_pack] at hv
  injection hv with hv'; cases hv'; exact ⟨rfl, rfl⟩

theorem hmac_inj {k₁ m₁ k₂ m₂ : Bytes} (h : hmac k₁ m₁ = hmac k₂ m₂) : k₁ = k₂ ∧ m₁ = m₂ :=
  kdfExtract_inj h

theorem concat_inj {a₁ b₁ a₂ b₂ : Bytes} (h : concat a₁ b₁ = concat a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hv := congrArg (fun b : Bytes => b.view? Concat.Concat.SubF) h
  dsimp only [Concat.concat, Concat.CanConcat.concat] at hv
  rw [BytesView.view_pack, BytesView.view_pack] at hv
  injection hv with hv'; cases hv'; exact ⟨rfl, rfl⟩

theorem litByte_inj {b₁ b₂ : UInt8} (h : litByte b₁ = litByte b₂) : b₁ = b₂ := by
  have hm := congrArg bytesToLiteral h
  simp only [litByte, bytesToLiteral_literalToBytes, Option.some.injEq] at hm
  have hd : (#[b₁] : Array UInt8)[0]? = (#[b₂] : Array UInt8)[0]? :=
    congrArg (fun a : ByteArray => a.data[0]?) hm
  simpa using hd

theorem rnd_inj_pair {t₁ n₁ t₂ n₂ : Nat} (h : rnd t₁ n₁ = rnd t₂ n₂) : t₁ = t₂ ∧ n₁ = n₂ := by
  have hv := congrArg (fun b : Bytes => b.view? Random.Random) h
  simp only [rnd, BytesView.view_pack, Option.some.injEq, Random.Random.mk.injEq] at hv
  exact hv

theorem kdfCk_fst_inj {ck₁ ck₂ : Bytes} (h : (kdfCk ck₁).1 = (kdfCk ck₂).1) : ck₁ = ck₂ :=
  (hmac_inj h).1

theorem kdfCk_snd_inj {ck₁ ck₂ : Bytes} (h : (kdfCk ck₁).2 = (kdfCk ck₂).2) : ck₁ = ck₂ :=
  (hmac_inj h).1

theorem kdfCk_fst_ne_snd (ck₁ ck₂ : Bytes) : (kdfCk ck₁).1 ≠ (kdfCk ck₂).2 := by
  intro h; have hm := litByte_inj (hmac_inj h).2; revert hm; decide

theorem hkdfBlock1_inj {p₁ i₁ p₂ i₂ : Bytes} (h : hkdfBlock1 p₁ i₁ = hkdfBlock1 p₂ i₂) :
    p₁ = p₂ ∧ i₁ = i₂ := by
  obtain ⟨hp, hm⟩ := hmac_inj h
  exact ⟨hp, (concat_inj hm).1⟩

theorem hkdfBlock2_inj {p₁ i₁ p₂ i₂ : Bytes} (h : hkdfBlock2 p₁ i₁ = hkdfBlock2 p₂ i₂) :
    p₁ = p₂ ∧ i₁ = i₂ := by
  obtain ⟨hp, hm⟩ := hmac_inj h
  exact ⟨hp, (concat_inj (concat_inj hm).2).1⟩

theorem hkdfBlock3_inj {p₁ i₁ p₂ i₂ : Bytes} (h : hkdfBlock3 p₁ i₁ = hkdfBlock3 p₂ i₂) :
    p₁ = p₂ ∧ i₁ = i₂ := by
  obtain ⟨hp, hm⟩ := hmac_inj h
  exact ⟨hp, (concat_inj (concat_inj hm).2).1⟩

theorem kdfRk_fst_inj {rk₁ dh₁ rk₂ dh₂ : Bytes}
    (h : (kdfRk rk₁ dh₁).1 = (kdfRk rk₂ dh₂).1) : rk₁ = rk₂ ∧ dh₁ = dh₂ :=
  hmac_inj (hmac_inj h).1

theorem kdfRk_snd_inj {rk₁ dh₁ rk₂ dh₂ : Bytes}
    (h : (kdfRk rk₁ dh₁).2 = (kdfRk rk₂ dh₂).2) : rk₁ = rk₂ ∧ dh₁ = dh₂ :=
  hmac_inj (hmac_inj h).1

theorem createChain_fst_inj {rk₁ pk₁ sk₁ rk₂ pk₂ sk₂ : Bytes}
    (h : (createChain rk₁ pk₁ sk₁).1 = (createChain rk₂ pk₂ sk₂).1) : rk₁ = rk₂ :=
  (kdfRk_fst_inj h).1

theorem createChain_snd_inj {rk₁ pk₁ sk₁ rk₂ pk₂ sk₂ : Bytes}
    (h : (createChain rk₁ pk₁ sk₁).2 = (createChain rk₂ pk₂ sk₂).2) : rk₁ = rk₂ :=
  (kdfRk_snd_inj h).1

theorem chainKeyAt_add (ck : Bytes) : ∀ m n : Nat,
    chainKeyAt ck (m + n) = chainKeyAt (chainKeyAt ck m) n
  | 0, _ => by simp [chainKeyAt]
  | m + 1, n => by rw [Nat.add_right_comm, Nat.add_assoc]; exact chainKeyAt_add (kdfCk ck).1 m n

theorem chainKeyAt_succ_eq_kdfCk_fst (ck : Bytes) (n : Nat) :
    chainKeyAt ck (n + 1) = (kdfCk (chainKeyAt ck n)).1 := by rw [chainKeyAt_add ck n 1]; rfl

theorem chainKeyAt_inj {n : Nat} : ∀ {ck₁ ck₂ : Bytes},
    chainKeyAt ck₁ n = chainKeyAt ck₂ n → ck₁ = ck₂ := by
  induction n with
  | zero => intro _ _ h; exact h
  | succ _ ih => intro _ _ h; exact kdfCk_fst_inj (ih h)

theorem chainKeyAt_step_inj {ck : Bytes} {n₁ n₂ : Nat}
    (h : chainKeyAt ck n₁ = chainKeyAt ck n₂) : n₁ = n₂ := by
  have hd := congrArg saltDepth h; simp only [saltDepth_chainKeyAt] at hd; omega

theorem kdfCk_snd_chainKeyAt_inj {ck : Bytes} {n₁ n₂ : Nat}
    (h : (kdfCk (chainKeyAt ck n₁)).2 = (kdfCk (chainKeyAt ck n₂)).2) : n₁ = n₂ :=
  chainKeyAt_step_inj (kdfCk_snd_inj h)

theorem counter_le_of_chainKeyAt_derivation {ck₀ ck : Bytes} {ns n : UInt32} {d : Nat}
    (hck : ck = chainKeyAt ck₀ ns.toNat)
    (hmk : (kdfCk (chainKeyAt ck₀ n.toNat)).2 = (kdfCk (chainKeyAt ck d)).2) :
    n.toNat = ns.toNat + d ∧ ns ≤ n := by
  subst hck; rw [← chainKeyAt_add] at hmk
  have heq := kdfCk_snd_chainKeyAt_inj hmk
  exact ⟨heq, UInt32.le_iff_toNat_le.mpr (by omega)⟩

/-! ## Key-shape distinctness, `IsChainRoot`, and `RootDescends` -/

theorem hkdfBlock1_ne_hkdfBlock2 (p₁ i₁ p₂ i₂ : Bytes) :
    hkdfBlock1 p₁ i₁ ≠ hkdfBlock2 p₂ i₂ := by
  intro h
  obtain ⟨_, hm⟩ := hmac_inj h
  obtain ⟨_, hr⟩ := concat_inj hm
  exact (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hr).elim

theorem hkdfBlock1_ne_hkdfBlock3 (p₁ i₁ p₂ i₂ : Bytes) :
    hkdfBlock1 p₁ i₁ ≠ hkdfBlock3 p₂ i₂ := by
  intro h
  obtain ⟨_, hm⟩ := hmac_inj h
  obtain ⟨_, hr⟩ := concat_inj hm
  exact (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hr).elim

theorem hkdfBlock2_ne_hkdfBlock3 (p₁ i₁ p₂ i₂ : Bytes) :
    hkdfBlock2 p₁ i₁ ≠ hkdfBlock3 p₂ i₂ := by
  intro h
  obtain ⟨_, hm⟩ := hmac_inj h
  obtain ⟨_, hr⟩ := concat_inj hm
  obtain ⟨_, hb⟩ := concat_inj hr
  have hbyte := litByte_inj hb
  revert hbyte; decide

theorem hkdfBlock1_ne_kdfCk_fst (p i ck : Bytes) : hkdfBlock1 p i ≠ (kdfCk ck).1 := by
  intro h; obtain ⟨_, hm⟩ := hmac_inj h
  exact (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm).elim

theorem hkdfBlock1_ne_kdfCk_snd (p i ck : Bytes) : hkdfBlock1 p i ≠ (kdfCk ck).2 := by
  intro h; obtain ⟨_, hm⟩ := hmac_inj h
  exact (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm).elim

theorem hkdfBlock2_ne_kdfCk_fst (p i ck : Bytes) : hkdfBlock2 p i ≠ (kdfCk ck).1 := by
  intro h; obtain ⟨_, hm⟩ := hmac_inj h
  exact (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm).elim

theorem hkdfBlock2_ne_kdfCk_snd (p i ck : Bytes) : hkdfBlock2 p i ≠ (kdfCk ck).2 := by
  intro h; obtain ⟨_, hm⟩ := hmac_inj h
  exact (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm).elim

theorem hkdfBlock3_ne_kdfCk_fst (p i ck : Bytes) : hkdfBlock3 p i ≠ (kdfCk ck).1 := by
  intro h; obtain ⟨_, hm⟩ := hmac_inj h
  exact (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm).elim

theorem hkdfBlock3_ne_kdfCk_snd (p i ck : Bytes) : hkdfBlock3 p i ≠ (kdfCk ck).2 := by
  intro h; obtain ⟨_, hm⟩ := hmac_inj h
  exact (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm).elim

theorem kdfRk_fst_ne_snd (rk₁ dh₁ rk₂ dh₂ : Bytes) :
    (kdfRk rk₁ dh₁).1 ≠ (kdfRk rk₂ dh₂).2 :=
  hkdfBlock1_ne_hkdfBlock2 _ _ _ _

theorem createChain_fst_ne_snd (rk₁ pk₁ sk₁ rk₂ pk₂ sk₂ : Bytes) :
    (createChain rk₁ pk₁ sk₁).1 ≠ (createChain rk₂ pk₂ sk₂).2 :=
  hkdfBlock1_ne_hkdfBlock2 _ _ _ _

theorem createChain_fst_ne_kdfCk_fst (rk pk sk ck : Bytes) :
    (createChain rk pk sk).1 ≠ (kdfCk ck).1 :=
  hkdfBlock1_ne_kdfCk_fst _ _ _

theorem createChain_fst_ne_kdfCk_snd (rk pk sk ck : Bytes) :
    (createChain rk pk sk).1 ≠ (kdfCk ck).2 :=
  hkdfBlock1_ne_kdfCk_snd _ _ _

theorem createChain_snd_ne_kdfCk_fst (rk pk sk ck : Bytes) :
    (createChain rk pk sk).2 ≠ (kdfCk ck).1 :=
  hkdfBlock2_ne_kdfCk_fst _ _ _

theorem createChain_snd_ne_kdfCk_snd (rk pk sk ck : Bytes) :
    (createChain rk pk sk).2 ≠ (kdfCk ck).2 :=
  hkdfBlock2_ne_kdfCk_snd _ _ _

theorem whisperRatchet_ne_pqxdhLabel : lit "WhisperRatchet" ≠ pqxdhLabel := by
  intro h
  have hm := congrArg bytesToLiteral h
  simp only [pqxdhLabel, lit, bytesToLiteral_literalToBytes, Option.some.injEq,
    String.toUTF8_eq_toByteArray, String.toByteArray_inj] at hm
  revert hm; decide

theorem pqxdhKdf_rk_ne_ck (ikm₁ ikm₂ : Bytes) :
    (pqxdhKdf ikm₁).rk ≠ (pqxdhKdf ikm₂).ck :=
  hkdfBlock1_ne_hkdfBlock2 _ _ _ _

theorem pqxdhKdf_rk_ne_pqr (ikm₁ ikm₂ : Bytes) :
    (pqxdhKdf ikm₁).rk ≠ (pqxdhKdf ikm₂).pqr :=
  hkdfBlock1_ne_hkdfBlock3 _ _ _ _

theorem pqxdhKdf_ck_ne_pqr (ikm₁ ikm₂ : Bytes) :
    (pqxdhKdf ikm₁).ck ≠ (pqxdhKdf ikm₂).pqr :=
  hkdfBlock2_ne_hkdfBlock3 _ _ _ _

theorem pqxdhKdf_rk_ne_createChain_fst (ikm rk pk sk : Bytes) :
    (pqxdhKdf ikm).rk ≠ (createChain rk pk sk).1 := by
  intro h
  exact whisperRatchet_ne_pqxdhLabel (hkdfBlock1_inj h).2.symm

theorem pqxdhKdf_rk_ne_createChain_snd (ikm rk pk sk : Bytes) :
    (pqxdhKdf ikm).rk ≠ (createChain rk pk sk).2 :=
  hkdfBlock1_ne_hkdfBlock2 _ _ _ _

theorem pqxdhKdf_ck_ne_createChain_fst (ikm rk pk sk : Bytes) :
    (pqxdhKdf ikm).ck ≠ (createChain rk pk sk).1 :=
  (hkdfBlock1_ne_hkdfBlock2 _ _ _ _).symm

theorem pqxdhKdf_ck_ne_createChain_snd (ikm rk pk sk : Bytes) :
    (pqxdhKdf ikm).ck ≠ (createChain rk pk sk).2 := by
  intro h
  exact whisperRatchet_ne_pqxdhLabel (hkdfBlock2_inj h).2.symm

theorem pqxdhKdf_pqr_ne_createChain_fst (ikm rk pk sk : Bytes) :
    (pqxdhKdf ikm).pqr ≠ (createChain rk pk sk).1 :=
  (hkdfBlock1_ne_hkdfBlock3 _ _ _ _).symm

theorem pqxdhKdf_pqr_ne_createChain_snd (ikm rk pk sk : Bytes) :
    (pqxdhKdf ikm).pqr ≠ (createChain rk pk sk).2 :=
  (hkdfBlock2_ne_hkdfBlock3 _ _ _ _).symm

theorem pqxdhKdf_rk_ne_kdfCk_fst (ikm ck : Bytes) : (pqxdhKdf ikm).rk ≠ (kdfCk ck).1 :=
  hkdfBlock1_ne_kdfCk_fst _ _ _

theorem pqxdhKdf_rk_ne_kdfCk_snd (ikm ck : Bytes) : (pqxdhKdf ikm).rk ≠ (kdfCk ck).2 :=
  hkdfBlock1_ne_kdfCk_snd _ _ _

theorem pqxdhKdf_ck_ne_kdfCk_fst (ikm ck : Bytes) : (pqxdhKdf ikm).ck ≠ (kdfCk ck).1 :=
  hkdfBlock2_ne_kdfCk_fst _ _ _

theorem pqxdhKdf_ck_ne_kdfCk_snd (ikm ck : Bytes) : (pqxdhKdf ikm).ck ≠ (kdfCk ck).2 :=
  hkdfBlock2_ne_kdfCk_snd _ _ _

theorem pqxdhKdf_pqr_ne_kdfCk_fst (ikm ck : Bytes) : (pqxdhKdf ikm).pqr ≠ (kdfCk ck).1 :=
  hkdfBlock3_ne_kdfCk_fst _ _ _

theorem pqxdhKdf_pqr_ne_kdfCk_snd (ikm ck : Bytes) : (pqxdhKdf ikm).pqr ≠ (kdfCk ck).2 :=
  hkdfBlock3_ne_kdfCk_snd _ _ _

theorem rnd_ne_kdfExtract (t n : Nat) (s m : Bytes) : rnd t n ≠ kdfExtract s m := by
  intro h; have hd := congrArg saltDepth h; simp at hd

theorem rnd_ne_hmac (t n : Nat) (k m : Bytes) : rnd t n ≠ hmac k m :=
  rnd_ne_kdfExtract t n k m

theorem rnd_ne_createChain_fst (t n : Nat) (rk pk sk : Bytes) :
    rnd t n ≠ (createChain rk pk sk).1 :=
  rnd_ne_kdfExtract t n _ _

theorem rnd_ne_createChain_snd (t n : Nat) (rk pk sk : Bytes) :
    rnd t n ≠ (createChain rk pk sk).2 :=
  rnd_ne_kdfExtract t n _ _

theorem rnd_ne_kdfCk_fst (t n : Nat) (ck : Bytes) : rnd t n ≠ (kdfCk ck).1 :=
  rnd_ne_kdfExtract t n _ _

theorem rnd_ne_kdfCk_snd (t n : Nat) (ck : Bytes) : rnd t n ≠ (kdfCk ck).2 :=
  rnd_ne_kdfExtract t n _ _

theorem rnd_ne_pqxdhKdf_rk (t n : Nat) (ikm : Bytes) : rnd t n ≠ (pqxdhKdf ikm).rk :=
  rnd_ne_kdfExtract t n _ _

theorem rnd_ne_pqxdhKdf_ck (t n : Nat) (ikm : Bytes) : rnd t n ≠ (pqxdhKdf ikm).ck :=
  rnd_ne_kdfExtract t n _ _

theorem rnd_ne_pqxdhKdf_pqr (t n : Nat) (ikm : Bytes) : rnd t n ≠ (pqxdhKdf ikm).pqr :=
  rnd_ne_kdfExtract t n _ _

/-- A chain root `ck₀` is not the `.1` step of any `kdfCk`. -/
def IsChainRoot (ck₀ : Bytes) : Prop := ∀ x, ck₀ ≠ (kdfCk x).1

theorem isChainRoot_rnd (t n : Nat) : IsChainRoot (rnd t n) :=
  fun x => rnd_ne_kdfCk_fst t n x

theorem isChainRoot_createChain_fst (rk pk sk : Bytes) :
    IsChainRoot (createChain rk pk sk).1 :=
  fun x => createChain_fst_ne_kdfCk_fst rk pk sk x

theorem isChainRoot_createChain_snd (rk pk sk : Bytes) :
    IsChainRoot (createChain rk pk sk).2 :=
  fun x => createChain_snd_ne_kdfCk_fst rk pk sk x

theorem isChainRoot_pqxdhKdf_rk (ikm : Bytes) : IsChainRoot (pqxdhKdf ikm).rk :=
  fun x => pqxdhKdf_rk_ne_kdfCk_fst ikm x

theorem isChainRoot_pqxdhKdf_ck (ikm : Bytes) : IsChainRoot (pqxdhKdf ikm).ck :=
  fun x => pqxdhKdf_ck_ne_kdfCk_fst ikm x

theorem isChainRoot_pqxdhKdf_pqr (ikm : Bytes) : IsChainRoot (pqxdhKdf ikm).pqr :=
  fun x => pqxdhKdf_pqr_ne_kdfCk_fst ikm x

theorem isChainRoot_keys1_rk : IsChainRoot keys1.rk := by
  obtain ⟨ikm, h⟩ := keys1_eq_pqxdhKdf; rw [h]; exact isChainRoot_pqxdhKdf_rk ikm

theorem isChainRoot_keys1_ck : IsChainRoot keys1.ck := by
  obtain ⟨ikm, h⟩ := keys1_eq_pqxdhKdf; rw [h]; exact isChainRoot_pqxdhKdf_ck ikm

theorem isChainRoot_keys1_pqr : IsChainRoot keys1.pqr := by
  obtain ⟨ikm, h⟩ := keys1_eq_pqxdhKdf; rw [h]; exact isChainRoot_pqxdhKdf_pqr ikm

theorem chainKeyAt_root_inj {ck₁ ck₂ : Bytes} (h₁ : IsChainRoot ck₁) (h₂ : IsChainRoot ck₂) :
    ∀ {n₁ n₂ : Nat}, chainKeyAt ck₁ n₁ = chainKeyAt ck₂ n₂ → ck₁ = ck₂ ∧ n₁ = n₂
  | 0, 0, h => ⟨h, rfl⟩
  | 0, n₂ + 1, h => by rw [chainKeyAt_succ_eq_kdfCk_fst] at h; exact False.elim (h₁ _ h)
  | n₁ + 1, 0, h => by rw [chainKeyAt_succ_eq_kdfCk_fst] at h; exact False.elim (h₂ _ h.symm)
  | n₁ + 1, n₂ + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst, chainKeyAt_succ_eq_kdfCk_fst] at h
    obtain ⟨rfl, rfl⟩ := chainKeyAt_root_inj h₁ h₂ (kdfCk_fst_inj h); exact ⟨rfl, rfl⟩

theorem not_chainKeyAt_eq_of_root {R c : Bytes} {n m : Nat} (hR : IsChainRoot R)
    (hd : saltDepth c < saltDepth R) (h : chainKeyAt R n = chainKeyAt c m) : False := by
  have h1 := congrArg saltDepth h
  rw [saltDepth_chainKeyAt, saltDepth_chainKeyAt] at h1
  obtain ⟨k, hk⟩ : ∃ k, m = (k + 1) + n := ⟨m - n - 1, by omega⟩
  rw [hk, chainKeyAt_add c (k + 1) n] at h
  have h2 := chainKeyAt_inj h
  rw [chainKeyAt_succ_eq_kdfCk_fst] at h2
  exact hR _ h2

theorem eq_of_derivesMsgKey_of_isChainRoot {ck ck₀ : Bytes} (hroot : IsChainRoot ck₀)
    (h : DerivesMsgKey ck (kdfCk ck₀).2) : ck = ck₀ := by
  rcases h with ⟨steps, hmk⟩
  have hck := kdfCk_snd_inj hmk.symm
  cases steps with
  | zero => exact hck
  | succ n =>
    rw [chainKeyAt_succ_eq_kdfCk_fst] at hck
    exact False.elim (hroot _ hck.symm)

theorem eq_of_derivesMsgKey_createChain_zero {ck rk₀ pk₀ sk₀ : Bytes}
    (h : DerivesMsgKey ck (kdfCk (createChain rk₀ pk₀ sk₀).2).2) :
    ck = (createChain rk₀ pk₀ sk₀).2 :=
  eq_of_derivesMsgKey_of_isChainRoot (isChainRoot_createChain_snd rk₀ pk₀ sk₀) h

theorem eq_of_rootDescends_of_ne_createChain_fst {rk target : Bytes}
    (h : RootDescends rk target)
    (hne : ∀ rk' pk sk, target ≠ (createChain rk' pk sk).1) : rk = target := by
  generalize htarget : target = t at h
  cases h with
  | refl => rfl
  | step _ => exact False.elim (hne _ _ _ htarget)

theorem eq_of_rootDescends_pqxdhKdf_rk {rk ikm : Bytes}
    (h : RootDescends rk (pqxdhKdf ikm).rk) : rk = (pqxdhKdf ikm).rk :=
  eq_of_rootDescends_of_ne_createChain_fst h (pqxdhKdf_rk_ne_createChain_fst ikm)

theorem eq_of_rootDescends_pqxdhKdf_ck {rk ikm : Bytes}
    (h : RootDescends rk (pqxdhKdf ikm).ck) : rk = (pqxdhKdf ikm).ck :=
  eq_of_rootDescends_of_ne_createChain_fst h (pqxdhKdf_ck_ne_createChain_fst ikm)

theorem eq_of_rootDescends_pqxdhKdf_pqr {rk ikm : Bytes}
    (h : RootDescends rk (pqxdhKdf ikm).pqr) : rk = (pqxdhKdf ikm).pqr :=
  eq_of_rootDescends_of_ne_createChain_fst h (pqxdhKdf_pqr_ne_createChain_fst ikm)

theorem eq_of_rootDescends_keys1_rk {rk : Bytes} (h : RootDescends rk keys1.rk) :
    rk = keys1.rk := by
  obtain ⟨ikm, heq⟩ := keys1_eq_pqxdhKdf
  rw [heq] at h ⊢
  exact eq_of_rootDescends_pqxdhKdf_rk h

theorem eq_of_rootDescends_keys1_ck {rk : Bytes} (h : RootDescends rk keys1.ck) :
    rk = keys1.ck := by
  obtain ⟨ikm, heq⟩ := keys1_eq_pqxdhKdf
  rw [heq] at h ⊢
  exact eq_of_rootDescends_pqxdhKdf_ck h

theorem eq_of_rootDescends_rnd {rk : Bytes} {t n : Nat} (h : RootDescends rk (rnd t n)) :
    rk = rnd t n :=
  eq_of_rootDescends_of_saltDepth_zero h (saltDepth_rnd t n)

theorem eq_of_rootDescends_createChain_snd {rk rk₀ pk₀ sk₀ : Bytes}
    (h : RootDescends rk (createChain rk₀ pk₀ sk₀).2) :
    rk = (createChain rk₀ pk₀ sk₀).2 := by
  generalize htarget : (createChain rk₀ pk₀ sk₀).2 = target at h
  cases h with
  | refl => rfl
  | step _ => exact False.elim (createChain_fst_ne_snd _ _ _ rk₀ pk₀ sk₀ htarget.symm)

theorem eq_or_rootDescends_of_createChain_fst {rk rk₀ pk₀ sk₀ : Bytes}
    (h : RootDescends rk (createChain rk₀ pk₀ sk₀).1) :
    rk = (createChain rk₀ pk₀ sk₀).1 ∨ RootDescends rk rk₀ := by
  generalize htarget : (createChain rk₀ pk₀ sk₀).1 = target at h
  cases h with
  | refl => exact .inl rfl
  | step h' =>
    have heq := createChain_fst_inj htarget.symm
    subst heq
    exact .inr h'


/-! ## Test predicate bundle -/

/-- Bundle of trace predicates (`MessageKey`, `AttackerKnows`, `Compromised`, `HonestDH`) allowing
mutant-tightness tests to perturb individual disjuncts. -/
structure TestTracePredicates where
  MessageKey : Bytes → Prop
  AttackerKnows : Bytes → Prop
  Compromised : Bytes → Prop
  HonestDH : Bytes → Prop

def mkTestTracePredicates (tr : ExecTrace) (Knows : Bytes → Prop := fun t => t.AttackerKnows tr) :
    TestTracePredicates where
  MessageKey seed := ∃ pqSalt, MessageSeedUsed tr seed pqSalt
  AttackerKnows seed := ∃ pqSalt, MessageSeedUsed tr seed pqSalt ∧ TRKeyKnown Knows seed pqSalt
  Compromised := CompromisedKey tr
  HonestDH := HonestDHKey tr

def FSQueryP (P : TestTracePredicates) : Prop :=
  ∀ mk : Bytes,
    P.MessageKey mk →
    P.AttackerKnows mk →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk)

def PCSQueryP (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk : Bytes,
    P.MessageKey mk →
    P.AttackerKnows mk →
    P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem fsQuery_iff_test (tr : ExecTrace) (Knows : Bytes → Prop) :
    FSQuery tr Knows ↔ FSQueryP (mkTestTracePredicates tr Knows) := by
  constructor
  · intro h mk _ ⟨pqSalt, hseed, hkn⟩
    exact h mk pqSalt hseed hkn
  · intro h mk pqSalt hseed hkn
    exact h mk ⟨pqSalt, hseed⟩ ⟨pqSalt, hseed, hkn⟩

theorem pcsQuery_iff_test (tr : ExecTrace) (Knows : Bytes → Prop) :
    PCSQuery tr Knows ↔ PCSQueryP (mkTestTracePredicates tr Knows) := by
  constructor
  · intro h mk rk_prev ownSk peerSk _ ⟨pqSalt, hseed, hkn⟩ hOwn hPeer hGen
    exact h mk pqSalt rk_prev ownSk peerSk hseed hkn hOwn hPeer hGen
  · intro h mk pqSalt rk_prev ownSk peerSk hseed hkn hOwn hPeer hGen
    exact h mk rk_prev ownSk peerSk ⟨pqSalt, hseed⟩ ⟨pqSalt, hseed, hkn⟩ hOwn hPeer hGen

/-! ## No-compromise reduction and `ExposedKey` helpers -/

/-- Disjunction of the five `TREvent.Exposed*` events for `k`. -/
def ExposedKey (tr : ExecTrace) (k : Bytes) : Prop :=
  (∃ s i, tr.EventLogged (TREvent.ExposedRK s k i)) ∨
  (∃ s i, tr.EventLogged (TREvent.ExposedDHs s k i)) ∨
  (∃ s ns i, tr.EventLogged (TREvent.ExposedCKs s k ns i)) ∨
  (∃ s nr i, tr.EventLogged (TREvent.ExposedCKr s k nr i)) ∨
  (∃ s n i, tr.EventLogged (TREvent.ExposedMK s k n i))

theorem exposedKey_imp_compromised {tr : ExecTrace} {Knows : Bytes → Prop} {k : Bytes}
    (h : ExposedKey tr k) : (mkTestTracePredicates tr Knows).Compromised k := by
  rcases h with h | h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl h))))

theorem not_thm7Excuse_of_noCompromise {tr : ExecTrace} (hnc : NoCompromise tr)
    {b : Participant} {ikB spk pqpk : Bytes} {i : Nat} :
    ¬ AliceHandshakeWasCompromised b ikB spk pqpk i tr := by
  rcases hnc with ⟨hIK, _hSPK, _hPQ, _hOPK, hDH, _hKEM⟩
  rintro (⟨j, hj, _⟩ | ⟨j, hj, _⟩)
  · exact hIK b ikB ⟨j, hj⟩
  · exact hDH ⟨j, hj⟩

theorem not_thm9Excuse_of_noCompromise {tr : ExecTrace} (hnc : NoCompromise tr)
    {b a : Participant} {ikB ikA spk pqpk : Bytes} {opk : Option Bytes} {i : Nat} :
    ¬ BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr := by
  rcases hnc with ⟨hIK, hSPK, _hPQ, _hOPK, hDH, _hKEM⟩
  rintro ((⟨j, hj, _⟩ | ⟨j, hj, _⟩ | ⟨j, hj, _⟩) | ⟨hI, _⟩ | ⟨hD, _⟩)
  · exact hIK a ikA ⟨j, hj⟩
  · exact hSPK b spk ⟨j, hj⟩
  · exact hDH ⟨j, hj⟩
  · exact hIK b ikB hI
  · exact hDH hD

theorem not_handshakeExcusedAt_of_noCompromise {tr : ExecTrace} (hnc : NoCompromise tr)
    {j : Nat} : ¬ HandshakeWasCompromisedAt tr j := by
  rintro (⟨_, _, _, _, _, _, _, _, _, _, _, h7⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, h9⟩)
  · exact not_thm7Excuse_of_noCompromise hnc h7
  · exact not_thm9Excuse_of_noCompromise hnc h9

theorem not_handshakeRootCompromised_of_noCompromise {tr : ExecTrace} (hnc : NoCompromise tr)
    {k : Bytes} : ¬ HandshakeRootCompromised tr k := by
  rintro ⟨⟨keys, j, hhk, hkb⟩, hall⟩
  exact not_handshakeExcusedAt_of_noCompromise hnc (hall keys j hhk hkb)

theorem compromised_iff_exposedKey_of_noCompromise {tr : ExecTrace} {Knows : Bytes → Prop}
    (hnc : NoCompromise tr) {k : Bytes} :
    (mkTestTracePredicates tr Knows).Compromised k ↔ ExposedKey tr k := by
  constructor
  · rintro (h | h | h | h | h | hhs | ⟨_, hdh⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))
    · exact False.elim (not_handshakeRootCompromised_of_noCompromise hnc hhs)
    · exact False.elim (hnc.2.2.2.2.1 hdh)
  · exact exposedKey_imp_compromised

theorem compromised_iff_exposedKey_of_evIdx {tr : ExecTrace} {Knows : Bytes → Prop}
    (hno : evIdx tr isCompromise = []) {k : Bytes} :
    (mkTestTracePredicates tr Knows).Compromised k ↔ ExposedKey tr k :=
  compromised_iff_exposedKey_of_noCompromise (noCompromise_of_evIdx hno)

theorem not_exposedKey_of_trEvIdx {tr : ExecTrace}
    (hno : trEvIdx tr isAnyTRExposure = []) {k : Bytes} :
    ¬ ExposedKey tr k := by
  rintro (⟨s, i, h⟩ | ⟨s, i, h⟩ | ⟨s, ns, i, h⟩ | ⟨s, nr, i, h⟩ | ⟨s, n, i, h⟩)
  · exact not_tr_logged hno (e := .ExposedRK s k i) rfl h
  · exact not_tr_logged hno (e := .ExposedDHs s k i) rfl h
  · exact not_tr_logged hno (e := .ExposedCKs s k ns i) rfl h
  · exact not_tr_logged hno (e := .ExposedCKr s k nr i) rfl h
  · exact not_tr_logged hno (e := .ExposedMK s k n i) rfl h

theorem not_compromised_of_evIdx {tr : ExecTrace} {Knows : Bytes → Prop}
    (hnoP : evIdx tr isCompromise = [])
    (hnoT : trEvIdx tr isAnyTRExposure = []) {k : Bytes} :
    ¬ (mkTestTracePredicates tr Knows).Compromised k := by
  rw [compromised_iff_exposedKey_of_evIdx hnoP]
  exact not_exposedKey_of_trEvIdx hnoT

/-! ## Trace-peeling helpers for `ExposedKey` -/

abbrev TREntry := ProtocolEvent.ExecEntryT TREvent

theorem proj_inj {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

theorem at?_append_cases {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    {tr : ExecTrace} {e : E1} {x : E2} {i : Nat}
    (h : ((tr.append e).at? i : Option E2) = some x) :
    (i < tr.length ∧ (tr.at? i : Option E2) = some x) ∨
    (i = tr.length ∧
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = some x) := by
  have hlt : i < (tr.append e).length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := E2) (tr.append e) i
    rw [h] at this; exact this
  have hlen : (tr.append e).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rcases (show i < tr.length ∨ i = tr.length by omega) with hi | rfl
  · rw [at?_append_of_lt tr e hi] at h; exact .inl ⟨hi, h⟩
  · simp only [Trace.at?, hlt, ↓reduceDIte] at h
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte] at h; exact .inr ⟨rfl, h⟩

theorem eventLogged_append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    {ev : TREvent} (h : (tr.append e).EventLogged ev) : tr.EventLogged ev := by
  rcases h with ⟨i, hi⟩
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
  rcases at?_append_cases hi with ⟨_, hi⟩ | ⟨_, hp⟩
  · exact ⟨i, by rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact hi⟩
  · rw [hnone] at hp; cases hp

theorem eventLogged_append_ev {tr : ExecTrace} {ev₀ ev : TREvent}
    (h : (tr.append (EvT ev₀)).EventLogged ev) : tr.EventLogged ev ∨ ev₀ = ev := by
  rcases h with ⟨i, hi⟩
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
  rcases at?_append_cases hi with ⟨_, hi⟩ | ⟨_, hp⟩
  · exact .inl ⟨i, by rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact hi⟩
  · rw [proj_inj] at hp; injection hp with hp; injection hp with hp; exact .inr hp

def exposedKeyOf : TREvent → Option Bytes
  | .ExposedRK _ k _ | .ExposedDHs _ k _ | .ExposedCKs _ k _ _
  | .ExposedCKr _ k _ _ | .ExposedMK _ k _ _ => some k
  | _ => none

theorem exposedKey_append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E} {k : Bytes}
    (h : ExposedKey (tr.append e) k)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) =
      none := by rfl) :
    ExposedKey tr k := by
  rcases h with ⟨s, i, h⟩ | ⟨s, i, h⟩ | ⟨s, ns, i, h⟩ | ⟨s, nr, i, h⟩ | ⟨s, n, i, h⟩
  · exact .inl ⟨s, i, eventLogged_append_other hnone h⟩
  · exact .inr (.inl ⟨s, i, eventLogged_append_other hnone h⟩)
  · exact .inr (.inr (.inl ⟨s, ns, i, eventLogged_append_other hnone h⟩))
  · exact .inr (.inr (.inr (.inl ⟨s, nr, i, eventLogged_append_other hnone h⟩)))
  · exact .inr (.inr (.inr (.inr ⟨s, n, i, eventLogged_append_other hnone h⟩)))

theorem exposedKey_append_ev {tr : ExecTrace} {ev₀ : TREvent} {k : Bytes}
    (h : ExposedKey (tr.append (EvT ev₀)) k) :
    ExposedKey tr k ∨ exposedKeyOf ev₀ = some k := by
  rcases h with ⟨s, i, h⟩ | ⟨s, i, h⟩ | ⟨s, ns, i, h⟩ | ⟨s, nr, i, h⟩ | ⟨s, n, i, h⟩
  · rcases eventLogged_append_ev h with h | rfl; exact .inl (.inl ⟨s, i, h⟩); exact .inr rfl
  · rcases eventLogged_append_ev h with h | rfl; exact .inl (.inr (.inl ⟨s, i, h⟩)); exact .inr rfl
  · rcases eventLogged_append_ev h with h | rfl
    · exact .inl (.inr (.inr (.inl ⟨s, ns, i, h⟩)))
    · exact .inr rfl
  · rcases eventLogged_append_ev h with h | rfl
    · exact .inl (.inr (.inr (.inr (.inl ⟨s, nr, i, h⟩))))
    · exact .inr rfl
  · rcases eventLogged_append_ev h with h | rfl
    · exact .inl (.inr (.inr (.inr (.inr ⟨s, n, i, h⟩))))
    · exact .inr rfl

theorem exposedKey_append_ev_nonExpose {tr : ExecTrace} {ev₀ : TREvent}
    (hno : exposedKeyOf ev₀ = none) {k : Bytes}
    (h : ExposedKey (tr.append (EvT ev₀)) k) :
    ExposedKey tr k := by
  rcases exposedKey_append_ev h with h | hk; exact h; rw [hno] at hk; cases hk

theorem exposedKey_append_expose {tr : ExecTrace} {ev₀ : TREvent} {k₀ k : Bytes}
    (h : ExposedKey ((tr.append (EvT ev₀)).append (NetE k₀)) k)
    (hexp : exposedKeyOf ev₀ = some k₀ := by rfl) :
    ExposedKey tr k ∨ k = k₀ := by
  rcases exposedKey_append_ev (exposedKey_append_other h) with h | hk
  · exact .inl h
  · rw [hexp] at hk; injection hk with hk; exact .inr hk.symm

theorem exposedKey_encTr {tr : ExecTrace} {me : Participant} {stH : Nat}
    {st : TRState} {pq k : Bytes}
    (h : ExposedKey (encTr tr me stH st pq) k) :
    ExposedKey tr k := by
  dsimp only [encTr] at h
  have h := exposedKey_append_other (exposedKey_append_other h)
  have h := exposedKey_append_ev_nonExpose rfl (exposedKey_append_ev_nonExpose rfl h)
  exact exposedKey_append_other (exposedKey_append_other (exposedKey_append_other h))

end Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon
