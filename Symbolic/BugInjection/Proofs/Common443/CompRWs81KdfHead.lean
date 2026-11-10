/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompRWs81KdfHead
open ByteSpecs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompRNbscTable Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj
def padKey (k : HwBytes) : HwBytes := k ++ List.replicate (64 - k.length) 0
theorem kblk_eq_map_padKey (k : HwBytes) (pad : BitVec 8) : kblk k pad = (padKey k).map (· ^^^ pad) := rfl
theorem kblk_inj_padKey {k₁ k₂ : HwBytes} (pad : BitVec 8) (h : kblk k₁ pad = kblk k₂ pad) : padKey k₁ = padKey k₂ := by
  have h' := congrArg (List.map (· ^^^ pad)) h
  rw [kblk_eq_map_padKey, kblk_eq_map_padKey, map_xor_xor, map_xor_xor] at h'; exact h'
theorem hmacWith_padKey_inj {k₁ k₂ m₁ m₂ : HwBytes} (hk₁ : k₁.length ≤ 64) (hk₂ : k₂.length ≤ 64) (h₁ : (hmacWith F0 k₁ m₁).take 4 ≠ compTag4) (heq : hmacWith F0 k₁ m₁ = hmacWith F0 k₂ m₂) : padKey k₁ = padKey k₂ ∧ m₁ = m₂ := by
  have hin₁ := hmac_inner_untagged k₁ m₁ hk₁ h₁; rw [hmacWith_eq k₁ m₁ hk₁] at h₁ heq; rw [hmacWith_eq k₂ m₂ hk₂] at heq; have ho := sha256With_inj_of_untagged h₁ heq
  obtain ⟨-, hino⟩ :=
    List.append_inj ho (by rw [kblk_length k₁ 0x5c hk₁, kblk_length k₂ 0x5c hk₂])
  have hi := sha256With_inj_of_untagged hin₁ hino
  obtain ⟨hki, hm⟩ :=
    List.append_inj hi (by rw [kblk_length k₁ 0x36 hk₁, kblk_length k₂ 0x36 hk₂])
  exact ⟨kblk_inj_padKey 0x36 hki, hm⟩
theorem eq_of_padKey_eq {k₁ k₂ : HwBytes} (hl : k₁.length = k₂.length) (h : padKey k₁ = padKey k₂) : k₁ = k₂ := List.append_inj_left h hl
theorem four_le_of_take4 {a : HwBytes} (h : a.take 4 = compTag4) : 4 ≤ a.length := by have := congrArg List.length h; simp only [List.length_take, compTag4, List.length_cons, List.length_nil] at this; omega
theorem not_onTab_of_opad {s : ShaState} {b : HwBytes} (hb : b.take 4 = compTag4Opad) : ¬ OnTab s b := by intro h; apply h; unfold compSha256; simp only [hb, beq_self_eq_true, Bool.or_true, ↓reduceIte]; exact compDefaultSha256_take4 _ _
theorem take4_kblk {k : HwBytes} (pad : BitVec 8) (hk : 4 ≤ k.length) : (kblk k pad).take 4 = (k.take 4).map (· ^^^ pad) := by
  rw [kblk_eq_map_padKey, padKey, List.map_append,
    List.take_append_of_le_length (by simp only [List.length_map]; exact hk)]
  simp
theorem hmac_key_untagged (k m : HwBytes) (hk : k.length ≤ 64) (h : (hmacWith F0 k m).take 4 ≠ compTag4) : k.take 4 ≠ compTag4 := by intro hkt; exact not_onTab_of_opad (by rw [take4_kblk 0x5c (four_le_of_take4 hkt), hkt]; decide) (hmac_outer_first_onTab k m hk h)
theorem chunks64_cons_of_le {x : List (BitVec 8)} (hx : 64 ≤ x.length) : chunks64 x = x.take 64 :: chunks64 (x.drop 64) := by
  conv_lhs => rw [← List.take_append_drop 64 x]
  exact chunks64_append64 _ _ (by simp only [List.length_take]; omega)
theorem padTail64_length_ge (m : HwBytes) : 64 ≤ (padTail64 m).length := by have h1 := sha256Pad_length_mod (List.replicate 64 (0 : BitVec 8) ++ m); rw [sha256Pad_append64 _ _ (by simp only [List.length_replicate])] at h1; have h2 : m.length + 9 ≤ (padTail64 m).length := (by simp only [padTail64, List.length_append, List.length_cons, List.length_nil, List.length_replicate, toBEBytes_length]; omega); simp only [List.length_append, List.length_replicate] at h1; omega
theorem take4_padTail64 {m : HwBytes} (hm : 4 ≤ m.length) : (padTail64 m).take 4 = m.take 4 := by simp only [padTail64, List.append_assoc]; exact List.take_append_of_le_length hm
theorem hmac_msg_untagged (k m : HwBytes) (hk : k.length ≤ 64) (h : (hmacWith F0 k m).take 4 ≠ compTag4) : m.take 4 ≠ compTag4 := by
  intro hmt; have h4 := four_le_of_take4 hmt; have hin := hmac_inner_untagged k m hk h; have hx := kblk_length k 0x36 hk; have hpl := padTail64_length_ge m
  have hon := onTab_of_sha256With_untagged _ hin [kblk k 0x36] ((padTail64 m).take 64)
    (chunks64 ((padTail64 m).drop 64))
    (by rw [sha256Pad_append64 _ _ hx, chunks64_append64 _ _ hx, chunks64_cons_of_le hpl]; rfl)
  refine hT2_0 _ _ ?_ hon; rw [toBEBytes_tagW, List.take_take, show min 4 64 = 4 from rfl, take4_padTail64 h4, hmt]
theorem take4_append_left {a b : HwBytes} (h : (a ++ b).take 4 ≠ compTag4) : a.take 4 ≠ compTag4 := by intro ha; exact h (by rw [List.take_append_of_le_length (four_le_of_take4 ha), ha])
section UPar
variable {S : Sem} {g : Ghost}
def UShapeAgree (S : Sem) (g : Ghost) (u₁ u₂ : DY.Bytes) : Prop := gamma compI0 S g u₁ = gamma compI0 S g u₂ → (gamma compI0 S g u₁).take 4 ≠ compTag4 → (gamma' compI0 S g u₁).shape = (gamma' compI0 S g u₂).shape
theorem UShapeAgree.symm {u₁ u₂ : DY.Bytes} (h : UShapeAgree S g u₁ u₂) : UShapeAgree S g u₂ u₁ := fun he hu => (h he.symm (he ▸ hu)).symm
theorem UShapeAgree.of_shapeAgree {u₁ u₂ : DY.Bytes} (h : ShapeAgree S g u₁ u₂) : UShapeAgree S g u₁ u₂ := fun he _ => h he
theorem UShapeAgree.shapeAgree {u₁ u₂ : DY.Bytes} (h : UShapeAgree S g u₁ u₂) (hu : (gamma compI0 S g u₁).take 4 ≠ compTag4) : ShapeAgree S g u₁ u₂ :=
  fun he => h he hu
end UPar
inductive UPar (S : Sem) (g : Ghost) : DY.Bytes → DY.Bytes → Prop
  | base {u₁ u₂ : DY.Bytes} (h : UShapeAgree S g u₁ u₂) : UPar S g u₁ u₂
  | kdf {k₁ k₂ m₁ m₂ : DY.Bytes}
      (hk₁ : (gamma compI0 S g k₁).length ≤ 64) (hk₂ : (gamma compI0 S g k₂).length ≤ 64)
      (hlen : padKey (gamma compI0 S g k₁) = padKey (gamma compI0 S g k₂) → (gamma compI0 S g k₁).length = (gamma compI0 S g k₂).length)
      (hK : UPar S g k₁ k₂) (hM : UPar S g m₁ m₂) :
      UPar S g (DY.KdfExtract.kdfExtract k₁ m₁) (DY.KdfExtract.kdfExtract k₂ m₂)
  | concat {a₁ a₂ b₁ b₂ : DY.Bytes}
      (hl : (gamma compI0 S g a₁).length = (gamma compI0 S g a₂).length)
      (hA : UPar S g a₁ a₂)
      (hbu : (gamma compI0 S g (DY.Concat.concat a₁ b₁)).take 4 ≠ compTag4 → (gamma compI0 S g b₁).take 4 ≠ compTag4)
      (hB : UPar S g b₁ b₂) :
      UPar S g (DY.Concat.concat a₁ b₁) (DY.Concat.concat a₂ b₂)
  | symm {u₁ u₂ : DY.Bytes} (h : UPar S g u₁ u₂) : UPar S g u₂ u₁
theorem UPar.ushapeAgree {S : Sem} {g : Ghost} {u₁ u₂ : DY.Bytes} (h : UPar S g u₁ u₂) : UShapeAgree S g u₁ u₂ := by
  induction h with
  | base h => exact h
  | kdf hk₁ hk₂ hlen _ _ ihK ihM =>
    intro he hu; rw [gamma_kdfExtract, gamma_kdfExtract] at he; rw [gamma_kdfExtract] at hu; obtain ⟨hp, hm⟩ := hmacWith_padKey_inj hk₁ hk₂ hu he; have hkeq := eq_of_padKey_eq (hlen hp) hp; rw [shape_kdfExtract, shape_kdfExtract, ihK hkeq (hmac_key_untagged _ _ hk₁ hu), ihM hm (hmac_msg_untagged _ _ hk₁ hu)]
  | concat hl _ hbu _ ihA ihB =>
    intro he hu; have hu' := hu; rw [gamma_concat_eq] at hu'; rw [gamma_concat_eq, gamma_concat_eq] at he; obtain ⟨h1, h2⟩ := List.append_inj he hl; rw [shape_concat, shape_concat, ihA h1 (take4_append_left hu'), ihB h2 (hbu hu)]
  | symm _ ih => exact ih.symm
theorem UPar.shapeAgree {S : Sem} {g : Ghost} {u₁ u₂ : DY.Bytes} (h : UPar S g u₁ u₂) (hu : (gamma compI0 S g u₁).take 4 ≠ compTag4) : ShapeAgree S g u₁ u₂ := h.ushapeAgree.shapeAgree hu
theorem UPar.of_shapeAgree {S : Sem} {g : Ghost} {u₁ u₂ : DY.Bytes} (h : ShapeAgree S g u₁ u₂) : UPar S g u₁ u₂ := .base (UShapeAgree.of_shapeAgree h)
section KdfHead
variable {S : Sem} {g : Ghost}
theorem upar_kdf_head {k₁ m₁ u : DY.Bytes} (hpart : (∃ k₂ m₂, u = DY.KdfExtract.kdfExtract k₂ m₂ ∧ (gamma compI0 S g k₁).length ≤ 64 ∧ (gamma compI0 S g k₂).length ≤ 64 ∧ (padKey (gamma compI0 S g k₁) = padKey (gamma compI0 S g k₂) → (gamma compI0 S g k₁).length = (gamma compI0 S g k₂).length) ∧ UPar S g k₁ k₂ ∧ UPar S g m₁ m₂) ∨ (∃ s, u = DY.DiffieHellman.dhPk s) ∨ (∃ p s, u = (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)) ∨ KdfFree (gamma compI0 S g u) ∨ (gamma compI0 S g u).length ≠ 32 ∨ (gamma' compI0 S g (DY.KdfExtract.kdfExtract k₁ m₁)).shape = (gamma' compI0 S g u).shape) : UPar S g (DY.KdfExtract.kdfExtract k₁ m₁) u := by
  rcases hpart with ⟨k₂, m₂, rfl, hk₁, hk₂, hlen, hK, hM⟩ | ⟨s, rfl⟩ | ⟨p, s, rfl⟩ | hf | hl | hs
  · exact .kdf hk₁ hk₂ hlen hK hM
  · exact .of_shapeAgree (shapeAgree_kdf_dhPk _ _ _)
  · exact .of_shapeAgree (shapeAgree_kdf_dh _ _ _ _)
  · exact .of_shapeAgree (shapeAgree_kdf_of_kdfFree hf)
  · exact .of_shapeAgree (shapeAgree_kdf_of_length hl)
  · exact .of_shapeAgree (shapeAgree_of_shape_eq hs)
end KdfHead
end Symbolic.BugInjection.Proofs.Common443.CompRWs81KdfHead
