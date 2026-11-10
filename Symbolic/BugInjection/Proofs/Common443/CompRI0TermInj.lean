/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
public import Symbolic.BugInjection.Proofs.Common443.CompRI0Census
public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj
open ByteSpecs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompRNbscTable Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
section Unfold
variable (i : ExternInterpretation) (S : Sem) (g : Ghost)
theorem shape_kdfExtract (k m : DY.Bytes) : (gamma' i S g (DY.KdfExtract.kdfExtract k m)).shape = ({ salt := (gamma' i S g k).shape, ikm := (gamma' i S g m).shape } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack := by
  unfold gamma'
  show ((({salt := k, ikm := m} : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (gAll i S g)).shape = _
  rw [DY.Bytes.rec_eq (gKdf0 i) (gAll i S g)]; rfl
theorem gamma_kdfExtract (k m : DY.Bytes) : gamma i S g (DY.KdfExtract.kdfExtract k m) = hmacWith (sha256CompressFunction i) (gamma i S g k) (gamma i S g m) := by
  unfold gamma gamma'
  show ((({salt := k, ikm := m} : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (gAll i S g)).val = _
  rw [DY.Bytes.rec_eq (gKdf0 i) (gAll i S g)]; rfl
theorem shape_concat (a b : DY.Bytes) : (gamma' i S g (DY.Concat.concat a b)).shape = ({ lhs := (gamma' i S g a).shape, rhs := (gamma' i S g b).shape } : DY.Concat.Concat.SubF DY.Bytes).pack := by
  unfold gamma'
  show ((({lhs := a, rhs := b} : DY.Concat.Concat.SubF DY.Bytes).pack).rec (gAll i S g)).shape = _
  rw [DY.Bytes.rec_eq gConcat0 (gAll i S g)]; rfl
end Unfold
def ShapeAgree (S : Sem) (g : Ghost) (u₁ u₂ : DY.Bytes) : Prop := gamma compI0 S g u₁ = gamma compI0 S g u₂ → (gamma' compI0 S g u₁).shape = (gamma' compI0 S g u₂).shape
section Steps
variable {S : Sem} {g : Ghost}
theorem ShapeAgree.symm {u₁ u₂ : DY.Bytes} (h : ShapeAgree S g u₁ u₂) : ShapeAgree S g u₂ u₁ := fun he => (h he.symm).symm
theorem shapeAgree_of_gamma_ne {u₁ u₂ : DY.Bytes} (h : gamma compI0 S g u₁ ≠ gamma compI0 S g u₂) : ShapeAgree S g u₁ u₂ := fun he => absurd he h
theorem shapeAgree_of_length_ne {u₁ u₂ : DY.Bytes} (h : (gamma compI0 S g u₁).length ≠ (gamma compI0 S g u₂).length) : ShapeAgree S g u₁ u₂ :=
  fun he => absurd (congrArg List.length he) h
theorem shapeAgree_of_shape_eq {u₁ u₂ : DY.Bytes} (h : (gamma' compI0 S g u₁).shape = (gamma' compI0 S g u₂).shape) : ShapeAgree S g u₁ u₂ := fun _ => h
theorem gamma_kdfExtract_length (k m : DY.Bytes) : (gamma compI0 S g (DY.KdfExtract.kdfExtract k m)).length = 32 := by rw [gamma_kdfExtract]; exact hmacWith_length _ _ _
end Steps
def LitShaped (S : Sem) (g : Ghost) (u : DY.Bytes) : Prop := (gamma' compI0 S g u).shape = litOf (gamma compI0 S g u)
inductive Par (S : Sem) (g : Ghost) : DY.Bytes → DY.Bytes → Prop
  | refl (u : DY.Bytes) : Par S g u u
  | sep {u₁ u₂ : DY.Bytes} (h : gamma compI0 S g u₁ ≠ gamma compI0 S g u₂) : Par S g u₁ u₂
  | shape {u₁ u₂ : DY.Bytes}
      (h : (gamma' compI0 S g u₁).shape = (gamma' compI0 S g u₂).shape) : Par S g u₁ u₂
  | lit {u₁ u₂ : DY.Bytes} (h₁ : LitShaped S g u₁) (h₂ : LitShaped S g u₂) : Par S g u₁ u₂
  | rand {t₁ t₂ z₁ z₂ : Nat} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
      (hσ : g.σ t₁ z₁ = g.σ t₂ z₂ → t₁ = t₂ ∧ z₁ = z₂) :
      Par S g (randTerm t₁ z₁) (randTerm t₂ z₂)
  | kdf {k₁ k₂ m₁ m₂ : DY.Bytes}
      (hl : (gamma compI0 S g k₁).length = (gamma compI0 S g k₂).length)
      (hk : (gamma compI0 S g k₁).length ≤ 64)
      (hu : (gamma compI0 S g (DY.KdfExtract.kdfExtract k₁ m₁)).take 4 ≠ compTag4)
      (hK : Par S g k₁ k₂) (hM : Par S g m₁ m₂) :
      Par S g (DY.KdfExtract.kdfExtract k₁ m₁) (DY.KdfExtract.kdfExtract k₂ m₂)
  | concat {a₁ a₂ b₁ b₂ : DY.Bytes}
      (hl : (gamma compI0 S g a₁).length = (gamma compI0 S g a₂).length)
      (hA : Par S g a₁ a₂) (hB : Par S g b₁ b₂) :
      Par S g (DY.Concat.concat a₁ b₁) (DY.Concat.concat a₂ b₂)
  | dhPk {s₁ s₂ : DY.Bytes}
      (hc : gamma compI0 S g (DY.DiffieHellman.dhPk s₁) = gamma compI0 S g (DY.DiffieHellman.dhPk s₂) → gamma compI0 S g s₁ = gamma compI0 S g s₂)
      (hS : Par S g s₁ s₂) :
      Par S g (DY.DiffieHellman.dhPk s₁) (DY.DiffieHellman.dhPk s₂)
  | dh {p₁ p₂ s₁ s₂ : DY.Bytes}
      (hc : gamma compI0 S g (({ pk := p₁, sk := s₁ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) = gamma compI0 S g (({ pk := p₂, sk := s₂ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) → gamma compI0 S g p₁ = gamma compI0 S g p₂ ∧ gamma compI0 S g s₁ = gamma compI0 S g s₂)
      (hP : Par S g p₁ p₂) (hS : Par S g s₁ s₂) :
      Par S g (({ pk := p₁, sk := s₁ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) (({ pk := p₂, sk := s₂ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)
  | symEnc {k₁ k₂ v₁ v₂ m₁ m₂ : DY.Bytes}
      (hc : gamma compI0 S g (DY.SymEnc.symEnc k₁ v₁ m₁) = gamma compI0 S g (DY.SymEnc.symEnc k₂ v₂ m₂) → gamma compI0 S g k₁ = gamma compI0 S g k₂ ∧ gamma compI0 S g v₁ = gamma compI0 S g v₂ ∧ gamma compI0 S g m₁ = gamma compI0 S g m₂)
      (hK : Par S g k₁ k₂) (hV : Par S g v₁ v₂) (hM : Par S g m₁ m₂) :
      Par S g (DY.SymEnc.symEnc k₁ v₁ m₁) (DY.SymEnc.symEnc k₂ v₂ m₂)
  | trunc8 {a₁ a₂ : DY.Bytes}
      (hc : gamma compI0 S g (DY.Trunc.trunc8 a₁) = gamma compI0 S g (DY.Trunc.trunc8 a₂) → gamma compI0 S g a₁ = gamma compI0 S g a₂)
      (hA : Par S g a₁ a₂) :
      Par S g (DY.Trunc.trunc8 a₁) (DY.Trunc.trunc8 a₂)
  | symm {u₁ u₂ : DY.Bytes} (h : Par S g u₁ u₂) : Par S g u₂ u₁
theorem shapeAgree_kdf_of_length {S : Sem} {g : Ghost} {k m u : DY.Bytes} (h : (gamma compI0 S g u).length ≠ 32) : ShapeAgree S g (DY.KdfExtract.kdfExtract k m) u :=
  shapeAgree_of_length_ne (by rw [gamma_kdfExtract_length]; exact Ne.symm h)
def rowDigests : List HwBytes := compSha256Rows.map fun r => digestOfOut r.2.2
theorem sha256With_tag_or_row (m : HwBytes) : (sha256With F0 m).take 4 = compTag4 ∨ sha256With F0 m ∈ rowDigests := by
  by_cases h : (sha256With F0 m).take 4 = compTag4
  · exact Or.inl h
  · right
    rcases eq_nil_or_snoc (chunks64 (sha256Pad m)) with h0 | ⟨L', b, hL⟩
    · exact absurd h0 (chunks64_sha256Pad_ne_nil m)
    · have hon : OnTab (L'.foldl F0 sha256IV) b := onTab_of_sha256With_untagged m h L' b [] hL; obtain ⟨r, hr, _, _, hF⟩ := row_step hon
      have hsha : sha256With F0 m = digestOfOut r.2.2 := by unfold sha256With digestOfOut; rw [hL, List.foldl_append, List.foldl_cons, List.foldl_nil, hF]
      rw [hsha, rowDigests]; exact List.mem_map.mpr ⟨r, hr, rfl⟩
theorem hmacWith_tag_or_row (k m : HwBytes) : (hmacWith F0 k m).take 4 = compTag4 ∨ hmacWith F0 k m ∈ rowDigests := by unfold hmacWith; exact sha256With_tag_or_row _
theorem gamma_kdfExtract_tag_or_row {S : Sem} {g : Ghost} (k m : DY.Bytes) : (gamma compI0 S g (DY.KdfExtract.kdfExtract k m)).take 4 = compTag4 ∨ gamma compI0 S g (DY.KdfExtract.kdfExtract k m) ∈ rowDigests := by rw [gamma_kdfExtract]; exact hmacWith_tag_or_row _ _
def KdfFree (v : HwBytes) : Prop := v.take 4 ≠ compTag4 ∧ v ∉ rowDigests
instance (v : HwBytes) : Decidable (KdfFree v) := by unfold KdfFree; infer_instance
theorem gamma_kdfExtract_ne_of_kdfFree {S : Sem} {g : Ghost} {k m : DY.Bytes} {v : HwBytes} (hv : KdfFree v) : gamma compI0 S g (DY.KdfExtract.kdfExtract k m) ≠ v := by
  intro he
  rcases gamma_kdfExtract_tag_or_row (S := S) (g := g) k m with h | h
  · exact hv.1 (he ▸ h)
  · exact hv.2 (he ▸ h)
theorem shapeAgree_kdf_of_kdfFree {S : Sem} {g : Ghost} {k m u : DY.Bytes} (hu : KdfFree (gamma compI0 S g u)) : ShapeAgree S g (DY.KdfExtract.kdfExtract k m) u := shapeAgree_of_gamma_ne (gamma_kdfExtract_ne_of_kdfFree hu)
def x25519Vals : List HwBytes := (List.finRange 12).map compPubOfIdx ++
    ((List.finRange 12).flatMap fun i => (List.finRange 12).map fun j => compDhByIdx i j) ++
    [compDefaultPub, compDefaultDh, CompRI0Census.zeroDh]
theorem compLookupPub_mem (s : HwBytes) : compLookupPub s ∈ x25519Vals := by
  rcases CompRI0Census.compLookupPub_cases s with h | ⟨i, h⟩
  · rw [h]; simp [x25519Vals]
  · rw [h]; unfold x25519Vals; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
theorem compLookupDh_mem (s p : HwBytes) : compLookupDh s p ∈ x25519Vals := by
  rcases CompRI0Census.compLookupDh_cases s p with ⟨_, h⟩ | ⟨_, i, j, _, _, h⟩ | ⟨_, _, h⟩
  · rw [h]; simp [x25519Vals]
  · rw [h]; unfold x25519Vals; exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩))
  · rw [h]; simp [x25519Vals]
theorem x25519Vals_untagged : ∀ v ∈ x25519Vals, v.take 4 ≠ compTag4 := by decide +kernel
theorem x25519Vals_not_row : ∀ v ∈ x25519Vals, v ∉ rowDigests := by decide +kernel
theorem kdfFree_of_mem_x25519Vals {v : HwBytes} (hv : v ∈ x25519Vals) : KdfFree v := ⟨x25519Vals_untagged v hv, x25519Vals_not_row v hv⟩
theorem shapeAgree_kdf_dhPk {S : Sem} {g : Ghost} (k m s : DY.Bytes) : ShapeAgree S g (DY.KdfExtract.kdfExtract k m) (DY.DiffieHellman.dhPk s) :=
  shapeAgree_kdf_of_kdfFree (by
    rw [gamma_dhPk_compI0]; exact kdfFree_of_mem_x25519Vals (compLookupPub_mem _))
theorem shapeAgree_kdf_dh {S : Sem} {g : Ghost} (k m p s : DY.Bytes) : ShapeAgree S g (DY.KdfExtract.kdfExtract k m) (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) :=
  shapeAgree_kdf_of_kdfFree (by
    rw [gamma_dh_pack_compI0]; exact kdfFree_of_mem_x25519Vals (compLookupDh_mem _ _))
theorem x25519Vals_length : ∀ v ∈ x25519Vals, v.length = 32 := by decide +kernel
theorem gamma_trunc8_length_le {S : Sem} {g : Ghost} (a : DY.Bytes) : (gamma compI0 S g (DY.Trunc.trunc8 a)).length ≤ 8 := by rw [gamma_trunc8_eq]; exact List.length_take_le 8 _
theorem shapeAgree_trunc8_of_len32 {S : Sem} {g : Ghost} {a u : DY.Bytes} (hu : (gamma compI0 S g u).length = 32) : ShapeAgree S g (DY.Trunc.trunc8 a) u :=
  shapeAgree_of_length_ne (by have := gamma_trunc8_length_le (S := S) (g := g) a; omega)
end Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj
