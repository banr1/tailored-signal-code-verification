/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Stage1Trials -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineIkm
public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkHole
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.DiffieHellman
import Symbolic.Specifications.Model.EquationalTheory.Kem
import ProofLib.Lemmas
import Symbolic.Proofs.Swarm.CREF.GammaBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Memo-Descent Helpers and DH-Hole Shape Injectivity

Provides child-to-parent memo-descent lemmas and proves DH-hole shape injectivity across distinct
32-byte random secrets (`eq_of_dh_randTerm32_shape_eq_of_ne`), opposite-parity `kdfRk` steps, and
opposite-role PQXDH input key materials (`eq_of_shape_eq_of_spineRk`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY.DiffieHellman
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (chainKeyAt kdfCk kdfRk hmac hkdfBlock1 hkdfBlock2)
open DY.Libsignal.PQXDH (pqxdhIkm pqxdhKdf)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF (gamma'_pack_concat gamma'_pack_kdf)

/-! ## Child-to-parent memo descent -/

theorem memo_mem_of_node_child
    {v : HwBytes} {self sh : DY.Bytes} {cs : List ConcretizedTerm} {c : ConcretizedTerm}
    {e : DY.Bytes × DY.Bytes × HwBytes}
    (hc : c ∈ cs) (he : e ∈ c.memo) :
    e ∈ (node v self sh cs).memo := by
  unfold node
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c, hc, he⟩)

theorem memo_mem_of_concat_left (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (a b : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g a).memo) :
    e ∈ (gamma' i S g (DY.Concat.concat a b)).memo := by
  have hp := gamma'_pack_concat i S g { lhs := a, rhs := b }
  change e ∈ (gamma' i S g ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack).memo
  rw [hp]; exact memo_mem_of_node_child List.mem_cons_self he

theorem memo_mem_of_concat_right (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (a b : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g b).memo) :
    e ∈ (gamma' i S g (DY.Concat.concat a b)).memo := by
  have hp := gamma'_pack_concat i S g { lhs := a, rhs := b }
  change e ∈ (gamma' i S g ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack).memo
  rw [hp]; exact memo_mem_of_node_child (List.mem_cons_of_mem _ (List.mem_singleton_self _)) he

theorem memo_mem_of_kdfExtract_left (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt ikm : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g salt).memo) :
    e ∈ (gamma' i S g (DY.KdfExtract.kdfExtract salt ikm)).memo := by
  have hp := gamma'_pack_kdf i S g { salt := salt, ikm := ikm }
  change e ∈ (gamma' i S g ({ salt := salt, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).memo
  rw [hp]; exact memo_mem_of_node_child List.mem_cons_self he

theorem memo_mem_of_kdfExtract_right (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt ikm : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g ikm).memo) :
    e ∈ (gamma' i S g (DY.KdfExtract.kdfExtract salt ikm)).memo := by
  have hp := gamma'_pack_kdf i S g { salt := salt, ikm := ikm }
  change e ∈ (gamma' i S g ({ salt := salt, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).memo
  rw [hp]; exact memo_mem_of_node_child (List.mem_cons_of_mem _ (List.mem_singleton_self _)) he

theorem memo_mem_of_hmac_left (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (k m : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g k).memo) :
    e ∈ (gamma' i S g (hmac k m)).memo := memo_mem_of_kdfExtract_left i S g k m he

theorem memo_mem_of_hmac_right (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (k m : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g m).memo) :
    e ∈ (gamma' i S g (hmac k m)).memo := memo_mem_of_kdfExtract_right i S g k m he

theorem memo_mem_of_hkdfBlock1_prk (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (prk info : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g prk).memo) :
    e ∈ (gamma' i S g (hkdfBlock1 prk info)).memo := memo_mem_of_hmac_left i S g prk _ he

theorem memo_mem_of_hkdfBlock2_prk (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (prk info : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g prk).memo) :
    e ∈ (gamma' i S g (hkdfBlock2 prk info)).memo := memo_mem_of_hmac_left i S g prk _ he

theorem memo_mem_of_kdfCk_fst (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ck : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g ck).memo) :
    e ∈ (gamma' i S g (kdfCk ck).1).memo := memo_mem_of_hmac_left i S g ck _ he

theorem memo_mem_of_kdfCk_snd (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ck : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g ck).memo) :
    e ∈ (gamma' i S g (kdfCk ck).2).memo := memo_mem_of_hmac_left i S g ck _ he

theorem memo_mem_of_chainKeyAt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {ck : DY.Bytes} {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g ck).memo) :
    ∀ n : Nat, e ∈ (gamma' i S g (chainKeyAt ck n)).memo
  | 0 => he
  | n + 1 => memo_mem_of_chainKeyAt i S g (memo_mem_of_kdfCk_fst i S g ck he) n

theorem memo_mem_of_kdfRk_fst_rk (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (rk dhOut : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g rk).memo) :
    e ∈ (gamma' i S g (kdfRk rk dhOut).1).memo :=
  memo_mem_of_hkdfBlock1_prk i S g _ _ (memo_mem_of_kdfExtract_left i S g rk dhOut he)

theorem memo_mem_of_kdfRk_snd_rk (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (rk dhOut : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g rk).memo) :
    e ∈ (gamma' i S g (kdfRk rk dhOut).2).memo :=
  memo_mem_of_hkdfBlock2_prk i S g _ _ (memo_mem_of_kdfExtract_left i S g rk dhOut he)

/-! ## DH-hole shape injectivity for distinct `randTerm 32` secrets -/

unseal DY.Bytes in
private instance subDhCL (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDh i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem dhPk_injective {sk₁ sk₂ : DY.Bytes} (h : dhPk sk₁ = dhPk sk₂) : sk₁ = sk₂ := by
  have h1 := congrArg (fun u : DY.Bytes => u.view? DY.DiffieHellman.DhPk.SubF) h
  change DY.Bytes.view? (({ sk := sk₁ } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack) DY.DiffieHellman.DhPk.SubF =
    DY.Bytes.view? (({ sk := sk₂ } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack) DY.DiffieHellman.DhPk.SubF at h1
  rw [DY.BytesView.view_pack, DY.BytesView.view_pack, Option.some.injEq] at h1
  exact congrArg DY.DiffieHellman.DhPk.SubF.sk h1

theorem randTerm32_injective {t₁ t₂ : Nat} (h : randTerm t₁ 32 = randTerm t₂ 32) : t₁ = t₂ := by
  have h1 := congrArg (fun u : DY.Bytes => u.view? DY.Random.Random) h
  change DY.Bytes.view? (({ timestamp := t₁, size := 32 } : DY.Random.Random DY.Bytes).pack) DY.Random.Random =
    DY.Bytes.view? (({ timestamp := t₂, size := 32 } : DY.Random.Random DY.Bytes).pack) DY.Random.Random at h1
  rw [DY.BytesView.view_pack, DY.BytesView.view_pack, Option.some.injEq] at h1
  exact congrArg DY.Random.Random.timestamp h1

theorem eq_randTerm32_of_shape_eq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (t : Nat)
    {u : DY.Bytes} (hsh : (gamma' i S g (randTerm t 32)).shape = (gamma' i S g u).shape) :
    randTerm t 32 = u := by
  have hdh : (gamma' i S g (dhPk (randTerm t 32))).shape = (gamma' i S g (dhPk u)).shape := by
    rw [Symbolic.Swarm.CREF.TR.G1.shape_dhPk_tr, Symbolic.Swarm.CREF.TR.G1.shape_dhPk_tr, hsh]
  exact dhPk_injective (Symbolic.Swarm.CREF.TR.G1.eq_dhPk_randTerm32_of_shape_eq i S g t hdh)

theorem shape_dh_pack_inj (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) {p₁ s₁ p₂ s₂ : DY.Bytes}
    (h : (gamma' i S g (({ pk := p₁, sk := s₁ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)).shape =
         (gamma' i S g (({ pk := p₂, sk := s₂ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)).shape) :
    (gamma' i S g p₁).shape = (gamma' i S g p₂).shape ∧ (gamma' i S g s₁).shape = (gamma' i S g s₂).shape := by
  have h1 : (gamma' i S g (({ pk := p₁, sk := s₁ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)).shape =
      ({ pk := (gamma' i S g p₁).shape, sk := (gamma' i S g s₁).shape } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
    unfold gamma'; show ((({ pk := p₁, sk := s₁ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape = _
    rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g)]; rfl
  have h2 : (gamma' i S g (({ pk := p₂, sk := s₂ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)).shape =
      ({ pk := (gamma' i S g p₂).shape, sk := (gamma' i S g s₂).shape } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
    unfold gamma'; show ((({ pk := p₂, sk := s₂ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape = _
    rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g)]; rfl
  rw [h1, h2] at h
  have hv := congrArg (fun u : DY.Bytes => u.view? DY.DiffieHellman.Dh.SubF) h
  change DY.Bytes.view? (({ pk := (gamma' i S g p₁).shape, sk := (gamma' i S g s₁).shape } :
      DY.DiffieHellman.Dh.SubF DY.Bytes).pack) DY.DiffieHellman.Dh.SubF =
    DY.Bytes.view? (({ pk := (gamma' i S g p₂).shape, sk := (gamma' i S g s₂).shape } :
      DY.DiffieHellman.Dh.SubF DY.Bytes).pack) DY.DiffieHellman.Dh.SubF at hv
  rw [DY.BytesView.view_pack, DY.BytesView.view_pack, Option.some.injEq] at hv
  exact ⟨congrArg DY.DiffieHellman.Dh.SubF.pk hv, congrArg DY.DiffieHellman.Dh.SubF.sk hv⟩

theorem dh_eq_pack_and_or (pk' sk : DY.Bytes) :
    ∃ P S_k : DY.Bytes, dh pk' sk = ({ pk := P, sk := S_k } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack ∧
      (S_k = sk ∨ P = dhPk sk) := by
  dsimp only [CanDH.dh]
  cases pk'.view? DY.DiffieHellman.DhPk.SubF with
  | none => exact ⟨pk', sk, rfl, Or.inl rfl⟩
  | some y =>
    by_cases hle : sk ≤ y.sk <;> simp only [hle, ↓reduceIte]
    · exact ⟨dhPk y.sk, sk, rfl, Or.inl rfl⟩
    · exact ⟨dhPk sk, y.sk, rfl, Or.inr rfl⟩

/-- Shape equality of DH terms with distinct 32-byte random secret keys implies term equality. -/
theorem eq_of_dh_randTerm32_shape_eq_of_ne (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pk₁' pk₂' : DY.Bytes) (t₁ t₂ : Nat) (hne : t₁ ≠ t₂)
    (hsh : (gamma' i S g (dh pk₁' (randTerm t₁ 32))).shape =
           (gamma' i S g (dh pk₂' (randTerm t₂ 32))).shape) :
    dh pk₁' (randTerm t₁ 32) = dh pk₂' (randTerm t₂ 32) := by
  obtain ⟨P₁, S₁, hd₁, hor₁⟩ := dh_eq_pack_and_or pk₁' (randTerm t₁ 32)
  obtain ⟨P₂, S₂, hd₂, hor₂⟩ := dh_eq_pack_and_or pk₂' (randTerm t₂ 32)
  rw [hd₁, hd₂] at hsh ⊢
  obtain ⟨hP, hS⟩ := shape_dh_pack_inj i S g hsh
  rcases hor₁ with rfl | rfl
  · have hS₂ : randTerm t₁ 32 = S₂ := eq_randTerm32_of_shape_eq i S g t₁ hS
    rcases hor₂ with rfl | rfl
    · exact False.elim (hne (randTerm32_injective hS₂))
    · rw [Symbolic.Swarm.CREF.TR.G1.eq_dhPk_randTerm32_of_shape_eq i S g t₂ hP.symm, hS₂]
  · have hP₂ : dhPk (randTerm t₁ 32) = P₂ := Symbolic.Swarm.CREF.TR.G1.eq_dhPk_randTerm32_of_shape_eq i S g t₁ hP
    rcases hor₂ with rfl | rfl
    · rw [hP₂, eq_randTerm32_of_shape_eq i S g t₂ hS.symm]
    · exact False.elim (hne (randTerm32_injective (dhPk_injective hP₂)))

theorem dh_pack_inj {p₁ s₁ p₂ s₂ : DY.Bytes}
    (h : (({ pk := p₁, sk := s₁ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) =
         (({ pk := p₂, sk := s₂ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)) : p₁ = p₂ ∧ s₁ = s₂ := by
  have hv := congrArg (fun u : DY.Bytes => u.view? DY.DiffieHellman.Dh.SubF) h
  change DY.Bytes.view? (({ pk := p₁, sk := s₁ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) DY.DiffieHellman.Dh.SubF =
    DY.Bytes.view? (({ pk := p₂, sk := s₂ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) DY.DiffieHellman.Dh.SubF at hv
  rw [DY.BytesView.view_pack, DY.BytesView.view_pack, Option.some.injEq] at hv
  exact ⟨congrArg DY.DiffieHellman.Dh.SubF.pk hv, congrArg DY.DiffieHellman.Dh.SubF.sk hv⟩

theorem dh_pair_cases (pk' sk_a sk_b : DY.Bytes) :
    (pk'.view? DY.DiffieHellman.DhPk.SubF = none ∧
      dh pk' sk_a = (({ pk := pk', sk := sk_a } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) ∧
      dh pk' sk_b = (({ pk := pk', sk := sk_b } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)) ∨
    ∃ sk2 : DY.Bytes,
      dh pk' sk_a = (if sk_a ≤ sk2 then (({ pk := dhPk sk2, sk := sk_a } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)
        else (({ pk := dhPk sk_a, sk := sk2 } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)) ∧
      dh pk' sk_b = (if sk_b ≤ sk2 then (({ pk := dhPk sk2, sk := sk_b } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)
        else (({ pk := dhPk sk_b, sk := sk2 } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)) := by
  dsimp only [CanDH.dh]; cases pk'.view? DY.DiffieHellman.DhPk.SubF with
  | none => exact Or.inl ⟨rfl, rfl, rfl⟩
  | some y => exact Or.inr ⟨y.sk, rfl, rfl⟩

theorem dh_randTerm32_self_of_dh_eq_of_ne {pk₁' pk₀' : DY.Bytes} {t₀ t₁ : Nat} (hne₀ : t₀ ≠ t₁)
    (hprev : dh pk₁' (randTerm t₀ 32) = dh pk₀' (randTerm t₁ 32)) :
    dh pk₁' (randTerm t₁ 32) = (({ pk := dhPk (randTerm t₁ 32), sk := randTerm t₁ 32 } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by
  obtain ⟨P₀, S₀, hd₀, hor₀⟩ := dh_eq_pack_and_or pk₀' (randTerm t₁ 32); rw [hd₀] at hprev
  rcases dh_pair_cases pk₁' (randTerm t₀ 32) (randTerm t₁ 32) with ⟨hview, hd_a, _⟩ | ⟨sk2, hd_a, hd_b⟩
  · rw [hd_a] at hprev; obtain ⟨hP, hS⟩ := dh_pack_inj hprev
    rcases hor₀ with rfl | rfl
    · exact False.elim (hne₀ (randTerm32_injective hS))
    · rw [hP] at hview
      change DY.Bytes.view? (({ sk := randTerm t₁ 32 } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack) DY.DiffieHellman.DhPk.SubF = none at hview
      rw [DY.BytesView.view_pack] at hview; cases hview
  · rw [hd_a] at hprev; rw [hd_b]
    have hy : sk2 = randTerm t₁ 32 := by
      by_cases hle₀ : randTerm t₀ 32 ≤ sk2 <;> simp only [hle₀, ↓reduceIte] at hprev <;>
        obtain ⟨hP, hS⟩ := dh_pack_inj hprev <;> rcases hor₀ with rfl | rfl
      · exact False.elim (hne₀ (randTerm32_injective hS))
      · exact dhPk_injective hP
      · exact hS
      · exact False.elim (hne₀ (randTerm32_injective (dhPk_injective hP)))
    rw [hy]; by_cases hle₁ : randTerm t₁ 32 ≤ randTerm t₁ 32 <;> simp only [hle₁, ↓reduceIte]

theorem eq_of_dh_randTerm32_shape_eq_of_prev_eq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pk₁' pk₂' pk₀' : DY.Bytes) (t₀ t₁ t₂ : Nat) (hne₀ : t₀ ≠ t₁)
    (hprev : dh pk₁' (randTerm t₀ 32) = dh pk₀' (randTerm t₂ 32))
    (hsh : (gamma' i S g (dh pk₁' (randTerm t₁ 32))).shape = (gamma' i S g (dh pk₂' (randTerm t₂ 32))).shape) :
    dh pk₁' (randTerm t₁ 32) = dh pk₂' (randTerm t₂ 32) := by
  by_cases hne : t₁ ≠ t₂
  · exact eq_of_dh_randTerm32_shape_eq_of_ne i S g pk₁' pk₂' t₁ t₂ hne hsh
  · have heq : t₁ = t₂ := Classical.not_not.mp hne; subst heq
    obtain ⟨P₂, S₂, hd₂, _⟩ := dh_eq_pack_and_or pk₂' (randTerm t₁ 32)
    rw [dh_randTerm32_self_of_dh_eq_of_ne hne₀ hprev, hd₂] at hsh ⊢
    obtain ⟨hP, hS⟩ := shape_dh_pack_inj i S g hsh
    rw [Symbolic.Swarm.CREF.TR.G1.eq_dhPk_randTerm32_of_shape_eq i S g t₁ hP, eq_randTerm32_of_shape_eq i S g t₁ hS]

open ShapeModKem in
theorem topDhSecret_shape_eq
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {rk₁ rk₂ pk₁' pk₂' : DY.Bytes} {t₁ t₂ : Nat}
    (h₁ : TopDhSecret rk₁ pk₁' t₁) (h₂ : TopDhSecret rk₂ pk₂' t₂)
    (hrk : (gamma' i S g rk₁).shape = (gamma' i S g rk₂).shape) :
    (gamma' i S g (dh pk₁' (randTerm t₁ 32))).shape =
      (gamma' i S g (dh pk₂' (randTerm t₂ 32))).shape := by
  rcases h₁ with ⟨r₁, rfl⟩ | ⟨b₁, c₁, d₁, ss₁, rfl⟩ <;>
    rcases h₂ with ⟨r₂, rfl⟩ | ⟨b₂, c₂, d₂, ss₂, rfl⟩
  · exact (shape_kdfRk_fst_inj i S g hrk).2
  · exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).1 hrk.symm)
  · exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).1 hrk)
  · have hikm := shape_pqxdhKdf_rk_inj i S g hrk; unfold pqxdhIkm at hikm
    exact (shape_concat_inj i S g (shape_concat_inj i S g hikm).2).1

/-- Shape-equal `RkHole` terms of opposite parities at shape-equal root keys are equal. -/
theorem eq_of_rkHole_shape_eq_of_rk_shape_eq
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {b b' : Bool} {rk₁ rk₂ d₁ d₂ : DY.Bytes}
    (h₁ : RkHole b rk₁ d₁) (h₂ : RkHole b' rk₂ d₂) (hp : (b ^^ b') = true)
    (hrk : (gamma' i S g rk₁).shape = (gamma' i S g rk₂).shape)
    (hsh : (gamma' i S g d₁).shape = (gamma' i S g d₂).shape) :
    d₁ = d₂ := by
  cases b <;> cases b'
  · cases hp
  · rcases h₁ with ⟨pk₁', t₀, t₁, rfl, htop₁, hne₀⟩
    rcases h₂ with ⟨pk₂', pk₀', t₂, rfl, htop₂⟩
    by_cases hne : t₁ ≠ t₂
    · exact eq_of_dh_randTerm32_shape_eq_of_ne i S g pk₁' pk₂' t₁ t₂ hne hsh
    · have heq : t₁ = t₂ := Classical.not_not.mp hne; subst heq
      exact eq_of_dh_randTerm32_shape_eq_of_prev_eq i S g pk₁' pk₂' pk₀' t₀ t₁ t₁ hne₀
        (eq_of_dh_randTerm32_shape_eq_of_ne i S g pk₁' pk₀' t₀ t₁ hne₀
          (topDhSecret_shape_eq i S g htop₁ htop₂ hrk)) hsh
  · rcases h₂ with ⟨pk₂', t₀, t₂, rfl, htop₂, hne₀⟩
    rcases h₁ with ⟨pk₁', pk₀', t₁, rfl, htop₁⟩
    by_cases hne : t₂ ≠ t₁
    · exact (eq_of_dh_randTerm32_shape_eq_of_ne i S g pk₂' pk₁' t₂ t₁ hne hsh.symm).symm
    · have heq : t₂ = t₁ := Classical.not_not.mp hne; subst heq
      exact (eq_of_dh_randTerm32_shape_eq_of_prev_eq i S g pk₂' pk₁' pk₀' t₀ t₂ t₂ hne₀
        (eq_of_dh_randTerm32_shape_eq_of_ne i S g pk₂' pk₀' t₀ t₂ hne₀
          (topDhSecret_shape_eq i S g htop₂ htop₁ hrk.symm)) hsh.symm).symm
  · cases hp

theorem shape_pqxdhIkm_inj_of_hole
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {a₁ b₁ c₁ a₂ b₂ c₂ ss₁ ss₂ : DY.Bytes} {d₁ d₂ : Option DY.Bytes}
    (ha : (gamma' i S g a₁).shape = (gamma' i S g a₂).shape → a₁ = a₂)
    (hb : (gamma' i S g b₁).shape = (gamma' i S g b₂).shape → b₁ = b₂)
    (hc : (gamma' i S g c₁).shape = (gamma' i S g c₂).shape → c₁ = c₂)
    (hd : ∀ v₁ v₂, d₁ = some v₁ → d₂ = some v₂ →
      (gamma' i S g v₁).shape = (gamma' i S g v₂).shape → v₁ = v₂)
    (hk₁ : ShapeModKem.KemLeaf ss₁) (hk₂ : ShapeModKem.KemLeaf ss₂)
    (h : (gamma' i S g (pqxdhIkm a₁ b₁ c₁ d₁ ss₁)).shape =
      (gamma' i S g (pqxdhIkm a₂ b₂ c₂ d₂ ss₂)).shape) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ ∧ d₁ = d₂ ∧
    (gamma' i S g ss₁).shape = (gamma' i S g ss₂).shape := by
  unfold pqxdhIkm at h
  obtain ⟨_, h1⟩ := ShapeModKem.shape_concat_inj i S g h
  obtain ⟨sha, h2⟩ := ShapeModKem.shape_concat_inj i S g h1
  obtain ⟨shb, h3⟩ := ShapeModKem.shape_concat_inj i S g h2
  obtain ⟨shc, h4⟩ := ShapeModKem.shape_concat_inj i S g h3
  cases d₁ with
  | none =>
    cases d₂ with
    | none => exact ⟨ha sha, hb shb, hc shc, rfl, h4⟩
    | some v₂ => exact False.elim (ShapeModKem.shape_kemLeaf_ne_concat i S g hk₁ h4)
  | some v₁ =>
    cases d₂ with
    | none => exact False.elim (ShapeModKem.shape_kemLeaf_ne_concat i S g hk₂ h4.symm)
    | some v₂ =>
      obtain ⟨shd, hss⟩ := ShapeModKem.shape_concat_inj i S g h4
      have hdv : v₁ = v₂ := hd v₁ v₂ rfl rfl shd; subst hdv
      exact ⟨ha sha, hb shb, hc shc, rfl, hss⟩

/-- Opposite-role `pqxdhIkm` terms with equal shapes have equal DH tuples and equal-shape KEM
leaves. -/
theorem shape_pqxdhIkm_inj_of_roleHoles
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {P_ik P_spk P_opk P_ek : Nat → Prop}
    (h_ik_spk : ∀ t, P_ik t → P_spk t → False)
    (h_ek_ik : ∀ t, P_ek t → P_ik t → False)
    (h_ek_spk : ∀ t, P_ek t → P_spk t → False)
    (h_ek_opk : ∀ t, P_ek t → P_opk t → False)
    {c c' : Bool} {a₁ b₁ e₁ a₂ b₂ e₂ ss₁ ss₂ : DY.Bytes} {d₁ d₂ : Option DY.Bytes}
    (h₁ : IkmRoleHoles P_ik P_spk P_opk P_ek c a₁ b₁ e₁ d₁)
    (h₂ : IkmRoleHoles P_ik P_spk P_opk P_ek c' a₂ b₂ e₂ d₂)
    (hp : (c ^^ c') = true)
    (hk₁ : ShapeModKem.KemLeaf ss₁) (hk₂ : ShapeModKem.KemLeaf ss₂)
    (h : (gamma' i S g (pqxdhIkm a₁ b₁ e₁ d₁ ss₁)).shape =
      (gamma' i S g (pqxdhIkm a₂ b₂ e₂ d₂ ss₂)).shape) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ e₁ = e₂ ∧ d₁ = d₂ ∧
    (gamma' i S g ss₁).shape = (gamma' i S g ss₂).shape := by
  cases c <;> cases c'
  · cases hp
  · rcases h₁ with ⟨⟨pa₁, ta₁, rfl, ha₁⟩, ⟨pb₁, tb₁, rfl, hb₁⟩, ⟨pe₁, te₁, rfl, he₁⟩, hd₁⟩
    rcases h₂ with ⟨⟨pa₂, ta₂, rfl, ha₂⟩, ⟨pb₂, tb₂, rfl, hb₂⟩, ⟨pe₂, te₂, rfl, he₂⟩, hd₂⟩
    refine shape_pqxdhIkm_inj_of_hole i S g
      (eq_of_dh_randTerm32_shape_eq_of_ne i S g pa₁ pa₂ ta₁ ta₂ (fun h => h_ik_spk ta₁ ha₁ (h ▸ ha₂)))
      (eq_of_dh_randTerm32_shape_eq_of_ne i S g pb₁ pb₂ tb₁ tb₂ (fun h => h_ek_ik tb₁ hb₁ (h ▸ hb₂)))
      (eq_of_dh_randTerm32_shape_eq_of_ne i S g pe₁ pe₂ te₁ te₂ (fun h => h_ek_spk te₁ he₁ (h ▸ he₂)))
      (fun v₁ v₂ hv₁ hv₂ hsh => ?_) hk₁ hk₂ h
    rcases hd₁ v₁ hv₁ with ⟨pd₁, td₁, rfl, hdv₁⟩; rcases hd₂ v₂ hv₂ with ⟨pd₂, td₂, rfl, hdv₂⟩
    exact eq_of_dh_randTerm32_shape_eq_of_ne i S g pd₁ pd₂ td₁ td₂ (fun h => h_ek_opk td₁ hdv₁ (h ▸ hdv₂)) hsh
  · rcases h₁ with ⟨⟨pa₁, ta₁, rfl, ha₁⟩, ⟨pb₁, tb₁, rfl, hb₁⟩, ⟨pe₁, te₁, rfl, he₁⟩, hd₁⟩
    rcases h₂ with ⟨⟨pa₂, ta₂, rfl, ha₂⟩, ⟨pb₂, tb₂, rfl, hb₂⟩, ⟨pe₂, te₂, rfl, he₂⟩, hd₂⟩
    refine shape_pqxdhIkm_inj_of_hole i S g
      (eq_of_dh_randTerm32_shape_eq_of_ne i S g pa₁ pa₂ ta₁ ta₂ (fun h => h_ik_spk ta₂ ha₂ (h ▸ ha₁)))
      (eq_of_dh_randTerm32_shape_eq_of_ne i S g pb₁ pb₂ tb₁ tb₂ (fun h => h_ek_ik tb₂ hb₂ (h ▸ hb₁)))
      (eq_of_dh_randTerm32_shape_eq_of_ne i S g pe₁ pe₂ te₁ te₂ (fun h => h_ek_spk te₂ he₂ (h ▸ he₁)))
      (fun v₁ v₂ hv₁ hv₂ hsh => ?_) hk₁ hk₂ h
    rcases hd₁ v₁ hv₁ with ⟨pd₁, td₁, rfl, hdv₁⟩; rcases hd₂ v₂ hv₂ with ⟨pd₂, td₂, rfl, hdv₂⟩
    exact eq_of_dh_randTerm32_shape_eq_of_ne i S g pd₁ pd₂ td₁ td₂ (fun h => h_ek_opk td₂ hdv₂ (h ▸ hdv₁)) hsh
  · cases hp

/-- Given `IkmRoleHoles` on `B` and KEM canonicity on peel-reached pairs, base injectivity holds
on all opposite-role base pairs reached by `PK`. -/
theorem hbase_of_roleHoles_and_kemCanon
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {P_ik P_spk P_opk P_ek : Nat → Prop}
    (h_ik_spk : ∀ t, P_ik t → P_spk t → False)
    (h_ek_ik : ∀ t, P_ek t → P_ik t → False)
    (h_ek_spk : ∀ t, P_ek t → P_spk t → False)
    (h_ek_opk : ∀ t, P_ek t → P_opk t → False)
    {B : Bool → DY.Bytes → Prop} {PK : DY.Bytes → DY.Bytes → Prop}
    (hB : ∀ c m, B c m → ∃ (a b e : DY.Bytes) (d : Option DY.Bytes) (ss : DY.Bytes),
      m = pqxdhIkm a b e d ss ∧ IkmRoleHoles P_ik P_spk P_opk P_ek c a b e d ∧
      ShapeModKem.KemLeaf ss)
    (hkem : ∀ (c c' : Bool) (a b e : DY.Bytes) (d : Option DY.Bytes) (ss₁ ss₂ : DY.Bytes),
      PK (pqxdhIkm a b e d ss₁) (pqxdhIkm a b e d ss₂) →
      B c (pqxdhIkm a b e d ss₁) → B c' (pqxdhIkm a b e d ss₂) → (c ^^ c') = true →
      (gamma' i S g ss₁).shape = (gamma' i S g ss₂).shape → ss₁ = ss₂)
    (c c' : Bool) (m₁ m₂ : DY.Bytes)
    (hP : PK m₁ m₂) (hm₁ : B c m₁) (hm₂ : B c' m₂) (hp : (c ^^ c') = true)
    (hsh : (gamma' i S g m₁).shape = (gamma' i S g m₂).shape) :
    m₁ = m₂ := by
  rcases hB c m₁ hm₁ with ⟨a₁, b₁, e₁, d₁, ss₁, rfl, hr₁, hk₁⟩
  rcases hB c' m₂ hm₂ with ⟨a₂, b₂, e₂, d₂, ss₂, rfl, hr₂, hk₂⟩
  obtain ⟨rfl, rfl, rfl, rfl, hss⟩ :=
    shape_pqxdhIkm_inj_of_roleHoles i S g h_ik_spk h_ek_ik h_ek_spk h_ek_opk
      hr₁ hr₂ hp hk₁ hk₂ hsh
  rw [hkem c c' a₁ b₁ e₁ d₁ ss₁ ss₂ hP hm₁ hm₂ hp hss]

private theorem xor_not_not_cl (b b' : Bool) : ((!b) ^^ (!b')) = (b ^^ b') := by
  cases b <;> cases b' <;> rfl

open ShapeModKem in
theorem spineRk_kdfRk_fst_inv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {B : Bool → DY.Bytes → Prop} {b : Bool} {r d : DY.Bytes}
    (h : SpineRk B b (kdfRk r d).1) : SpineRk B (!b) r ∧ RkHole (!b) r d := by
  generalize hx : (kdfRk r d).1 = x at h; cases h with
  | hsRk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ r d).1 (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | hsCk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ r d).2.2.1 (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | rkStep1 hr hd =>
    obtain ⟨rfl, rfl⟩ := Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective (Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective hx).1
    rw [Bool.not_not]; exact ⟨hr, hd⟩
  | rkStep2 _ _ => exact False.elim (shape_kdfRk_fst_ne_snd i S g r d _ _ (congrArg (fun u => (gamma' i S g u).shape) hx))
  | ckStep1 _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g r d _).1 (congrArg (fun u => (gamma' i S g u).shape) hx))
  | ckStep2 _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g r d _).2.1 (congrArg (fun u => (gamma' i S g u).shape) hx))

open ShapeModKem in
theorem spineRk_kdfRk_snd_inv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {B : Bool → DY.Bytes → Prop} {b : Bool} {r d : DY.Bytes}
    (h : SpineRk B b (kdfRk r d).2) : SpineRk B (!b) r ∧ RkHole (!b) r d := by
  generalize hx : (kdfRk r d).2 = x at h; cases h with
  | hsRk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ r d).2.1 (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | hsCk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ r d).2.2.2 (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | rkStep1 _ _ => exact False.elim (shape_kdfRk_fst_ne_snd i S g _ _ r d (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | rkStep2 hr hd =>
    obtain ⟨rfl, rfl⟩ := Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective (Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective hx).1
    rw [Bool.not_not]; exact ⟨hr, hd⟩
  | ckStep1 _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g r d _).2.2.1 (congrArg (fun u => (gamma' i S g u).shape) hx))
  | ckStep2 _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g r d _).2.2.2 (congrArg (fun u => (gamma' i S g u).shape) hx))

open ShapeModKem in
theorem spineRk_kdfCk_fst_inv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {B : Bool → DY.Bytes → Prop} {b : Bool} {c : DY.Bytes} (h : SpineRk B b (kdfCk c).1) : SpineRk B b c := by
  generalize hx : (kdfCk c).1 = x at h; cases h with
  | hsRk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ c).1 (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | hsCk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ c).2.2.1 (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | rkStep1 _ _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ c).1 (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | rkStep2 _ _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ c).2.2.1 (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | ckStep1 hc => obtain ⟨rfl, _⟩ := Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective hx; exact hc
  | ckStep2 _ => exact False.elim (shape_kdfCk_fst_ne_snd i S g c _ (congrArg (fun u => (gamma' i S g u).shape) hx))

open ShapeModKem in
theorem spineRk_kdfCk_snd_inv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {B : Bool → DY.Bytes → Prop} {b : Bool} {c : DY.Bytes} (h : SpineRk B b (kdfCk c).2) : SpineRk B b c := by
  generalize hx : (kdfCk c).2 = x at h; cases h with
  | hsRk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ c).2.1 (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | hsCk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ c).2.2.2 (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | rkStep1 _ _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ c).2.1 (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | rkStep2 _ _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ c).2.2.2 (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | ckStep1 _ => exact False.elim (shape_kdfCk_fst_ne_snd i S g _ c (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | ckStep2 hc => obtain ⟨rfl, _⟩ := Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective hx; exact hc

open ShapeModKem in
theorem spineRk_pqxdhKdf_rk_inv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {B : Bool → DY.Bytes → Prop} {b : Bool} {m : DY.Bytes} (h : SpineRk B b (pqxdhKdf m).rk) : B b m := by
  generalize hx : (pqxdhKdf m).rk = x at h; cases h with
  | hsRk hm => obtain ⟨rfl⟩ := (Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective (Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective hx).1).2; exact hm
  | hsCk _ => exact False.elim (shape_pqxdhKdf_rk_ne_ck i S g m _ (congrArg (fun u => (gamma' i S g u).shape) hx))
  | rkStep1 _ _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g m _ _).1 (congrArg (fun u => (gamma' i S g u).shape) hx))
  | rkStep2 _ _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g m _ _).2.1 (congrArg (fun u => (gamma' i S g u).shape) hx))
  | ckStep1 _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g m _).1 (congrArg (fun u => (gamma' i S g u).shape) hx))
  | ckStep2 _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g m _).2.1 (congrArg (fun u => (gamma' i S g u).shape) hx))

open ShapeModKem in
theorem spineRk_pqxdhKdf_ck_inv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {B : Bool → DY.Bytes → Prop} {b : Bool} {m : DY.Bytes} (h : SpineRk B b (pqxdhKdf m).ck) : B b m := by
  generalize hx : (pqxdhKdf m).ck = x at h; cases h with
  | hsRk _ => exact False.elim (shape_pqxdhKdf_rk_ne_ck i S g _ m (congrArg (fun u => (gamma' i S g u).shape) hx.symm))
  | hsCk hm => obtain ⟨rfl⟩ := (Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective (Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective hx).1).2; exact hm
  | rkStep1 _ _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g m _ _).2.2.1 (congrArg (fun u => (gamma' i S g u).shape) hx))
  | rkStep2 _ _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g m _ _).2.2.2 (congrArg (fun u => (gamma' i S g u).shape) hx))
  | ckStep1 _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g m _).2.2.1 (congrArg (fun u => (gamma' i S g u).shape) hx))
  | ckStep2 _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g m _).2.2.2 (congrArg (fun u => (gamma' i S g u).shape) hx))

theorem spineRk_is_hmac {B : Bool → DY.Bytes → Prop} {b : Bool} {x : DY.Bytes} (h : SpineRk B b x) : ∃ k m, x = hmac k m := by
  cases h <;> exact ⟨_, _, rfl⟩

private theorem hmac_ne_concat_cl (k m l r : DY.Bytes) : hmac k m ≠ DY.Concat.concat l r :=
  fun h => Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

private theorem hmac_ne_dh_cl (k m p s : DY.Bytes) : hmac k m ≠ dh p s := by
  intro h; obtain ⟨P, S_k, hd, _⟩ := dh_eq_pack_and_or p s; rw [hd] at h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

private theorem hmac_ne_kemLeaf_cl {k m x : DY.Bytes} (hk : ShapeModKem.KemLeaf x) : hmac k m ≠ x := by
  rcases hk with ⟨pk, e, rfl⟩ | ⟨sk, ct, rfl⟩ <;>
    exact fun h => Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

private theorem concat_ne_dh_cl (l r p s : DY.Bytes) : DY.Concat.concat l r ≠ dh p s := by
  intro h; obtain ⟨P, S_k, hd, _⟩ := dh_eq_pack_and_or p s; rw [hd] at h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

private theorem concat_ne_kemLeaf_cl {l r x : DY.Bytes} (hk : ShapeModKem.KemLeaf x) : DY.Concat.concat l r ≠ x := by
  rcases hk with ⟨pk, e, rfl⟩ | ⟨sk, ct, rfl⟩ <;>
    exact fun h => Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

private theorem dh_ne_kemLeaf_cl {p s x : DY.Bytes} (hk : ShapeModKem.KemLeaf x) : dh p s ≠ x := by
  rcases hk with ⟨pk, e, rfl⟩ | ⟨sk, ct, rfl⟩ <;>
    (intro h; obtain ⟨P, S_k, hd, _⟩ := dh_eq_pack_and_or p s; rw [hd] at h;
     exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h)

private theorem dh_ne_discontinuity_cl (p s : DY.Bytes) : dh p s ≠ DY.Libsignal.PQXDH.discontinuity := by
  intro h; obtain ⟨P, S_k, hd, _⟩ := dh_eq_pack_and_or p s; rw [hd] at h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

def DeadLeaf (x : DY.Bytes) : Prop :=
  (∀ k m, x ≠ hmac k m) ∧
  (∀ r, x ≠ DY.Concat.concat DY.Libsignal.PQXDH.discontinuity r) ∧
  (∀ p s, x ≠ dh p s)

theorem deadLeaf_of_kemLeaf {x : DY.Bytes} (hk : ShapeModKem.KemLeaf x) : DeadLeaf x :=
  ⟨fun _ _ h => hmac_ne_kemLeaf_cl hk h.symm,
   fun _ h => concat_ne_kemLeaf_cl hk h.symm,
   fun _ _ h => dh_ne_kemLeaf_cl hk h.symm⟩

theorem deadLeaf_of_concat_dh (p₀ s₀ r₀ : DY.Bytes) :
    DeadLeaf (DY.Concat.concat (dh p₀ s₀) r₀) :=
  ⟨fun k m h => hmac_ne_concat_cl k m _ _ h.symm,
   fun _ h => dh_ne_discontinuity_cl p₀ s₀ (Symbolic.Swarm.CREF.TR.G1.concat_injective h).1,
   fun p s h => concat_ne_dh_cl _ _ p s h⟩

def PeelInv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (B : Bool → DY.Bytes → Prop) (x₁ x₂ : DY.Bytes) : Prop :=
  (∃ b₁ b₂ : Bool, (b₁ ^^ b₂) = true ∧
    SpineRk B b₁ x₁ ∧ SpineRk B b₂ x₂ ∧
    (gamma' i S g x₁).shape = (gamma' i S g x₂).shape) ∨
  (∃ c₁ c₂ : Bool, (c₁ ^^ c₂) = true ∧
    B c₁ x₁ ∧ B c₂ x₂ ∧
    (gamma' i S g x₁).shape = (gamma' i S g x₂).shape) ∨
  (∃ p s : DY.Bytes, x₁ = dh p s ∧ x₁ = x₂) ∨
  DeadLeaf x₁

theorem peelInv_of_hmac {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {P_ik P_spk P_opk P_ek : Nat → Prop} {B : Bool → DY.Bytes → Prop}
    (hB : ∀ c m, B c m → ∃ a b e d ss,
      m = pqxdhIkm a b e d ss ∧ IkmRoleHoles P_ik P_spk P_opk P_ek c a b e d ∧ ShapeModKem.KemLeaf ss)
    {k m y : DY.Bytes} (h : PeelInv i S g B (hmac k m) y) :
    ∃ b₁ b₂ : Bool, (b₁ ^^ b₂) = true ∧
      SpineRk B b₁ (hmac k m) ∧ SpineRk B b₂ y ∧
      (gamma' i S g (hmac k m)).shape = (gamma' i S g y).shape := by
  rcases h with h1 | ⟨c₁, _, _, hB₁, _, _⟩ | ⟨p, s, hd, _⟩ | hk
  · exact h1
  · obtain ⟨a, b, e, d, ss, heq, _, _⟩ := hB c₁ _ hB₁; exact False.elim (hmac_ne_concat_cl k m _ _ heq)
  · exact False.elim (hmac_ne_dh_cl k m p s hd)
  · exact False.elim (hk.1 k m rfl)

theorem peelInv_of_pqxdhIkm {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {B : Bool → DY.Bytes → Prop} {a b c s y : DY.Bytes} {d : Option DY.Bytes}
    (h : PeelInv i S g B (pqxdhIkm a b c d s) y) :
    ∃ c₁ c₂ : Bool, (c₁ ^^ c₂) = true ∧
      B c₁ (pqxdhIkm a b c d s) ∧ B c₂ y ∧
      (gamma' i S g (pqxdhIkm a b c d s)).shape = (gamma' i S g y).shape := by
  rcases h with ⟨b₁, _, _, hsp₁, _, _⟩ | h2 | ⟨p, sk, hd, _⟩ | hk
  · obtain ⟨k, m, heq⟩ := spineRk_is_hmac hsp₁; exact False.elim (hmac_ne_concat_cl k m _ _ heq.symm)
  · exact h2
  · exact False.elim (concat_ne_dh_cl _ _ p sk hd)
  · exact False.elim (hk.2.1 _ rfl)

theorem peelInv_of_dh {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {P_ik P_spk P_opk P_ek : Nat → Prop} {B : Bool → DY.Bytes → Prop}
    (hB : ∀ c m, B c m → ∃ a b e d ss,
      m = pqxdhIkm a b e d ss ∧ IkmRoleHoles P_ik P_spk P_opk P_ek c a b e d ∧ ShapeModKem.KemLeaf ss)
    {p s y : DY.Bytes} (h : PeelInv i S g B (dh p s) y) :
    dh p s = y := by
  rcases h with ⟨b₁, _, _, hsp₁, _, _⟩ | ⟨c₁, _, _, hB₁, _, _⟩ | ⟨_, _, _, heq⟩ | hk
  · obtain ⟨k, m, heq⟩ := spineRk_is_hmac hsp₁; exact False.elim (hmac_ne_dh_cl k m p s heq.symm)
  · obtain ⟨a, b, e, d, ss, heq, _, _⟩ := hB c₁ _ hB₁; exact False.elim (concat_ne_dh_cl _ _ p s heq.symm)
  · exact heq
  · exact False.elim (hk.2.2 p s rfl)

open ShapeModKem in
theorem peelInv_of_peel (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {P_ik P_spk P_opk P_ek : Nat → Prop} {B : Bool → DY.Bytes → Prop}
    (h_ik_spk : ∀ t, P_ik t → P_spk t → False)
    (h_ek_ik : ∀ t, P_ek t → P_ik t → False)
    (h_ek_spk : ∀ t, P_ek t → P_spk t → False)
    (h_ek_opk : ∀ t, P_ek t → P_opk t → False)
    (hB : ∀ c m, B c m → ∃ a b e d ss,
      m = pqxdhIkm a b e d ss ∧ IkmRoleHoles P_ik P_spk P_opk P_ek c a b e d ∧ KemLeaf ss)
    {b b' : Bool} {u₀ v₀ : DY.Bytes}
    (hp₀ : (b ^^ b') = true) (hu₀ : SpineRk B b u₀) (hv₀ : SpineRk B b' v₀)
    (hsh₀ : (gamma' i S g u₀).shape = (gamma' i S g v₀).shape)
    {x₁ x₂ : DY.Bytes} (hP : SpineIkm.Peel u₀ v₀ x₁ x₂) :
    PeelInv i S g B x₁ x₂ := by
  induction hP with
  | refl => exact Or.inl ⟨b, b', hp₀, hu₀, hv₀, hsh₀⟩
  | rk1L _ ih =>
    obtain ⟨b₁, b₂, hp, hsp₁, hsp₂, hsh⟩ := peelInv_of_hmac hB ih
    exact Or.inl ⟨!b₁, !b₂, (xor_not_not_cl b₁ b₂).trans hp,
      (spineRk_kdfRk_fst_inv i S g hsp₁).1, (spineRk_kdfRk_fst_inv i S g hsp₂).1,
      (shape_kdfRk_fst_inj i S g hsh).1⟩
  | rk1R _ ih =>
    obtain ⟨b₁, b₂, hp, hsp₁, hsp₂, hsh⟩ := peelInv_of_hmac hB ih
    obtain ⟨hrk, hdh⟩ := shape_kdfRk_fst_inj i S g hsh
    have hd₁ := (spineRk_kdfRk_fst_inv i S g hsp₁).2
    have heq := eq_of_rkHole_shape_eq_of_rk_shape_eq i S g hd₁
      (spineRk_kdfRk_fst_inv i S g hsp₂).2 ((xor_not_not_cl b₁ b₂).trans hp) hrk hdh
    cases b₁ <;> { obtain ⟨pk', _, _, hd, _⟩ := hd₁; exact Or.inr (Or.inr (Or.inl ⟨pk', _, hd, heq⟩)) }
  | rk2L _ ih =>
    obtain ⟨b₁, b₂, hp, hsp₁, hsp₂, hsh⟩ := peelInv_of_hmac hB ih
    exact Or.inl ⟨!b₁, !b₂, (xor_not_not_cl b₁ b₂).trans hp,
      (spineRk_kdfRk_snd_inv i S g hsp₁).1, (spineRk_kdfRk_snd_inv i S g hsp₂).1,
      (shape_kdfRk_snd_inj i S g hsh).1⟩
  | rk2R _ ih =>
    obtain ⟨b₁, b₂, hp, hsp₁, hsp₂, hsh⟩ := peelInv_of_hmac hB ih
    obtain ⟨hrk, hdh⟩ := shape_kdfRk_snd_inj i S g hsh
    have hd₁ := (spineRk_kdfRk_snd_inv i S g hsp₁).2
    have heq := eq_of_rkHole_shape_eq_of_rk_shape_eq i S g hd₁
      (spineRk_kdfRk_snd_inv i S g hsp₂).2 ((xor_not_not_cl b₁ b₂).trans hp) hrk hdh
    cases b₁ <;> { obtain ⟨pk', _, _, hd, _⟩ := hd₁; exact Or.inr (Or.inr (Or.inl ⟨pk', _, hd, heq⟩)) }
  | ck1 _ ih =>
    obtain ⟨b₁, b₂, hp, hsp₁, hsp₂, hsh⟩ := peelInv_of_hmac hB ih
    exact Or.inl ⟨b₁, b₂, hp, spineRk_kdfCk_fst_inv i S g hsp₁,
      spineRk_kdfCk_fst_inv i S g hsp₂, shape_kdfCk_fst_inj i S g hsh⟩
  | ck2 _ ih =>
    obtain ⟨b₁, b₂, hp, hsp₁, hsp₂, hsh⟩ := peelInv_of_hmac hB ih
    exact Or.inl ⟨b₁, b₂, hp, spineRk_kdfCk_snd_inv i S g hsp₁,
      spineRk_kdfCk_snd_inv i S g hsp₂, shape_kdfCk_snd_inj i S g hsh⟩
  | hsRk _ ih =>
    obtain ⟨b₁, b₂, hp, hsp₁, hsp₂, hsh⟩ := peelInv_of_hmac hB ih
    exact Or.inr (Or.inl ⟨b₁, b₂, hp, spineRk_pqxdhKdf_rk_inv i S g hsp₁,
      spineRk_pqxdhKdf_rk_inv i S g hsp₂, shape_pqxdhKdf_rk_inj i S g hsh⟩)
  | hsCk _ ih =>
    obtain ⟨b₁, b₂, hp, hsp₁, hsp₂, hsh⟩ := peelInv_of_hmac hB ih
    exact Or.inr (Or.inl ⟨b₁, b₂, hp, spineRk_pqxdhKdf_ck_inv i S g hsp₁,
      spineRk_pqxdhKdf_ck_inv i S g hsp₂, shape_pqxdhKdf_ck_inj i S g hsh⟩)
  | ikmDh1 _ ih =>
    obtain ⟨c₁, c₂, hp, hB₁, hB₂, hsh⟩ := peelInv_of_pqxdhIkm ih
    obtain ⟨a₁', b₁', e₁', d₁', ss₁', heq₁, hr₁, hk₁⟩ := hB c₁ _ hB₁
    obtain ⟨a₂', b₂', e₂', d₂', ss₂', heq₂, hr₂, hk₂⟩ := hB c₂ _ hB₂
    have ha₁ := (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective heq₁).2).1
    have ha₂ := (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective heq₂).2).1
    rw [heq₁, heq₂] at hsh
    obtain ⟨heq_a, _, _, _, _⟩ := shape_pqxdhIkm_inj_of_roleHoles i S g
      h_ik_spk h_ek_ik h_ek_spk h_ek_opk hr₁ hr₂ hp hk₁ hk₂ hsh
    cases c₁ <;> {
      obtain ⟨pk', _, hd, _⟩ := hr₁.1
      exact Or.inr (Or.inr (Or.inl ⟨pk', _, ha₁.trans hd, ha₁.trans (heq_a.trans ha₂.symm)⟩)) }
  | ikmDh2 _ ih =>
    obtain ⟨c₁, c₂, hp, hB₁, hB₂, hsh⟩ := peelInv_of_pqxdhIkm ih
    obtain ⟨a₁', b₁', e₁', d₁', ss₁', heq₁, hr₁, hk₁⟩ := hB c₁ _ hB₁
    obtain ⟨a₂', b₂', e₂', d₂', ss₂', heq₂, hr₂, hk₂⟩ := hB c₂ _ hB₂
    have hb₁ := (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective heq₁).2).2).1
    have hb₂ := (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective heq₂).2).2).1
    rw [heq₁, heq₂] at hsh
    obtain ⟨_, heq_b, _, _, _⟩ := shape_pqxdhIkm_inj_of_roleHoles i S g
      h_ik_spk h_ek_ik h_ek_spk h_ek_opk hr₁ hr₂ hp hk₁ hk₂ hsh
    cases c₁ <;> {
      obtain ⟨pk', _, hd, _⟩ := hr₁.2.1
      exact Or.inr (Or.inr (Or.inl ⟨pk', _, hb₁.trans hd, hb₁.trans (heq_b.trans hb₂.symm)⟩)) }
  | ikmDh3 _ ih =>
    obtain ⟨c₁, c₂, hp, hB₁, hB₂, hsh⟩ := peelInv_of_pqxdhIkm ih
    obtain ⟨a₁', b₁', e₁', d₁', ss₁', heq₁, hr₁, hk₁⟩ := hB c₁ _ hB₁
    obtain ⟨a₂', b₂', e₂', d₂', ss₂', heq₂, hr₂, hk₂⟩ := hB c₂ _ hB₂
    have he₁ := (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective heq₁).2).2).2).1
    have he₂ := (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective heq₂).2).2).2).1
    rw [heq₁, heq₂] at hsh
    obtain ⟨_, _, heq_e, _, _⟩ := shape_pqxdhIkm_inj_of_roleHoles i S g
      h_ik_spk h_ek_ik h_ek_spk h_ek_opk hr₁ hr₂ hp hk₁ hk₂ hsh
    cases c₁ <;> {
      obtain ⟨pk', _, hd, _⟩ := hr₁.2.2.1
      exact Or.inr (Or.inr (Or.inl ⟨pk', _, he₁.trans hd, he₁.trans (heq_e.trans he₂.symm)⟩)) }
  | ikmDh4 _ ih =>
    obtain ⟨c₁, c₂, hp, hB₁, hB₂, hsh⟩ := peelInv_of_pqxdhIkm ih
    obtain ⟨a₁', b₁', e₁', d₁', ss₁', heq₁, hr₁, hk₁⟩ := hB c₁ _ hB₁
    obtain ⟨a₂', b₂', e₂', d₂', ss₂', heq₂, hr₂, hk₂⟩ := hB c₂ _ hB₂
    have hrest₁ := (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective heq₁).2).2).2).2
    have hrest₂ := (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective heq₂).2).2).2).2
    cases hd₁_opt : d₁' with
    | none => rw [hd₁_opt] at hrest₁; exact False.elim (concat_ne_kemLeaf_cl hk₁ hrest₁)
    | some v₁ =>
      rw [hd₁_opt] at hrest₁
      cases hd₂_opt : d₂' with
      | none => rw [hd₂_opt] at hrest₂; exact False.elim (concat_ne_kemLeaf_cl hk₂ hrest₂)
      | some v₂ =>
        rw [hd₂_opt] at hrest₂
        have hv₁ := (Symbolic.Swarm.CREF.TR.G1.concat_injective hrest₁).1
        have hv₂ := (Symbolic.Swarm.CREF.TR.G1.concat_injective hrest₂).1
        rw [heq₁, heq₂] at hsh
        obtain ⟨_, _, _, heq_d, _⟩ := shape_pqxdhIkm_inj_of_roleHoles i S g
          h_ik_spk h_ek_ik h_ek_spk h_ek_opk hr₁ hr₂ hp hk₁ hk₂ hsh
        rw [hd₁_opt, hd₂_opt, Option.some.injEq] at heq_d
        cases c₁ <;> {
          obtain ⟨pk', _, hd, _⟩ := hr₁.2.2.2 v₁ hd₁_opt
          exact Or.inr (Or.inr (Or.inl ⟨pk', _, hv₁.trans hd, hv₁.trans (heq_d.trans hv₂.symm)⟩)) }
  | @ikmKem a₁ b₁ c₁ a₂ b₂ c₂ s₁ s₂ d₁_opt d₂_opt _ ih =>
    obtain ⟨role₁, role₂, hp, hB₁, hB₂, hsh⟩ := peelInv_of_pqxdhIkm ih
    obtain ⟨a₁', b₁', e₁', d₁', ss₁', heq₁, hr₁, hk₁⟩ := hB role₁ _ hB₁
    have hrest₁ := (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective (Symbolic.Swarm.CREF.TR.G1.concat_injective heq₁).2).2).2).2
    refine Or.inr (Or.inr (Or.inr ?_))
    cases d₁_opt with
    | none =>
      cases hd₁' : d₁' with
      | none => rw [hd₁'] at hrest₁; dsimp only at hrest₁; exact hrest₁ ▸ deadLeaf_of_kemLeaf hk₁
      | some v₁ =>
        rw [hd₁'] at hrest₁; dsimp only at hrest₁
        cases role₁ <;> {
          obtain ⟨pk', t, hd, _⟩ := hr₁.2.2.2 v₁ hd₁'; rw [hd] at hrest₁
          exact hrest₁ ▸ deadLeaf_of_concat_dh pk' (randTerm t 32) ss₁' }
    | some u₁ =>
      cases hd₁' : d₁' with
      | none => rw [hd₁'] at hrest₁; dsimp only at hrest₁; exact False.elim (concat_ne_kemLeaf_cl hk₁ hrest₁)
      | some v₁ =>
        rw [hd₁'] at hrest₁; dsimp only at hrest₁
        exact (Symbolic.Swarm.CREF.TR.G1.concat_injective hrest₁).2 ▸ deadLeaf_of_kemLeaf hk₁

theorem hdh_of_spineRk (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {P_ik P_spk P_opk P_ek : Nat → Prop} {B : Bool → DY.Bytes → Prop}
    (h_ik_spk : ∀ t, P_ik t → P_spk t → False)
    (h_ek_ik : ∀ t, P_ek t → P_ik t → False)
    (h_ek_spk : ∀ t, P_ek t → P_spk t → False)
    (h_ek_opk : ∀ t, P_ek t → P_opk t → False)
    (hB : ∀ c m, B c m → ∃ a b e d ss,
      m = pqxdhIkm a b e d ss ∧ IkmRoleHoles P_ik P_spk P_opk P_ek c a b e d ∧
      ShapeModKem.KemLeaf ss)
    {b b' : Bool} {u₀ v₀ : DY.Bytes}
    (hp₀ : (b ^^ b') = true) (hu₀ : SpineRk B b u₀) (hv₀ : SpineRk B b' v₀)
    (hsh₀ : (gamma' i S g u₀).shape = (gamma' i S g v₀).shape)
    (d₁ d₂ : DY.Bytes) (hP : SpineIkm.Peel u₀ v₀ d₁ d₂) (hd₁ : SpineIkm.DhHole d₁) :
    d₁ = d₂ := by
  obtain ⟨p, s, rfl, _⟩ := hd₁
  exact peelInv_of_dh hB (peelInv_of_peel i S g h_ik_spk h_ek_ik h_ek_spk h_ek_opk
    hB hp₀ hu₀ hv₀ hsh₀ hP)

/-! ## Spine shape injectivity for `SpineRk` -/

theorem self_mem_memo_hmac (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt ikm : DY.Bytes) :
    (hmac salt ikm, (gamma' i S g (hmac salt ikm)).shape, (gamma' i S g (hmac salt ikm)).bytes) ∈
      (gamma' i S g (hmac salt ikm)).memo := by
  have hp := gamma'_pack_kdf i S g { salt := salt, ikm := ikm }
  change (({ salt := salt, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack,
    (gamma' i S g ({ salt := salt, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).shape,
    (gamma' i S g ({ salt := salt, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).bytes) ∈
    (gamma' i S g ({ salt := salt, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).memo
  rw [hp]; exact List.mem_cons_self

private theorem spineRk_to_spineR_dh {B : Bool → DY.Bytes → Prop} {b : Bool} {u : DY.Bytes}
    (hu : SpineRk B b u) : SpineIkm.SpineR (fun d => ∃ p s, d = dh p s) B b u := by
  induction hu with
  | hsRk h => exact .hsRk h
  | hsCk h => exact .hsCk h
  | @rkStep1 c _ _ _ hd ih =>
    exact .rkStep1 ih (by cases c <;> [obtain ⟨p, _, t, rfl, -⟩ := hd; obtain ⟨p, _, t, rfl, -⟩ := hd] <;> exact ⟨p, _, rfl⟩)
  | @rkStep2 c _ _ _ hd ih =>
    exact .rkStep2 ih (by cases c <;> [obtain ⟨p, _, t, rfl, -⟩ := hd; obtain ⟨p, _, t, rfl, -⟩ := hd] <;> exact ⟨p, _, rfl⟩)
  | ckStep1 _ ih => exact .ckStep1 ih
  | ckStep2 _ ih => exact .ckStep2 ih

theorem eq_of_shape_eq_of_spineRk (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {P_ik P_spk P_opk P_ek : Nat → Prop} {B : Bool → DY.Bytes → Prop}
    (h_ik_spk : ∀ t, P_ik t → P_spk t → False) (h_ek_ik : ∀ t, P_ek t → P_ik t → False)
    (h_ek_spk : ∀ t, P_ek t → P_spk t → False) (h_ek_opk : ∀ t, P_ek t → P_opk t → False)
    (hB : ∀ c m, B c m → ∃ a b e d ss,
      m = pqxdhIkm a b e d ss ∧ IkmRoleHoles P_ik P_spk P_opk P_ek c a b e d ∧ ShapeModKem.KemLeaf ss)
    {b b' : Bool} {u₀ v₀ : DY.Bytes}
    (hkem : ∀ (c c' : Bool) (a b e : DY.Bytes) (d : Option DY.Bytes) (ss₁ ss₂ : DY.Bytes),
      SpineIkm.PeelKdf u₀ v₀ (pqxdhIkm a b e d ss₁) (pqxdhIkm a b e d ss₂) →
      B c (pqxdhIkm a b e d ss₁) → B c' (pqxdhIkm a b e d ss₂) → (c ^^ c') = true →
      (gamma' i S g ss₁).shape = (gamma' i S g ss₂).shape → ss₁ = ss₂)
    (hu₀ : SpineRk B b u₀) (hv₀ : SpineRk B b' v₀)
    (hsh₀ : (gamma' i S g u₀).shape = (gamma' i S g v₀).shape) (hp₀ : (b ^^ b') = true) :
    u₀ = v₀ :=
  SpineIkm.eq_of_shape_eq_of_spineR_peel
    (by rintro _ _ hP ⟨_, _, rfl⟩ _ _
        exact peelInv_of_dh hB (peelInv_of_peel i S g h_ik_spk h_ek_ik h_ek_spk h_ek_opk hB hp₀ hu₀ hv₀ hsh₀ hP))
    (hbase_of_roleHoles_and_kemCanon i S g h_ik_spk h_ek_ik h_ek_spk h_ek_opk hB hkem)
    (spineRk_to_spineR_dh hu₀) (spineRk_to_spineR_dh hv₀) .refl hsh₀ hp₀

end Symbolic.Swarm.CREF.TR.G1.Spine
