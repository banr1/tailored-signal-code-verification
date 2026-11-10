/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.SpqrRkForgedMac
import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.ALaCarte.Basic
import Symbolic.Specifications.Model.EquationalTheory.X25519
public import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeIdInv
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkInvCons
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.ALaCarte.Basic

/-!
# DH-Pack and Non-Honest Ratchet-Key Peel Lemmas

Proves `KdfRkSafe` and `gamma'`-shape peel lemmas for `Dh.SubF`, `X25519.Variant`, and
`NotRandDhPkShape`, establishing `dh_not_termShapeId_attackerKnows_cases` and
`variant_variation_ne_zero_of_attackerKnows_reachable_peel`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (chainKeyAt litByte)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.COMPOSED.CompTrace

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## `Dh.SubF` and `X25519.Variant` peel lemmas -/

section UnsealedPeelHelpers
unseal DY.Bytes

private theorem pack_inj_peel {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    {x₁ x₂ : SubF DY.Bytes} (h : BytesView.pack x₁ = BytesView.pack x₂) : x₁ = x₂ := by
  have h1 : DY.Bytes.view? (BytesView.pack x₁) SubF = some x₁ := DY.BytesView.view_pack (SubF := SubF) x₁
  have h2 : DY.Bytes.view? (BytesView.pack x₂) SubF = some x₂ := DY.BytesView.view_pack (SubF := SubF) x₂
  rw [h, h2] at h1; injection h1 with h1; exact h1.symm

private theorem dhPk_inj_peel {sk₁ sk₂ : DY.Bytes}
    (h : DiffieHellman.dhPk sk₁ = DiffieHellman.dhPk sk₂) : sk₁ = sk₂ := by
  have hinj : ({ sk := sk₁ } : DY.DiffieHellman.DhPk.SubF DY.Bytes) = { sk := sk₂ } := pack_inj_peel h
  injection hinj

theorem kdfRkSafe_dh_pack_inv {T : ExecTrace} {pk₀ sk₀ : DY.Bytes}
    (h : KdfRkSafe T (({ pk := pk₀, sk := sk₀ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)) :
    (pk₀.AttackerKnows T ∧ sk₀.AttackerKnows T) ∨
    (∃ s0 : DY.Bytes, pk₀ = dhPk s0 ∧ s0.AttackerKnows T ∧ (dhPk sk₀).AttackerKnows T) := by
  obtain ⟨p0, s0, heq, hp0_ak, hs0_ak⟩ := (kdfRkSafe_dh_iff { pk := pk₀, sk := sk₀ }).mp h
  unfold DiffieHellman.CanDH.dh instCanDHBytes at heq; dsimp only at heq
  have hpack := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF p0
  rcases hv : p0.view? DY.DiffieHellman.DhPk.SubF with _ | ⟨⟨a0⟩⟩
  · rw [hv] at heq; dsimp only at heq; have hinj := pack_inj_peel heq; injection hinj with h1 h2; subst h1; subst h2; exact .inl ⟨hp0_ak, hs0_ak⟩
  · rw [hv] at hpack heq; dsimp only at hpack heq; split at heq <;>
      (have hinj := pack_inj_peel heq; injection hinj with h1 h2; subst h1; subst h2; rw [← hpack] at hp0_ak) <;>
      [exact .inl ⟨hp0_ak, hs0_ak⟩; exact .inr ⟨s0, rfl, hs0_ak, hp0_ak⟩]

end UnsealedPeelHelpers

theorem attackerKnows_x25519Key_srk {tr : ExecTrace} {pk : DY.Bytes} (h : pk.AttackerKnows tr) :
    (X25519.normalizeX25519Key pk).AttackerKnows tr := by
  unfold X25519.normalizeX25519Key; have hpack := DY.Bytes.pack_view? X25519.Variant.SubF pk
  rcases hv : pk.view? X25519.Variant.SubF with _ | v; · exact h
  rw [hv] at hpack; dsimp only at hpack; rw [← hpack] at h
  exact DY.Bytes.AttackerKnows.prove X25519.normalizeX25519Key.attackerKnowledge _ tr ⟨v, h, rfl⟩

theorem attackerKnows_chainKeyAt_srk {tr : ExecTrace} :
    ∀ (k : Nat) {ck : DY.Bytes}, ck.AttackerKnows tr → (chainKeyAt ck k).AttackerKnows tr
  | 0, _, hck => hck
  | k + 1, ck, hck => attackerKnows_chainKeyAt_srk k
      (KdfExtract.attacker_knows_kdfExtract ck (litByte 0x02) tr hck (Literal.attacker_knows_literalToBytes _ tr))

/-- If `X25519.normalizeX25519Key pk` has `TermShapeId`, then `pk` itself has `TermShapeId`. -/
theorem termShapeId_of_termShapeId_x25519Key {pk : DY.Bytes}
    (h : TermShapeId (X25519.normalizeX25519Key pk)) : TermShapeId pk := by
  intro i S g
  unfold X25519.normalizeX25519Key at h
  have hpack := DY.Bytes.pack_view? X25519.Variant.SubF pk
  rcases hv : pk.view? X25519.Variant.SubF with _ | ⟨k, v, t⟩
  · rw [hv] at h; exact h i S g
  · rw [hv] at h hpack; dsimp only at h hpack
    rw [← hpack, shape_x25519Variant_raw_tr i S g k v t, h i S g]

/-! ## `KdfRkSafeS` alias -/

abbrev KdfRkSafeS := KdfRkSafe

theorem kdfRkSafeS_variant_iff {T : ExecTrace} (v : X25519.Variant.SubF DY.Bytes) :
    KdfRkSafeS T v.pack ↔ ¬(v.variation = 0 ∧ v.torsion = 0) ∧ DY.Bytes.view? v.key DY.X25519.Variant.SubF = none ∧ KdfRkSafeS T v.key := kdfRkSafe_variant_iff v

abbrev StSafeRkS := StSafeRk

abbrev JRkS := JRk

theorem JRkS_reachable {T tr : ExecTrace} (hreach : ReachableTrace tr) (hle : tr ≤ T) : JRkS T tr :=
  JRk_reachable hreach hle

theorem kdfRkSafeS_of_attackerKnows_reachable {T : ExecTrace} (hT : ReachableTrace T) {b : DY.Bytes} (hAK : b.AttackerKnows T) : KdfRkSafeS T b :=
  kdfRkSafe_of_attackerKnows_reachable hT hAK

/-! ## `NotRandDhPkShape` and `createChain` peeling -/

unseal DY.Bytes in
private instance subLit0Peel (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction concretizeLit (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

/-- Non-honest-ephemeral DH public key shape property: either `(gamma' i S g k).shape` is not
`dhPk _`, or `k = dhPk a₀` where `(gamma' i S g a₀).shape` is not `randTerm _ 32`. -/
def NotRandDhPkShape (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (k : DY.Bytes) : Prop :=
  (∀ s₀ : DY.Bytes, (gamma' i S g k).shape ≠ dhPk s₀) ∨
  ∃ a₀ : DY.Bytes, k = dhPk a₀ ∧ ∀ t : Nat, (gamma' i S g a₀).shape ≠ randTerm t 32

theorem notRandDhPkShape_of_not_termShapeId (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {k : DY.Bytes} (hnot : ¬TermShapeId k) : NotRandDhPkShape i S g k := by
  have hpack := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF k
  rcases hv : k.view? DY.DiffieHellman.DhPk.SubF with _ | ⟨⟨a₀⟩⟩
  · refine .inl fun s₀ hsh => ?_
    obtain ⟨sk₀, hk_eq, _⟩ := view?_dhPk_shape_eq_some_inv i S g k s₀
      (by rw [hsh]; exact DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := s₀ })
    have hv2 : (dhPk sk₀).view? DY.DiffieHellman.DhPk.SubF = some { sk := sk₀ } :=
      DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := sk₀ }
    rw [hk_eq, hv2] at hv; cases hv
  · rw [hv] at hpack; dsimp only at hpack
    refine .inr ⟨a₀, hpack.symm, fun t ht => hnot ?_⟩
    have ha₀_eq : a₀ = randTerm t 32 :=
      (eq_randTerm32_of_shape_eq i S g t ((termShapeId_randTerm32 t i S g).trans ht.symm)).symm
    rw [← hpack, ha₀_eq]
    exact termShapeId_dhPk (termShapeId_randTerm32 t)

theorem notRandDhPkShape_or_eq_dhPk_randTerm32 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (k : DY.Bytes) :
    NotRandDhPkShape i S g k ∨ ∃ t : Nat, k = dhPk (randTerm t 32) := by
  have hpack := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF k
  rcases hv : k.view? DY.DiffieHellman.DhPk.SubF with _ | ⟨⟨a₀⟩⟩
  · refine .inl (.inl fun s₀ hsh => ?_)
    obtain ⟨sk₀, hk_eq, _⟩ := view?_dhPk_shape_eq_some_inv i S g k s₀
      (by rw [hsh]; exact DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := s₀ })
    have hv2 : (dhPk sk₀).view? DY.DiffieHellman.DhPk.SubF = some { sk := sk₀ } :=
      DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := sk₀ }
    rw [hk_eq, hv2] at hv; cases hv
  · rw [hv] at hpack; dsimp only at hpack
    by_cases hex : ∃ t : Nat, (gamma' i S g a₀).shape = randTerm t 32
    · obtain ⟨t, ht⟩ := hex
      have ha₀_eq : a₀ = randTerm t 32 :=
        (eq_randTerm32_of_shape_eq i S g t ((termShapeId_randTerm32 t i S g).trans ht.symm)).symm
      exact .inr ⟨t, hpack.symm.trans (congrArg dhPk ha₀_eq)⟩
    · exact .inl (.inr ⟨a₀, hpack.symm, fun t ht => hex ⟨t, ht⟩⟩)

theorem not_notRandDhPkShape_dhPk_randTerm32 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (t : Nat) : ¬NotRandDhPkShape i S g (dhPk (randTerm t 32)) := by
  rintro (h1 | ⟨a₀, heq, ha₀⟩)
  · apply h1 (randTerm t 32)
    rw [Symbolic.Swarm.CREF.TR.G1.shape_dhPk_tr, termShapeId_randTerm32 t i S g]
  · have ha₀_eq : randTerm t 32 = a₀ := dhPk_inj_peel heq
    subst ha₀_eq
    exact ha₀ t (termShapeId_randTerm32 t i S g)

section UnsealedNotRandDhPk
unseal DY.Bytes

private theorem randTerm_timestamp_inj_peel {t₁ t₂ n₁ n₂ : Nat} (h : randTerm t₁ n₁ = randTerm t₂ n₂) : t₁ = t₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.Random.Random) { timestamp := t₁, size := n₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.Random.Random) { timestamp := t₂, size := n₂ }
  change DY.Bytes.view? (randTerm t₁ n₁) _ = _ at h1; change DY.Bytes.view? (randTerm t₂ n₂) _ = _ at h2
  rw [h, h2] at h1; injection h1 with h1; injection h1 with ht _; exact ht.symm

private theorem dh_shape_eq_pack_or_dhPk_peel (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (pk sk : DY.Bytes) :
    (gamma' i S g (DiffieHellman.dh pk sk)).shape = ({ pk := (gamma' i S g pk).shape, sk := (gamma' i S g sk).shape } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack ∨
    ∃ s₀ s₁ : DY.Bytes, (gamma' i S g (DiffieHellman.dh pk sk)).shape = ({ pk := dhPk s₀, sk := s₁ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
  unfold DiffieHellman.CanDH.dh instCanDHBytes; dsimp only
  rcases pk.view? DY.DiffieHellman.DhPk.SubF with _ | ⟨⟨a⟩⟩; · exact .inl (shape_dh_pack_hsb i S g { pk := pk, sk := sk })
  dsimp only; split
  · refine .inr ⟨(gamma' i S g a).shape, (gamma' i S g sk).shape, ?_⟩; rw [shape_dh_pack_hsb]; dsimp only
    change ({ pk := (gamma' i S g (dhPk a)).shape, sk := (gamma' i S g sk).shape } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack = _
    rw [Symbolic.Swarm.CREF.TR.G1.shape_dhPk_tr]; rfl
  · refine .inr ⟨(gamma' i S g sk).shape, (gamma' i S g a).shape, ?_⟩; rw [shape_dh_pack_hsb]; dsimp only
    change ({ pk := (gamma' i S g (dhPk sk)).shape, sk := (gamma' i S g a).shape } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack = _
    rw [Symbolic.Swarm.CREF.TR.G1.shape_dhPk_tr]; rfl

private theorem dh_dhPk_randTerm_shape_cases_peel (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (a : DY.Bytes) (t : Nat) :
    (gamma' i S g (DiffieHellman.dh (dhPk a) (randTerm t 32))).shape =
      ({ pk := dhPk (gamma' i S g a).shape, sk := randTerm t 32 } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack ∨
    (gamma' i S g (DiffieHellman.dh (dhPk a) (randTerm t 32))).shape =
      ({ pk := dhPk (randTerm t 32), sk := (gamma' i S g a).shape } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
  unfold DiffieHellman.CanDH.dh instCanDHBytes; dsimp only
  have hva : (({ sk := a } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).view? DY.DiffieHellman.DhPk.SubF = some { sk := a } :=
    DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := a }
  rw [hva]; dsimp only; split
  · left; rw [shape_dh_pack_hsb]; dsimp only
    change ({ pk := (gamma' i S g (dhPk a)).shape, sk := (gamma' i S g (randTerm t 32)).shape } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack = _
    rw [Symbolic.Swarm.CREF.TR.G1.shape_dhPk_tr, termShapeId_randTerm32 t i S g]; rfl
  · right; rw [shape_dh_pack_hsb]; dsimp only
    change ({ pk := (gamma' i S g (dhPk (randTerm t 32))).shape, sk := (gamma' i S g a).shape } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack = _
    rw [Symbolic.Swarm.CREF.TR.G1.shape_dhPk_tr, termShapeId_randTerm32 t i S g]; rfl

/-- General DH `.shape` inversion for `NotRandDhPkShape`: if `NotRandDhPkShape i S g k₂` holds and
`(DiffieHellman.dh k₁ (randTerm t₁ 32)).shape = (DiffieHellman.dh k₂ (randTerm t₂ 32)).shape`,
then `NotRandDhPkShape i S g k₁` holds and `t₁ = t₂`. -/
theorem dh_shape_eq_of_notRandDhPkShape (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {k₁ k₂ : DY.Bytes} {t₁ t₂ : Nat} (hk₂ : NotRandDhPkShape i S g k₂)
    (hdh : (gamma' i S g (DiffieHellman.dh k₁ (randTerm t₁ 32))).shape =
      (gamma' i S g (DiffieHellman.dh k₂ (randTerm t₂ 32))).shape) :
    NotRandDhPkShape i S g k₁ ∧ t₁ = t₂ := by
  rcases hk₂ with hne₂ | ⟨a₂, rfl, ha₂⟩
  · have hrhs : (gamma' i S g (DiffieHellman.dh k₂ (randTerm t₂ 32))).shape =
        ({ pk := (gamma' i S g k₂).shape, sk := randTerm t₂ 32 } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
      unfold DiffieHellman.CanDH.dh instCanDHBytes; dsimp only
      have hpack := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF k₂
      rcases hv : k₂.view? DY.DiffieHellman.DhPk.SubF with _ | ⟨⟨a⟩⟩
      · rw [shape_dh_pack_hsb, termShapeId_randTerm32 t₂ i S g]
      · rw [hv] at hpack; dsimp only at hpack
        have hsh_eq : (gamma' i S g (dhPk a)).shape = (gamma' i S g k₂).shape := congrArg (fun x => (gamma' i S g x).shape) hpack
        rw [Symbolic.Swarm.CREF.TR.G1.shape_dhPk_tr] at hsh_eq
        exact False.elim (hne₂ (gamma' i S g a).shape hsh_eq.symm)
    rw [hrhs] at hdh
    rcases dh_shape_eq_pack_or_dhPk_peel i S g k₁ (randTerm t₁ 32) with hlhs | ⟨s₀, s₁, hlhs⟩
    · rw [hlhs, termShapeId_randTerm32 t₁ i S g] at hdh
      have hinj := pack_inj_peel hdh; injection hinj with hpk_eq hsk_eq
      exact ⟨.inl (fun s₀ => hpk_eq ▸ hne₂ s₀), randTerm_timestamp_inj_peel hsk_eq⟩
    · rw [hlhs] at hdh; have hinj := pack_inj_peel hdh; injection hinj with hpk_eq _
      exact False.elim (hne₂ s₀ hpk_eq.symm)
  · have hpack₁ := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF k₁
    rcases hv₁ : k₁.view? DY.DiffieHellman.DhPk.SubF with _ | ⟨⟨a₁⟩⟩
    · have hlhs : (gamma' i S g (DiffieHellman.dh k₁ (randTerm t₁ 32))).shape =
          ({ pk := (gamma' i S g k₁).shape, sk := randTerm t₁ 32 } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
        unfold DiffieHellman.CanDH.dh instCanDHBytes; dsimp only; rw [hv₁]; dsimp only
        rw [shape_dh_pack_hsb, termShapeId_randTerm32 t₁ i S g]
      rw [hlhs] at hdh
      have h_dhPk : ∃ s₀, (gamma' i S g k₁).shape = dhPk s₀ := by
        rcases dh_dhPk_randTerm_shape_cases_peel i S g a₂ t₂ with hrhs | hrhs <;>
          (rw [hrhs] at hdh; have hinj := pack_inj_peel hdh; injection hinj with hpk_eq _; exact ⟨_, hpk_eq⟩)
      obtain ⟨s₀, hs₀⟩ := h_dhPk
      obtain ⟨sk₀, hk₁_eq, _⟩ := view?_dhPk_shape_eq_some_inv i S g k₁ s₀
        (by rw [hs₀]; exact DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := s₀ })
      have hv2 : (dhPk sk₀).view? DY.DiffieHellman.DhPk.SubF = some { sk := sk₀ } :=
        DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := sk₀ }
      rw [hk₁_eq, hv2] at hv₁; cases hv₁
    · rw [hv₁] at hpack₁; dsimp only at hpack₁; have hk₁_eq : k₁ = dhPk a₁ := hpack₁.symm
      rw [hk₁_eq] at hdh ⊢
      rcases dh_dhPk_randTerm_shape_cases_peel i S g a₁ t₁ with hlhs | hlhs <;>
        rcases dh_dhPk_randTerm_shape_cases_peel i S g a₂ t₂ with hrhs | hrhs <;>
        (rw [hlhs, hrhs] at hdh; have hinj := pack_inj_peel hdh; injection hinj with hpk_eq hsk_eq;
         have hpk_inj := dhPk_inj_peel hpk_eq)
      · exact ⟨.inr ⟨a₁, rfl, fun t => hpk_inj ▸ ha₂ t⟩, randTerm_timestamp_inj_peel hsk_eq⟩
      · exact False.elim (ha₂ t₁ hsk_eq.symm)
      · exact False.elim (ha₂ t₁ hpk_inj.symm)
      · exact ⟨.inr ⟨a₁, rfl, fun t => hsk_eq ▸ ha₂ t⟩, randTerm_timestamp_inj_peel hpk_inj⟩

theorem dh_eq_of_shape_eq_dh_dhPk_randTerm32 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {k₁ : DY.Bytes} {t₁ t_m t₀ : Nat}
    (hdh : (gamma' i S g (DiffieHellman.dh k₁ (randTerm t₁ 32))).shape =
      (gamma' i S g (DiffieHellman.dh (dhPk (randTerm t_m 32)) (randTerm t₀ 32))).shape) :
    (∃ t_k : Nat, k₁ = dhPk (randTerm t_k 32)) ∧
    DiffieHellman.dh k₁ (randTerm t₁ 32) = DiffieHellman.dh (dhPk (randTerm t_m 32)) (randTerm t₀ 32) := by
  rcases notRandDhPkShape_or_eq_dhPk_randTerm32 i S g k₁ with hnr₁ | ⟨t_k, rfl⟩
  · exact False.elim (not_notRandDhPkShape_dhPk_randTerm32 i S g t_m
      (dh_shape_eq_of_notRandDhPkShape i S g hnr₁ hdh.symm).1)
  · refine ⟨⟨t_k, rfl⟩, ?_⟩
    have hid₁ := termShapeId_dh (termShapeId_dhPk (termShapeId_randTerm32 t_k)) (termShapeId_randTerm32 t₁) i S g
    have hid₂ := termShapeId_dh (termShapeId_dhPk (termShapeId_randTerm32 t_m)) (termShapeId_randTerm32 t₀) i S g
    exact hid₁.symm.trans (hdh.trans hid₂)

end UnsealedNotRandDhPk

/-! ## DH secret inversion for non-`TermShapeId` ratchet keys -/

/-- When `pk.AttackerKnows T` and an attacker-known `dh_u` matches the `gamma'` shape of
`DiffieHellman.dh (X25519.normalizeX25519Key pk) (randTerm t_dhs 32)` under `¬TermShapeId pk`,
either `(randTerm t_dhs 32).AttackerKnows T` or both `(dhPk (randTerm t_dhs 32)).AttackerKnows T`
and `X25519.normalizeX25519Key pk = dhPk a₀` with `a₀.AttackerKnows T`. -/
theorem dh_not_termShapeId_attackerKnows_cases (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hreach : ReachableTrace T) {pk dh_u : DY.Bytes} {t_dhs : Nat}
    (hpk_ak : pk.AttackerKnows T)
    (hdh_u_ak : dh_u.AttackerKnows T)
    (hdh_sh : (gamma' i S g dh_u).shape = (gamma' i S g (DiffieHellman.dh (X25519.normalizeX25519Key pk) (randTerm t_dhs 32))).shape) :
    (randTerm t_dhs 32).AttackerKnows T ∨
    ((dhPk (randTerm t_dhs 32)).AttackerKnows T ∧
      ∃ a₀ : DY.Bytes, DY.X25519.normalizeX25519Key pk = dhPk a₀ ∧ a₀.AttackerKnows T) := by
  let r := randTerm t_dhs 32
  have hdh_u_safe : KdfRkSafe T dh_u := kdfRkSafe_of_attackerKnows_reachable hreach hdh_u_ak
  have hk_ak : (X25519.normalizeX25519Key pk).AttackerKnows T := attackerKnows_x25519Key_srk hpk_ak
  have hpack_k := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF (X25519.normalizeX25519Key pk)
  rcases hvk : (X25519.normalizeX25519Key pk).view? DY.DiffieHellman.DhPk.SubF with _ | ⟨⟨a₀⟩⟩
  · have hdhr : DiffieHellman.dh (X25519.normalizeX25519Key pk) r =
        ({ pk := X25519.normalizeX25519Key pk, sk := r } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
      unfold DiffieHellman.CanDH.dh instCanDHBytes; dsimp only; rw [hvk]
    have hview_u : DY.Bytes.view? (gamma' i S g dh_u).shape DY.DiffieHellman.Dh.SubF =
        some { pk := (gamma' i S g (X25519.normalizeX25519Key pk)).shape, sk := (gamma' i S g r).shape } := by
      rw [hdh_sh, hdhr, shape_dh_pack_hsb]; exact DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) _
    obtain ⟨pk₀, sk₀, rfl, hpk₀_sh, hsk₀_sh⟩ := view?_dh_shape_eq_some_inv i S g dh_u _ _ hview_u
    have hsk₀_eq : sk₀ = r := (eq_randTerm32_of_shape_eq i S g t_dhs hsk₀_sh.symm).symm; subst hsk₀_eq
    rcases kdfRkSafe_dh_pack_inv hdh_u_safe with ⟨_, hr_ak⟩ | ⟨s0, rfl, _, _⟩
    · exact .inl hr_ak
    · have hview_k : DY.Bytes.view? (gamma' i S g (X25519.normalizeX25519Key pk)).shape DY.DiffieHellman.DhPk.SubF =
          some { sk := (gamma' i S g s0).shape } := by
        rw [← hpk₀_sh, Symbolic.Swarm.CREF.TR.G1.shape_dhPk_tr]; exact DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) _
      obtain ⟨sk_k, hk_eq, _⟩ := view?_dhPk_shape_eq_some_inv i S g (X25519.normalizeX25519Key pk) _ hview_k
      have hv_sk : (dhPk sk_k).view? DY.DiffieHellman.DhPk.SubF = some { sk := sk_k } :=
        DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := sk_k }
      rw [hk_eq, hv_sk] at hvk; contradiction
  · rw [hvk] at hpack_k; dsimp only at hpack_k; have hk_eq : X25519.normalizeX25519Key pk = dhPk a₀ := hpack_k.symm
    have hdhr : DiffieHellman.dh (dhPk a₀) r = ({ pk := dhPk a₀, sk := r } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack ∨
        DiffieHellman.dh (dhPk a₀) r = ({ pk := dhPk r, sk := a₀ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
      unfold DiffieHellman.CanDH.dh instCanDHBytes; dsimp only
      have hva : (({ sk := a₀ } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).view? DY.DiffieHellman.DhPk.SubF = some { sk := a₀ } :=
        DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := a₀ }
      rw [hva]; dsimp only; split <;> [exact .inl rfl; exact .inr rfl]
    have hk_dhPk_ak : (dhPk a₀).AttackerKnows T := hk_eq ▸ hk_ak
    rw [hk_eq] at hdh_sh
    rcases ((kdfRkSafe_dhPk_iff a₀).mp (kdfRkSafe_of_attackerKnows_reachable hreach hk_dhPk_ak)).2 with ⟨t_sk, rfl⟩ | ha₀_ak
    · rcases hdhr with hdhr_eq | hdhr_eq
      · have hview_u : DY.Bytes.view? (gamma' i S g dh_u).shape DY.DiffieHellman.Dh.SubF =
            some { pk := (gamma' i S g (dhPk (randTerm t_sk 32))).shape, sk := (gamma' i S g r).shape } := by
          rw [hdh_sh, hdhr_eq, shape_dh_pack_hsb]; exact DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) _
        obtain ⟨pk₀, sk₀, rfl, hpk₀_sh, hsk₀_sh⟩ := view?_dh_shape_eq_some_inv i S g dh_u _ _ hview_u
        have hpk₀_eq : pk₀ = dhPk (randTerm t_sk 32) := (eq_dhPk_randTerm32_of_shape_eq i S g t_sk hpk₀_sh.symm).symm; subst hpk₀_eq
        have hsk₀_eq : sk₀ = r := (eq_randTerm32_of_shape_eq i S g t_dhs hsk₀_sh.symm).symm; subst hsk₀_eq
        rcases kdfRkSafe_dh_pack_inv hdh_u_safe with ⟨_, hr_ak⟩ | ⟨s0, hdhPk_eq, hs0_ak, hdhPk_r_ak⟩
        · exact .inl hr_ak
        · rw [← dhPk_inj_peel hdhPk_eq] at hs0_ak
          exact .inr ⟨hdhPk_r_ak, randTerm t_sk 32, hk_eq, hs0_ak⟩
      · have hview_u : DY.Bytes.view? (gamma' i S g dh_u).shape DY.DiffieHellman.Dh.SubF =
            some { pk := (gamma' i S g (dhPk r)).shape, sk := (gamma' i S g (randTerm t_sk 32)).shape } := by
          rw [hdh_sh, hdhr_eq, shape_dh_pack_hsb]; exact DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) _
        obtain ⟨pk₀, sk₀, rfl, hpk₀_sh, hsk₀_sh⟩ := view?_dh_shape_eq_some_inv i S g dh_u _ _ hview_u
        have hpk₀_eq : pk₀ = dhPk r := (eq_dhPk_randTerm32_of_shape_eq i S g t_dhs hpk₀_sh.symm).symm; subst hpk₀_eq
        have hsk₀_eq : sk₀ = randTerm t_sk 32 := (eq_randTerm32_of_shape_eq i S g t_sk hsk₀_sh.symm).symm; subst hsk₀_eq
        rcases kdfRkSafe_dh_pack_inv hdh_u_safe with ⟨hdhPk_r_ak, hsk₀_ak⟩ | ⟨s0, hdhPk_eq, hs0_ak, _⟩
        · exact .inr ⟨hdhPk_r_ak, randTerm t_sk 32, hk_eq, hsk₀_ak⟩
        · rw [← dhPk_inj_peel hdhPk_eq] at hs0_ak; exact .inl hs0_ak
    · rcases hdhr with hdhr_eq | hdhr_eq
      · have hview_u : DY.Bytes.view? (gamma' i S g dh_u).shape DY.DiffieHellman.Dh.SubF =
            some { pk := (gamma' i S g (dhPk a₀)).shape, sk := (gamma' i S g r).shape } := by
          rw [hdh_sh, hdhr_eq, shape_dh_pack_hsb]; exact DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) _
        obtain ⟨pk₀, sk₀, rfl, _, hsk₀_sh⟩ := view?_dh_shape_eq_some_inv i S g dh_u _ _ hview_u
        have hsk₀_eq : sk₀ = r := (eq_randTerm32_of_shape_eq i S g t_dhs hsk₀_sh.symm).symm; subst hsk₀_eq
        rcases kdfRkSafe_dh_pack_inv hdh_u_safe with ⟨_, hr_ak⟩ | ⟨_, _, _, hdhPk_r_ak⟩
        · exact .inl hr_ak
        · exact .inr ⟨hdhPk_r_ak, a₀, hk_eq, ha₀_ak⟩
      · have hview_u : DY.Bytes.view? (gamma' i S g dh_u).shape DY.DiffieHellman.Dh.SubF =
            some { pk := (gamma' i S g (dhPk r)).shape, sk := (gamma' i S g a₀).shape } := by
          rw [hdh_sh, hdhr_eq, shape_dh_pack_hsb]; exact DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) _
        obtain ⟨pk₀, sk₀, rfl, hpk₀_sh, _⟩ := view?_dh_shape_eq_some_inv i S g dh_u _ _ hview_u
        have hpk₀_eq : pk₀ = dhPk r := (eq_dhPk_randTerm32_of_shape_eq i S g t_dhs hpk₀_sh.symm).symm; subst hpk₀_eq
        rcases kdfRkSafe_dh_pack_inv hdh_u_safe with ⟨hdhPk_r_ak, _⟩ | ⟨s0, hdhPk_eq, hs0_ak, _⟩
        · exact .inr ⟨hdhPk_r_ak, a₀, hk_eq, ha₀_ak⟩
        · rw [← dhPk_inj_peel hdhPk_eq] at hs0_ak; exact .inl hs0_ak

/-- On any reachable trace `tr`, every attacker-known `X25519.Variant.SubF` term has
`¬(v.variation = 0 ∧ v.torsion = 0)` and `DY.Bytes.view? v.key DY.X25519.Variant.SubF = none`. -/
theorem variant_variation_ne_zero_of_attackerKnows_reachable_peel
    {tr : ExecTrace} (hreach : ReachableTrace tr)
    {u : DY.Bytes} (hu : u.AttackerKnows tr)
    (v : DY.X25519.Variant.SubF DY.Bytes)
    (hview : u.view? DY.X25519.Variant.SubF = some v) :
    ¬(v.variation = 0 ∧ v.torsion = 0) ∧ DY.Bytes.view? v.key DY.X25519.Variant.SubF = none := by
  have hpack := DY.Bytes.pack_view? DY.X25519.Variant.SubF u
  rw [hview] at hpack; dsimp only at hpack
  have hsafe : KdfRkSafeS tr v.pack := by
    rw [show v.pack = u from hpack]
    exact kdfRkSafeS_of_attackerKnows_reachable hreach hu
  obtain ⟨hvar, hkv, _⟩ := (kdfRkSafeS_variant_iff v).mp hsafe
  exact ⟨hvar, hkv⟩

end Symbolic.Swarm.CREF.TR.G1
