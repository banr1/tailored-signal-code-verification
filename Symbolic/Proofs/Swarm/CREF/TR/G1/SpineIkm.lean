/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeModKem
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Seed Spine Grammars over IKM Bases and DH Holes

Defines `SpineB B` (honest seed spine over an arbitrary IKM base predicate `B`) and `SpineR W B`
(role-parity-indexed seed spine with `kdfRk` DH holes `W`), together with the lockstep subterm
relation `Peel` and the shape-injectivity theorems `eq_of_shape_eq_of_spineB` and
`eq_of_shape_eq_of_spineR_peel`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.SpineIkm

cref_open
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal.TripleRatchet (kdfCk kdfRk chainKeyAt)
open DY.Libsignal.PQXDH (pqxdhIkm pqxdhKdf)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.G1 (ShapeId eq_of_shape_eq_of_shapeId)

/-- The seed grammar over IKM-level bases `B` (`ShapeModKem.SpineK` with `IkmK KP` replaced by `B`). -/
inductive SpineB (B : DY.Bytes → Prop) : DY.Bytes → Prop
  | hsRk {ikm : DY.Bytes} : B ikm → SpineB B (pqxdhKdf ikm).rk
  | hsCk {ikm : DY.Bytes} : B ikm → SpineB B (pqxdhKdf ikm).ck
  | rkStep1 {rk dhOut : DY.Bytes} : SpineB B rk → ShapeId dhOut → SpineB B (kdfRk rk dhOut).1
  | rkStep2 {rk dhOut : DY.Bytes} : SpineB B rk → ShapeId dhOut → SpineB B (kdfRk rk dhOut).2
  | ckStep1 {ck : DY.Bytes} : SpineB B ck → SpineB B (kdfCk ck).1
  | ckStep2 {ck : DY.Bytes} : SpineB B ck → SpineB B (kdfCk ck).2

/-- Base injectivity at `(i, S, g)`: equal-shape `B` IKMs are equal. -/
def BaseShapeInj (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (B : DY.Bytes → Prop) : Prop :=
  ∀ m₁ m₂ : DY.Bytes, B m₁ → B m₂ → (gamma' i S g m₁).shape = (gamma' i S g m₂).shape → m₁ = m₂

open ShapeModKem in
/-- Two `SpineB` terms with equal shapes are equal under base injectivity `BaseShapeInj i S g B`. -/
theorem eq_of_shape_eq_of_spineB {B : DY.Bytes → Prop}
    {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} (hbase : BaseShapeInj i S g B)
    {u v : DY.Bytes}
    (hu : SpineB B u) (hv : SpineB B v)
    (h : (gamma' i S g u).shape = (gamma' i S g v).shape) : u = v := by
  induction hu generalizing v with
  | hsRk hm₁ =>
    cases hv with
    | hsRk hm₂ =>
      rw [hbase _ _ hm₁ hm₂ (shape_pqxdhKdf_rk_inj i S g h)]
    | hsCk _ => exact False.elim (shape_pqxdhKdf_rk_ne_ck i S g _ _ h)
    | rkStep1 _ _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).1 h)
    | rkStep2 _ _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).2.1 h)
    | ckStep1 _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).1 h)
    | ckStep2 _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).2.1 h)
  | hsCk hm₁ =>
    cases hv with
    | hsRk _ => exact False.elim (shape_pqxdhKdf_rk_ne_ck i S g _ _ h.symm)
    | hsCk hm₂ =>
      rw [hbase _ _ hm₁ hm₂ (shape_pqxdhKdf_ck_inj i S g h)]
    | rkStep1 _ _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).2.2.1 h)
    | rkStep2 _ _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).2.2.2 h)
    | ckStep1 _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).2.2.1 h)
    | ckStep2 _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).2.2.2 h)
  | rkStep1 _ hd₁ ih =>
    cases hv with
    | hsRk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).1 h.symm)
    | hsCk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).2.2.1 h.symm)
    | rkStep1 hr₂ hd₂ =>
      obtain ⟨hrk, hdh⟩ := shape_kdfRk_fst_inj i S g h
      rw [ih hr₂ hrk, eq_of_shape_eq_of_shapeId hd₁ hd₂ hdh]
    | rkStep2 _ _ => exact False.elim (shape_kdfRk_fst_ne_snd i S g _ _ _ _ h)
    | ckStep1 _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).1 h)
    | ckStep2 _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).2.1 h)
  | rkStep2 _ hd₁ ih =>
    cases hv with
    | hsRk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).2.1 h.symm)
    | hsCk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).2.2.2 h.symm)
    | rkStep1 _ _ => exact False.elim (shape_kdfRk_fst_ne_snd i S g _ _ _ _ h.symm)
    | rkStep2 hr₂ hd₂ =>
      obtain ⟨hrk, hdh⟩ := shape_kdfRk_snd_inj i S g h
      rw [ih hr₂ hrk, eq_of_shape_eq_of_shapeId hd₁ hd₂ hdh]
    | ckStep1 _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).2.2.1 h)
    | ckStep2 _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).2.2.2 h)
  | ckStep1 _ ih =>
    cases hv with
    | hsRk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).1 h.symm)
    | hsCk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).2.2.1 h.symm)
    | rkStep1 _ _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).1 h.symm)
    | rkStep2 _ _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).2.2.1 h.symm)
    | ckStep1 hc₂ => rw [ih hc₂ (shape_kdfCk_fst_inj i S g h)]
    | ckStep2 _ => exact False.elim (shape_kdfCk_fst_ne_snd i S g _ _ h)
  | ckStep2 _ ih =>
    cases hv with
    | hsRk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).2.1 h.symm)
    | hsCk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).2.2.2 h.symm)
    | rkStep1 _ _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).2.1 h.symm)
    | rkStep2 _ _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).2.2.2 h.symm)
    | ckStep1 _ => exact False.elim (shape_kdfCk_fst_ne_snd i S g _ _ h.symm)
    | ckStep2 hc₂ => rw [ih hc₂ (shape_kdfCk_snd_inj i S g h)]

/-! ## Role-Parity Spine Grammar with DH Holes -/

/-- Role- and `kdfRk`-depth-parity-indexed seed grammar with DH hole predicate `W`. -/
inductive SpineR (W : DY.Bytes → Prop) (B : Bool → DY.Bytes → Prop) : Bool → DY.Bytes → Prop
  | hsRk {b : Bool} {ikm : DY.Bytes} : B b ikm → SpineR W B b (pqxdhKdf ikm).rk
  | hsCk {b : Bool} {ikm : DY.Bytes} : B b ikm → SpineR W B b (pqxdhKdf ikm).ck
  | rkStep1 {b : Bool} {rk dhOut : DY.Bytes} :
      SpineR W B b rk → W dhOut → SpineR W B (!b) (kdfRk rk dhOut).1
  | rkStep2 {b : Bool} {rk dhOut : DY.Bytes} :
      SpineR W B b rk → W dhOut → SpineR W B (!b) (kdfRk rk dhOut).2
  | ckStep1 {b : Bool} {ck : DY.Bytes} : SpineR W B b ck → SpineR W B b (kdfCk ck).1
  | ckStep2 {b : Bool} {ck : DY.Bytes} : SpineR W B b ck → SpineR W B b (kdfCk ck).2

theorem SpineR.mono {W W' : DY.Bytes → Prop} {B B' : Bool → DY.Bytes → Prop}
    (hW : ∀ m, W m → W' m) (hB : ∀ c m, B c m → B' c m) {b : Bool}
    {u : DY.Bytes} (hu : SpineR W B b u) : SpineR W' B' b u := by
  induction hu with
  | hsRk hi => exact .hsRk (hB _ _ hi)
  | hsCk hi => exact .hsCk (hB _ _ hi)
  | rkStep1 _ hd ih => exact .rkStep1 ih (hW _ hd)
  | rkStep2 _ hd ih => exact .rkStep2 ih (hW _ hd)
  | ckStep1 _ ih => exact .ckStep1 ih
  | ckStep2 _ ih => exact .ckStep2 ih

theorem spineR_chainKeyAt {W : DY.Bytes → Prop} {B : Bool → DY.Bytes → Prop} {b : Bool}
    {ck : DY.Bytes} (h : SpineR W B b ck) : ∀ n : Nat, SpineR W B b (chainKeyAt ck n)
  | 0 => h
  | n + 1 => spineR_chainKeyAt (.ckStep1 h) n

/-- Corresponding subterm pairs reached from `(u₀, v₀)` by peeling the same constructor off both
sides: through `kdfRk` (root key and DH input), `kdfCk` and `pqxdhKdf` (the IKM). -/
inductive Peel (u₀ v₀ : DY.Bytes) : DY.Bytes → DY.Bytes → Prop
  | refl : Peel u₀ v₀ u₀ v₀
  | rk1L {r₁ r₂ d₁ d₂ : DY.Bytes} : Peel u₀ v₀ (kdfRk r₁ d₁).1 (kdfRk r₂ d₂).1 → Peel u₀ v₀ r₁ r₂
  | rk1R {r₁ r₂ d₁ d₂ : DY.Bytes} : Peel u₀ v₀ (kdfRk r₁ d₁).1 (kdfRk r₂ d₂).1 → Peel u₀ v₀ d₁ d₂
  | rk2L {r₁ r₂ d₁ d₂ : DY.Bytes} : Peel u₀ v₀ (kdfRk r₁ d₁).2 (kdfRk r₂ d₂).2 → Peel u₀ v₀ r₁ r₂
  | rk2R {r₁ r₂ d₁ d₂ : DY.Bytes} : Peel u₀ v₀ (kdfRk r₁ d₁).2 (kdfRk r₂ d₂).2 → Peel u₀ v₀ d₁ d₂
  | ck1 {c₁ c₂ : DY.Bytes} : Peel u₀ v₀ (kdfCk c₁).1 (kdfCk c₂).1 → Peel u₀ v₀ c₁ c₂
  | ck2 {c₁ c₂ : DY.Bytes} : Peel u₀ v₀ (kdfCk c₁).2 (kdfCk c₂).2 → Peel u₀ v₀ c₁ c₂
  | hsRk {m₁ m₂ : DY.Bytes} : Peel u₀ v₀ (pqxdhKdf m₁).rk (pqxdhKdf m₂).rk → Peel u₀ v₀ m₁ m₂
  | hsCk {m₁ m₂ : DY.Bytes} : Peel u₀ v₀ (pqxdhKdf m₁).ck (pqxdhKdf m₂).ck → Peel u₀ v₀ m₁ m₂
  | ikmDh1 {a₁ b₁ c₁ a₂ b₂ c₂ s₁ s₂ : DY.Bytes} {d₁ d₂ : Option DY.Bytes} :
      Peel u₀ v₀ (pqxdhIkm a₁ b₁ c₁ d₁ s₁) (pqxdhIkm a₂ b₂ c₂ d₂ s₂) → Peel u₀ v₀ a₁ a₂
  | ikmDh2 {a₁ b₁ c₁ a₂ b₂ c₂ s₁ s₂ : DY.Bytes} {d₁ d₂ : Option DY.Bytes} :
      Peel u₀ v₀ (pqxdhIkm a₁ b₁ c₁ d₁ s₁) (pqxdhIkm a₂ b₂ c₂ d₂ s₂) → Peel u₀ v₀ b₁ b₂
  | ikmDh3 {a₁ b₁ c₁ a₂ b₂ c₂ s₁ s₂ : DY.Bytes} {d₁ d₂ : Option DY.Bytes} :
      Peel u₀ v₀ (pqxdhIkm a₁ b₁ c₁ d₁ s₁) (pqxdhIkm a₂ b₂ c₂ d₂ s₂) → Peel u₀ v₀ c₁ c₂
  | ikmDh4 {a₁ b₁ c₁ a₂ b₂ c₂ s₁ s₂ e₁ e₂ : DY.Bytes} :
      Peel u₀ v₀ (pqxdhIkm a₁ b₁ c₁ (some e₁) s₁) (pqxdhIkm a₂ b₂ c₂ (some e₂) s₂) →
        Peel u₀ v₀ e₁ e₂
  | ikmKem {a₁ b₁ c₁ a₂ b₂ c₂ s₁ s₂ : DY.Bytes} {d₁ d₂ : Option DY.Bytes} :
      Peel u₀ v₀ (pqxdhIkm a₁ b₁ c₁ d₁ s₁) (pqxdhIkm a₂ b₂ c₂ d₂ s₂) → Peel u₀ v₀ s₁ s₂

/-- Base IKM pair `(m₁, m₂)` reached by lockstep peeling through `pqxdhKdf` from `(u₀, v₀)`. -/
def PeelKdf (u₀ v₀ m₁ m₂ : DY.Bytes) : Prop :=
  Peel u₀ v₀ (pqxdhKdf m₁).rk (pqxdhKdf m₂).rk ∨ Peel u₀ v₀ (pqxdhKdf m₁).ck (pqxdhKdf m₂).ck

theorem PeelKdf.peel {u₀ v₀ m₁ m₂ : DY.Bytes} (h : PeelKdf u₀ v₀ m₁ m₂) : Peel u₀ v₀ m₁ m₂ :=
  h.elim .hsRk .hsCk

/-- DH hole of the honest spine: a DH output with a `ShapeId` secret and normalized public input. -/
def DhHole (d : DY.Bytes) : Prop :=
  ∃ pk sk : DY.Bytes, d = dh (DY.X25519.normalizeX25519Key pk) sk ∧ ShapeId sk

theorem dhHole_agree {pk sk : DY.Bytes} (hsk : ShapeId sk) :
    DhHole (DY.Libsignal.PQXDH.agree pk sk) :=
  ⟨pk, sk, rfl, hsk⟩

theorem xor_not_not (b b' : Bool) : ((!b) ^^ (!b')) = (b ^^ b') := by
  cases b <;> cases b' <;> rfl

open ShapeModKem in
/-- Two `SpineR` terms reached by `Peel` from `(u₀, v₀)` with equal shapes and index xor `p` are
equal, given injectivity on reached hole pairs and role-xor-`p` base pairs. -/
theorem eq_of_shape_eq_of_spineR_peel {W : DY.Bytes → Prop} {B : Bool → DY.Bytes → Prop}
    {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {u₀ v₀ : DY.Bytes} {p : Bool}
    (hhole : ∀ d₁ d₂ : DY.Bytes, Peel u₀ v₀ d₁ d₂ → W d₁ → W d₂ →
      (gamma' i S g d₁).shape = (gamma' i S g d₂).shape → d₁ = d₂)
    (hbase : ∀ (c c' : Bool) (m₁ m₂ : DY.Bytes), PeelKdf u₀ v₀ m₁ m₂ → B c m₁ → B c' m₂ →
      (c ^^ c') = p → (gamma' i S g m₁).shape = (gamma' i S g m₂).shape → m₁ = m₂)
    {b : Bool} {u : DY.Bytes} (hu : SpineR W B b u) :
    ∀ {b' : Bool} {v : DY.Bytes}, SpineR W B b' v → Peel u₀ v₀ u v →
      (gamma' i S g u).shape = (gamma' i S g v).shape → (b ^^ b') = p → u = v := by
  induction hu with
  | hsRk hm₁ =>
    intro b' v hv hP h hp
    cases hv with
    | hsRk hm₂ => rw [hbase _ _ _ _ (.inl hP) hm₁ hm₂ hp (shape_pqxdhKdf_rk_inj i S g h)]
    | hsCk _ => exact False.elim (shape_pqxdhKdf_rk_ne_ck i S g _ _ h)
    | rkStep1 _ _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).1 h)
    | rkStep2 _ _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).2.1 h)
    | ckStep1 _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).1 h)
    | ckStep2 _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).2.1 h)
  | hsCk hm₁ =>
    intro b' v hv hP h hp
    cases hv with
    | hsRk _ => exact False.elim (shape_pqxdhKdf_rk_ne_ck i S g _ _ h.symm)
    | hsCk hm₂ => rw [hbase _ _ _ _ (.inr hP) hm₁ hm₂ hp (shape_pqxdhKdf_ck_inj i S g h)]
    | rkStep1 _ _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).2.2.1 h)
    | rkStep2 _ _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).2.2.2 h)
    | ckStep1 _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).2.2.1 h)
    | ckStep2 _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).2.2.2 h)
  | rkStep1 _ hd₁ ih =>
    intro b' v hv hP h hp
    cases hv with
    | hsRk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).1 h.symm)
    | hsCk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).2.2.1 h.symm)
    | rkStep1 hr₂ hd₂ =>
      obtain ⟨hrk, hdh⟩ := shape_kdfRk_fst_inj i S g h
      rw [ih hr₂ (.rk1L hP) hrk (by rw [← xor_not_not]; exact hp),
        hhole _ _ (.rk1R hP) hd₁ hd₂ hdh]
    | rkStep2 _ _ => exact False.elim (shape_kdfRk_fst_ne_snd i S g _ _ _ _ h)
    | ckStep1 _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).1 h)
    | ckStep2 _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).2.1 h)
  | rkStep2 _ hd₁ ih =>
    intro b' v hv hP h hp
    cases hv with
    | hsRk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).2.1 h.symm)
    | hsCk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfRk i S g _ _ _).2.2.2 h.symm)
    | rkStep1 _ _ => exact False.elim (shape_kdfRk_fst_ne_snd i S g _ _ _ _ h.symm)
    | rkStep2 hr₂ hd₂ =>
      obtain ⟨hrk, hdh⟩ := shape_kdfRk_snd_inj i S g h
      rw [ih hr₂ (.rk2L hP) hrk (by rw [← xor_not_not]; exact hp),
        hhole _ _ (.rk2R hP) hd₁ hd₂ hdh]
    | ckStep1 _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).2.2.1 h)
    | ckStep2 _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).2.2.2 h)
  | ckStep1 _ ih =>
    intro b' v hv hP h hp
    cases hv with
    | hsRk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).1 h.symm)
    | hsCk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).2.2.1 h.symm)
    | rkStep1 _ _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).1 h.symm)
    | rkStep2 _ _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).2.2.1 h.symm)
    | ckStep1 hc₂ => rw [ih hc₂ (.ck1 hP) (shape_kdfCk_fst_inj i S g h) hp]
    | ckStep2 _ => exact False.elim (shape_kdfCk_fst_ne_snd i S g _ _ h)
  | ckStep2 _ ih =>
    intro b' v hv hP h hp
    cases hv with
    | hsRk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).2.1 h.symm)
    | hsCk _ => exact False.elim ((shape_pqxdhKdf_ne_kdfCk i S g _ _).2.2.2 h.symm)
    | rkStep1 _ _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).2.1 h.symm)
    | rkStep2 _ _ => exact False.elim ((shape_kdfRk_ne_kdfCk i S g _ _ _).2.2.2 h.symm)
    | ckStep1 _ => exact False.elim (shape_kdfCk_fst_ne_snd i S g _ _ h.symm)
    | ckStep2 hc₂ => rw [ih hc₂ (.ck2 hP) (shape_kdfCk_snd_inj i S g h) hp]

end Symbolic.Swarm.CREF.TR.G1.SpineIkm
