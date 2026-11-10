/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Stage1Kyber -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import Init.Data.String
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac

/-!
# Shape Injectivity Modulo KEM Leaves

Proves per-functor `.shape` injectivity and cross-family disjointness (`shape_*_inj`,
`shape_*_ne_*`) for Triple Ratchet and PQXDH KDF terms under `gamma'`, together with KEM leaf
disjointness from concatenations (`shape_kemLeaf_ne_concat`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.ShapeModKem

cref_open
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal.TripleRatchet (hmac hkdfBlock1 hkdfBlock2 kdfCk kdfRk lit litByte)
open DY.Libsignal.PQXDH (pqxdhIkm pqxdhKdf)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.G1 (ShapeId)

/-- A KEM shared-secret leaf term: either the `.2` of an encapsulation or an implicit-rejection
`kemRejKey sk ct`. -/
def KemLeaf (ss : DY.Bytes) : Prop :=
  (∃ pk e : DY.Bytes, ss = (DY.PQKem.kemEncap pk e).2) ∨
  (∃ sk ct : DY.Bytes, ss = DY.PQKem.kemRejKey sk ct)

section Functors

open Symbolic.Swarm.CREF.TR.RecvDecStep (shape_kdfExtract_tr shape_concat_tr)
open Symbolic.Swarm.CREF.TR.G1 (concat_injective kdfExtract_injective shape_literalToBytes
  eq_of_shape_eq_of_shapeId)
open DY.Libsignal.PQXDH (pqxdhLabel)

private theorem literalToBytes_ne_concat (b : ByteArray) (x y : DY.Bytes) :
    Literal.literalToBytes b ≠ Concat.concat x y := by
  intro h
  have h1 := congrArg (fun u => u.view? DY.Concat.Concat.SubF) h
  change (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).view? DY.Concat.Concat.SubF =
    (({ lhs := x, rhs := y } : DY.Concat.Concat.SubF DY.Bytes).pack).view? DY.Concat.Concat.SubF at h1
  rw [Symbolic.DYBridge.DY.Bytes.view?_pack_cross, BytesView.view_pack] at h1
  cases h1

private theorem literalToBytes_injective {a b : ByteArray}
    (h : (Literal.literalToBytes a : DY.Bytes) = Literal.literalToBytes b) : a = b := by
  have h1 := congrArg (fun u : DY.Bytes => u.view? DY.Literal.Literal.SubF) h
  change (({ lit := a } : DY.Literal.Literal.SubF DY.Bytes).pack).view? DY.Literal.Literal.SubF =
    (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).view? DY.Literal.Literal.SubF at h1
  rw [BytesView.view_pack, BytesView.view_pack, Option.some.injEq] at h1
  cases h1
  rfl

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

theorem shape_concat_inj {a₁ b₁ a₂ b₂ : DY.Bytes}
    (h : (gamma' i S g (Concat.concat a₁ b₁)).shape = (gamma' i S g (Concat.concat a₂ b₂)).shape) :
    (gamma' i S g a₁).shape = (gamma' i S g a₂).shape ∧
    (gamma' i S g b₁).shape = (gamma' i S g b₂).shape := by
  rw [shape_concat_tr, shape_concat_tr] at h
  exact concat_injective h

theorem shape_kdfExtract_inj {s₁ m₁ s₂ m₂ : DY.Bytes}
    (h : (gamma' i S g (KdfExtract.kdfExtract s₁ m₁)).shape =
      (gamma' i S g (KdfExtract.kdfExtract s₂ m₂)).shape) :
    (gamma' i S g s₁).shape = (gamma' i S g s₂).shape ∧
    (gamma' i S g m₁).shape = (gamma' i S g m₂).shape := by
  rw [shape_kdfExtract_tr, shape_kdfExtract_tr] at h
  exact kdfExtract_injective h

unseal DY.Bytes in
private instance subKemRejSMK : DY.Bytes.SubFunction (concretizeKemRej S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
private theorem shape_kemRejKey_ne_concat (sk ct a b : DY.Bytes) :
    (gamma' i S g (DY.PQKem.kemRejKey sk ct)).shape ≠ (gamma' i S g (Concat.concat a b)).shape := by
  rw [shape_concat_tr]
  intro h
  have h1 : (gamma' i S g (DY.PQKem.kemRejKey sk ct)).shape =
      DY.PQKem.kemRejKey (gamma' i S g sk).shape (gamma' i S g ct).shape := by
    unfold gamma'
    show ((({ sk := sk, cipher := ct } : DY.PQKem.RejKey.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape = _
    rw [DY.Bytes.rec_eq (concretizeKemRej S) (concretizeAll i S g)]
    rfl
  rw [h1] at h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

theorem shape_kemLeaf_ne_concat {ss a b : DY.Bytes} (h : KemLeaf ss) :
    (gamma' i S g ss).shape ≠ (gamma' i S g (Concat.concat a b)).shape := by
  rcases h with ⟨pk, e, rfl⟩ | ⟨sk, ct, rfl⟩
  · exact Symbolic.Swarm.CREF.Stage1Kyber.shape_kemSS_ne_concat i S g pk e a b
  · exact shape_kemRejKey_ne_concat i S g sk ct a b

theorem shape_hkdfBlock1_inj {p₁ n₁ p₂ n₂ : DY.Bytes}
    (h : (gamma' i S g (hkdfBlock1 p₁ n₁)).shape = (gamma' i S g (hkdfBlock1 p₂ n₂)).shape) :
    (gamma' i S g p₁).shape = (gamma' i S g p₂).shape ∧
    (gamma' i S g n₁).shape = (gamma' i S g n₂).shape := by
  unfold hkdfBlock1 hmac at h
  obtain ⟨hp, hc⟩ := shape_kdfExtract_inj i S g h
  exact ⟨hp, (shape_concat_inj i S g hc).1⟩

theorem shape_hkdfBlock2_inj {p₁ n₁ p₂ n₂ : DY.Bytes}
    (h : (gamma' i S g (hkdfBlock2 p₁ n₁)).shape = (gamma' i S g (hkdfBlock2 p₂ n₂)).shape) :
    (gamma' i S g p₁).shape = (gamma' i S g p₂).shape ∧
    (gamma' i S g n₁).shape = (gamma' i S g n₂).shape := by
  unfold hkdfBlock2 hmac at h
  obtain ⟨_, hc⟩ := shape_kdfExtract_inj i S g h
  obtain ⟨hb1, _⟩ := shape_concat_inj i S g hc
  exact shape_hkdfBlock1_inj i S g hb1

theorem shape_hkdfBlock1_ne_hkdfBlock2 (p₁ n₁ p₂ n₂ : DY.Bytes) :
    (gamma' i S g (hkdfBlock1 p₁ n₁)).shape ≠ (gamma' i S g (hkdfBlock2 p₂ n₂)).shape := by
  intro h
  unfold hkdfBlock1 hkdfBlock2 hmac at h
  obtain ⟨_, hc⟩ := shape_kdfExtract_inj i S g h
  obtain ⟨_, hr⟩ := shape_concat_inj i S g hc
  unfold litByte at hr
  rw [shape_literalToBytes, shape_concat_tr] at hr
  exact literalToBytes_ne_concat _ _ _ hr

theorem shape_kdfCk_fst_inj {c₁ c₂ : DY.Bytes}
    (h : (gamma' i S g (kdfCk c₁).1).shape = (gamma' i S g (kdfCk c₂).1).shape) :
    (gamma' i S g c₁).shape = (gamma' i S g c₂).shape := by
  unfold kdfCk hmac at h
  exact (shape_kdfExtract_inj i S g h).1

theorem shape_kdfCk_snd_inj {c₁ c₂ : DY.Bytes}
    (h : (gamma' i S g (kdfCk c₁).2).shape = (gamma' i S g (kdfCk c₂).2).shape) :
    (gamma' i S g c₁).shape = (gamma' i S g c₂).shape := by
  unfold kdfCk hmac at h
  exact (shape_kdfExtract_inj i S g h).1

theorem shape_kdfCk_fst_ne_snd (c₁ c₂ : DY.Bytes) :
    (gamma' i S g (kdfCk c₁).1).shape ≠ (gamma' i S g (kdfCk c₂).2).shape := by
  intro h
  unfold kdfCk hmac at h
  obtain ⟨_, hr⟩ := shape_kdfExtract_inj i S g h
  unfold litByte at hr
  rw [shape_literalToBytes, shape_literalToBytes] at hr
  have h1 := congrArg (fun a : ByteArray => a.data[0]?) (literalToBytes_injective hr)
  cases h1

theorem shape_kdfRk_fst_inj {r₁ d₁ r₂ d₂ : DY.Bytes}
    (h : (gamma' i S g (kdfRk r₁ d₁).1).shape = (gamma' i S g (kdfRk r₂ d₂).1).shape) :
    (gamma' i S g r₁).shape = (gamma' i S g r₂).shape ∧
    (gamma' i S g d₁).shape = (gamma' i S g d₂).shape := by
  unfold kdfRk at h
  obtain ⟨hprk, _⟩ := shape_hkdfBlock1_inj i S g h
  exact shape_kdfExtract_inj i S g hprk

theorem shape_kdfRk_snd_inj {r₁ d₁ r₂ d₂ : DY.Bytes}
    (h : (gamma' i S g (kdfRk r₁ d₁).2).shape = (gamma' i S g (kdfRk r₂ d₂).2).shape) :
    (gamma' i S g r₁).shape = (gamma' i S g r₂).shape ∧
    (gamma' i S g d₁).shape = (gamma' i S g d₂).shape := by
  unfold kdfRk at h
  obtain ⟨hprk, _⟩ := shape_hkdfBlock2_inj i S g h
  exact shape_kdfExtract_inj i S g hprk

theorem shape_kdfRk_fst_ne_snd (r₁ d₁ r₂ d₂ : DY.Bytes) :
    (gamma' i S g (kdfRk r₁ d₁).1).shape ≠ (gamma' i S g (kdfRk r₂ d₂).2).shape :=
  shape_hkdfBlock1_ne_hkdfBlock2 i S g _ _ _ _

theorem shape_pqxdhKdf_rk_inj {m₁ m₂ : DY.Bytes}
    (h : (gamma' i S g (pqxdhKdf m₁).rk).shape = (gamma' i S g (pqxdhKdf m₂).rk).shape) :
    (gamma' i S g m₁).shape = (gamma' i S g m₂).shape := by
  unfold pqxdhKdf at h
  obtain ⟨hprk, _⟩ := shape_hkdfBlock1_inj i S g h
  exact (shape_kdfExtract_inj i S g hprk).2

theorem shape_pqxdhKdf_ck_inj {m₁ m₂ : DY.Bytes}
    (h : (gamma' i S g (pqxdhKdf m₁).ck).shape = (gamma' i S g (pqxdhKdf m₂).ck).shape) :
    (gamma' i S g m₁).shape = (gamma' i S g m₂).shape := by
  unfold pqxdhKdf at h
  obtain ⟨hprk, _⟩ := shape_hkdfBlock2_inj i S g h
  exact (shape_kdfExtract_inj i S g hprk).2

theorem shape_pqxdhKdf_rk_ne_ck (m₁ m₂ : DY.Bytes) :
    (gamma' i S g (pqxdhKdf m₁).rk).shape ≠ (gamma' i S g (pqxdhKdf m₂).ck).shape :=
  shape_hkdfBlock1_ne_hkdfBlock2 i S g _ _ _ _

private theorem shape_pqxdhLabel_ne_whisperRatchet :
    (gamma' i S g pqxdhLabel).shape ≠ (gamma' i S g (lit "WhisperRatchet")).shape := by
  intro h
  unfold pqxdhLabel lit at h
  rw [shape_literalToBytes, shape_literalToBytes] at h
  have hm := literalToBytes_injective h
  rw [String.toUTF8_eq_toByteArray, String.toUTF8_eq_toByteArray, String.toByteArray_inj] at hm
  have hl := congrArg String.toList hm; revert hl; decide

theorem shape_pqxdhKdf_ne_kdfRk (m r d : DY.Bytes) :
    (gamma' i S g (pqxdhKdf m).rk).shape ≠ (gamma' i S g (kdfRk r d).1).shape ∧
    (gamma' i S g (pqxdhKdf m).rk).shape ≠ (gamma' i S g (kdfRk r d).2).shape ∧
    (gamma' i S g (pqxdhKdf m).ck).shape ≠ (gamma' i S g (kdfRk r d).1).shape ∧
    (gamma' i S g (pqxdhKdf m).ck).shape ≠ (gamma' i S g (kdfRk r d).2).shape := by
  refine ⟨fun h => ?_, shape_hkdfBlock1_ne_hkdfBlock2 i S g _ _ _ _,
    fun h => shape_hkdfBlock1_ne_hkdfBlock2 i S g _ _ _ _ h.symm, fun h => ?_⟩
  · exact shape_pqxdhLabel_ne_whisperRatchet i S g (shape_hkdfBlock1_inj i S g h).2
  · exact shape_pqxdhLabel_ne_whisperRatchet i S g (shape_hkdfBlock2_inj i S g h).2

private theorem shape_hkdfBlock1_ne_hmac_litByte (p n c : DY.Bytes) (b : UInt8) :
    (gamma' i S g (hkdfBlock1 p n)).shape ≠ (gamma' i S g (hmac c (litByte b))).shape := by
  intro h
  unfold hkdfBlock1 hmac litByte at h
  obtain ⟨_, hr⟩ := shape_kdfExtract_inj i S g h
  rw [shape_concat_tr, shape_literalToBytes i S g ⟨#[b]⟩] at hr
  exact literalToBytes_ne_concat _ _ _ hr.symm

private theorem shape_hkdfBlock2_ne_hmac_litByte (p n c : DY.Bytes) (b : UInt8) :
    (gamma' i S g (hkdfBlock2 p n)).shape ≠ (gamma' i S g (hmac c (litByte b))).shape := by
  intro h
  unfold hkdfBlock2 hmac litByte at h
  obtain ⟨_, hr⟩ := shape_kdfExtract_inj i S g h
  rw [shape_concat_tr, shape_literalToBytes i S g ⟨#[b]⟩] at hr
  exact literalToBytes_ne_concat _ _ _ hr.symm

theorem shape_pqxdhKdf_ne_kdfCk (m c : DY.Bytes) :
    (gamma' i S g (pqxdhKdf m).rk).shape ≠ (gamma' i S g (kdfCk c).1).shape ∧
    (gamma' i S g (pqxdhKdf m).rk).shape ≠ (gamma' i S g (kdfCk c).2).shape ∧
    (gamma' i S g (pqxdhKdf m).ck).shape ≠ (gamma' i S g (kdfCk c).1).shape ∧
    (gamma' i S g (pqxdhKdf m).ck).shape ≠ (gamma' i S g (kdfCk c).2).shape :=
  ⟨shape_hkdfBlock1_ne_hmac_litByte i S g _ _ _ _,
   shape_hkdfBlock1_ne_hmac_litByte i S g _ _ _ _,
   shape_hkdfBlock2_ne_hmac_litByte i S g _ _ _ _,
   shape_hkdfBlock2_ne_hmac_litByte i S g _ _ _ _⟩

theorem shape_kdfRk_ne_kdfCk (r d c : DY.Bytes) :
    (gamma' i S g (kdfRk r d).1).shape ≠ (gamma' i S g (kdfCk c).1).shape ∧
    (gamma' i S g (kdfRk r d).1).shape ≠ (gamma' i S g (kdfCk c).2).shape ∧
    (gamma' i S g (kdfRk r d).2).shape ≠ (gamma' i S g (kdfCk c).1).shape ∧
    (gamma' i S g (kdfRk r d).2).shape ≠ (gamma' i S g (kdfCk c).2).shape :=
  ⟨shape_hkdfBlock1_ne_hmac_litByte i S g _ _ _ _,
   shape_hkdfBlock1_ne_hmac_litByte i S g _ _ _ _,
   shape_hkdfBlock2_ne_hmac_litByte i S g _ _ _ _,
   shape_hkdfBlock2_ne_hmac_litByte i S g _ _ _ _⟩

end Functors

end Symbolic.Swarm.CREF.TR.G1.ShapeModKem
