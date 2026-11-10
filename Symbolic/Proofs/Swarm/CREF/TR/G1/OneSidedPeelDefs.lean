/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Stage1Kyber -- shake: keep
import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.BaseAttackerKnowledge
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.Sign
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.Literal
import Symbolic.DYBridge.DY.EquationalTheory.Concat
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.EquationalTheory.DiffieHellman
import Symbolic.DYBridge.DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.EquationalTheory.X25519
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTR
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac
import VCVio.Prelude.Core

/-!
# Shape Inversions and KEM Ciphertext Closure

Proves `gamma'`-shape inversion for `Concat`- and `Dh`-headed terms (`concat_shape_eq_inv`,
`dhPack_shape_eq_inv`) together with the `CtClosed` invariant for attacker-known KEM ciphertexts,
shared secrets, and implicit-rejection keys on reachable composed traces.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY.DiffieHellman
open CryptoProofLib.Refinement (ExternInterpretation)

/-! ## `Concat`-headed shapes -/

def ConcatViewMotive (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sh_l sh_r : DY.Bytes)
    (u : DY.Bytes) : Prop :=
  DY.Bytes.view? (gamma' i S g u).shape DY.Concat.Concat.SubF = some { lhs := sh_l, rhs := sh_r } →
    ∃ l r : DY.Bytes, u = Concat.concat l r ∧ (gamma' i S g l).shape = sh_l ∧
      (gamma' i S g r).shape = sh_r

private theorem container_pack_inj_sub_peel
    (f g : Type → Type)
    [DY.ALaCarte.FunctorSizeOf f] [DY.ALaCarte.FunctorSizeOf g]
    [DY.ALaCarte.SubFunctorTC f g] [DY.ALaCarte.Representable g]
    (x : f (DY.ALaCarte.ContainerFor g)) :
    DY.ALaCarte.Container.pack g (DY.ALaCarte.SubFunctorTC.inj (g := g) x) =
      DY.ALaCarte.Container.pack f x := by
  have hv := DY.ALaCarte.Container.pack_view g (DY.ALaCarte.Container.pack f x)
  rw [Symbolic.DYBridge.DY.ALaCarte.Container.view_pack_cross f g x] at hv
  exact hv

private theorem lift_partialFunDep_peel
    {f g : Type → Type} [DY.ALaCarte.FunctorSizeOf f] [DY.ALaCarte.FunctorSizeOf g]
    [DY.ALaCarte.SubFunctorTC f g] [DY.ALaCarte.Representable g]
    {motive : DY.ALaCarte.ContainerFor g → Prop}
    (h : DY.ALaCarte.Container.PartialFunDep f (g := g) motive)
    (x : f (DY.ALaCarte.ContainerFor g))
    (rec : ∀ y : DY.ALaCarte.ContainerFor g,
      sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf (DY.ALaCarte.SubFunctorTC.inj (g := g) x) → motive y) :
    motive (DY.ALaCarte.Container.pack g (DY.ALaCarte.SubFunctorTC.inj (g := g) x)) := by
  rw [container_pack_inj_sub_peel f g x]
  exact h x fun y hy => rec y (DY.ALaCarte.SubFunctorTC.sizeOf_inj (g := g) x ▸ hy)

unseal DY.Bytes in
private theorem partialFunDep_not_concat
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sh_l sh_r : DY.Bytes)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hg : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm),
      DY.Bytes.view? (gF x rec).shape DY.Concat.Concat.SubF = none) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF) (ConcatViewMotive i S g sh_l sh_r) := by
  intro x _ hview
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview; unfold gamma' at hview
  rw [DY.Bytes.rec_eq gF (concretizeAll i S g) x, hg x _] at hview; contradiction

unseal DY.Bytes in
private theorem partialFunDep_concat (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (sh_l sh_r : DY.Bytes) :
    DY.ALaCarte.Container.PartialFunDep DY.Concat.Concat.SubF (g := DY.BytesF)
      (ConcatViewMotive i S g sh_l sh_r) := by
  intro x _ hview
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview; unfold gamma' at hview
  rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll i S g) x] at hview; dsimp only [concretizeConcat, node] at hview
  rw [DY.BytesView.view_pack (SubF := DY.Concat.Concat.SubF)] at hview
  injection hview with h1; cases h1
  exact ⟨x.lhs, x.rhs, (Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x).symm, rfl, rfl⟩

unseal DY.Bytes in
private instance subKemRejOSPD (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemRej S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
theorem view?_concat_shape_eq_some_inv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (u sh_l sh_r : DY.Bytes) : ConcatViewMotive i S g sh_l sh_r u := by
  refine DY.ALaCarte.Container.rec (f := DY.BytesF) (motive := ConcatViewMotive i S g sh_l sh_r) ?_ u
  rintro ⟨⟨id, hid⟩, val⟩ rec
  match id with
  | 0 =>
    exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeRandom g)
      (fun _ _ => by dsimp only [concretizeRandom]; split <;> erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) val rec
  | 1 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;>
    [exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r concretizeLit (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec; omega]
  | 2 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;> [exact lift_partialFunDep_peel (partialFunDep_concat i S g sh_l sh_r) v rec; omega]
  | 3 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ | _
         · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeDhPk i) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeDh i) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · omega
  | 4 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;>
    [exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeKdf i) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec; omega]
  | 5 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;>
    [exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeSym i) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec; omega]
  | 6 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;>
    [exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r concretizeTrunc (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec; omega]
  | 7 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;>
    [exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeVariant i) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec; omega]
  | 8 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ | _ | _ | _
         · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeKemPk S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeKemEncap i)
             (fun _ _ => by dsimp only [concretizeKemEncap]; split <;> erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeKemSS i S)
             (fun _ _ => by dsimp only [concretizeKemSS]; split <;> erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeKemRej S)
             (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · omega
  | 9 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ | _
         · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeVk S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeSign S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · omega
  | 10 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ | _ | _ | _ | _ | _ | _
          · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeSpqrInit S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeSpqrSendState S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeSpqrSendKey S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeSpqrSendMsg S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeSpqrRecvState S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeSpqrRecvKey S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeSpqrChainKey S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · omega
  | 11 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;>
    [exact lift_partialFunDep_peel (partialFunDep_not_concat i S g sh_l sh_r (concretizeTrWire g) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec; omega]
  | _ + 12 => omega

/-- If `u` has the shape of `concat l₁ r₁`, then `u = concat l₀ r₀` with matching child shapes. -/
theorem concat_shape_eq_inv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) {u l₁ r₁ : DY.Bytes}
    (hsh : (gamma' i S g u).shape = (gamma' i S g (Concat.concat l₁ r₁)).shape) :
    ∃ l₀ r₀ : DY.Bytes, u = Concat.concat l₀ r₀ ∧
      (gamma' i S g l₀).shape = (gamma' i S g l₁).shape ∧
      (gamma' i S g r₀).shape = (gamma' i S g r₁).shape := by
  have hview : DY.Bytes.view? (gamma' i S g u).shape DY.Concat.Concat.SubF =
      some { lhs := (gamma' i S g l₁).shape, rhs := (gamma' i S g r₁).shape } := by
    rw [hsh, Symbolic.Swarm.CREF.TR.RecvDecStep.shape_concat_tr]
    exact DY.BytesView.view_pack (SubF := DY.Concat.Concat.SubF) _
  exact view?_concat_shape_eq_some_inv i S g u _ _ hview

/-! ## `Dh`-headed shapes -/

def DhViewMotive (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sh_pk sh_sk : DY.Bytes)
    (u : DY.Bytes) : Prop :=
  DY.Bytes.view? (gamma' i S g u).shape DY.DiffieHellman.Dh.SubF = some { pk := sh_pk, sk := sh_sk } →
    ∃ pk₀ sk₀ : DY.Bytes, u = (({ pk := pk₀, sk := sk₀ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) ∧
      (gamma' i S g pk₀).shape = sh_pk ∧ (gamma' i S g sk₀).shape = sh_sk

unseal DY.Bytes in
private theorem partialFunDep_not_dhPack
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sh_pk sh_sk : DY.Bytes)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hg : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm),
      DY.Bytes.view? (gF x rec).shape DY.DiffieHellman.Dh.SubF = none) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF) (DhViewMotive i S g sh_pk sh_sk) := by
  intro x _ hview
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview; unfold gamma' at hview
  rw [DY.Bytes.rec_eq gF (concretizeAll i S g) x, hg x _] at hview; contradiction

unseal DY.Bytes in
private theorem partialFunDep_dhPack (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (sh_pk sh_sk : DY.Bytes) :
    DY.ALaCarte.Container.PartialFunDep DY.DiffieHellman.Dh.SubF (g := DY.BytesF)
      (DhViewMotive i S g sh_pk sh_sk) := by
  intro x _ hview
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview; unfold gamma' at hview
  rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g) x] at hview; dsimp only [concretizeDh, node] at hview
  rw [DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF)] at hview
  injection hview with h1; cases h1
  exact ⟨x.pk, x.sk, (Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x).symm, rfl, rfl⟩

unseal DY.Bytes in
theorem view?_dhPack_shape_eq_some_inv_c (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (u sh_pk sh_sk : DY.Bytes) : DhViewMotive i S g sh_pk sh_sk u := by
  refine DY.ALaCarte.Container.rec (f := DY.BytesF) (motive := DhViewMotive i S g sh_pk sh_sk) ?_ u
  rintro ⟨⟨id, hid⟩, val⟩ rec
  match id with
  | 0 =>
    exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeRandom g)
      (fun _ _ => by dsimp only [concretizeRandom]; split <;> erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) val rec
  | 1 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;>
    [exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk concretizeLit (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec; omega]
  | 2 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;>
    [exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk concretizeConcat (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec; omega]
  | 3 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ | _
         · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeDhPk i) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · exact lift_partialFunDep_peel (partialFunDep_dhPack i S g sh_pk sh_sk) v rec
         · omega
  | 4 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;>
    [exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeKdf i) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec; omega]
  | 5 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;>
    [exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeSym i) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec; omega]
  | 6 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;>
    [exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk concretizeTrunc (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec; omega]
  | 7 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;>
    [exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeVariant i) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec; omega]
  | 8 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ | _ | _ | _
         · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeKemPk S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeKemEncap i)
             (fun _ _ => by dsimp only [concretizeKemEncap]; split <;> erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeKemSS i S)
             (fun _ _ => by dsimp only [concretizeKemSS]; split <;> erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeKemRej S)
             (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · omega
  | 9 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ | _
         · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeVk S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeSign S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
         · omega
  | 10 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ | _ | _ | _ | _ | _ | _
          · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeSpqrInit S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeSpqrSendState S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeSpqrSendKey S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeSpqrSendMsg S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeSpqrRecvState S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeSpqrRecvKey S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeSpqrChainKey S) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec
          · omega
  | 11 => rcases val with ⟨⟨sid, _⟩, v⟩; rcases sid with _ | _ <;>
    [exact lift_partialFunDep_peel (partialFunDep_not_dhPack i S g sh_pk sh_sk (concretizeTrWire g) (fun _ _ => by erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _])) v rec; omega]
  | _ + 12 => omega

theorem shape_dhPack_c (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (p s : DY.Bytes) :
    (gamma' i S g (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)).shape =
      ({ pk := (gamma' i S g p).shape, sk := (gamma' i S g s).shape } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
  unfold gamma'; show ((({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape = _
  rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g)]; rfl

/-- If `u` has the shape of the `Dh` pack `{p₁, s₁}`, then `u` is a `Dh` pack with matching child
shapes. -/
theorem dhPack_shape_eq_inv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) {u p₁ s₁ : DY.Bytes}
    (hsh : (gamma' i S g u).shape =
      (gamma' i S g (({ pk := p₁, sk := s₁ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)).shape) :
    ∃ pk₀ sk₀ : DY.Bytes, u = (({ pk := pk₀, sk := sk₀ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) ∧
      (gamma' i S g pk₀).shape = (gamma' i S g p₁).shape ∧
      (gamma' i S g sk₀).shape = (gamma' i S g s₁).shape := by
  have hview : DY.Bytes.view? (gamma' i S g u).shape DY.DiffieHellman.Dh.SubF =
      some { pk := (gamma' i S g p₁).shape, sk := (gamma' i S g s₁).shape } := by
    rw [hsh, shape_dhPack_c]
    exact DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) _
  exact view?_dhPack_shape_eq_some_inv_c i S g u _ _ hview

/-! ## KEM ciphertext and shared-secret provenance (`CtClosed`) -/

section Stage1CtClosed

open DY DY.Comparse
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg RecvChain SessionInfo KeyDir
  KeyComponent createChain consumeMessageKey setRecvChain findRecvChain recvChainFor kdfCk
  chainKeyAt trMsgKeys trHonestWireMsg parseTrSignalMsg spqrA2B spqrB2A messageVersion
  x25519LowOrder maxReceiverChains)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles
  PreKeyMsgHandles pqxdhKdf opkUsedB registerIdentity registerCorruptIdentity genSignedPrekey
  genPQPrekey genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK compromiseOPK invertDH
  invertKEM)
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED.CompPresPQXDH
open Symbolic.Swarm.CREF.Stage1Kyber

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-- Provenance of `PQKem.Encap`, `PQKem.SharedSecret`, and `PQKem.RejKey` nodes reachable through
destructible wrappers in `AttackerKnows T`. -/
inductive CtClosed (T : ExecTrace) : DY.Bytes → Prop
  | atom {b : DY.Bytes} :
      DY.Bytes.view? b DY.DiffieHellman.DhPk.SubF = none → DY.Bytes.view? b DY.PQKem.Pk.SubF = none →
      DY.Bytes.view? b DY.PQKem.Encap.SubF = none → DY.Bytes.view? b DY.PQKem.SharedSecret.SubF = none →
      DY.Bytes.view? b DY.Concat.Concat.SubF = none → DY.Bytes.view? b DY.SymEnc.Enc.SubF = none →
      DY.Bytes.view? b DY.TrWire.TrWireMsg.SubF = none →
      DY.Bytes.view? b DY.X25519.Variant.SubF = none → DY.Bytes.view? b DY.Spqr.InitState.SubF = none →
      DY.Bytes.view? b DY.Spqr.SendState.SubF = none → DY.Bytes.view? b DY.Spqr.RecvState.SubF = none →
      DY.Bytes.view? b DY.PQKem.RejKey.SubF = none →
      CtClosed T b
  | dhPk {sk : DY.Bytes} : CtClosed T sk → CtClosed T (DiffieHellman.dhPk sk)
  | kemPk {sk : DY.Bytes} : CtClosed T sk → CtClosed T (DY.PQKem.kemPk sk)
  | encap (x : DY.PQKem.Encap.SubF DY.Bytes) :
      (x.entropy.AttackerKnows T ∨ ∃ t a b ikA ikB spk pqpk opk ek ct keys,
        T.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5) ∧
        x.pk = pqpk ∧ x.entropy = randTerm (t + 1) 32) → CtClosed T x.pack
  | kemSS (x : DY.PQKem.SharedSecret.SubF DY.Bytes) :
      (x.entropy.AttackerKnows T ∨ ∃ t a b ikA ikB spk pqpk opk ek ct keys,
        T.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5) ∧
        x.pk = pqpk ∧ x.entropy = randTerm (t + 1) 32) → CtClosed T x.pack
  | rejKey {sk ct : DY.Bytes} : sk.AttackerKnows T → ct.AttackerKnows T → CtClosed T (DY.PQKem.kemRejKey sk ct)
  | concat {l r : DY.Bytes} : CtClosed T l → CtClosed T r → CtClosed T (Concat.concat l r)
  | symEnc {k iv m : DY.Bytes} : CtClosed T m → CtClosed T (SymEnc.symEnc k iv m)
  | trWireMsg (x : TrWire.TrWireMsg.SubF DY.Bytes) :
      CtClosed T x.senderRatchetKey → CtClosed T x.ciphertext → CtClosed T x.pqRatchet → CtClosed T x.pack
  | variant (x : X25519.Variant.SubF DY.Bytes) : CtClosed T x.key → CtClosed T x.pack
  | spqrInit (x : Spqr.InitState.SubF DY.Bytes) : CtClosed T x.authKey → CtClosed T x.params → CtClosed T x.pack
  | spqrSendState (x : Spqr.SendState.SubF DY.Bytes) : CtClosed T x.st → CtClosed T x.coins → CtClosed T x.pack
  | spqrRecvState (x : Spqr.RecvState.SubF DY.Bytes) : CtClosed T x.st → CtClosed T x.msg → CtClosed T x.pack

section UnsealedCtClosed
unseal DY.Bytes

private theorem pack_inj_ct {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    {x₁ x₂ : SubF DY.Bytes} (h : BytesView.pack x₁ = BytesView.pack x₂) : x₁ = x₂ := by
  have h1 : DY.Bytes.view? (BytesView.pack x₁) SubF = some x₁ := DY.BytesView.view_pack (SubF := SubF) x₁
  have h2 : DY.Bytes.view? (BytesView.pack x₂) SubF = some x₂ := DY.BytesView.view_pack (SubF := SubF) x₂
  rw [h, h2] at h1; injection h1 with h1; exact h1.symm

private theorem dh_eq_pack_ct (p s : DY.Bytes) :
    ∃ pk' sk', DiffieHellman.dh p s = ({ pk := pk', sk := sk' } : DiffieHellman.Dh.SubF DY.Bytes).pack := by
  dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh]; split <;> [split <;> exact ⟨_, _, rfl⟩; exact ⟨_, _, rfl⟩]

private theorem spqrSend_snd_fst_eq_ct (st coins : DY.Bytes) :
    (∃ k p i, (Spqr.spqrSend st coins).2.1 = Spqr.spqrChainKey k p i) ∨
    (∃ x : Spqr.SendKey.SubF DY.Bytes, (Spqr.spqrSend st coins).2.1 = x.pack) := by
  dsimp only [Spqr.spqrSend]; split <;> [exact .inl ⟨_, _, _, rfl⟩; exact .inr ⟨_, rfl⟩]

private theorem spqrRecv_snd_eq_ct {st msg : DY.Bytes} {idx : UInt32} {r : DY.Bytes × DY.Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r) :
    r.2 = Spqr.zeroKey ∨ (∃ k p i, r.2 = Spqr.spqrChainKey k p i) ∨
    (∃ x : Spqr.RecvKey.SubF DY.Bytes, r.2 = x.pack) := by
  unfold Spqr.spqrRecv at hrecv; split at hrecv; · cases hrecv
  split at hrecv <;>
    [(split at hrecv <;> [skip; cases hrecv]; injection hrecv with hr; rw [← hr]; dsimp only;
      split <;> [exact .inl rfl; exact .inr (.inl ⟨_, _, _, rfl⟩)]);
     (injection hrecv with hr; rw [← hr]; exact .inr (.inr ⟨_, rfl⟩))]

theorem ctClosed_random (T : ExecTrace) (r : DY.Random.SubF DY.Bytes) : CtClosed T (DY.Random.Random.pack r) :=
  .atom (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
theorem ctClosed_literal (T : ExecTrace) (b : ByteArray) : CtClosed T (Literal.literalToBytes b) :=
  .atom (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
theorem ctClosed_dh (T : ExecTrace) (pk sk : DY.Bytes) : CtClosed T (DiffieHellman.dh pk sk) := by
  obtain ⟨p, s, heq⟩ := dh_eq_pack_ct pk sk; rw [heq]
  exact .atom (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
theorem ctClosed_kdfExtract (T : ExecTrace) (s i : DY.Bytes) : CtClosed T (KdfExtract.kdfExtract s i) :=
  .atom (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
theorem ctClosed_trunc8 (T : ExecTrace) (inp : DY.Bytes) : CtClosed T (Trunc.trunc8 inp) :=
  .atom (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
theorem ctClosed_vk (T : ExecTrace) (sk : DY.Bytes) : CtClosed T (Signature.vk sk) :=
  .atom (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
theorem ctClosed_sign (T : ExecTrace) (sk m r : DY.Bytes) : CtClosed T (Signature.sign sk m r) :=
  .atom (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
theorem ctClosed_spqrChainKey (T : ExecTrace) (k p i : DY.Bytes) : CtClosed T (Spqr.spqrChainKey k p i) :=
  .atom (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
theorem ctClosed_spqrSend_state {T : ExecTrace} {st coins : DY.Bytes}
    (hst : CtClosed T st) (hc : CtClosed T coins) : CtClosed T (Spqr.spqrSend st coins).1 :=
  .spqrSendState { st := st, coins := coins } hst hc
theorem ctClosed_spqrSend_key (T : ExecTrace) (st coins : DY.Bytes) : CtClosed T (Spqr.spqrSend st coins).2.1 := by
  rcases spqrSend_snd_fst_eq_ct st coins with ⟨k, p, i, heq⟩ | ⟨x, heq⟩ <;> rw [heq]
  · exact ctClosed_spqrChainKey T k p i
  · exact .atom (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
theorem ctClosed_spqrSend_msg (T : ExecTrace) (st coins : DY.Bytes) : CtClosed T (Spqr.spqrSend st coins).2.2 :=
  .atom (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
theorem ctClosed_spqrRecv_state {T : ExecTrace} {st msg : DY.Bytes} {idx : UInt32} {r : DY.Bytes × DY.Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r) (hst : CtClosed T st) (hmsg : CtClosed T msg) : CtClosed T r.1 := by
  rw [Spqr.spqrRecv_state st msg idx r hrecv]; exact .spqrRecvState { st := st, msg := msg } hst hmsg
theorem ctClosed_spqrRecv_key {T : ExecTrace} {st msg : DY.Bytes} {idx : UInt32} {r : DY.Bytes × DY.Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r) : CtClosed T r.2 := by
  rcases spqrRecv_snd_eq_ct hrecv with heq | ⟨k, p, i, heq⟩ | ⟨x, heq⟩ <;> rw [heq]
  · exact ctClosed_literal T _
  · exact ctClosed_spqrChainKey T k p i
  · exact .atom (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)

theorem ctClosed_dhPk_iff {T : ExecTrace} (sk : DY.Bytes) : CtClosed T (DiffieHellman.dhPk sk) ↔ CtClosed T sk := by
  refine ⟨fun hs => ?_, CtClosed.dhPk⟩; generalize hx : DiffieHellman.dhPk sk = x at hs
  have hview : DY.Bytes.view? x DY.DiffieHellman.DhPk.SubF = some { sk := sk } := hx ▸ DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) { sk := sk }
  cases hs
  case atom hdp _ _ _ _ _ _ _ _ _ _ _ => rw [hdp] at hview; contradiction
  case dhPk h => have hinj : ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes) = _ := pack_inj_ct hx; injection hinj with h1; subst h1; exact h
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem ctClosed_kemPk_iff {T : ExecTrace} (sk : DY.Bytes) : CtClosed T (DY.PQKem.kemPk sk) ↔ CtClosed T sk := by
  refine ⟨fun hs => ?_, CtClosed.kemPk⟩; generalize hx : DY.PQKem.kemPk sk = x at hs
  have hview : DY.Bytes.view? x DY.PQKem.Pk.SubF = some { sk := sk } := hx ▸ DY.BytesView.view_pack (SubF := DY.PQKem.Pk.SubF) { sk := sk }
  cases hs
  case atom _ hkp _ _ _ _ _ _ _ _ _ _ => rw [hkp] at hview; contradiction
  case kemPk h => have hinj : ({ sk := sk } : DY.PQKem.Pk.SubF DY.Bytes) = _ := pack_inj_ct hx; injection hinj with h1; subst h1; exact h
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem ctClosed_encap_iff {T : ExecTrace} (x : DY.PQKem.Encap.SubF DY.Bytes) :
    CtClosed T x.pack ↔ (x.entropy.AttackerKnows T ∨ ∃ t a b ikA ikB spk pqpk opk ek ct keys,
      T.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5) ∧ x.pk = pqpk ∧ x.entropy = randTerm (t + 1) 32) := by
  refine ⟨fun hs => ?_, CtClosed.encap x⟩; generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.PQKem.Encap.SubF = some x := hx ▸ DY.BytesView.view_pack (SubF := DY.PQKem.Encap.SubF) x
  cases hs
  case atom _ _ he _ _ _ _ _ _ _ _ _ => rw [he] at hview; contradiction
  case encap _ h => have hx' := pack_inj_ct hx; subst hx'; exact h
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem ctClosed_kemSS_iff {T : ExecTrace} (x : DY.PQKem.SharedSecret.SubF DY.Bytes) :
    CtClosed T x.pack ↔ (x.entropy.AttackerKnows T ∨ ∃ t a b ikA ikB spk pqpk opk ek ct keys,
      T.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5) ∧ x.pk = pqpk ∧ x.entropy = randTerm (t + 1) 32) := by
  refine ⟨fun hs => ?_, CtClosed.kemSS x⟩; generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.PQKem.SharedSecret.SubF = some x := hx ▸ DY.BytesView.view_pack (SubF := DY.PQKem.SharedSecret.SubF) x
  cases hs
  case atom _ _ _ hss _ _ _ _ _ _ _ _ => rw [hss] at hview; contradiction
  case kemSS _ h => have hx' := pack_inj_ct hx; subst hx'; exact h
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem ctClosed_rejKey_iff {T : ExecTrace} (sk ct : DY.Bytes) :
    CtClosed T (DY.PQKem.kemRejKey sk ct) ↔ sk.AttackerKnows T ∧ ct.AttackerKnows T := by
  refine ⟨fun hs => ?_, fun ⟨hsk, hct⟩ => .rejKey hsk hct⟩; generalize hx : DY.PQKem.kemRejKey sk ct = x at hs
  have hview : DY.Bytes.view? x DY.PQKem.RejKey.SubF = some { sk := sk, cipher := ct } :=
    hx ▸ DY.BytesView.view_pack (SubF := DY.PQKem.RejKey.SubF) { sk := sk, cipher := ct }
  cases hs
  case atom _ _ _ _ _ _ _ _ _ _ _ hrk => rw [hrk] at hview; contradiction
  case rejKey hsk hct =>
    have hinj : ({ sk := sk, cipher := ct } : DY.PQKem.RejKey.SubF DY.Bytes) = _ := pack_inj_ct hx
    injection hinj with h1 h2; subst h1 h2; exact ⟨hsk, hct⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem ctClosed_concat_iff {T : ExecTrace} (l r : DY.Bytes) : CtClosed T (Concat.concat l r) ↔ CtClosed T l ∧ CtClosed T r := by
  refine ⟨fun hs => ?_, fun ⟨hl, hr⟩ => .concat hl hr⟩; generalize hx : Concat.concat l r = x at hs
  have hview : DY.Bytes.view? x DY.Concat.Concat.SubF = some { lhs := l, rhs := r } := hx ▸ DY.BytesView.view_pack (SubF := DY.Concat.Concat.SubF) { lhs := l, rhs := r }
  cases hs
  case atom _ _ _ _ hc _ _ _ _ _ _ _ => rw [hc] at hview; contradiction
  case concat hl hr => have hinj : ({ lhs := l, rhs := r } : DY.Concat.Concat.SubF DY.Bytes) = _ := pack_inj_ct hx; injection hinj with h1 h2; subst h1 h2; exact ⟨hl, hr⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem ctClosed_symEnc_iff {T : ExecTrace} (k iv m : DY.Bytes) : CtClosed T (SymEnc.symEnc k iv m) ↔ CtClosed T m := by
  refine ⟨fun hs => ?_, CtClosed.symEnc⟩; generalize hx : SymEnc.symEnc k iv m = x at hs
  have hview : DY.Bytes.view? x DY.SymEnc.Enc.SubF = some { key := k, iv := iv, msg := m } := hx ▸ DY.BytesView.view_pack (SubF := DY.SymEnc.Enc.SubF) { key := k, iv := iv, msg := m }
  cases hs
  case atom _ _ _ _ _ he _ _ _ _ _ _ => rw [he] at hview; contradiction
  case symEnc hm => have hinj : ({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes) = _ := pack_inj_ct hx; injection hinj with _ _ h3; subst h3; exact hm
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem ctClosed_trWireMsg_iff {T : ExecTrace} (w : TrWire.TrWireMsg.SubF DY.Bytes) :
    CtClosed T w.pack ↔ CtClosed T w.senderRatchetKey ∧ CtClosed T w.ciphertext ∧ CtClosed T w.pqRatchet := by
  refine ⟨fun hs => ?_, fun ⟨h1, h2, h3⟩ => .trWireMsg w h1 h2 h3⟩; generalize hx : w.pack = x at hs
  have hview : DY.Bytes.view? x DY.TrWire.TrWireMsg.SubF = some w := hx ▸ DY.BytesView.view_pack (SubF := DY.TrWire.TrWireMsg.SubF) w
  cases hs
  case atom _ _ _ _ _ _ htw _ _ _ _ _ => rw [htw] at hview; contradiction
  case trWireMsg _ h1 h2 h3 => have hw := pack_inj_ct hx; subst hw; exact ⟨h1, h2, h3⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem ctClosed_variant_iff {T : ExecTrace} (v : X25519.Variant.SubF DY.Bytes) : CtClosed T v.pack ↔ CtClosed T v.key := by
  refine ⟨fun hs => ?_, CtClosed.variant v⟩; generalize hx : v.pack = x at hs
  have hview : DY.Bytes.view? x DY.X25519.Variant.SubF = some v := hx ▸ DY.BytesView.view_pack (SubF := DY.X25519.Variant.SubF) v
  cases hs
  case atom _ _ _ _ _ _ _ hv _ _ _ _ => rw [hv] at hview; contradiction
  case variant _ hk => have hv := pack_inj_ct hx; subst hv; exact hk
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem ctClosed_spqrInit_iff {T : ExecTrace} (x : Spqr.InitState.SubF DY.Bytes) : CtClosed T x.pack ↔ CtClosed T x.authKey ∧ CtClosed T x.params := by
  refine ⟨fun hs => ?_, fun ⟨hk, hp⟩ => .spqrInit x hk hp⟩; generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.InitState.SubF = some x := hx ▸ DY.BytesView.view_pack (SubF := DY.Spqr.InitState.SubF) x
  cases hs
  case atom _ _ _ _ _ _ _ _ hi _ _ _ => rw [hi] at hview; contradiction
  case spqrInit _ hk hp => have hx' := pack_inj_ct hx; subst hx'; exact ⟨hk, hp⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem ctClosed_spqrSendState_iff {T : ExecTrace} (x : Spqr.SendState.SubF DY.Bytes) : CtClosed T x.pack ↔ CtClosed T x.st ∧ CtClosed T x.coins := by
  refine ⟨fun hs => ?_, fun ⟨hst, hc⟩ => .spqrSendState x hst hc⟩; generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.SendState.SubF = some x := hx ▸ DY.BytesView.view_pack (SubF := DY.Spqr.SendState.SubF) x
  cases hs
  case atom _ _ _ _ _ _ _ _ _ hs' _ _ => rw [hs'] at hview; contradiction
  case spqrSendState _ hst hc => have hx' := pack_inj_ct hx; subst hx'; exact ⟨hst, hc⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem ctClosed_spqrRecvState_iff {T : ExecTrace} (x : Spqr.RecvState.SubF DY.Bytes) : CtClosed T x.pack ↔ CtClosed T x.st ∧ CtClosed T x.msg := by
  refine ⟨fun hs => ?_, fun ⟨hst, hm⟩ => .spqrRecvState x hst hm⟩; generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.RecvState.SubF = some x := hx ▸ DY.BytesView.view_pack (SubF := DY.Spqr.RecvState.SubF) x
  cases hs
  case atom _ _ _ _ _ _ _ _ _ _ hr _ => rw [hr] at hview; contradiction
  case spqrRecvState _ hst hm => have hx' := pack_inj_ct hx; subst hx'; exact ⟨hst, hm⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview

end UnsealedCtClosed

theorem ctClosed_x25519Key {T : ExecTrace} {pk : DY.Bytes} (h : CtClosed T pk) : CtClosed T (X25519.normalizeX25519Key pk) := by
  unfold X25519.normalizeX25519Key; have hpack := DY.Bytes.pack_view? X25519.Variant.SubF pk
  rcases hv : pk.view? X25519.Variant.SubF with _ | x; · exact h
  rw [hv] at hpack; dsimp only at hpack; rw [← hpack] at h; exact (ctClosed_variant_iff x).mp h

theorem ctClosed_x25519TorsionVariant {T : ExecTrace} {key : DY.Bytes} (v : Fin 4) (t : Fin 8 := 0)
    (h : CtClosed T key) : CtClosed T (X25519.x25519TorsionVariant key v t) := by
  dsimp only [X25519.x25519TorsionVariant]; split
  · exact ctClosed_x25519Key h
  · exact .variant { key := X25519.normalizeX25519Key key, variation := v, torsion := t } (ctClosed_x25519Key h)

theorem CtClosed.mono {T T' : ExecTrace} (hle : T ≤ T') {b : DY.Bytes} (h : CtClosed T b) : CtClosed T' b := by
  induction h with
  | atom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => exact .atom h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  | dhPk _ ih => exact .dhPk ih
  | kemPk _ ih => exact .kemPk ih
  | encap x h =>
    exact .encap x (h.imp (DY.Bytes.AttackerKnows_le _ T T' hle)
      fun ⟨t, a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, hev, hpk, he⟩ =>
        ⟨t, a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, CompTrace.eventLoggedAt_mono hle hev, hpk, he⟩)
  | kemSS x h =>
    exact .kemSS x (h.imp (DY.Bytes.AttackerKnows_le _ T T' hle)
      fun ⟨t, a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, hev, hpk, he⟩ =>
        ⟨t, a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, CompTrace.eventLoggedAt_mono hle hev, hpk, he⟩)
  | rejKey hsk hct =>
    exact .rejKey (DY.Bytes.AttackerKnows_le _ T T' hle hsk) (DY.Bytes.AttackerKnows_le _ T T' hle hct)
  | concat _ _ ih1 ih2 => exact .concat ih1 ih2
  | symEnc _ ih => exact .symEnc ih
  | trWireMsg x _ _ _ ih1 ih2 ih3 => exact .trWireMsg x ih1 ih2 ih3
  | variant x _ ih => exact .variant x ih
  | spqrInit x _ _ ih1 ih2 => exact .spqrInit x ih1 ih2
  | spqrSendState x _ _ ih1 ih2 => exact .spqrSendState x ih1 ih2
  | spqrRecvState x _ _ ih1 ih2 => exact .spqrRecvState x ih1 ih2

set_option maxHeartbeats 400000 in
theorem attackerKnows_imp_ctClosed {tr T : ExecTrace} (hle : tr ≤ T)
    (h_base : ∀ msg, Trace.BaseAttackerKnows tr msg → CtClosed T msg) {b : DY.Bytes} (hak : b.AttackerKnows tr) : CtClosed T b := by
  suffices h : b.AttackerKnows tr ∧ CtClosed T b from h.2
  refine DY.Bytes.AttackerKnows.is_least_fixpoint (fun x => x.AttackerKnows tr ∧ CtClosed T x) b tr ?_ ?_ hak
  · change SubAttackerKnowledge.Implies DY.Libsignal.Composed.attackerKnowledge (fun x => x.AttackerKnows tr ∧ CtClosed T x)
    dsimp [DY.Libsignal.Composed.attackerKnowledge]; apply SubAttackerKnowledge.combine.implies
    rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, _⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Random.attackerKnowledge]
      intro x hx; rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at hx; exact hx.elim
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Literal.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | n, _⟩ <;> [skip; omega]
      intro x hx; dsimp [Literal.attackerKnowledge.internal] at hx
      rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at hx
      rcases hx with ⟨bs, rfl⟩; exact ⟨Literal.attacker_knows_literalToBytes bs tr, ctClosed_literal T bs⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Concat.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | _ | n, _⟩ <;> try omega
      · intro x hx; dsimp [Concat.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at hx
        rcases hx with ⟨lhs, rhs, rfl, ⟨hl_ak, hl_s⟩, ⟨hr_ak, hr_s⟩⟩
        exact ⟨Concat.attacker_knows_concat lhs rhs tr hl_ak hr_ak, .concat hl_s hr_s⟩
      · intro x hx; dsimp [Concat.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at hx
        rcases hx with ⟨inp, rhs, i, hsplit, ⟨hinp_ak, hinp_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Concat.splitLeft.attackerKnowledge x tr
          (by rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred]; exact ⟨inp, rhs, i, hsplit, hinp_ak⟩),
          ((ctClosed_concat_iff x rhs).mp (Concat.concat_split inp i x rhs hsplit.symm ▸ hinp_s)).1⟩
      · intro x hx; dsimp [Concat.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hx
        rcases hx with ⟨inp, lhs, i, hsplit, ⟨hinp_ak, hinp_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Concat.splitRight.attackerKnowledge x tr
          (by rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred]; exact ⟨inp, lhs, i, hsplit, hinp_ak⟩),
          ((ctClosed_concat_iff lhs x).mp (Concat.concat_split inp i lhs x hsplit.symm ▸ hinp_s)).2⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DiffieHellman.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | n, _⟩ <;> try omega
      · intro x hx; dsimp [DiffieHellman.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hx
        rcases hx with ⟨sk, rfl, ⟨hsk_ak, hsk_s⟩⟩; exact ⟨DiffieHellman.attacker_knows_dhPk sk tr hsk_ak, .dhPk hsk_s⟩
      · intro x hx; dsimp [DiffieHellman.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at hx
        rcases hx with ⟨pk, sk, rfl, ⟨hpk_ak, _⟩, ⟨hsk_ak, _⟩⟩; exact ⟨DiffieHellman.attacker_knows_dh pk sk tr hpk_ak hsk_ak, ctClosed_dh T pk sk⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, KdfExtract.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | n, _⟩ <;> [skip; omega]
      intro x hx; dsimp [KdfExtract.attackerKnowledge.internal] at hx
      rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at hx
      rcases hx with ⟨salt, ikm, rfl, ⟨hs_ak, _⟩, ⟨hi_ak, _⟩⟩
      exact ⟨KdfExtract.attacker_knows_kdfExtract salt ikm tr hs_ak hi_ak, ctClosed_kdfExtract T salt ikm⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, SymEnc.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | n, _⟩ <;> try omega
      · rintro x ⟨k, iv, msg, rfl, ⟨hk_ak, _⟩, ⟨hiv_ak, _⟩, ⟨hm_ak, hm_s⟩⟩; exact ⟨SymEnc.attacker_knows_symEnc k iv msg tr hk_ak hiv_ak hm_ak, .symEnc hm_s⟩
      · rintro x ⟨key, iv, ct, hdec, ⟨hk_ak, _⟩, ⟨hiv_ak, _⟩, ⟨hct_ak, hct_s⟩⟩
        have heq := SymEnc.symDec_eq_some key iv ct x hdec.symm; rw [heq] at hct_s
        exact ⟨SymEnc.attacker_knows_symDec key iv ct x tr hk_ak hiv_ak hct_ak hdec.symm, (ctClosed_symEnc_iff key iv x).mp hct_s⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Trunc.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | n, _⟩ <;> [skip; omega]
      rintro x ⟨m, rfl, ⟨hm_ak, _⟩⟩; exact ⟨Trunc.attacker_knows_trunc8 m tr hm_ak, ctClosed_trunc8 T m⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, X25519.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | n, _⟩ <;> try omega
      · rintro x ⟨key, v, t, rfl, ⟨hk_ak, hk_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove X25519.x25519Variant.attackerKnowledge _ tr ⟨key, v, t, rfl, hk_ak⟩, ctClosed_x25519TorsionVariant v t hk_s⟩
      · rintro x ⟨v, ⟨hv_ak, hv_s⟩, rfl⟩
        exact ⟨DY.Bytes.AttackerKnows.prove X25519.normalizeX25519Key.attackerKnowledge _ tr ⟨v, hv_ak, rfl⟩, (ctClosed_variant_iff v).mp hv_s⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, PQKem.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | _ | _ | _ | n, _⟩ <;> try omega
      · rintro x ⟨sk, rfl, ⟨hsk_ak, hsk_s⟩⟩; exact ⟨DY.Bytes.AttackerKnows.prove PQKem.kemPk.attackerKnowledge _ tr ⟨sk, rfl, hsk_ak⟩, .kemPk hsk_s⟩
      · rintro x ⟨pk, e, rhs, heq, ⟨hpk_ak, _⟩, ⟨he_ak, _⟩⟩
        refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemEncapCipher.attackerKnowledge x tr ⟨pk, e, rhs, heq, hpk_ak, he_ak⟩, ?_⟩
        have h1 : x = ({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack := (congrArg Prod.fst heq).trans (kemEncap_fst_eq_pack pk e)
        rw [h1]; exact .encap { pk := pk, entropy := e } (.inl (DY.Bytes.AttackerKnows_le e tr T hle he_ak))
      · rintro x ⟨pk, e, lhs, heq, ⟨hpk_ak, _⟩, ⟨he_ak, _⟩⟩
        refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemEncapSS.attackerKnowledge x tr ⟨pk, e, lhs, heq, hpk_ak, he_ak⟩, ?_⟩
        have h2 : x = ({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack := (congrArg Prod.snd heq).trans (kemEncap_snd_eq_pack pk e)
        rw [h2]; exact .kemSS { pk := pk, entropy := e } (.inl (DY.Bytes.AttackerKnows_le e tr T hle he_ak))
      · rintro x ⟨sk, ct, hdec, ⟨hsk_ak, _⟩, ⟨hct_ak, hct_s⟩⟩
        refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemDecap.attackerKnowledge x tr ⟨sk, ct, hdec, hsk_ak, hct_ak⟩, ?_⟩
        obtain ⟨e, hct_eq, rfl⟩ := CompTermAlgebra.kemDecap_eq_some_iff.mp hdec.symm
        rw [hct_eq, kemEncap_fst_eq_pack] at hct_s; rw [kemEncap_snd_eq_pack]
        exact .kemSS { pk := DY.PQKem.kemPk sk, entropy := e } ((ctClosed_encap_iff { pk := DY.PQKem.kemPk sk, entropy := e }).mp hct_s)
      · rintro x ⟨sk, ct, rfl, ⟨hsk_ak, _⟩, ⟨hct_ak, _⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove PQKem.kemRejKey.attackerKnowledge _ tr ⟨sk, ct, rfl, hsk_ak, hct_ak⟩,
          .rejKey (DY.Bytes.AttackerKnows_le _ tr T hle hsk_ak) (DY.Bytes.AttackerKnows_le _ tr T hle hct_ak)⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Signature.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | n, _⟩ <;> try omega
      · intro x hx; dsimp [Signature.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at hx
        rcases hx with ⟨sk, rfl, ⟨hsk_ak, _⟩⟩; exact ⟨Signature.attacker_knows_vk sk tr hsk_ak, ctClosed_vk T sk⟩
      · intro x hx; dsimp [Signature.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hx
        rcases hx with ⟨sk, m, r, rfl, ⟨hsk_ak, _⟩, ⟨hm_ak, _⟩, ⟨hr_ak, _⟩⟩
        exact ⟨Signature.attacker_knows_sign sk m r tr hsk_ak hm_ak hr_ak, ctClosed_sign T sk m r⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Spqr.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, _⟩ <;> try omega
      · rintro x ⟨authKey, params, rfl, ⟨hk_ak, hk_s⟩, ⟨hp_ak, hp_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrInit.attackerKnowledge _ tr ⟨authKey, params, rfl, hk_ak, hp_ak⟩, .spqrInit { authKey := authKey, params := params } hk_s hp_s⟩
      · rintro x ⟨authKey, params, idx, rfl, ⟨hk_ak, _⟩, ⟨hp_ak, _⟩, ⟨hi_ak, _⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrChainKey.attackerKnowledge _ tr ⟨authKey, params, idx, rfl, hk_ak, hp_ak, hi_ak⟩, ctClosed_spqrChainKey T authKey params idx⟩
      · rintro x ⟨st, coins, rfl, ⟨hst_ak, hst_s⟩, ⟨hc_ak, hc_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendState.attackerKnowledge _ tr ⟨st, coins, rfl, hst_ak, hc_ak⟩, ctClosed_spqrSend_state hst_s hc_s⟩
      · rintro x ⟨st, coins, rfl, ⟨hst_ak, _⟩, ⟨hc_ak, _⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendKey.attackerKnowledge _ tr ⟨st, coins, rfl, hst_ak, hc_ak⟩, ctClosed_spqrSend_key T st coins⟩
      · rintro x ⟨st, coins, rfl, ⟨hst_ak, _⟩, ⟨hc_ak, _⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendMsg.attackerKnowledge _ tr ⟨st, coins, rfl, hst_ak, hc_ak⟩, ctClosed_spqrSend_msg T st coins⟩
      · rintro x ⟨st, msg, idx, r, hrecv, rfl, ⟨hst_ak, hst_s⟩, ⟨hm_ak, hm_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrRecvState.attackerKnowledge _ tr ⟨st, msg, idx, r, hrecv, rfl, hst_ak, hm_ak⟩, ctClosed_spqrRecv_state hrecv hst_s hm_s⟩
      · rintro x ⟨st, msg, idx, r, hrecv, rfl, ⟨hst_ak, _⟩, ⟨hm_ak, _⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrRecvKey.attackerKnowledge _ tr ⟨st, msg, idx, r, hrecv, rfl, hst_ak, hm_ak⟩, ctClosed_spqrRecv_key hrecv⟩
      · rintro x (⟨s, ⟨hs_ak, hs_s⟩, harg⟩ | ⟨s, ⟨hs_ak, hs_s⟩, harg⟩ | ⟨s, ⟨hs_ak, hs_s⟩, harg⟩)
        · have hargs := (ctClosed_spqrInit_iff s).mp hs_s
          refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge x tr (.inl ⟨s, hs_ak, harg⟩), ?_⟩
          rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
        · have hargs := (ctClosed_spqrSendState_iff s).mp hs_s
          refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge x tr (.inr (.inl ⟨s, hs_ak, harg⟩)), ?_⟩
          rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
        · have hargs := (ctClosed_spqrRecvState_iff s).mp hs_s
          refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge x tr (.inr (.inr ⟨s, hs_ak, harg⟩)), ?_⟩
          rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, TrWire.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | n, _⟩ <;> try omega
      · rintro x ⟨w, rfl, ⟨h1_ak, h1_s⟩, ⟨h2_ak, h2_s⟩, ⟨h3_ak, h3_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove TrWire.trWireMsg.attackerKnowledge _ tr ⟨w, rfl, h1_ak, h2_ak, h3_ak⟩, .trWireMsg w h1_s h2_s h3_s⟩
      · rintro x ⟨w, ⟨hw_ak, hw_s⟩, hmem⟩; have hargs_s := (ctClosed_trWireMsg_iff w).mp hw_s
        refine ⟨DY.Bytes.AttackerKnows.prove TrWire.trWireMsgArg.attackerKnowledge x tr ⟨w, hw_ak, hmem⟩, ?_⟩
        rcases hmem with rfl | rfl | rfl; exacts [hargs_s.1, hargs_s.2.1, hargs_s.2.2]
    · omega
  · intro x hx; simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, SubAttackerKnowledge.fromPred] at hx
    exact ⟨DY.Bytes.AttackerKnows.prove_from_base x tr hx, h_base x hx⟩

private theorem ctClosed_dhPk_rand (T : ExecTrace) (t : Nat) : CtClosed T (DiffieHellman.dhPk (randTerm t 32)) :=
  .dhPk (ctClosed_random T { timestamp := t, size := 32 })

private theorem ctClosed_chainKeyAt_succ {T : ExecTrace} {ck0 x : DY.Bytes} {n : Nat}
    (hx : x = chainKeyAt ck0 (n + 1)) : CtClosed T x := by
  subst hx; rw [CompTermAlgebra.chainKeyAt_succ_eq_kdfCk_fst]; exact ctClosed_kdfExtract T _ _

private theorem ctClosed_of_eq_chainKeyAt_createChain_snd {T : ExecTrace} {rk pk sk x : DY.Bytes} {n : Nat}
    (hx : x = chainKeyAt (createChain rk pk sk).2 n) : CtClosed T x := by
  cases n with
  | zero => subst hx; exact ctClosed_kdfExtract T _ _
  | succ n => exact ctClosed_chainKeyAt_succ hx

private theorem ctClosed_of_eq_chainKeyAt_pqxdhKdf_ck {T : ExecTrace} {ikm x : DY.Bytes} {n : Nat}
    (hx : x = chainKeyAt (pqxdhKdf ikm).ck n) : CtClosed T x := by
  cases n with
  | zero => subst hx; exact ctClosed_kdfExtract T _ _
  | succ n => exact ctClosed_chainKeyAt_succ hx

private theorem ctClosed_trHonestWireMsg {T : ExecTrace} {rk ct pqMsg : DY.Bytes} (ns pn : UInt32)
    (hrk : CtClosed T rk) (hct : CtClosed T ct) (hpq : CtClosed T pqMsg) :
    CtClosed T (trHonestWireMsg rk ns pn ct pqMsg) :=
  .trWireMsg
    { version := messageVersion, senderRatchetKey := rk, counter := ns, previousCounter := pn,
      ciphertext := ct, pqRatchet := pqMsg, encodingVariation := DY.TrWire.canonicalVariation } hrk hct hpq

private theorem parseTrSignalMsg_pqRatchet_ctClosed {T : ExecTrace} {t : DY.Bytes} {msg : TRSignalMsg}
    (ht : CtClosed T t) (hparse : parseTrSignalMsg t = some msg) : CtClosed T msg.pqRatchet := by
  unfold parseTrSignalMsg at hparse
  simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at hparse
  rcases hparse with ⟨⟨wire, mac⟩, hsplit, x, hx, rfl⟩; dsimp only at hx ⊢
  rw [← Concat.concat_split t (t.length - Trunc.trunc8Length) wire mac hsplit] at ht
  have hwire : CtClosed T wire := ((ctClosed_concat_iff wire mac).mp ht).1
  rw [TrWire.trWireMsg_of_fields? hx] at hwire; exact ((ctClosed_trWireMsg_iff x).mp hwire).2.2

structure CtClosedCoreInv (tr : ExecTrace) : Prop where
  baseClosed : ∀ b, tr.BaseAttackerKnows b → CtClosed tr b
  spqrClosed : ∀ me st idx, TRStoredAt tr me st idx → CtClosed tr st.spqr
  pqSkPkAk : ∀ b sk idx, CompTrace.PQXDHStoredAt tr b { kind := .pqPrekey, sk := sk } idx →
    (DY.PQKem.kemPk sk).AttackerKnows tr
  bobDoneAk : ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
      ct.AttackerKnows tr ∧ pqpk.AttackerKnows tr

private theorem ctClosedCoreInv_nil : CtClosedCoreInv Trace.nil :=
  { baseClosed := fun b h => False.elim (Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1 b ▸ h)
    spqrClosed := fun _ _ _ h => by
      unfold TRStoredAt at h; rw [Trace.at?_eq_some] at h
      exact False.elim (Symbolic.DYBridge.DY.Trace.nil_length_not_lt _ h.1)
    pqSkPkAk := fun _ _ _ h => by
      unfold CompTrace.PQXDHStoredAt at h; rw [Trace.at?_eq_some] at h
      exact False.elim (Symbolic.DYBridge.DY.Trace.nil_length_not_lt _ h.1)
    bobDoneAk := fun _ _ _ _ _ _ _ _ _ _ _ h => by
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?_eq_some] at h
      exact False.elim (Symbolic.DYBridge.DY.Trace.nil_length_not_lt _ h.1) }

private theorem CtClosedCoreInv.of_attackerKnows {tr : ExecTrace} (hc : CtClosedCoreInv tr)
    {b : DY.Bytes} (hk : b.AttackerKnows tr) : CtClosed tr b :=
  attackerKnows_imp_ctClosed (Trace.le_refl tr) hc.baseClosed hk

private theorem CtClosedCoreInv.bobDoneAk_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace}
    (hc : CtClosedCoreInv tr) {e : E}
    (hne : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none)
    {b a : Participant} {ikB ikA spk pqpk : DY.Bytes} {opk : Option DY.Bytes}
    {ek ct : DY.Bytes} {keys : HandshakeKeys} {i : Nat}
    (hev : (tr.append e).EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i) :
    ct.AttackerKnows (tr.append e) ∧ pqpk.AttackerKnows (tr.append e) := by
  obtain ⟨h1, h2⟩ := hc.bobDoneAk b a ikB ikA spk pqpk opk ek ct keys i (eventLoggedAt_append_other hev hne)
  exact ⟨DY.Bytes.AttackerKnows_le _ _ _ (Trace.append_le tr e) h1,
         DY.Bytes.AttackerKnows_le _ _ _ (Trace.append_le tr e) h2⟩

private theorem CtClosedCoreInv.append_inert {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace}
    (hc : CtClosedCoreInv tr) (e : E)
    (hbase : ∀ b, (tr.append e).BaseAttackerKnows b → tr.BaseAttackerKnows b)
    (htr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.TRStEntry) = none)
    (hpq : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.PQXDHStEntry) = none)
    (hev : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none) :
    CtClosedCoreInv (tr.append e) :=
  let hle := Trace.append_le tr e
  { baseClosed := fun b hb => (hc.baseClosed b (hbase b hb)).mono hle
    spqrClosed := fun me st idx hst => (hc.spqrClosed me st idx (CompInv.CompPresBob.trStoredAt_append_other htr hst)).mono hle
    pqSkPkAk := fun b sk idx hst => DY.Bytes.AttackerKnows_le _ _ _ hle (hc.pqSkPkAk b sk idx (CompTrace.pqxdhStoredAt_append_other hpq hst))
    bobDoneAk := fun _ _ _ _ _ _ _ _ _ _ _ h => hc.bobDoneAk_other hev h }

private theorem CtClosedCoreInv.append_rnd {tr : ExecTrace} (hc : CtClosedCoreInv tr) (n : Nat) :
    CtClosedCoreInv (tr.append (RndE n)) :=
  hc.append_inert _ (fun b => (CompTrace.baseAttackerKnows_append_rnd tr n b).mp) rfl rfl rfl
private theorem CtClosedCoreInv.append_trEv {tr : ExecTrace} (hc : CtClosedCoreInv tr) (ev : TREvent) :
    CtClosedCoreInv (tr.append (TREvE ev)) :=
  hc.append_inert _ (fun b => (CompTrace.baseAttackerKnows_append_trEv tr ev b).mp) rfl rfl rfl
private theorem CtClosedCoreInv.append_cEv {tr : ExecTrace} (hc : CtClosedCoreInv tr) (ev : ComposedEvent) :
    CtClosedCoreInv (tr.append (CEvE ev)) :=
  hc.append_inert _ (fun b => (CompTrace.baseAttackerKnows_append_cEv tr ev b).mp) rfl rfl rfl

private theorem CtClosedCoreInv.append_ev_nonBob {tr : ExecTrace} (hc : CtClosedCoreInv tr)
    (ev : PQXDHEvent) (hnb : ∀ b a ikB ikA spk pqpk opk ek ct keys, ev ≠ .BobDone b a ikB ikA spk pqpk opk ek ct keys) :
    CtClosedCoreInv (tr.append (EvE ev)) := by
  have hle : tr ≤ tr.append (EvE ev) := Trace.append_le tr _
  refine { baseClosed := fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_pqEv tr ev b).mp hb)).mono hle
           spqrClosed := fun me st idx hst => (hc.spqrClosed me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle
           pqSkPkAk := fun b sk idx hst => DY.Bytes.AttackerKnows_le _ _ _ hle (hc.pqSkPkAk b sk idx (CompTrace.pqxdhStoredAt_append_other rfl hst))
           bobDoneAk := fun b a ikB ikA spk pqpk opk ek ct keys i hev => ?_ }
  rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev'⟩ | ⟨_, hEq⟩
  · obtain ⟨h1, h2⟩ := hc.bobDoneAk b a ikB ikA spk pqpk opk ek ct keys i hev'
    exact ⟨DY.Bytes.AttackerKnows_le _ _ _ hle h1, DY.Bytes.AttackerKnows_le _ _ _ hle h2⟩
  · exact absurd hEq (hnb b a ikB ikA spk pqpk opk ek ct keys)

private theorem CtClosedCoreInv.append_ev_bobDone {tr : ExecTrace} (hc : CtClosedCoreInv tr)
    (b a : Participant) (ikB ikA spk pqpk : DY.Bytes) (opk : Option DY.Bytes)
    (ek ct : DY.Bytes) (keys : HandshakeKeys) (hct : ct.AttackerKnows tr) (hpq : pqpk.AttackerKnows tr) :
    CtClosedCoreInv (tr.append (EvE (.BobDone b a ikB ikA spk pqpk opk ek ct keys))) := by
  let ev := PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys
  have hle : tr ≤ tr.append (EvE ev) := Trace.append_le tr _
  refine { baseClosed := fun x hx => (hc.baseClosed x ((CompTrace.baseAttackerKnows_append_pqEv tr ev x).mp hx)).mono hle
           spqrClosed := fun me st idx hst => (hc.spqrClosed me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle
           pqSkPkAk := fun p sk idx hst => DY.Bytes.AttackerKnows_le _ _ _ hle (hc.pqSkPkAk p sk idx (CompTrace.pqxdhStoredAt_append_other rfl hst))
           bobDoneAk := fun b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i hev => ?_ }
  rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev'⟩ | ⟨_, hEq⟩
  · obtain ⟨h1, h2⟩ := hc.bobDoneAk b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i hev'
    exact ⟨DY.Bytes.AttackerKnows_le _ _ _ hle h1, DY.Bytes.AttackerKnows_le _ _ _ hle h2⟩
  · injection hEq with _ _ _ _ _ hpqEq _ _ hctEq _; subst hpqEq hctEq
    exact ⟨DY.Bytes.AttackerKnows_le _ _ _ hle hct, DY.Bytes.AttackerKnows_le _ _ _ hle hpq⟩

private theorem CtClosedCoreInv.append_st_nonPq {tr : ExecTrace} (hc : CtClosedCoreInv tr)
    (me : Participant) (st : PQXDHState) (hnp : st.kind ≠ .pqPrekey) :
    CtClosedCoreInv (tr.append (StE me st)) := by
  have hle : tr ≤ tr.append (StE me st) := Trace.append_le tr _
  refine { baseClosed := fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_pqSt tr me st b).mp hb)).mono hle
           spqrClosed := fun me' st' idx hst => (hc.spqrClosed me' st' idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle
           pqSkPkAk := fun b sk idx hst => ?_, bobDoneAk := fun _ _ _ _ _ _ _ _ _ _ _ h => hc.bobDoneAk_other rfl h }
  rcases CompTrace.pqxdhStoredAt_append_same hst with ⟨_, hst'⟩ | ⟨_, _, hEq⟩
  · exact DY.Bytes.AttackerKnows_le _ _ _ hle (hc.pqSkPkAk b sk idx hst')
  · subst hEq; exact absurd rfl hnp

private theorem CtClosedCoreInv.append_net {tr : ExecTrace} (hc : CtClosedCoreInv tr) {msg : DY.Bytes}
    (hmsg : CtClosed (tr.append (NetE msg)) msg) : CtClosedCoreInv (tr.append (NetE msg)) := by
  have hle : tr ≤ tr.append (NetE msg) := Trace.append_le tr (NetE msg)
  refine { baseClosed := fun b hb => ?_
           spqrClosed := fun me st idx hst => (hc.spqrClosed me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl hst)).mono hle
           pqSkPkAk := fun b sk idx hst => DY.Bytes.AttackerKnows_le _ _ _ hle (hc.pqSkPkAk b sk idx (CompTrace.pqxdhStoredAt_append_other rfl hst))
           bobDoneAk := fun _ _ _ _ _ _ _ _ _ _ _ h => hc.bobDoneAk_other rfl h }
  rcases (CompTrace.baseAttackerKnows_append_net tr msg b).mp hb with rfl | hb' <;> [exact hmsg; exact (hc.baseClosed b hb').mono hle]

private theorem CtClosedCoreInv.append_net_of_closed {tr : ExecTrace} (hc : CtClosedCoreInv tr)
    {msg : DY.Bytes} (hmsg : CtClosed tr msg) : CtClosedCoreInv (tr.append (NetE msg)) :=
  hc.append_net (hmsg.mono (Trace.append_le tr (NetE msg)))
private theorem CtClosedCoreInv.append_net_rnd {tr : ExecTrace} (hc : CtClosedCoreInv tr) (t n : Nat) :
    CtClosedCoreInv (tr.append (NetE (CompTrace.mkRand t n))) :=
  hc.append_net (ctClosed_random _ { timestamp := t, size := n })

private theorem CtClosedCoreInv.append_trSt {tr : ExecTrace} (hc : CtClosedCoreInv tr)
    {me : Participant} {st : TRState} (hspqr : CtClosed tr st.spqr) :
    CtClosedCoreInv (tr.append (TRStE me st)) := by
  have hle : tr ≤ tr.append (TRStE me st) := Trace.append_le tr (TRStE me st)
  refine { baseClosed := fun b hb => (hc.baseClosed b ((CompTrace.baseAttackerKnows_append_trSt tr me st b).mp hb)).mono hle
           spqrClosed := fun me' st' idx hst => ?_, bobDoneAk := fun _ _ _ _ _ _ _ _ _ _ _ h => hc.bobDoneAk_other rfl h
           pqSkPkAk := fun b sk idx hst => DY.Bytes.AttackerKnows_le _ _ _ hle (hc.pqSkPkAk b sk idx (CompTrace.pqxdhStoredAt_append_other rfl hst)) }
  rcases CompInv.CompPresBob.trStoredAt_append_same hst with ⟨_, hst'⟩ | ⟨_, _, rfl⟩
  · exact (hc.spqrClosed me' st' idx hst').mono hle
  · exact hspqr.mono hle

private theorem CtClosedCoreInv.logSkippedKeys_preserves (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32) (tr : ExecTrace),
      CtClosedCoreInv tr → CtClosedCoreInv ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k).run tr).2.val
  | 0, _, _, _, hc => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [Traceful.run_pure]; exact hc
  | k + 1, ck, n, tr, hc => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    exact CtClosedCoreInv.logSkippedKeys_preserves s pk rIdx src k (kdfCk ck).1 (n + 1) _ (hc.append_trEv _)

private theorem CtClosedCoreInv.append_logMessageKeyAndStore {tr : ExecTrace} (hc : CtClosedCoreInv tr)
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (seed pqSalt : DY.Bytes)
    (n : UInt32) (rIdx prev : Nat) (st : TRState) (hspqr : CtClosed tr st.spqr) :
    CtClosedCoreInv ((DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx prev st).run tr).2.val := by
  rw [CompPresTRExp.run_logMessageKeyAndStore_snd]
  exact (hc.append_trEv _).append_trSt (hspqr.mono (Trace.append_le tr _))

private theorem ctClosed_receiveSignalMsg_at {tr : ExecTrace} (hc : CtClosedCoreInv tr) {α : Type}
    (msgIdx : Nat) {f : TRSignalMsg → Traceful α}
    (hf : ∀ msg, CtClosed tr msg.pqRatchet → CtClosedCoreInv ((f msg).run tr).2.val) :
    CtClosedCoreInv (((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at msgIdx tr hc fun raw _ hraw => ?_
  rcases hparse : parseTrSignalMsg raw with _ | msg; · dsimp only; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hc
  dsimp only; rw [CompTrace.run_bind_assoc_snd]
  exact CompTrace.bind_guardP_at _ tr hc fun _ =>
    hf msg (parseTrSignalMsg_pqRatchet_ctClosed (hc.of_attackerKnows hraw) hparse)

private theorem ctClosed_preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) (tr : ExecTrace) (hc : CtClosedCoreInv tr) :
    CtClosedCoreInv ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hc (hc.append_rnd 32)
    fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ => ?_
  have htl : ∀ {α : Type} (g : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= g).run t).2.val = ((g t.length).run t).2.val := fun g t => by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let hs := aliceOut tr ikA ikBPk spkPk pqPk opk
  let tr1 := tr.append (RndE 32); let tr2 := tr1.append (RndE 32)
  let dhsA := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr2.length 32
  let stA : TRState :=
    { peer := b, myIk := DY.Libsignal.PQXDH.serializedIk hs.ikA, peerIk := DY.Libsignal.PQXDH.serializedIk hs.ikB,
      rk := (createChain hs.keys.rk hs.spk dhsA).1, dhs := dhsA, cks := (createChain hs.keys.rk hs.spk dhsA).2,
      ns := 0, pn := 0, sid := Concat.concat (DiffieHellman.dhPk dhsA) hs.keys.rk, initiator := true, rIdx := 1,
      recv := [{ ratchetKey := hs.spk, chainKey := hs.keys.ck, index := 0, rIdx := 1 }],
      spqr := Spqr.spqrInit hs.keys.pqr spqrA2B }
  let tr3 := tr2.append (RndE 32); let tr4 := tr3.append (NetE hs.ek); let tr5 := tr4.append (NetE hs.ct)
  let evA := PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys
  let tr6 := tr5.append (EvE evA); let tr7 := tr6.append (TREvE (TREvent.InitSession a b (DiffieHellman.dhPk dhsA) hs.spk))
  rw [CompTrace.run_genRand_bind_snd]; dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, htl,
    CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  change CtClosedCoreInv ((tr7.append (CEvE (ComposedEvent.HandshakeSession (stA.sessionInfo a) tr5.length))).append (TRStE a stA))
  have hc4 : CtClosedCoreInv tr4 := (((hc.append_rnd 32).append_rnd 32).append_rnd 32).append_net_of_closed (ctClosed_dhPk_rand _ _)
  have hle46 : tr4 ≤ tr6 := Trace.le_trans tr4 tr5 tr6 (Trace.append_le tr4 _) (Trace.append_le tr5 _)
  have hlen5 : tr5.length = tr.length + 5 := by
    simp only [tr5, tr4, tr3, tr2, tr1, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have had6 : tr6.EventLoggedAt evA (tr.length + 5) := by
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, ← hlen5]; exact CompPresPQXDH.at?_append_eq tr5 (EvE evA)
  have hct6 : CtClosed tr6 hs.ct :=
    .encap { pk := pqPk, entropy := randTerm (tr.length + 1) 32 }
      (.inr ⟨tr.length, a, b, hs.ikA, hs.ikB, hs.spk, pqPk, hs.opk, hs.ek, hs.ct, hs.keys, had6, rfl, rfl⟩)
  have hc6 : CtClosedCoreInv tr6 :=
    { baseClosed := fun x hx =>
        ((CompTrace.baseAttackerKnows_append_net tr4 hs.ct x).mp ((CompTrace.baseAttackerKnows_append_pqEv tr5 evA x).mp hx)).elim
          (· ▸ hct6) (fun hx4 => (hc4.baseClosed x hx4).mono hle46)
      spqrClosed := fun me st idx hst => (hc4.spqrClosed me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl (CompInv.CompPresBob.trStoredAt_append_other rfl hst))).mono hle46
      pqSkPkAk := fun p sk idx hst => DY.Bytes.AttackerKnows_le _ _ _ hle46 (hc4.pqSkPkAk p sk idx (CompTrace.pqxdhStoredAt_append_other rfl (CompTrace.pqxdhStoredAt_append_other rfl hst)))
      bobDoneAk := fun b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i hev => by
        rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev5⟩ | ⟨_, hEq⟩
        · obtain ⟨h1, h2⟩ := hc4.bobDoneAk b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i (eventLoggedAt_append_other hev5 rfl)
          exact ⟨DY.Bytes.AttackerKnows_le _ _ _ hle46 h1, DY.Bytes.AttackerKnows_le _ _ _ hle46 h2⟩
        · dsimp only [evA] at hEq; cases hEq }
  exact ((hc6.append_trEv _).append_cEv _).append_trSt
    (.spqrInit { authKey := hs.keys.pqr, params := spqrA2B } (ctClosed_kdfExtract _ _ _) (ctClosed_literal _ _))

private theorem ctClosed_bobStart_commit {tr : ExecTrace} (hc : CtClosedCoreInv tr)
    (b a : Participant) (sB sS sQ : DY.Bytes) (o : Option DY.Bytes) (ikA ek ct : DY.Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (dhs spqr' seed pqSalt m : DY.Bytes) (c' : RecvChain)
    (hctAk : ct.AttackerKnows tr) (hpqAk : (DY.PQKem.kemPk sQ).AttackerKnows tr) (hspqr : CtClosed tr spqr') :
    let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    CtClosedCoreInv (((do
      let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
      ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (DiffieHellman.dhPk sB) ikA
        (DiffieHellman.dhPk sS) (DY.PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys)
      if true then
        ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
        ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
      ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
      let skipped := msg.counter.toNat - c.index.toNat
      let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
      DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
        msg.counter c.rIdx childIdx
        { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr).2.val) := by
  intro st c; let doneIdx := tr.length
  have htl : ∀ {α : Type} (g : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= g).run t).2.val = ((g t.length).run t).2.val := fun g t => by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let tr₁ := tr.append (EvE (.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS) (DY.PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys))
  let tr₂ := tr₁.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
  let tr₃ := tr₂.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))); let tr₄ := tr₃.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
  have hc₄ : CtClosedCoreInv tr₄ := (((hc.append_ev_bobDone b a _ ikA _ _ _ ek ct keys hctAk hpqAk).append_trEv _).append_trEv _).append_cEv _
  have hle₀₄ : tr ≤ tr₄ := Trace.le_trans _ _ _ (Trace.append_le tr _) (Trace.le_trans _ _ _ (Trace.append_le tr₁ _) (Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le tr₃ _)))
  let skipped := msg.counter.toNat - c.index.toNat; let childIdx := tr₄.length + skipped + 2
  let skipAct := DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
  let restAct : Unit → Traceful Nat := fun _ => do
    ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
    DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
      msg.counter c.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }
  rw [htl, CompPresTRExp.run_logEvent_bind_snd]; simp only [↓reduceIte]
  rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, htl]
  change CtClosedCoreInv (((skipAct >>= restAct).run tr₄).2.val)
  rw [CompInv.CompPresBob.run_logSkippedKeys_bind_snd]
  let tr₅ := (skipAct.run tr₄).2.val; have hle₄₅ : tr₄ ≤ tr₅ := (skipAct.run tr₄).2.property
  have hc₅ : CtClosedCoreInv tr₅ := CtClosedCoreInv.logSkippedKeys_preserves (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx skipped c.chainKey c.index tr₄ hc₄
  let tr₆ := tr₅.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
  have hc₆ : CtClosedCoreInv tr₆ := hc₅.append_trEv _
  have hle₀₆ : tr ≤ tr₆ := Trace.le_trans _ _ _ hle₀₄ (Trace.le_trans _ _ _ hle₄₅ (Trace.append_le tr₅ _))
  dsimp only [restAct]; rw [CompPresTRExp.run_logEvent_bind_snd]
  exact hc₆.append_logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
    msg.counter c.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' } (hspqr.mono hle₀₆)

private theorem ctClosed_preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : CtClosedCoreInv tr) :
    CtClosedCoreInv ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hc
    fun sB sS sQ o ikA _ ek ct _ keys _ _ hstQ _ _ _ hctNet _ hbob => ?_
  have hctAk0 : ct.AttackerKnows tr := DY.Bytes.AttackerKnows.prove_from_base ct tr hctNet.baseAttackerKnows
  have hpqAk0 : (DY.PQKem.kemPk sQ).AttackerKnows tr := hc.pqSkPkAk b sQ kh.pqspk hstQ
  refine ctClosed_receiveSignalMsg_at hc mh.msg fun msg hpq => ?_; dsimp only
  refine CompInv.CompPresBob.bind_ensureReceiverChain_bobInitSt
    a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey tr hc fun _ => ?_
  let dhs := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32
  let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
  let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
  let tr₁ := tr.append (RndE 32); have hc₁ : CtClosedCoreInv tr₁ := hc.append_rnd 32
  rcases hConsume : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hc₁
  dsimp only; rcases hSpqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hc₁
  dsimp only; have hle₀₁ : tr ≤ tr₁ := Trace.append_le tr _
  have hpqr₁ : CtClosed tr₁ keys.pqr := by
    dsimp only [DY.Libsignal.PQXDH.bobAgreement] at hbob; injection hbob with hkeys_eq
    rw [← hkeys_eq]; exact ctClosed_kdfExtract tr₁ _ _
  have hspqr₁ : CtClosed tr₁ spqr' :=
    ctClosed_spqrRecv_state hSpqr (.spqrInit { authKey := keys.pqr, params := spqrB2A } hpqr₁ (ctClosed_literal _ _)) (hpq.mono hle₀₁)
  let tr₂ := tr₁.append (NetE key); have hle₁₂ : tr₁ ≤ tr₂ := Trace.append_le tr₁ _
  have hc₂ : CtClosedCoreInv tr₂ := hc₁.append_net_of_closed (ctClosed_spqrRecv_key hSpqr)
  have hle₀₂ : tr ≤ tr₂ := Trace.le_trans tr tr₁ tr₂ hle₀₁ hle₁₂
  have hspqr₂ : CtClosed tr₂ spqr' := hspqr₁.mono hle₁₂
  have hctAk₂ : ct.AttackerKnows tr₂ := DY.Bytes.AttackerKnows_le _ _ _ hle₀₂ hctAk0
  have hpqAk₂ : (DY.PQKem.kemPk sQ).AttackerKnows tr₂ := DY.Bytes.AttackerKnows_le _ _ _ hle₀₂ hpqAk0
  rw [CompPresTRExp.run_sendMessage_bind_snd]
  change CtClosedCoreInv (((Network.receiveMessage pqIdx >>= fun pqSalt =>
    DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed >>= fun m => _).run tr₂).2.val)
  refine CompTrace.bind_receiveMessage_at pqIdx tr₂ hc₂ fun pqSalt _ _ => ?_
  refine CompInv.CompPresBob.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr₂ hc₂ fun m _ => ?_
  cases o with
  | none =>
    dsimp only [Option.map]
    exact ctClosed_bobStart_commit hc₂ b a sB sS sQ none ikA ek ct keys msg dhs spqr' seed pqSalt m c' hctAk₂ hpqAk₂ hspqr₂
  | some oSk =>
    dsimp only [Option.map]; rw [CompTrace.run_bind_snd]
    unfold DY.Libsignal.PQXDH.guardTrace; rw [Traceful.run_mk]; dsimp only
    by_cases hused : (!opkUsedB tr₂ b (DiffieHellman.dhPk oSk)) = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hused h]; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd]
      let tr₃ := tr₂.append (EvE (.OPKUsed b (DiffieHellman.dhPk oSk)))
      have hle₂₃ : tr₂ ≤ tr₃ := Trace.append_le tr₂ _
      exact ctClosed_bobStart_commit (hc₂.append_ev_nonBob _ (by intros; rintro ⟨⟩)) b a sB sS sQ (some oSk)
        ikA ek ct keys msg dhs spqr' seed pqSalt m c'
        (DY.Bytes.AttackerKnows_le _ _ _ hle₂₃ hctAk₂) (DY.Bytes.AttackerKnows_le _ _ _ hle₂₃ hpqAk₂) (hspqr₂.mono hle₂₃)
    · rw [ite_eq_right_iff.mpr fun h => absurd h hused]; dsimp only; exact hc₂

private theorem ctClosed_preserves_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CtClosedCoreInv tr) :
    CtClosedCoreInv ((DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  obtain ⟨_, _, _, _, _, hdhs, _, _, _, _⟩ := hinv.trStOK me st stateIdx hst
  have hspqr0 : CtClosed tr st.spqr := hc.spqrClosed me st stateIdx hst
  apply CompTrace.bind_guardP_at _ tr hc; intro _
  rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_sendMessage_bind_snd]
  let m := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32; let tr1 := tr.append (RndE 32)
  let coins := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr1.length coinsLen; let tr2 := tr1.append (RndE coinsLen)
  let key := (Spqr.spqrSend st.spqr coins).2.1; let tr3 := tr2.append (NetE key)
  have hc3 : CtClosedCoreInv tr3 := ((hc.append_rnd 32).append_rnd coinsLen).append_net_of_closed (ctClosed_spqrSend_key tr2 st.spqr coins)
  have hle03 : tr ≤ tr3 := Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 (Trace.append_le tr _) (Trace.append_le tr1 _)) (Trace.append_le tr2 _)
  apply CompTrace.bind_receiveMessage_at pqIdx tr3 hc3; intro pqSalt _ _
  rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
    CompPresTRExp.run_logMessageKeyAndStore_bind_snd, CompPresTRExp.run_sendMessage_snd]
  let tr4 := tr3.append (TREvE (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m))
  have hc4 : CtClosedCoreInv tr4 := hc3.append_trEv _
  have hle04 : tr ≤ tr4 := Trace.le_trans tr tr3 tr4 hle03 (Trace.append_le tr3 _)
  let st' : TRState := { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := (Spqr.spqrSend st.spqr coins).1 }
  have hspqr'_safe4 : CtClosed tr4 st'.spqr := ctClosed_spqrSend_state (hspqr0.mono hle04) (ctClosed_random tr4 _)
  have hc6 : CtClosedCoreInv ((DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) .sender (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st').run tr4).2.val :=
    hc4.append_logMessageKeyAndStore me (st.sessionInfo me) .sender
      (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx st' hspqr'_safe4
  rw [CompPresTRExp.run_logMessageKeyAndStore_snd] at hc6
  let tr5 := tr4.append (TREvE (TREvent.MessageKey (st.sessionInfo me) .sender
    (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx))
  let tr6 := tr5.append (TRStE me st')
  have hdhs_safe : CtClosed tr6 (DiffieHellman.dhPk st.dhs) := by
    rcases hdhs with ⟨t, hdhs_eq, _⟩ | ⟨t, _, hdhs_eq, _, _⟩ <;> [rw [hdhs_eq]; rw [hdhs_eq]] <;> exact ctClosed_dhPk_rand tr6 _
  let mk := trMsgKeys pqSalt (kdfCk st.cks).2
  let wire := trHonestWireMsg (DiffieHellman.dhPk st.dhs) st.ns st.pn
    (SymEnc.symEnc mk.cipherKey mk.iv m) (Spqr.spqrSend st.spqr coins).2.2
  have hwire_safe6 : CtClosed tr6 wire :=
    ctClosed_trHonestWireMsg st.ns st.pn hdhs_safe (.symEnc (ctClosed_random tr6 _)) (ctClosed_spqrSend_msg tr6 st.spqr coins)
  exact hc6.append_net_of_closed (.concat hwire_safe6 (ctClosed_trunc8 tr6 _))

private theorem ctClosed_preserves_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : CtClosedCoreInv tr) :
    CtClosedCoreInv ((DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  have hspqr0 : CtClosed tr st.spqr := hc.spqrClosed me st stateIdx hst
  apply ctClosed_receiveSignalMsg_at hc msgIdx; intro msg hpq_safe
  apply CompPresTRExp.bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hc; intro ⟨ev⟩ _
  cases ev with
  | SkippedKeyStored s pk n seed rIdx _sourceStateIdx =>
    dsimp only; apply CompTrace.bind_guardP_at _ tr hc; intro _
    apply CompPresTRExp.bind_guardTrace_at _ tr hc; intro _
    rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; rw [CompPresTRExp.run_sendMessage_bind_snd]
    let tr1 := tr.append (NetE key); have hc1 : CtClosedCoreInv tr1 := hc.append_net_of_closed (ctClosed_spqrRecv_key hspqr_recv)
    have hle01 : tr ≤ tr1 := Trace.append_le tr _
    apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1; intro pqSalt _ _
    apply CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1; intro m
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    let tr2 := tr1.append (TREvE (TREvent.SkippedKeyUsed s skippedKeyEventIdx))
    let tr3 := tr2.append (TREvE (TREvent.Received me st.peer pk n m))
    have hc3 : CtClosedCoreInv tr3 := (hc1.append_trEv _).append_trEv _
    have hle03 : tr ≤ tr3 := Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 hle01 (Trace.append_le tr1 _)) (Trace.append_le tr2 _)
    exact hc3.append_logMessageKeyAndStore me s .receiver seed pqSalt n rIdx stateIdx { st with spqr := spqr' } ((ctClosed_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle03)
  | _ => dsimp only; rw [Traceful.run_failure]; exact hc

private theorem ctClosed_preserves_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr : ExecTrace) (hc : CtClosedCoreInv tr) :
    CtClosedCoreInv ((DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  have hspqr0 : CtClosed tr st.spqr := hc.spqrClosed me st stateIdx hst
  apply ctClosed_receiveSignalMsg_at hc msgIdx; intro msg hpq_safe
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor
  rcases hfind : findRecvChain st.recv msg.ratchetKey with _ | c
  · dsimp only; rcases hlow : x25519LowOrder msg.ratchetKey with _ | _
    · simp only [Bool.false_eq_true, ↓reduceIte, DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_bind_assoc_snd]
      apply CompTrace.bind_guardP_at _ tr hc; intro _
      rw [CompTrace.run_bind_assoc_snd, CompTrace.run_genRand_bind_snd, CompTrace.run_pure_bind_snd, CompTrace.run_pure_bind_snd]
      let tr1 := tr.append (RndE 32); have hc1 : CtClosedCoreInv tr1 := hc.append_rnd 32
      have hle01 : tr ≤ tr1 := Trace.append_le tr _
      let dhs' := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 32
      let rk1 := (createChain st.rk msg.ratchetKey st.dhs).1; let ckr := (createChain st.rk msg.ratchetKey st.dhs).2
      let rk2 := (createChain rk1 msg.ratchetKey dhs').1; let cks2 := (createChain rk1 msg.ratchetKey dhs').2
      let c_new : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := ckr, index := 0, rIdx := st.rIdx + 2 }
      let recv1 := (st.recv ++ [c_new]).drop ((st.recv.length + 1) - maxReceiverChains)
      let pn1 := if st.ns = 0 then 0 else st.ns - 1
      let st1 : TRState := { st with rk := rk2, dhs := dhs', cks := cks2, ns := 0, pn := pn1, rIdx := st.rIdx + 2, recv := recv1 }
      rcases hcons : consumeMessageKey c_new msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hc1
      dsimp only; rcases hspqr_recv : Spqr.spqrRecv st1.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hc1
      dsimp only; rw [CompPresTRExp.run_sendMessage_bind_snd]
      let tr2 := tr1.append (NetE key); have hc2 : CtClosedCoreInv tr2 := hc1.append_net_of_closed (ctClosed_spqrRecv_key hspqr_recv)
      have hle02 : tr ≤ tr2 := Trace.le_trans tr tr1 tr2 hle01 (Trace.append_le tr1 _)
      apply CompTrace.bind_receiveMessage_at pqIdx tr2 hc2; intro pqSalt _ _
      apply CompPresTRExp.bind_verifyMacAndDecrypt_at st1 msg pqSalt seed tr2 hc2; intro m
      simp only [↓reduceIte]; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent),
        CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompTrace.run_bind_snd]
      let tr3 := tr2.append (TREvE (TREvent.DHRatchet me st1.peer msg.ratchetKey (DiffieHellman.dhPk st1.dhs)))
      let tr4 := tr3.append (TREvE (TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2)))
      have hc4 : CtClosedCoreInv tr4 := (hc2.append_trEv _).append_trEv _
      have hle04 : tr ≤ tr4 := Trace.le_trans tr tr2 tr4 hle02 (Trace.le_trans tr2 tr3 tr4 (Trace.append_le tr2 _) (Trace.append_le tr3 _))
      have hc5 := CtClosedCoreInv.logSkippedKeys_preserves (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
        (msg.counter.toNat - c_new.index.toNat) c_new.chainKey c_new.index tr4 hc4
      have hle45 := ((DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
        c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4).2.property
      rcases hsk_res : (DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c_new.rIdx stateIdx
          c_new.chainKey c_new.index (msg.counter.toNat - c_new.index.toNat)).run tr4 with ⟨_ | u, tr5_sub⟩
      · rw [hsk_res] at hc5; exact hc5
      · rw [hsk_res] at hc5 hle45; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
        let tr6 := tr5_sub.val.append (TREvE (TREvent.Received me st1.peer msg.ratchetKey msg.counter m))
        have hc6 : CtClosedCoreInv tr6 := hc5.append_trEv _
        have hle06 : tr ≤ tr6 := Trace.le_trans tr tr4 tr6 hle04 (Trace.le_trans tr4 tr5_sub.val tr6 hle45 (Trace.append_le tr5_sub.val _))
        exact hc6.append_logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed pqSalt msg.counter
          c_new.rIdx stateIdx { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
          ((ctClosed_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle06)
    · simp only [↓reduceIte]; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hc
  · dsimp only; rw [CompTrace.run_pure_bind_snd]
    rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; rw [CompPresTRExp.run_sendMessage_bind_snd]
    let tr1 := tr.append (NetE key); have hc1 : CtClosedCoreInv tr1 := hc.append_net_of_closed (ctClosed_spqrRecv_key hspqr_recv)
    have hle01 : tr ≤ tr1 := Trace.append_le tr _
    apply CompTrace.bind_receiveMessage_at pqIdx tr1 hc1; intro pqSalt _ _
    apply CompPresTRExp.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr1 hc1; intro m
    simp only [Bool.false_eq_true, ↓reduceIte]; rw [CompTrace.run_bind_snd]
    have hc2 := CtClosedCoreInv.logSkippedKeys_preserves (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
      (msg.counter.toNat - c.index.toNat) c.chainKey c.index tr1 hc1
    have hle12 := ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
      c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1).2.property
    rcases hsk_res : (DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
        c.chainKey c.index (msg.counter.toNat - c.index.toNat)).run tr1 with ⟨_ | u, tr2_sub⟩
    · rw [hsk_res] at hc2; exact hc2
    · rw [hsk_res] at hc2 hle12; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
      let tr3 := tr2_sub.val.append (TREvE (TREvent.Received me st.peer msg.ratchetKey msg.counter m))
      have hc3 : CtClosedCoreInv tr3 := hc2.append_trEv _
      have hle03 : tr ≤ tr3 := Trace.le_trans tr tr1 tr3 hle01 (Trace.le_trans tr1 tr2_sub.val tr3 hle12 (Trace.append_le tr2_sub.val _))
      exact hc3.append_logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter
        c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }
        ((ctClosed_spqrRecv_state hspqr_recv hspqr0 hpq_safe).mono hle03)

private theorem ctClosed_preserves_genPQPrekey (b : Participant) (idStateIdx : Nat)
    (tr : ExecTrace) (hc : CtClosedCoreInv tr) :
    CtClosedCoreInv ((genPQPrekey b idStateIdx).run tr).2.val := by
  have hst_bind : ∀ {S α : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
      (p : Participant) (s : S) (k : Nat → Traceful α) (t : ExecTrace),
      ((PersistentLocalState.storeLocalState p s >>= k).run t).2.val =
        ((k t.length).run (t.append (⟨⟨p, s⟩⟩ : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState S)))).2.val :=
    fun p s k t => by
      simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
        Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
      rw [CompTrace.run_bind_snd, Traceful.run_mk]
  unfold genPQPrekey; refine bind_getKey_at b idStateIdx .identity tr hc fun ikSk _ => ?_
  rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
    hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
  let sk := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr.length 64
  let tr1 := tr.append (RndE 64); let tr2 := tr1.append (RndE 64)
  let nonce := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr1.length 64
  let pk := DY.PQKem.kemPk sk
  let tr3 := tr2.append (EvE (.PQPrekeyPublished b pk))
  let tr4 := tr3.append (StE b { kind := .pqPrekey, sk := sk }); let tr5 := tr4.append (NetE pk)
  change CtClosedCoreInv (tr5.append (NetE (Signature.sign ikSk nonce (DY.Libsignal.PQXDH.encodeKEM pk))))
  have hc3 : CtClosedCoreInv tr3 := ((hc.append_rnd 64).append_rnd 64).append_ev_nonBob _ (by intros; rintro ⟨⟩)
  have hle35 : tr3 ≤ tr5 := Trace.le_trans tr3 tr4 tr5 (Trace.append_le tr3 _) (Trace.append_le tr4 _)
  have hpkAk5 : pk.AttackerKnows tr5 :=
    DY.Bytes.AttackerKnows.prove_from_base pk tr5 ((CompTrace.baseAttackerKnows_append_net tr4 pk pk).mpr (.inl rfl))
  have hc5 : CtClosedCoreInv tr5 :=
    { baseClosed := fun x hx => by
        rcases (CompTrace.baseAttackerKnows_append_net tr4 pk x).mp hx with rfl | hx4
        · exact .kemPk (ctClosed_random _ _)
        · exact (hc3.baseClosed x ((CompTrace.baseAttackerKnows_append_pqSt tr3 b _ x).mp hx4)).mono hle35
      spqrClosed := fun me st idx hst =>
        (hc3.spqrClosed me st idx (CompInv.CompPresBob.trStoredAt_append_other rfl
          (CompInv.CompPresBob.trStoredAt_append_other rfl hst))).mono hle35
      pqSkPkAk := fun p sk' idx hst => by
        rcases CompTrace.pqxdhStoredAt_append_same (CompTrace.pqxdhStoredAt_append_other rfl hst) with ⟨_, hst3⟩ | ⟨_, _, hEq⟩
        · exact DY.Bytes.AttackerKnows_le _ _ _ hle35 (hc3.pqSkPkAk p sk' idx hst3)
        · injection hEq with _ hsk; subst hsk; exact hpkAk5
      bobDoneAk := fun b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i hev => by
        obtain ⟨h1, h2⟩ := hc3.bobDoneAk b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i
          (eventLoggedAt_append_other (eventLoggedAt_append_other hev rfl) rfl)
        exact ⟨DY.Bytes.AttackerKnows_le _ _ _ hle35 h1, DY.Bytes.AttackerKnows_le _ _ _ hle35 h2⟩ }
  exact hc5.append_net_of_closed (ctClosed_sign _ _ _ _)

private theorem ctClosed_preserves_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CtClosedCoreInv tr) :
    CtClosedCoreInv ((DY.Libsignal.TripleRatchet.exposeKey me stateIdx k).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hc; intro st hst
  obtain ⟨_, keys, _, hkeys, _, hdhs, _, hrk, hcks, hrecv⟩ := hinv.trStOK me st stateIdx hst
  cases k with
  | rk =>
    dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    obtain ⟨r, p, s, hrk_eq⟩ := hrk
    exact (hc.append_trEv _).append_net_of_closed (by rw [hrk_eq]; exact ctClosed_kdfExtract _ _ _)
  | dhs =>
    dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    have hc1 := hc.append_trEv (TREvent.ExposedDHs (st.sessionInfo me) st.dhs st.rIdx)
    rcases hdhs with ⟨t, hdhs_eq, _⟩ | ⟨t, _, hdhs_eq, _, _⟩
    · rw [hdhs_eq] at hc1 ⊢; exact hc1.append_net_rnd (t + 2) 32
    · rw [hdhs_eq] at hc1 ⊢; exact hc1.append_net_rnd t 32
  | cks =>
    dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    obtain ⟨_, _, _, _, _, hcks_eq⟩ := hcks
    exact (hc.append_trEv _).append_net_of_closed (ctClosed_of_eq_chainKeyAt_createChain_snd hcks_eq)
  | ckr pk =>
    dsimp only; rcases hfind : findRecvChain st.recv pk with _ | c; · dsimp only; rw [Traceful.run_failure]; exact hc
    dsimp only; have hc_mem : c ∈ st.recv := CompPresTRExp.findRecvChain_mem hfind
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    refine (hc.append_trEv _).append_net_of_closed ?_
    obtain ⟨ikm, hikm⟩ := CompInv.CompPubInv.handshakeKeysAt_eq_pqxdhKdf hinv hkeys
    rcases hrecv c hc_mem with ⟨_, _, hck⟩ | ⟨n, _, _, hck⟩ | ⟨_, _, _, _, _, hck⟩
    · exact ctClosed_of_eq_chainKeyAt_pqxdhKdf_ck (n := 0) (by rw [hck, hikm]; rfl)
    · exact ctClosed_of_eq_chainKeyAt_pqxdhKdf_ck (n := n + 1) (by rw [hck, hikm])
    · exact ctClosed_of_eq_chainKeyAt_createChain_snd hck

private theorem ctClosed_preserves_exposeSkipped (skippedKeyEventIdx : Nat)
    (tr : ExecTrace) (hinv : SpqrInv tr) (hc : CtClosedCoreInv tr) :
    CtClosedCoreInv ((DY.Libsignal.TripleRatchet.exposeSkipped skippedKeyEventIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  apply CompPresTRExp.bind_getEntry_at (E := CompTrace.TREntry) skippedKeyEventIdx tr hc; intro ⟨ev⟩ he
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    dsimp only; obtain ⟨_, _, _, _, hseed⟩ := hinv.skipOK s pk n seed rIdx src skippedKeyEventIdx
      (by rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1])
    apply CompPresTRExp.bind_guardTrace_at _ tr hc; intro _
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
    have hseed_shape : ∃ c, seed = (kdfCk c).2 := by rcases hseed with ⟨m, rfl⟩ | ⟨_, _, _, m, _, rfl⟩ <;> exact ⟨_, rfl⟩
    obtain ⟨c, rfl⟩ := hseed_shape; exact (hc.append_trEv _).append_net_of_closed (ctClosed_kdfExtract _ _ _)
  | _ => dsimp only; rw [Traceful.run_failure]; exact hc

set_option maxHeartbeats 400000 in
theorem ctClosedCoreInv_of_reachable {tr : ExecTrace} (hr : ReachableTrace tr) : CtClosedCoreInv tr := by
  induction hr with
  | Base => exact ctClosedCoreInv_nil
  | Step input hPre hReachPre hc =>
    have hinv : SpqrInv _ := spqrInv_of_reachable _ hReachPre
    have hst_bind : ∀ {S α : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
        (p : Participant) (s : S) (k : Nat → Traceful α) (t : ExecTrace),
        ((PersistentLocalState.storeLocalState p s >>= k).run t).2.val =
          ((k t.length).run (t.append (⟨⟨p, s⟩⟩ : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState S)))).2.val :=
      fun p s k t => by
        simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
        rw [CompTrace.run_bind_snd, Traceful.run_mk]
    have hst_snd : ∀ {S : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
        (p : Participant) (s : S) (t : ExecTrace),
        ((PersistentLocalState.storeLocalState p s).run t).2.val =
          t.append (⟨⟨p, s⟩⟩ : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState S)) :=
      fun p s t => by
        simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
    have hlog_snd : ∀ {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)] (ev : E) (t : ExecTrace),
        ((ProtocolEvent.logEvent ev).run t).2.val = t.append (⟨ev⟩ : ProtocolEvent.ExecEntryT E) := fun ev t => by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
      rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
    rcases input with ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k, _⟩, inp⟩
    · change DY.Bytes at inp; change CtClosedCoreInv ((Network.sendMessage inp).run _).2.val; rw [CompPresTRExp.run_sendMessage_snd]
      exact hc.append_net_of_closed (hc.of_attackerKnows hPre)
    · change Participant at inp; change CtClosedCoreInv ((registerIdentity inp).run _).2.val; unfold registerIdentity
      refine bind_guardOnTrace_at _ _ hc fun _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, hst_snd]
      exact ((((hc.append_rnd 32).append_ev_nonBob _ (by intros; rintro ⟨⟩)).append_net_of_closed
        (ctClosed_dhPk_rand _ _)).append_net_of_closed (ctClosed_vk _ _)).append_st_nonPq inp _ (fun h => by cases h)
    · rcases inp with ⟨p, skIdx⟩; change CtClosedCoreInv ((registerCorruptIdentity p skIdx).run _).2.val; unfold registerCorruptIdentity
      refine bind_guardOnTrace_at _ _ hc fun _ => bind_receiveMessage_at skIdx _ hc fun _ _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, hlog_snd]
      exact (hc.append_ev_nonBob _ (by intros; rintro ⟨⟩)).append_ev_nonBob _ (by intros; rintro ⟨⟩)
    · rcases inp with ⟨b, idStateIdx⟩; change CtClosedCoreInv ((genSignedPrekey b idStateIdx).run _).2.val; unfold genSignedPrekey
      refine bind_getKey_at b idStateIdx .identity _ hc fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact (((((hc.append_rnd 32).append_rnd 64).append_ev_nonBob _ (by intros; rintro ⟨⟩)).append_st_nonPq b _
        (fun h => by cases h)).append_net_of_closed (ctClosed_dhPk_rand _ _)).append_net_of_closed (ctClosed_sign _ _ _ _)
    · rcases inp with ⟨b, idStateIdx⟩; exact ctClosed_preserves_genPQPrekey b idStateIdx _ hc
    · change Participant at inp; change CtClosedCoreInv ((genOneTimePrekey inp).run _).2.val; unfold genOneTimePrekey
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd, hst_bind,
        CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact (((hc.append_rnd 32).append_ev_nonBob _ (by intros; rintro ⟨⟩)).append_st_nonPq inp _
        (fun h => by cases h)).append_net_of_closed (ctClosed_dhPk_rand _ _)
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩; exact ctClosed_preserves_aliceStart a b idStateIdx regIdxB bh _ hc
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩; exact ctClosed_preserves_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩; exact ctClosed_preserves_messageEncrypt me stateIdx coinsLen pqIdx _ hinv hc
    · rcases inp with ⟨me, stateIdx⟩; change CtClosedCoreInv ((DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx).run _).2.val
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
      refine CompTrace.bind_getLocalState_tr_at me stateIdx _ hc fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, Traceful.run_failure]; exact hc.append_rnd 32
    · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩; exact ctClosed_preserves_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩; exact ctClosed_preserves_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ hc
    · rcases inp with ⟨me, stateIdx, k⟩; exact ctClosed_preserves_exposeKey me stateIdx k _ hinv hc
    · rcases inp with ⟨me, stateIdx⟩; change CtClosedCoreInv ((DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx).run _).2.val
      unfold DY.Libsignal.TripleRatchet.exposeSpqr
      apply CompTrace.bind_getLocalState_tr_at me stateIdx _ hc; intro st hst
      rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_sendMessage_snd]
      exact (hc.append_trEv _).append_net_of_closed ((hc.spqrClosed me st stateIdx hst).mono (Trace.append_le _ _))
    · exact ctClosed_preserves_exposeSkipped inp _ hinv hc
    · rcases inp with ⟨p, stateIdx⟩; change CtClosedCoreInv ((compromiseIK p stateIdx).run _).2.val; unfold compromiseIK
      refine bind_getKey_at p stateIdx .identity _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _⟩ := hinv.stOK p { kind := .identity, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact (hc.append_ev_nonBob _ (by intros; rintro ⟨⟩)).append_net_rnd t 32
    · rcases inp with ⟨b, stateIdx⟩; change CtClosedCoreInv ((compromiseSPK b stateIdx).run _).2.val; unfold compromiseSPK
      refine bind_getKey_at b stateIdx .signedPrekey _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .signedPrekey, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact (hc.append_ev_nonBob _ (by intros; rintro ⟨⟩)).append_net_rnd t 32
    · rcases inp with ⟨b, stateIdx⟩; change CtClosedCoreInv ((compromisePQSPK b stateIdx).run _).2.val; unfold compromisePQSPK
      refine bind_getKey_at b stateIdx .pqPrekey _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .pqPrekey, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact (hc.append_ev_nonBob _ (by intros; rintro ⟨⟩)).append_net_rnd t 64
    · rcases inp with ⟨b, stateIdx⟩; change CtClosedCoreInv ((compromiseOPK b stateIdx).run _).2.val; unfold compromiseOPK
      refine bind_getKey_at b stateIdx .oneTimePrekey _ hc fun sk hst => ?_
      obtain ⟨t, rfl, _, _⟩ := hinv.stOK b { kind := .oneTimePrekey, sk := sk } stateIdx hst
      refine CompPresPQXDH.Preserves.bind_guardOnTrace _ (fun _ hc _ => ?_) _ hc
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact (hc.append_ev_nonBob _ (by intros; rintro ⟨⟩)).append_net_rnd t 32
    · change CtClosedCoreInv ((DY.Libsignal.PQXDH.breakDH).run _).2.val; unfold DY.Libsignal.PQXDH.breakDH
      rw [hlog_snd]; exact hc.append_ev_nonBob _ (by intros; rintro ⟨⟩)
    · change CtClosedCoreInv ((DY.Libsignal.PQXDH.breakKEM).run _).2.val; unfold DY.Libsignal.PQXDH.breakKEM
      rw [hlog_snd]; exact hc.append_ev_nonBob _ (by intros; rintro ⟨⟩)
    · change Nat at inp; change CtClosedCoreInv ((invertDH inp).run _).2.val; unfold invertDH
      refine CompPresPQXDH.Preserves.bind_guardOnTrace DY.Libsignal.PQXDH.brokenDHB (fun tr hc _ => ?_) _ hc
      refine bind_receiveMessage_at inp tr hc fun pk _ hpk => ?_
      have hpk_safe : CtClosed tr (X25519.normalizeX25519Key pk) := ctClosed_x25519Key (hc.of_attackerKnows hpk)
      rcases hdh : DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
      · dsimp only; rw [Traceful.run_failure]; exact hc
      dsimp only; rw [CompPresTRExp.run_sendMessage_snd]; rw [dhSkOf_eq_some hdh] at hpk_safe
      exact hc.append_net_of_closed ((ctClosed_dhPk_iff sk).mp hpk_safe)
    · change Nat at inp; change CtClosedCoreInv ((invertKEM inp).run _).2.val; unfold invertKEM
      refine CompPresPQXDH.Preserves.bind_guardOnTrace DY.Libsignal.PQXDH.brokenKEMB (fun tr hc _ => ?_) _ hc
      refine bind_receiveMessage_at inp tr hc fun pk _ hpk => ?_
      have hpk_safe : CtClosed tr pk := hc.of_attackerKnows hpk
      rcases hkem : PQKem.invertKemPublicKey pk with _ | sk
      · dsimp only [liftM, monadLift, MonadLift.monadLift]; rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; exact hc
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [CompPresTRExp.run_sendMessage_snd]
      rw [kemPkInvert_eq_some hkem] at hpk_safe; exact hc.append_net_of_closed ((ctClosed_kemPk_iff sk).mp hpk_safe)
    · omega

/-- On any reachable composed trace `T`, every attacker-known term satisfies `CtClosed T`. -/
theorem ctClosed_of_attackerKnows_reachable {T : ExecTrace} (hT : ReachableTrace T)
    {b : DY.Bytes} (hAK : b.AttackerKnows T) : CtClosed T b :=
  (ctClosedCoreInv_of_reachable hT).of_attackerKnows hAK

/-- Every `BobDone` event on a reachable trace `T` carries an attacker-known `ct` and `pqpk`. -/
theorem bobDone_ct_pqpk_attackerKnows_of_reachable {T : ExecTrace} (hT : ReachableTrace T)
    {b a : Participant} {ikB ikA spk pqpk : DY.Bytes} {opk : Option DY.Bytes}
    {ek ct : DY.Bytes} {keys : HandshakeKeys} {idx : Nat}
    (hev : T.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) idx) :
    ct.AttackerKnows T ∧ pqpk.AttackerKnows T :=
  (ctClosedCoreInv_of_reachable hT).bobDoneAk b a ikB ikA spk pqpk opk ek ct keys idx hev

theorem kemEncap_fst_attackerKnows_inv {T : ExecTrace} (hT : ReachableTrace T)
    {pk e : DY.Bytes} (hk : (DY.PQKem.kemEncap pk e).1.AttackerKnows T) :
    e.AttackerKnows T ∨
      ∃ t a b ikA ikB spk pqpk opk ek ct keys,
        T.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5) ∧
        pk = pqpk ∧ e = randTerm (t + 1) 32 := by
  have hc := ctClosed_of_attackerKnows_reachable hT hk
  rw [kemEncap_fst_eq_pack] at hc; exact (ctClosed_encap_iff { pk := pk, entropy := e }).mp hc

theorem kemEncap_snd_attackerKnows_inv {T : ExecTrace} (hT : ReachableTrace T)
    {pk e : DY.Bytes} (hk : (DY.PQKem.kemEncap pk e).2.AttackerKnows T) :
    e.AttackerKnows T ∨
      ∃ t a b ikA ikB spk pqpk opk ek ct keys,
        T.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5) ∧
        pk = pqpk ∧ e = randTerm (t + 1) 32 := by
  have hc := ctClosed_of_attackerKnows_reachable hT hk
  rw [kemEncap_snd_eq_pack] at hc; exact (ctClosed_kemSS_iff { pk := pk, entropy := e }).mp hc

theorem kemRejKey_attackerKnows_iff_of_reachable {T : ExecTrace}
    (hreach : ReachableTrace T) (sk ct : DY.Bytes) :
    (DY.PQKem.kemRejKey sk ct).AttackerKnows T ↔ sk.AttackerKnows T ∧ ct.AttackerKnows T :=
  ⟨fun hk => (ctClosed_rejKey_iff sk ct).mp (ctClosed_of_attackerKnows_reachable hreach hk),
   fun ⟨hsk, hct⟩ => DY.Bytes.AttackerKnows.prove DY.PQKem.kemRejKey.attackerKnowledge _ T
     ⟨sk, ct, rfl, hsk, hct⟩⟩

end Stage1CtClosed

end Symbolic.Swarm.CREF.TR.G1.Spine
