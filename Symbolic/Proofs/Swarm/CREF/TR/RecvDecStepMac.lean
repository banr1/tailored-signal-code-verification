/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Trace.Basic
import DY.Trace.Monad
import DY.Bytes.Basic
import DY.ALaCarte.Basic
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
public import Symbolic.Specifications.Refinement.Concretization
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Symbolic Truncation Shape Inversion

Unfolds `(gamma' interpretation S g t).shape` across all composed `DY.BytesF` constructors and
proves that `Trunc.trunc8` is the unique term constructor producing a `Trunc8`-headed shape.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.TR.RecvDecStep

cref_open
open DY.Literal
open CryptoProofLib.Refinement (ExternInterpretation)

unseal DY.Bytes in
instance subRandomTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subLit0Tr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subConcat0Tr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeConcat (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subDhPkTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDhPk interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subDhTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDh interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subKdf0Tr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subSym0Tr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSym interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, symFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subTrunc0Tr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeTrunc (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩


unseal DY.Bytes in
instance subVariant0Tr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subSpqrInitTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrInit S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subSpqrSendStateTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendState S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subSpqrSendKeyTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendKey S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subSpqrSendMsgTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendMsg S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subSpqrRecvStateTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrRecvState S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subSpqrRecvKeyTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrRecvKey S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subSpqrChainKeyTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrChainKey S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subTrWire0Tr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, trWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subKemPkTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemPk S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subKemEncapTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemEncap interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subKemSS_Tr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemSS interpretation S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subKemRejTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemRej S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subVkTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVk S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
instance subSignTr' (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSign S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem shape_trunc8_tr (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (x : DY.Bytes) :
    (gamma' interpretation S g (Trunc.trunc8 x)).shape =
      Trunc.trunc8 (gamma' interpretation S g x).shape := by
  show (gamma' interpretation S g (({ input := x } : DY.Trunc.Trunc8.SubF DY.Bytes).pack)).shape = _
  unfold gamma'
  rw [DY.Bytes.rec_eq concretizeTrunc (concretizeAll interpretation S g)]
  rfl

theorem shape_kdfExtract_tr (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (s i : DY.Bytes) :
    (gamma' interpretation S g (KdfExtract.kdfExtract s i)).shape =
      KdfExtract.kdfExtract (gamma' interpretation S g s).shape (gamma' interpretation S g i).shape := by
  show (gamma' interpretation S g (({ salt := s, ikm := i } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack)).shape = _
  unfold gamma'
  rw [DY.Bytes.rec_eq (concretizeKdf interpretation) (concretizeAll interpretation S g)]
  rfl

theorem shape_concat_tr (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (l r : DY.Bytes) :
    (gamma' interpretation S g (Concat.concat l r)).shape =
      Concat.concat (gamma' interpretation S g l).shape (gamma' interpretation S g r).shape := by
  show (gamma' interpretation S g (({ lhs := l, rhs := r } : DY.Concat.Concat.SubF DY.Bytes).pack)).shape = _
  unfold gamma'
  rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll interpretation S g)]
  rfl

theorem shape_trWireMsg_tr (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (v : UInt8) (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes) (ev : DY.TrWire.EncodingVariation) :
    (gamma' interpretation S g (DY.TrWire.trWireMsg v rk c pc ct pq ev)).shape =
      DY.TrWire.trWireMsg
        v
        (gamma' interpretation S g rk).shape
        c
        pc
        (gamma' interpretation S g ct).shape
        (gamma' interpretation S g pq).shape
        { ev with fields := .extra 6 (.bytes (g.addr (DY.TrWire.trWireMsg v rk c pc ct pq ev))) 0 0 :: ev.fields } := by
  show (gamma' interpretation S g ((⟨v, rk, c, pc, ct, pq, ev⟩ : DY.TrWire.TrWireMsg.SubF DY.Bytes).pack)).shape = _
  unfold gamma'
  rw [DY.Bytes.rec_eq (concretizeTrWire g) (concretizeAll interpretation S g)]
  rfl

private theorem container_pack_inj_sub
    (f g : Type → Type)
    [DY.ALaCarte.FunctorSizeOf f] [DY.ALaCarte.FunctorSizeOf g]
    [DY.ALaCarte.SubFunctorTC f g] [DY.ALaCarte.Representable g]
    (x : f (DY.ALaCarte.ContainerFor g)) :
    DY.ALaCarte.Container.pack g (DY.ALaCarte.SubFunctorTC.inj (g := g) x) =
      DY.ALaCarte.Container.pack f x := by
  have hv := DY.ALaCarte.Container.pack_view g (DY.ALaCarte.Container.pack f x)
  rw [Symbolic.DYBridge.DY.ALaCarte.Container.view_pack_cross f g x] at hv
  exact hv

private theorem lift_partialFunDep
    {f g : Type → Type} [DY.ALaCarte.FunctorSizeOf f] [DY.ALaCarte.FunctorSizeOf g]
    [DY.ALaCarte.SubFunctorTC f g] [DY.ALaCarte.Representable g]
    {motive : DY.ALaCarte.ContainerFor g → Prop}
    (h : DY.ALaCarte.Container.PartialFunDep f (g := g) motive)
    (x : f (DY.ALaCarte.ContainerFor g))
    (rec : ∀ y : DY.ALaCarte.ContainerFor g,
      sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf (DY.ALaCarte.SubFunctorTC.inj (g := g) x) → motive y) :
    motive (DY.ALaCarte.Container.pack g (DY.ALaCarte.SubFunctorTC.inj (g := g) x)) := by
  rw [container_pack_inj_sub f g x]
  exact h x fun y hy => rec y (DY.ALaCarte.SubFunctorTC.sizeOf_inj (g := g) x ▸ hy)

unseal DY.Bytes in
theorem partialFunDep_not_trunc8
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sh_inp : DY.Bytes)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll interpretation S g)]
    (hg : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm),
      DY.Bytes.view? (gF x rec).shape DY.Trunc.Trunc8.SubF = none) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        DY.Bytes.view? (gamma' interpretation S g u).shape DY.Trunc.Trunc8.SubF =
          some { input := sh_inp } →
        ∃ inp : DY.Bytes, u = Trunc.trunc8 inp ∧ (gamma' interpretation S g inp).shape = sh_inp) := by
  intro x _ hview
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview
  change DY.Bytes.view? ((BytesView.pack x).rec (concretizeAll interpretation S g)).shape DY.Trunc.Trunc8.SubF = _ at hview
  rw [DY.Bytes.rec_eq gF (concretizeAll interpretation S g) x, hg x _] at hview
  contradiction

unseal DY.Bytes in
theorem partialFunDep_trunc8
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sh_inp : DY.Bytes) :
    DY.ALaCarte.Container.PartialFunDep DY.Trunc.Trunc8.SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        DY.Bytes.view? (gamma' interpretation S g u).shape DY.Trunc.Trunc8.SubF =
          some { input := sh_inp } →
        ∃ inp : DY.Bytes, u = Trunc.trunc8 inp ∧ (gamma' interpretation S g inp).shape = sh_inp) := by
  intro x _ hview
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview
  change DY.Bytes.view? ((BytesView.pack x).rec (concretizeAll interpretation S g)).shape DY.Trunc.Trunc8.SubF = _ at hview
  rw [DY.Bytes.rec_eq concretizeTrunc (concretizeAll interpretation S g) x] at hview
  dsimp only [concretizeTrunc, node] at hview
  rw [DY.BytesView.view_pack (SubF := DY.Trunc.Trunc8.SubF)] at hview
  injection hview with h1
  injection h1 with h2
  exact ⟨x.input, (Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x).symm, h2⟩

unseal DY.Bytes in
/-- Across all functor families of `DY.Libsignal.Composed.BytesF`, `Trunc.trunc8` is the unique
constructor whose concretized `.shape` has a `Trunc8` head. -/
theorem view?_trunc8_shape_eq_some_iff
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (u : DY.Bytes) (sh_inp : DY.Bytes) :
    DY.Bytes.view? (gamma' interpretation S g u).shape DY.Trunc.Trunc8.SubF =
      some { input := sh_inp } ↔
    ∃ inp : DY.Bytes,
      u = Trunc.trunc8 inp ∧ (gamma' interpretation S g inp).shape = sh_inp := by
  constructor
  · refine DY.ALaCarte.Container.rec (f := DY.BytesF)
      (motive := fun u : DY.Bytes =>
        DY.Bytes.view? (gamma' interpretation S g u).shape DY.Trunc.Trunc8.SubF =
          some { input := sh_inp } →
        ∃ inp : DY.Bytes, u = Trunc.trunc8 inp ∧ (gamma' interpretation S g inp).shape = sh_inp) ?_ u
    rintro ⟨⟨id, hid⟩, val⟩ rec
    match id with
    | 0 =>
      exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeRandom g)
        (fun _ _ => by dsimp only [concretizeRandom]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) val rec
    | 1 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp concretizeLit (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | n + 1 => omega
    | 2 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp concretizeConcat (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | n + 1 => omega
    | 3 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeDhPk interpretation) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | 1 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeDh interpretation) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | n + 2 => omega
    | 4 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeKdf interpretation) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | n + 1 => omega
    | 5 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeSym interpretation) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | n + 1 => omega
    | 6 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_trunc8 interpretation S g sh_inp) v rec
      | n + 1 => omega
    | 7 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeVariant interpretation) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | n + 1 => omega
    | 8 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeKemPk S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | 1 =>
        exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeKemEncap interpretation)
          (fun _ _ => by dsimp only [concretizeKemEncap]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | 2 =>
        exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeKemSS interpretation S)
          (fun _ _ => by dsimp only [concretizeKemSS]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | 3 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeKemRej S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | n + 4 => omega
    | 9 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeVk S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | 1 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeSign S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | n + 2 => omega
    | 10 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeSpqrInit S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | 1 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeSpqrSendState S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | 2 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeSpqrSendKey S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | 3 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeSpqrSendMsg S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | 4 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeSpqrRecvState S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | 5 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeSpqrRecvKey S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | 6 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeSpqrChainKey S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | n + 7 => omega
    | 11 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_trunc8 interpretation S g sh_inp (concretizeTrWire g) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec
      | n + 1 => omega
    | n + 12 => omega
  · rintro ⟨inp, rfl, rfl⟩
    rw [shape_trunc8_tr]
    exact DY.BytesView.view_pack (SubF := DY.Trunc.Trunc8.SubF) _

end Symbolic.Swarm.CREF.TR.RecvDecStep
