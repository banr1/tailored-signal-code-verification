/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Stage1Trials -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepPtAtomsTR

/-!
# Self-Memo Membership for Non-SPQR Non-Opaque Terms and MAC Shape Agreement

Defines `notSpqrHeaded` and `notOpaqueHeaded`, proves that every non-empty term satisfying both
carries a self-memo entry (`self_mem_memo_of_notSpqrHeaded`), and derives MAC shape agreement under
`¬MemoCollisionOn` (`g1_noSelfMemo_len8_of_notSpqrHeaded`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg trMsgKeys)

open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (computeMac hmac)
open CryptoProofLib.Refinement (ExternInterpretation)

unseal DY.Bytes in
private instance subRandomG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subLit0G1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subConcat0G1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeConcat (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhPkG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDhPk i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDh i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKdf0G1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSym0G1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSym i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, symFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subTrunc0G1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeTrunc (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVariant0G1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrInitG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrInit S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrSendStateG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendState S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrSendKeyG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrSendMsgG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendMsg S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrRecvStateG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrRecvState S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrRecvKeyG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrRecvKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrChainKeyG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrChainKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subTrWire0G1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, trWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemPkG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemPk S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemEncapG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemEncap i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemSSG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemSS i S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemRejG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemRej S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVkG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVk S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSignG1R (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSign S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

/-! ## `notSpqrHeaded`, `notOpaqueHeaded`, and self-memo membership -/

/-- `u` is not headed by any of the seven SPQR constructors. -/
def notSpqrHeaded (u : DY.Bytes) : Prop :=
  (u.view? DY.Spqr.InitState.SubF).isNone = true ∧
  (u.view? DY.Spqr.SendState.SubF).isNone = true ∧
  (u.view? DY.Spqr.SendKey.SubF).isNone = true ∧
  (u.view? DY.Spqr.SendMsg.SubF).isNone = true ∧
  (u.view? DY.Spqr.RecvState.SubF).isNone = true ∧
  (u.view? DY.Spqr.RecvKey.SubF).isNone = true ∧
  (u.view? DY.Spqr.ChainKey.SubF).isNone = true

theorem notSpqrHeaded_computeMac (mk ik1 ik2 w : DY.Bytes) :
    notSpqrHeaded (computeMac mk ik1 ik2 w) := by
  change notSpqrHeaded (({ input := hmac mk (Concat.concat ik1 (Concat.concat ik2 w)) } :
    DY.Trunc.Trunc8.SubF DY.Bytes).pack)
  unfold notSpqrHeaded
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendState.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendKey.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendMsg.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.RecvState.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.RecvKey.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.ChainKey.SubF]; rfl

/-- `u` is not headed by an opaque KEM or signature constructor. -/
def notOpaqueHeaded (u : DY.Bytes) : Prop :=
  (u.view? DY.PQKem.Pk.SubF).isNone = true ∧
  (u.view? DY.PQKem.Encap.SubF).isNone = true ∧
  (u.view? DY.PQKem.SharedSecret.SubF).isNone = true ∧
  (u.view? DY.Signature.Vk.SubF).isNone = true ∧
  (u.view? DY.Signature.Sign.SubF).isNone = true

theorem notOpaqueHeaded_computeMac (mk ik1 ik2 w : DY.Bytes) :
    notOpaqueHeaded (computeMac mk ik1 ik2 w) := by
  change notOpaqueHeaded (({ input := hmac mk (Concat.concat ik1 (Concat.concat ik2 w)) } :
    DY.Trunc.Trunc8.SubF DY.Bytes).pack)
  unfold notOpaqueHeaded
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Pk.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Encap.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.SharedSecret.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Signature.Vk.SubF]; rfl
  · rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Signature.Sign.SubF]; rfl

unseal DY.Bytes in
private theorem partialFunDep_node_self_memo
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hg : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm),
      ((BytesView.pack x : DY.Bytes), (gF x rec).shape, (gF x rec).bytes) ∈ (gF x rec).memo) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        gamma i S g u ≠ [] →
        notSpqrHeaded u → notOpaqueHeaded u →
        (u, (gamma' i S g u).shape, gamma i S g u) ∈ (gamma' i S g u).memo) := by
  intro x _
  refine (Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x) ▸ fun _ _ _ => ?_
  change (BytesView.pack x, ((BytesView.pack x).rec (concretizeAll i S g)).shape,
    ((BytesView.pack x).rec (concretizeAll i S g)).bytes) ∈ ((BytesView.pack x).rec (concretizeAll i S g)).memo
  rw [DY.Bytes.rec_eq gF (concretizeAll i S g) x]
  exact hg x _

private theorem random_self_memo_step
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (x : DY.Random.Random DY.Bytes)
    (hne : gamma i S g (BytesView.pack x) ≠ []) :
    (BytesView.pack x, (gamma' i S g (BytesView.pack x)).shape,
      gamma i S g (BytesView.pack x)) ∈ (gamma' i S g (BytesView.pack x)).memo := by
  change ((BytesView.pack x).rec (concretizeAll i S g)).bytes ≠ [] at hne
  change (BytesView.pack x, ((BytesView.pack x).rec (concretizeAll i S g)).shape,
    ((BytesView.pack x).rec (concretizeAll i S g)).bytes) ∈ ((BytesView.pack x).rec (concretizeAll i S g)).memo
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g) x] at hne ⊢
  dsimp only [concretizeRandom] at hne ⊢
  split at hne
  · exfalso
    apply hne
    rfl
  · next hsz =>
    simp only [hsz, ↓reduceIte, node, List.mem_cons, true_or]

unseal DY.Bytes in
private theorem partialFunDep_random_self_memo
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.ALaCarte.Container.PartialFunDep DY.Random.Random (g := DY.BytesF)
      (fun u : DY.Bytes =>
        gamma i S g u ≠ [] →
        notSpqrHeaded u → notOpaqueHeaded u →
        (u, (gamma' i S g u).shape, gamma i S g u) ∈ (gamma' i S g u).memo) := by
  intro x _
  exact (Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x) ▸ fun hne _ _ =>
    random_self_memo_step i S g x hne

private theorem spqr_absurd_step
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (hproj : ∀ u : DY.Bytes, notSpqrHeaded u → (u.view? SubF).isNone = true)
    (x : SubF DY.Bytes)
    (hns : notSpqrHeaded (BytesView.pack x)) :
    (BytesView.pack x, (gamma' i S g (BytesView.pack x)).shape,
      gamma i S g (BytesView.pack x)) ∈ (gamma' i S g (BytesView.pack x)).memo := by
  have hnone := hproj (BytesView.pack x) hns
  rw [DY.BytesView.view_pack (SubF := SubF)] at hnone
  cases hnone

unseal DY.Bytes in
private theorem partialFunDep_spqr_absurd
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (hproj : ∀ u : DY.Bytes, notSpqrHeaded u → (u.view? SubF).isNone = true) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        gamma i S g u ≠ [] →
        notSpqrHeaded u → notOpaqueHeaded u →
        (u, (gamma' i S g u).shape, gamma i S g u) ∈ (gamma' i S g u).memo) := by
  intro x _
  exact (Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x) ▸ fun _ hns _ =>
    spqr_absurd_step i S g hproj x hns

private theorem opaque_absurd_step
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (hproj : ∀ u : DY.Bytes, notOpaqueHeaded u → (u.view? SubF).isNone = true)
    (x : SubF DY.Bytes)
    (hno : notOpaqueHeaded (BytesView.pack x)) :
    (BytesView.pack x, (gamma' i S g (BytesView.pack x)).shape,
      gamma i S g (BytesView.pack x)) ∈ (gamma' i S g (BytesView.pack x)).memo := by
  have hnone := hproj (BytesView.pack x) hno
  rw [DY.BytesView.view_pack (SubF := SubF)] at hnone
  cases hnone

unseal DY.Bytes in
private theorem partialFunDep_opaque_absurd
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (hproj : ∀ u : DY.Bytes, notOpaqueHeaded u → (u.view? SubF).isNone = true) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        gamma i S g u ≠ [] →
        notSpqrHeaded u → notOpaqueHeaded u →
        (u, (gamma' i S g u).shape, gamma i S g u) ∈ (gamma' i S g u).memo) := by
  intro x _
  exact (Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x) ▸ fun _ _ hno =>
    opaque_absurd_step i S g hproj x hno

unseal DY.Bytes in
/-- Every `u : DY.Bytes` with `gamma i S g u ≠ []`, `notSpqrHeaded u`, and `notOpaqueHeaded u` has
a self-memo entry `(u, (gamma' i S g u).shape, gamma i S g u) ∈ (gamma' i S g u).memo`. -/
theorem self_mem_memo_of_notSpqrHeaded
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (u : DY.Bytes)
    (hne : gamma i S g u ≠ []) (hns : notSpqrHeaded u) (hno : notOpaqueHeaded u) :
    (u, (gamma' i S g u).shape, gamma i S g u) ∈ (gamma' i S g u).memo := by
  let M : DY.Bytes → Prop := fun u =>
    gamma i S g u ≠ [] →
    notSpqrHeaded u → notOpaqueHeaded u →
    (u, (gamma' i S g u).shape, gamma i S g u) ∈ (gamma' i S g u).memo
  have hpack : ∀ {SubF : Type → Type} [DY.ALaCarte.FunctorSizeOf SubF]
      [DY.ALaCarte.SubFunctorTC SubF DY.BytesF]
      (v : SubF (DY.ALaCarte.ContainerFor DY.BytesF)),
      M (DY.ALaCarte.Container.pack SubF v) →
      M (DY.ALaCarte.Container.pack DY.BytesF (DY.ALaCarte.SubFunctorTC.inj (g := DY.BytesF) v)) := by
    intro SubF _ _ v hm
    have hv : DY.ALaCarte.Container.view DY.BytesF (DY.ALaCarte.Container.pack SubF v) =
        some (DY.ALaCarte.SubFunctorTC.inj (g := DY.BytesF) v) := by
      rw [Symbolic.DYBridge.DY.ALaCarte.Container.view_pack_cross]
      rfl
    have hp := DY.ALaCarte.Container.pack_view (f := DY.BytesF) (DY.ALaCarte.Container.pack SubF v)
    rw [hv] at hp
    exact hp ▸ hm
  revert hne hns hno
  refine DY.ALaCarte.Container.rec (f := DY.BytesF) (motive := M) ?_ u
  rintro ⟨⟨id, hid⟩, val⟩ rec
  match id with
  | 0 => exact hpack _ (partialFunDep_random_self_memo i S g val rec)
  | 1 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact hpack _ (partialFunDep_node_self_memo i S g concretizeLit (fun _ _ => by simp [concretizeLit, node]) v rec)
    | n + 1 => omega
  | 2 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact hpack _ (partialFunDep_node_self_memo i S g concretizeConcat (fun _ _ => by simp [concretizeConcat, node]) v rec)
    | n + 1 => omega
  | 3 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact hpack _ (partialFunDep_node_self_memo i S g (concretizeDhPk i) (fun _ _ => by simp [concretizeDhPk, node]) v rec)
    | 1 => exact hpack _ (partialFunDep_node_self_memo i S g (concretizeDh i) (fun _ _ => by simp [concretizeDh, node]) v rec)
    | n + 2 => omega
  | 4 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact hpack _ (partialFunDep_node_self_memo i S g (concretizeKdf i) (fun _ _ => by simp [concretizeKdf, node]) v rec)
    | n + 1 => omega
  | 5 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact hpack _ (partialFunDep_node_self_memo i S g (concretizeSym i) (fun _ _ => by simp [concretizeSym, node]) v rec)
    | n + 1 => omega
  | 6 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact hpack _ (partialFunDep_node_self_memo i S g concretizeTrunc (fun _ _ => by simp [concretizeTrunc, node]) v rec)
    | n + 1 => omega
  | 7 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact hpack _ (partialFunDep_node_self_memo i S g (concretizeVariant i) (fun _ _ => by simp [concretizeVariant, node]) v rec)
    | n + 1 => omega
  | 8 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact hpack _ (partialFunDep_opaque_absurd i S g (fun _ h => h.1) v rec)
    | 1 => exact hpack _ (partialFunDep_opaque_absurd i S g (fun _ h => h.2.1) v rec)
    | 2 => exact hpack _ (partialFunDep_opaque_absurd i S g (fun _ h => h.2.2.1) v rec)
    | 3 => exact hpack _ (partialFunDep_node_self_memo i S g (concretizeKemRej S) (fun _ _ => by simp [concretizeKemRej, node]) v rec)
    | n + 4 => omega
  | 9 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact hpack _ (partialFunDep_opaque_absurd i S g (fun _ h => h.2.2.2.1) v rec)
    | 1 => exact hpack _ (partialFunDep_opaque_absurd i S g (fun _ h => h.2.2.2.2) v rec)
    | n + 2 => omega
  | 10 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact hpack _ (partialFunDep_spqr_absurd i S g (fun _ h => h.1) v rec)
    | 1 => exact hpack _ (partialFunDep_spqr_absurd i S g (fun _ h => h.2.1) v rec)
    | 2 => exact hpack _ (partialFunDep_spqr_absurd i S g (fun _ h => h.2.2.1) v rec)
    | 3 => exact hpack _ (partialFunDep_spqr_absurd i S g (fun _ h => h.2.2.2.1) v rec)
    | 4 => exact hpack _ (partialFunDep_spqr_absurd i S g (fun _ h => h.2.2.2.2.1) v rec)
    | 5 => exact hpack _ (partialFunDep_spqr_absurd i S g (fun _ h => h.2.2.2.2.2.1) v rec)
    | 6 => exact hpack _ (partialFunDep_spqr_absurd i S g (fun _ h => h.2.2.2.2.2.2) v rec)
    | n + 7 => omega
  | 11 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact hpack _ (partialFunDep_node_self_memo i S g (concretizeTrWire g) (fun _ _ => by simp [concretizeTrWire, node]) v rec)
    | n + 1 => omega
  | n + 12 => omega

/-! ## Memo propagation for `computeMac` and `whisperTrials` -/

theorem parseTrSignalMsg_eq_concat
    {t : DY.Bytes} {msg : TRSignalMsg}
    (hparse : parseTrSignalMsg t = some msg) :
    t = Concat.concat msg.wire msg.mac :=
  (parseTrSignalMsg_eq_some_concat_and_mac_length_le_8_tr32 hparse).1

private theorem g1Rep_length_hmacWith
    (F : ByteSpecs.ShaState → List (BitVec 8) → ByteSpecs.ShaState)
    (k m : List (BitVec 8)) :
    (ByteSpecs.hmacWith F k m).length = 32 := by
  unfold ByteSpecs.hmacWith ByteSpecs.sha256With
  generalize (ByteSpecs.chunks64 (ByteSpecs.sha256Pad _)).foldl F ByteSpecs.sha256IV = s
  rcases s with ⟨l, _⟩
  simp [ByteSpecs.toBEBytes, List.length_flatMap]

theorem gamma_computeMac_ne_nil (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (mk ik1 ik2 w : DY.Bytes) :
    gamma i S g (computeMac mk ik1 ik2 w) ≠ [] := by
  have hlen : (gamma i S g (computeMac mk ik1 ik2 w)).length = 8 := by
    unfold computeMac hmac gamma gamma'
    show (((({ input := KdfExtract.kdfExtract mk (Concat.concat ik1 (Concat.concat ik2 w)) } :
      DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes).length = 8
    rw [DY.Bytes.rec_eq concretizeTrunc (concretizeAll i S g)]
    dsimp only [concretizeTrunc, node]
    show (((({ salt := mk, ikm := Concat.concat ik1 (Concat.concat ik2 w) } :
      DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes.take 8).length = 8
    rw [DY.Bytes.rec_eq (concretizeKdf i) (concretizeAll i S g)]
    dsimp only [concretizeKdf, node]
    rw [List.length_take, g1Rep_length_hmacWith]
    rfl
  intro hnil
  rw [hnil] at hlen
  cases hlen

theorem memo_rhs_subset_memo_concat (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (l r : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes}
    (he : e ∈ (gamma' i S g r).memo) :
    e ∈ (gamma' i S g (Concat.concat l r)).memo := by
  unfold gamma' at he ⊢
  rw [show Concat.concat l r = ({ lhs := l, rhs := r } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq concretizeConcat (concretizeAll i S g)]
  simp [concretizeConcat, node, he]

theorem self_mem_memo_computeMac_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (mk ik1 ik2 w : DY.Bytes) :
    let cmac := computeMac mk ik1 ik2 w
    (cmac, (gamma' i S g cmac).shape, gamma i S g cmac) ∈ (gamma' i S g cmac).memo := by
  intro cmac
  change (cmac, (gamma' i S g cmac).shape, (gamma' i S g cmac).bytes) ∈ (gamma' i S g cmac).memo
  unfold cmac computeMac gamma'
  rw [show DY.Trunc.trunc8 (hmac mk (Concat.concat ik1 (Concat.concat ik2 w))) =
      ({ input := hmac mk (Concat.concat ik1 (Concat.concat ik2 w)) } :
        DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq concretizeTrunc (concretizeAll i S g)]
  simp [concretizeTrunc, node]

theorem computeMac_mem_whisperTrialTerms
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {salts : List DY.Bytes} {st : TRState} {msg : TRSignalMsg}
    {salt seed : DY.Bytes}
    (hst : st ∈ availableStates r tr)
    (hsalt : salt ∈ salts)
    (hseed : recvSeed st msg = some seed) :
    computeMac (trMsgKeys salt seed).macKey st.peerIk st.myIk msg.wire ∈
      (whisperTrials interpretation r S g tr msg).flatMap (trialTerms salts msg) := by
  unfold recvSeed at hseed
  split at hseed
  · next hver =>
    split at hseed
    · cases hseed
    · next c fresh hrc =>
      simp only [Option.map_eq_some_iff] at hseed
      obtain ⟨⟨s, c'⟩, hcmk, rfl⟩ := hseed
      exact Symbolic.Swarm.CREF.Stage1Trials.computeMac_mem_whisperTrialTerms_of_recvChainFor
        hver hst hrc hcmk hsalt
  · cases hseed

/-! ## Plaintext-atom exclusion and MAC shape agreement -/

theorem not_mem_ptAtoms_of_view_random_isNone
    (r₀ : ProtocolSetup) (ms : List Move) (extra : List VisEntry) (hextra : ∀ v ∈ extra, v.kind ≠ .pt)
    (u : DY.Bytes) (hview : (u.view? DY.Random.Random).isNone = true) :
    u ∉ plaintextTerms (runVis r₀ ms ++ extra) := by
  intro hu
  obtain ⟨j, rfl⟩ := ptAtoms_runVis_mem_inv_tr32 r₀ ms extra hextra hu
  unfold randTerm at hview
  rw [DY.BytesView.view_pack (SubF := DY.Random.Random)] at hview
  cases hview

theorem computeMac_not_mem_ptAtoms
    (r₀ : ProtocolSetup) (ms : List Move) (extra : List VisEntry) (hextra : ∀ v ∈ extra, v.kind ≠ .pt)
    (mk ik1 ik2 w : DY.Bytes) :
    computeMac mk ik1 ik2 w ∉ plaintextTerms (runVis r₀ ms ++ extra) := by
  refine not_mem_ptAtoms_of_view_random_isNone r₀ ms extra hextra _ ?_
  change ((({ input := hmac mk (Concat.concat ik1 (Concat.concat ik2 w)) } :
    DY.Trunc.Trunc8.SubF DY.Bytes).pack).view? DY.Random.Random).isNone = true
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random]
  rfl

/-- Under `notSpqrHeaded msg₀.mac`, `notOpaqueHeaded msg₀.mac`, and `¬MemoCollisionOn` over
`whisperTrials`, byte equality `gamma msg₀.mac = gamma cmac` implies
`(gamma' msg₀.mac).shape = (gamma' cmac).shape` whenever `msg₀.mac` is not a plaintext atom or
`cmac` is not attacker-known. -/
theorem g1_noSelfMemo_len8_of_notSpqrHeaded
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (b : HwBytes) (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (_ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hns : notSpqrHeaded msg₀.mac) (hno : notOpaqueHeaded msg₀.mac)
    (hNotMemo : ¬MemoCollisionOn interpretation r₀ S g
      (fun u => u.AttackerKnows (runTraceMoves r₀ ms)) (runTraceMoves r₀ ms) (runVis r₀ ms)
      (t₀ :: (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg₀).flatMap
        (trialTerms (honestSalts r₀ ms) msg₀)) [])
    (st₁ : TRState) (hst₁ : st₁ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (salt₁ : DY.Bytes) (hsalt₁ : salt₁ ∈ honestSalts r₀ ms)
    (seed₁ : DY.Bytes) (hseed₁ : recvSeed st₁ msg₀ = some seed₁)
    (hpt : msg₀.mac ∉ plaintextTerms (runVis r₀ ms) ∨
      ¬(computeMac (trMsgKeys salt₁ seed₁).macKey st₁.peerIk st₁.myIk msg₀.wire).AttackerKnows
        (runTraceMoves r₀ ms))
    (hMacEq : gamma interpretation S g msg₀.mac =
      gamma interpretation S g
        (computeMac (trMsgKeys salt₁ seed₁).macKey st₁.peerIk st₁.myIk msg₀.wire)) :
    (gamma' interpretation S g msg₀.mac).shape =
      (gamma' interpretation S g
        (computeMac (trMsgKeys salt₁ seed₁).macKey st₁.peerIk st₁.myIk msg₀.wire)).shape := by
  by_contra hne
  apply hNotMemo
  unfold MemoCollisionOn
  dsimp only
  let cmac := computeMac (trMsgKeys salt₁ seed₁).macKey st₁.peerIk st₁.myIk msg₀.wire
  have ht₀_cat : t₀ = Concat.concat msg₀.wire msg₀.mac :=
    parseTrSignalMsg_eq_concat hparse₀
  have hmac_ne_nil : gamma interpretation S g msg₀.mac ≠ [] := by
    rw [hMacEq]
    exact gamma_computeMac_ne_nil interpretation S g _ _ _ _
  have hmac_mem_mac :
      (msg₀.mac, (gamma' interpretation S g msg₀.mac).shape,
        gamma interpretation S g msg₀.mac) ∈
      (gamma' interpretation S g msg₀.mac).memo :=
    self_mem_memo_of_notSpqrHeaded interpretation S g msg₀.mac hmac_ne_nil hns hno
  have hmac_mem_t₀ :
      (msg₀.mac, (gamma' interpretation S g msg₀.mac).shape,
        gamma interpretation S g msg₀.mac) ∈
      (gamma' interpretation S g t₀).memo := by
    rw [ht₀_cat]
    exact memo_rhs_subset_memo_concat interpretation S g msg₀.wire msg₀.mac hmac_mem_mac
  have hcmac_mem :
      (cmac, (gamma' interpretation S g cmac).shape, gamma interpretation S g cmac) ∈
      (gamma' interpretation S g cmac).memo :=
    self_mem_memo_computeMac_tr interpretation S g _ _ _ _
  have hcmac_rt : cmac ∈
      (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg₀).flatMap
        (trialTerms (honestSalts r₀ ms) msg₀) :=
    computeMac_mem_whisperTrialTerms hst₁ hsalt₁ hseed₁
  have hinj : assumedInjective cmac = true := by
    have hv : (cmac.view? DY.Trunc.Trunc8.SubF).isSome = true := by
      dsimp only [cmac, computeMac, DY.Trunc.trunc8, DY.Trunc.CanTrunc8.trunc8]
      rw [DY.BytesView.view_pack]; rfl
    unfold assumedInjective
    rw [hv]
    simp
  have hcmac_not_pt : cmac ∉ plaintextTerms (runVis r₀ ms) ++ [] := by
    rw [List.append_nil]
    have h := computeMac_not_mem_ptAtoms r₀ ms [] (fun _ h => absurd h List.not_mem_nil)
      (trMsgKeys salt₁ seed₁).macKey st₁.peerIk st₁.myIk msg₀.wire
    rwa [List.append_nil] at h
  let x₁ : DY.Bytes × DY.Bytes × HwBytes :=
    (msg₀.mac, (gamma' interpretation S g msg₀.mac).shape, gamma interpretation S g msg₀.mac)
  let x₂ : DY.Bytes × DY.Bytes × HwBytes :=
    (cmac, (gamma' interpretation S g cmac).shape, gamma interpretation S g cmac)
  have hx₁_new : x₁ ∈ (t₀ :: (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg₀).flatMap
        (trialTerms (honestSalts r₀ ms) msg₀)).flatMap
      (fun u => (gamma' interpretation S g u).memo) := by
    rw [List.mem_flatMap]
    exact ⟨t₀, List.mem_cons_self .., hmac_mem_t₀⟩
  have hx₂_new : x₂ ∈ (t₀ :: (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg₀).flatMap
        (trialTerms (honestSalts r₀ ms) msg₀)).flatMap
      (fun u => (gamma' interpretation S g u).memo) := by
    rw [List.mem_flatMap]
    exact ⟨cmac, List.mem_cons_of_mem _ hcmac_rt, hcmac_mem⟩
  refine ⟨x₁, hx₁_new, x₂, List.mem_append_right _ hx₂_new,
    hne, Or.inr hinj, ?_, fun h2 => False.elim (hcmac_not_pt h2), hMacEq⟩
  intro h1
  rcases hpt with hmac_not_pt | hcmac_not_ak
  · rw [List.append_nil] at h1
    exact False.elim (hmac_not_pt h1)
  · exact ⟨hcmac_not_pt, hinj, hcmac_not_ak⟩

end Symbolic.Swarm.CREF.TR.G1
