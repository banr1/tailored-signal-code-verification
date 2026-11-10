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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import VCVio.Prelude.Core
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
# Wire-Message Shape Address Determination and Universal Shape Evaluation

Proves `trWireMsg_shape_eq_imp_addr_eq` (two `trWireMsg` terms with equal `.shape` under `gamma'`
have equal `g.addr`, scalar fields, and child shapes) and `gamma_eq_of_shape_eq` (any two `DY.Bytes`
terms with equal `.shape` under `gamma'` evaluate to the same `gamma` byte sequence via `evalShape`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open

open DY DY.Comparse DY.Literal DY.Libsignal
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.RecvRep

theorem concat_injective {a₁ b₁ a₂ b₂ : DY.Bytes}
    (h : Concat.concat a₁ b₁ = Concat.concat a₂ b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have h1 := congrArg (fun x => x.view? DY.Concat.Concat.SubF) h
  change Bytes.view? (({ lhs := a₁, rhs := b₁ } : DY.Concat.Concat.SubF DY.Bytes).pack)
      DY.Concat.Concat.SubF =
    Bytes.view? (({ lhs := a₂, rhs := b₂ } : DY.Concat.Concat.SubF DY.Bytes).pack)
      DY.Concat.Concat.SubF at h1
  rw [BytesView.view_pack, BytesView.view_pack, Option.some.injEq] at h1
  cases h1
  exact ⟨rfl, rfl⟩

theorem trWireMsg_injective
    {v₁ : UInt8} {rk₁ : DY.Bytes} {c₁ pc₁ : UInt32} {ct₁ pq₁ : DY.Bytes} {ev₁ : DY.TrWire.EncodingVariation}
    {v₂ : UInt8} {rk₂ : DY.Bytes} {c₂ pc₂ : UInt32} {ct₂ pq₂ : DY.Bytes} {ev₂ : DY.TrWire.EncodingVariation}
    (h : DY.TrWire.trWireMsg v₁ rk₁ c₁ pc₁ ct₁ pq₁ ev₁ =
         DY.TrWire.trWireMsg v₂ rk₂ c₂ pc₂ ct₂ pq₂ ev₂) :
    v₁ = v₂ ∧ rk₁ = rk₂ ∧ c₁ = c₂ ∧ pc₁ = pc₂ ∧ ct₁ = ct₂ ∧ pq₁ = pq₂ ∧ ev₁ = ev₂ := by
  have h1 := congrArg (fun b => b.view? DY.TrWire.TrWireMsg.SubF) h
  change Bytes.view?
      (({ version := v₁, senderRatchetKey := rk₁, counter := c₁, previousCounter := pc₁,
          ciphertext := ct₁, pqRatchet := pq₁, encodingVariation := ev₁ } :
        DY.TrWire.TrWireMsg.SubF DY.Bytes).pack) DY.TrWire.TrWireMsg.SubF =
    Bytes.view?
      (({ version := v₂, senderRatchetKey := rk₂, counter := c₂, previousCounter := pc₂,
          ciphertext := ct₂, pqRatchet := pq₂, encodingVariation := ev₂ } :
        DY.TrWire.TrWireMsg.SubF DY.Bytes).pack) DY.TrWire.TrWireMsg.SubF at h1
  rw [BytesView.view_pack, BytesView.view_pack, Option.some.injEq] at h1
  cases h1
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- If two `trWireMsg` terms have equal `.shape` under `gamma'`, then their `g.addr` values are
equal, their scalar/variation fields are equal, and all three `DY.Bytes` child `.shape`s are equal. -/
theorem trWireMsg_shape_eq_imp_addr_eq
    (interpretation₁ interpretation₂ : ExternInterpretation)
    (S₁ S₂ : OpaqueSymbolSemantics) (g₁ g₂ : Ghost)
    (v₁ : UInt8) (rk₁ : DY.Bytes) (c₁ pc₁ : UInt32) (ct₁ pq₁ : DY.Bytes) (ev₁ : DY.TrWire.EncodingVariation)
    (v₂ : UInt8) (rk₂ : DY.Bytes) (c₂ pc₂ : UInt32) (ct₂ pq₂ : DY.Bytes) (ev₂ : DY.TrWire.EncodingVariation)
    (hsh :
      (gamma' interpretation₁ S₁ g₁ (DY.TrWire.trWireMsg v₁ rk₁ c₁ pc₁ ct₁ pq₁ ev₁)).shape =
      (gamma' interpretation₂ S₂ g₂ (DY.TrWire.trWireMsg v₂ rk₂ c₂ pc₂ ct₂ pq₂ ev₂)).shape) :
    g₁.addr (DY.TrWire.trWireMsg v₁ rk₁ c₁ pc₁ ct₁ pq₁ ev₁) =
      g₂.addr (DY.TrWire.trWireMsg v₂ rk₂ c₂ pc₂ ct₂ pq₂ ev₂) ∧
    v₁ = v₂ ∧
    (gamma' interpretation₁ S₁ g₁ rk₁).shape = (gamma' interpretation₂ S₂ g₂ rk₂).shape ∧
    c₁ = c₂ ∧
    pc₁ = pc₂ ∧
    (gamma' interpretation₁ S₁ g₁ ct₁).shape = (gamma' interpretation₂ S₂ g₂ ct₂).shape ∧
    (gamma' interpretation₁ S₁ g₁ pq₁).shape = (gamma' interpretation₂ S₂ g₂ pq₂).shape ∧
    ev₁ = ev₂ := by
  change (gamma' interpretation₁ S₁ g₁
      ((⟨v₁, rk₁, c₁, pc₁, ct₁, pq₁, ev₁⟩ : DY.TrWire.TrWireMsg.SubF DY.Bytes).pack)).shape =
    (gamma' interpretation₂ S₂ g₂
      ((⟨v₂, rk₂, c₂, pc₂, ct₂, pq₂, ev₂⟩ : DY.TrWire.TrWireMsg.SubF DY.Bytes).pack)).shape at hsh
  unfold gamma' at hsh
  rw [DY.Bytes.rec_eq (concretizeTrWire g₁) (concretizeAll interpretation₁ S₁ g₁),
      DY.Bytes.rec_eq (concretizeTrWire g₂) (concretizeAll interpretation₂ S₂ g₂)] at hsh
  obtain ⟨hv, hrk, hc, hpc, hct, hpq, hev_addr⟩ := trWireMsg_injective hsh
  have hfields :
      DY.TrWire.FieldItem.extra 6 (.bytes (g₁.addr (DY.TrWire.trWireMsg v₁ rk₁ c₁ pc₁ ct₁ pq₁ ev₁))) 0 0 :: ev₁.fields =
      DY.TrWire.FieldItem.extra 6 (.bytes (g₂.addr (DY.TrWire.trWireMsg v₂ rk₂ c₂ pc₂ ct₂ pq₂ ev₂))) 0 0 :: ev₂.fields :=
    congrArg DY.TrWire.EncodingVariation.fields hev_addr
  injection hfields with hhead htail
  injection hhead with _ hpb _ _
  injection hpb with haddr
  have hev : ev₁ = ev₂ := by
    cases ev₁; cases ev₂
    dsimp only at hev_addr htail
    injection hev_addr with h1 h2 h3 h4 _
    subst h1 h2 h3 h4 htail
    rfl
  exact ⟨haddr, hv, hrk, hc, hpc, hct, hpq, hev⟩

theorem trWire_shape_eq_imp_addr_eq
    (interpretation₁ interpretation₂ : ExternInterpretation)
    (S₁ S₂ : OpaqueSymbolSemantics) (g₁ g₂ : Ghost)
    (v₁ : UInt8) (rk₁ : DY.Bytes) (c₁ pc₁ : UInt32) (ct₁ pq₁ : DY.Bytes) (ev₁ : DY.TrWire.EncodingVariation)
    (v₂ : UInt8) (rk₂ : DY.Bytes) (c₂ pc₂ : UInt32) (ct₂ pq₂ : DY.Bytes) (ev₂ : DY.TrWire.EncodingVariation)
    (hsh :
      (gamma' interpretation₁ S₁ g₁ (DY.TrWire.trWireMsg v₁ rk₁ c₁ pc₁ ct₁ pq₁ ev₁)).shape =
      (gamma' interpretation₂ S₂ g₂ (DY.TrWire.trWireMsg v₂ rk₂ c₂ pc₂ ct₂ pq₂ ev₂)).shape) :
    g₁.addr (DY.TrWire.trWireMsg v₁ rk₁ c₁ pc₁ ct₁ pq₁ ev₁) =
      g₂.addr (DY.TrWire.trWireMsg v₂ rk₂ c₂ pc₂ ct₂ pq₂ ev₂) ∧
    v₁ = v₂ ∧
    (gamma' interpretation₁ S₁ g₁ rk₁).shape = (gamma' interpretation₂ S₂ g₂ rk₂).shape ∧
    c₁ = c₂ ∧
    pc₁ = pc₂ ∧
    (gamma' interpretation₁ S₁ g₁ ct₁).shape = (gamma' interpretation₂ S₂ g₂ ct₂).shape ∧
    (gamma' interpretation₁ S₁ g₁ pq₁).shape = (gamma' interpretation₂ S₂ g₂ pq₂).shape ∧
    ev₁ = ev₂ :=
  trWireMsg_shape_eq_imp_addr_eq interpretation₁ interpretation₂ S₁ S₂ g₁ g₂
    v₁ rk₁ c₁ pc₁ ct₁ pq₁ ev₁ v₂ rk₂ c₂ pc₂ ct₂ pq₂ ev₂ hsh

/-! ## Universal Shape-to-Value Determination -/

unseal DY.Bytes in
private instance subRandomSA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subLit0SA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subConcat0SA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeConcat (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhPkSA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDhPk i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhSA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDh i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKdf0SA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSym0SA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSym i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, symFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subTrunc0SA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeTrunc (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVariant0SA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrInitSA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrInit S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrSendStateSA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendState S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrSendKeySA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrSendMsgSA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrSendMsg S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrRecvStateSA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrRecvState S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrRecvKeySA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrRecvKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrChainKeySA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrChainKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subTrWire0SA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, trWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemPkSA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemPk S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemEncapSA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemEncap i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemSSSA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemSS i S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemRejSA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemRej S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVkSA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVk S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSignSA (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSign S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

structure EvalG where
  val : HwBytes
  lhsVal : HwBytes := []
  rhsVal : HwBytes := []

def liftPF {SubF : Type → Type} [SubBytesFunctor SubF] (pf : DY.Bytes.PartialFunction SubF ConcretizedTerm) :
    DY.Bytes.PartialFunction SubF EvalG :=
  fun x rec =>
    { val := (pf x (fun y hy => { bytes := (rec y hy).val, shape := y, memo := [] })).bytes }

def evalConcat0 : DY.Bytes.PartialFunction DY.Concat.Concat.SubF EvalG :=
  fun x rec =>
    let l := rec x.lhs (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
    let r := rec x.rhs (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
    { val := l.val ++ r.val, lhsVal := l.val, rhsVal := r.val }

def evalTrWire0 : DY.Bytes.PartialFunction DY.TrWire.TrWireMsg.SubF EvalG :=
  fun x rec =>
    let rk := rec x.senderRatchetKey (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]; omega)
    let ct := rec x.ciphertext (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]; omega)
    let pq := rec x.pqRatchet (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
    match x.encodingVariation.fields with
    | .extra 6 (.bytes addr) 0 0 :: rest =>
      { val := trWireBytes addr { x.encodingVariation with fields := rest }
          { version := x.version.toNat, ratchetKey := rk.val, counter := x.counter.toNat,
            previousCounter := x.previousCounter.toNat, ciphertext := ct.val } pq.val }
    | _ => { val := [] }

def evalLitFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.Literal.SubF.internal id) EvalG
  | 0 => liftPF concretizeLit
def evalConcatFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.Concat.SubF.internal id) EvalG
  | 0 => evalConcat0
def evalDhFuns (i : ExternInterpretation) : (id : Fin 2) → DY.Bytes.PartialFunction (DY.DiffieHellman.SubF.internal id) EvalG
  | 0 => liftPF (concretizeDhPk i)
  | 1 => liftPF (concretizeDh i)
def evalKdfFuns (i : ExternInterpretation) : (id : Fin 1) → DY.Bytes.PartialFunction (DY.KdfExtract.SubF.internal id) EvalG
  | 0 => liftPF (concretizeKdf i)
def evalSymFuns (i : ExternInterpretation) : (id : Fin 1) → DY.Bytes.PartialFunction (DY.SymEnc.SubF.internal id) EvalG
  | 0 => liftPF (concretizeSym i)
def evalTruncFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.Trunc.SubF.internal id) EvalG
  | 0 => liftPF concretizeTrunc
def evalX25519Funs (i : ExternInterpretation) : (id : Fin 1) → DY.Bytes.PartialFunction (DY.X25519.SubF.internal id) EvalG
  | 0 => liftPF (concretizeVariant i)
def evalKemFuns (i : ExternInterpretation) (S : OpaqueSymbolSemantics) : (id : Fin 4) → DY.Bytes.PartialFunction (DY.PQKem.SubF.internal id) EvalG
  | 0 => liftPF (concretizeKemPk S)
  | 1 => liftPF (concretizeKemEncap i)
  | 2 => liftPF (concretizeKemSS i S)
  | 3 => liftPF (concretizeKemRej S)
def evalSigFuns (S : OpaqueSymbolSemantics) : (id : Fin 2) → DY.Bytes.PartialFunction (DY.Signature.SubF.internal id) EvalG
  | 0 => liftPF (concretizeVk S)
  | 1 => liftPF (concretizeSign S)
def evalSpqrFuns (S : OpaqueSymbolSemantics) : (id : Fin 7) → DY.Bytes.PartialFunction (DY.Spqr.SubF.internal id) EvalG
  | 0 => liftPF (concretizeSpqrInit S)
  | 1 => liftPF (concretizeSpqrSendState S)
  | 2 => liftPF (concretizeSpqrSendKey S)
  | 3 => liftPF (concretizeSpqrSendMsg S)
  | 4 => liftPF (concretizeSpqrRecvState S)
  | 5 => liftPF (concretizeSpqrRecvKey S)
  | 6 => liftPF (concretizeSpqrChainKey S)
def evalTrWireFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.TrWire.SubF.internal id) EvalG
  | 0 => evalTrWire0

def evalAllFuns (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : (id : Fin 12) →
    DY.Bytes.PartialFunction (DY.Libsignal.Composed.SubF.internal id) EvalG
  | 0 => liftPF (concretizeRandom g)
  | 1 => DY.Bytes.PartialFunction.combine evalLitFuns
  | 2 => DY.Bytes.PartialFunction.combine evalConcatFuns
  | 3 => DY.Bytes.PartialFunction.combine (evalDhFuns i)
  | 4 => DY.Bytes.PartialFunction.combine (evalKdfFuns i)
  | 5 => DY.Bytes.PartialFunction.combine (evalSymFuns i)
  | 6 => DY.Bytes.PartialFunction.combine evalTruncFuns
  | 7 => DY.Bytes.PartialFunction.combine (evalX25519Funs i)
  | 8 => DY.Bytes.PartialFunction.combine (evalKemFuns i S)
  | 9 => DY.Bytes.PartialFunction.combine (evalSigFuns S)
  | 10 => DY.Bytes.PartialFunction.combine (evalSpqrFuns S)
  | 11 => DY.Bytes.PartialFunction.combine evalTrWireFuns

def evalAll (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.Function EvalG :=
  DY.Bytes.PartialFunction.combine (evalAllFuns i S g)

def evalShape (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (b : DY.Bytes) : EvalG :=
  b.rec (evalAll i S g)

unseal DY.Bytes in
private instance subEvalRandom (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (liftPF (concretizeRandom g)) (evalAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [evalAll, evalAllFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subEvalLit0 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (liftPF concretizeLit) (evalAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [evalAll, evalAllFuns, evalLitFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subEvalConcat0 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction evalConcat0 (evalAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [evalAll, evalAllFuns, evalConcatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subEvalDhPk (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (liftPF (concretizeDhPk i)) (evalAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [evalAll, evalAllFuns, evalDhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subEvalDh (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (liftPF (concretizeDh i)) (evalAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [evalAll, evalAllFuns, evalDhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subEvalKdf0 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (liftPF (concretizeKdf i)) (evalAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [evalAll, evalAllFuns, evalKdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subEvalSym0 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (liftPF (concretizeSym i)) (evalAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [evalAll, evalAllFuns, evalSymFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subEvalTrunc0 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (liftPF concretizeTrunc) (evalAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [evalAll, evalAllFuns, evalTruncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subEvalVariant0 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (liftPF (concretizeVariant i)) (evalAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [evalAll, evalAllFuns, evalX25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subEvalTrWire0 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction evalTrWire0 (evalAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [evalAll, evalAllFuns, evalTrWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subEvalKemEncap (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (liftPF (concretizeKemEncap i)) (evalAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [evalAll, evalAllFuns, evalKemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subEvalKemSS (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (liftPF (concretizeKemSS i S)) (evalAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [evalAll, evalAllFuns, evalKemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subEvalKemRej (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (liftPF (concretizeKemRej S)) (evalAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [evalAll, evalAllFuns, evalKemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem evalShape_litOf (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (bs : HwBytes) :
    (evalShape i S g (litOf bs)).val = bs := by
  have h1 := RecvRep.gamma_litOf i S g bs
  change ((({ lit := _ } : DY.Literal.Literal.SubF DY.Bytes).pack).rec (evalAll i S g)).val = bs
  change ((({ lit := _ } : DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = bs at h1
  rw [DY.Bytes.rec_eq (liftPF concretizeLit) (evalAll i S g)]
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll i S g)] at h1
  exact h1

theorem evalShape_concat (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (l r : DY.Bytes) :
    evalShape i S g (Concat.concat l r) =
      { val := (evalShape i S g l).val ++ (evalShape i S g r).val,
        lhsVal := (evalShape i S g l).val,
        rhsVal := (evalShape i S g r).val } := by
  show (({ lhs := l, rhs := r } : DY.Concat.Concat.SubF DY.Bytes).pack).rec (evalAll i S g) = _
  rw [DY.Bytes.rec_eq evalConcat0 (evalAll i S g)]
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
private theorem partialFunDep_spqr_eval
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hleaf : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm),
      (gF x rec).shape = litOf (gF x rec).bytes) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        (evalShape i S g (gamma' i S g u).shape).val = (gamma' i S g u).bytes) := by
  intro x _
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x]
  change (evalShape i S g ((BytesView.pack x).rec (concretizeAll i S g)).shape).val =
    ((BytesView.pack x).rec (concretizeAll i S g)).bytes
  rw [DY.Bytes.rec_eq gF (concretizeAll i S g) x, hleaf x _, evalShape_litOf]

unseal DY.Bytes in
private theorem partialFunDep_eval_step
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hstep : ∀ (x : SubF DY.Bytes)
      (_ih : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x →
        (evalShape i S g (gamma' i S g y).shape).val = (gamma' i S g y).bytes),
      (evalShape i S g (gF x (fun y _ => gamma' i S g y)).shape).val =
        (gF x (fun y _ => gamma' i S g y)).bytes) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        (evalShape i S g (gamma' i S g u).shape).val = (gamma' i S g u).bytes) := by
  intro x ih
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x]
  change (evalShape i S g ((BytesView.pack x).rec (concretizeAll i S g)).shape).val =
    ((BytesView.pack x).rec (concretizeAll i S g)).bytes
  rw [DY.Bytes.rec_eq gF (concretizeAll i S g) x]
  exact hstep x ih

unseal DY.Bytes in
/-- For every `u : DY.Bytes`, `evalShape i S g` on `(gamma' i S g u).shape` recovers
`gamma i S g u = (gamma' i S g u).val`. -/
theorem evalShape_shape
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (u : DY.Bytes) :
    (evalShape i S g (gamma' i S g u).shape).val = gamma i S g u := by
  change (evalShape i S g (gamma' i S g u).shape).val = (gamma' i S g u).bytes
  refine DY.ALaCarte.Container.rec (f := DY.BytesF)
    (motive := fun u : DY.Bytes =>
      (evalShape i S g (gamma' i S g u).shape).val = (gamma' i S g u).bytes) ?_ u
  rintro ⟨⟨id, hid⟩, val⟩ rec
  match id with
  | 0 =>
    refine lift_partialFunDep (partialFunDep_eval_step i S g (concretizeRandom g) fun x _ => ?_) val rec
    dsimp only [concretizeRandom]
    split
    · exact evalShape_litOf i S g []
    · next h0 =>
      dsimp only [node]; unfold evalShape
      rw [DY.Bytes.rec_eq (liftPF (concretizeRandom g)) (evalAll i S g) x]
      simp only [liftPF, concretizeRandom, h0, ↓reduceIte, node]
  | 1 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 =>
      refine lift_partialFunDep (partialFunDep_eval_step i S g concretizeLit fun x _ => ?_) v rec
      dsimp only [concretizeLit, node]; unfold evalShape; rw [DY.Bytes.rec_eq (liftPF concretizeLit) (evalAll i S g) x]; rfl
    | n + 1 => omega
  | 2 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 =>
      refine lift_partialFunDep (partialFunDep_eval_step i S g concretizeConcat fun x ih => ?_) v rec
      have ihl := ih x.lhs (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      have ihr := ih x.rhs (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      dsimp only [concretizeConcat, node]
      change (evalShape i S g (Concat.concat (gamma' i S g x.lhs).shape (gamma' i S g x.rhs).shape)).val = _
      rw [evalShape_concat, ihl, ihr]
    | n + 1 => omega
  | 3 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 =>
      refine lift_partialFunDep (partialFunDep_eval_step i S g (concretizeDhPk i) fun x ih => ?_) v rec
      have ih1 := ih x.sk (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      dsimp only [concretizeDhPk, node]; unfold evalShape
      rw [DY.Bytes.rec_eq (liftPF (concretizeDhPk i)) (evalAll i S g)]; dsimp only [liftPF, concretizeDhPk, node]
      unfold evalShape at ih1; rw [ih1]
    | 1 =>
      refine lift_partialFunDep (partialFunDep_eval_step i S g (concretizeDh i) fun x ih => ?_) v rec
      have ih1 := ih x.pk (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      have ih2 := ih x.sk (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      dsimp only [concretizeDh, node]; unfold evalShape
      rw [DY.Bytes.rec_eq (liftPF (concretizeDh i)) (evalAll i S g)]; dsimp only [liftPF, concretizeDh, node]
      unfold evalShape at ih1 ih2; rw [ih1, ih2]
    | n + 2 => omega
  | 4 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 =>
      refine lift_partialFunDep (partialFunDep_eval_step i S g (concretizeKdf i) fun x ih => ?_) v rec
      have ih1 := ih x.salt (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      have ih2 := ih x.ikm (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      dsimp only [concretizeKdf, node]; unfold evalShape
      rw [DY.Bytes.rec_eq (liftPF (concretizeKdf i)) (evalAll i S g)]; dsimp only [liftPF, concretizeKdf, node]
      unfold evalShape at ih1 ih2; rw [ih1, ih2]
    | n + 1 => omega
  | 5 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 =>
      refine lift_partialFunDep (partialFunDep_eval_step i S g (concretizeSym i) fun x ih => ?_) v rec
      have ih1 := ih x.key (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]; omega)
      have ih2 := ih x.iv (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]; omega)
      have ih3 := ih x.msg (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      dsimp only [concretizeSym, node]; unfold evalShape
      rw [DY.Bytes.rec_eq (liftPF (concretizeSym i)) (evalAll i S g)]; dsimp only [liftPF, concretizeSym, node]
      unfold evalShape at ih1 ih2 ih3; rw [ih1, ih2, ih3]
    | n + 1 => omega
  | 6 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 =>
      refine lift_partialFunDep (partialFunDep_eval_step i S g concretizeTrunc fun x ih => ?_) v rec
      have ih1 := ih x.input (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      dsimp only [concretizeTrunc, node]; unfold evalShape
      rw [DY.Bytes.rec_eq (liftPF concretizeTrunc) (evalAll i S g)]; dsimp only [liftPF, concretizeTrunc, node]
      unfold evalShape at ih1; rw [ih1]
    | n + 1 => omega
  | 7 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 =>
      refine lift_partialFunDep (partialFunDep_eval_step i S g (concretizeVariant i) fun x ih => ?_) v rec
      have ih1 := ih x.key (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      dsimp only [concretizeVariant, node]; unfold evalShape
      rw [DY.Bytes.rec_eq (liftPF (concretizeVariant i)) (evalAll i S g)]; dsimp only [liftPF, concretizeVariant, node]
      unfold evalShape at ih1; rw [ih1]
    | n + 1 => omega
  | 8 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact lift_partialFunDep (partialFunDep_spqr_eval i S g (concretizeKemPk S) (fun _ _ => rfl)) v rec
    | 1 =>
      refine lift_partialFunDep (partialFunDep_eval_step i S g (concretizeKemEncap i) fun x ih => ?_) v rec
      have ih1 := ih x.pk (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      have ih2 := ih x.entropy (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      dsimp only [concretizeKemEncap]
      by_cases h32 : (gamma' i S g x.entropy).bytes.length = 32
      · simp only [h32, ↓reduceIte, node]
        unfold evalShape at ih1 ih2 ⊢
        rw [DY.Bytes.rec_eq (liftPF (concretizeKemEncap i)) (evalAll i S g)]
        dsimp only [liftPF, concretizeKemEncap]
        simp only [ih1, ih2, h32, ↓reduceIte, node]
      · simp only [h32, ↓reduceIte, opaqueNode]
        exact evalShape_litOf i S g []
    | 2 =>
      refine lift_partialFunDep (partialFunDep_eval_step i S g (concretizeKemSS i S) fun x ih => ?_) v rec
      have ih1 := ih x.pk (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      have ih2 := ih x.entropy (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      dsimp only [concretizeKemSS]
      by_cases h32 : (gamma' i S g x.entropy).bytes.length = 32
      · simp only [h32, ↓reduceIte, node]
        unfold evalShape at ih1 ih2 ⊢
        rw [DY.Bytes.rec_eq (liftPF (concretizeKemSS i S)) (evalAll i S g)]
        dsimp only [liftPF, concretizeKemSS]
        simp only [ih1, ih2, h32, ↓reduceIte, node]
      · simp only [h32, ↓reduceIte, opaqueNode]
        exact evalShape_litOf i S g _
    | 3 =>
      refine lift_partialFunDep (partialFunDep_eval_step i S g (concretizeKemRej S) fun x ih => ?_) v rec
      have ih1 := ih x.sk (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      have ih2 := ih x.cipher (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      dsimp only [concretizeKemRej, node]; unfold evalShape
      rw [DY.Bytes.rec_eq (liftPF (concretizeKemRej S)) (evalAll i S g)]; dsimp only [liftPF, concretizeKemRej, node]
      unfold evalShape at ih1 ih2; rw [ih1, ih2]
    | n + 4 => omega
  | 9 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact lift_partialFunDep (partialFunDep_spqr_eval i S g (concretizeVk S) (fun _ _ => rfl)) v rec
    | 1 => exact lift_partialFunDep (partialFunDep_spqr_eval i S g (concretizeSign S) (fun _ _ => rfl)) v rec
    | n + 2 => omega
  | 10 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 => exact lift_partialFunDep (partialFunDep_spqr_eval i S g (concretizeSpqrInit S) (fun _ _ => rfl)) v rec
    | 1 => exact lift_partialFunDep (partialFunDep_spqr_eval i S g (concretizeSpqrSendState S) (fun _ _ => rfl)) v rec
    | 2 => exact lift_partialFunDep (partialFunDep_spqr_eval i S g (concretizeSpqrSendKey S) (fun _ _ => rfl)) v rec
    | 3 => exact lift_partialFunDep (partialFunDep_spqr_eval i S g (concretizeSpqrSendMsg S) (fun _ _ => rfl)) v rec
    | 4 => exact lift_partialFunDep (partialFunDep_spqr_eval i S g (concretizeSpqrRecvState S) (fun _ _ => rfl)) v rec
    | 5 => exact lift_partialFunDep (partialFunDep_spqr_eval i S g (concretizeSpqrRecvKey S) (fun _ _ => rfl)) v rec
    | 6 => exact lift_partialFunDep (partialFunDep_spqr_eval i S g (concretizeSpqrChainKey S) (fun _ _ => rfl)) v rec
    | n + 7 => omega
  | 11 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩
    match sid with
    | 0 =>
      refine lift_partialFunDep (partialFunDep_eval_step i S g (concretizeTrWire g) fun x ih => ?_) v rec
      rcases x with ⟨ver, rk, ctr, pctr, ct, pq, ⟨vln, rktb, ch, pch, flds⟩⟩
      have ih1 := ih rk (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]; omega)
      have ih2 := ih ct (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]; omega)
      have ih3 := ih pq (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
      dsimp only [concretizeTrWire, node]
      unfold evalShape at ih1 ih2 ih3 ⊢
      rw [DY.Bytes.rec_eq evalTrWire0 (evalAll i S g)]
      simp only [evalTrWire0]
      rw [ih1, ih2, ih3]
    | n + 1 => omega
  | n + 12 => omega

/-- Any two `DY.Bytes` terms with equal `.shape` under `gamma'` have equal `gamma` bytes. -/
theorem gamma_eq_of_shape_eq
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (u₁ u₂ : DY.Bytes)
    (hsh : (gamma' i S g u₁).shape = (gamma' i S g u₂).shape) :
    gamma i S g u₁ = gamma i S g u₂ := by
  rw [← evalShape_shape i S g u₁, ← evalShape_shape i S g u₂, hsh]

end Symbolic.Swarm.CREF.TR.G1
