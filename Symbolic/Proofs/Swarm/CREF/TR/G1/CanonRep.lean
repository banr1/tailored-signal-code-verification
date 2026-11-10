/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Stage1Kyber -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR
public import Symbolic.Proofs.Swarm.CREF.TR.G1.G1Rep
public import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeIdInv
import all DY.Bytes.Basic
import all DY.ALaCarte.Basic
import all Comparse.Basic
import all Comparse.Formats.Basic
import all Comparse.Formats.Derived
import all DY.Comparse
import all DY.Actions.PersistentLocalState
import all DY.EquationalTheory.Literal
import all DY.EquationalTheory.DiffieHellman
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepPtAtomsTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkInvCons
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac
public import Symbolic.Proofs.Refinement.LemmasPure -- shake: keep

/-!
# Canonical Ratchet-Key Representations (`ShapeRigid` and `CaseA'`)

Defines `NoLitSubterm`, `ShapeRigid`, `CaseA'`, `CaseB'`, `InstallWitnessTR`, and `JunkTR` over the
composed term algebra. Proves unique shape preimages for `ShapeRigid` terms
(`eq_of_shape_eq_shapeRigid`), memo membership of stored ratchet keys (`rk_mem_prefixTerms_memo_tr`),
and ratchet-key agreement under `¬RecvCollision` (`rk_eq_of_noncolliding_caseA'`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Literal DY.X25519
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (RecvChain hmac hkdfBlock1 hkdfBlock2 lit createChain x25519LowOrder
  kdfRk messageVersion findRecvChain recvChainFor)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open Symbolic.Swarm.CREF.TR

/-! ## `NoLitSubterm`, `ShapeRigid`, `CaseA'`, and `CaseB'` -/

def noLitRandom : DY.Bytes.PartialFunction DY.Random.SubF Bool := fun x _ => x.size != 0
def noLitLit0 : DY.Bytes.PartialFunction DY.Literal.Literal.SubF Bool := fun _ _ => false
def noLitConcat0 : DY.Bytes.PartialFunction DY.Concat.Concat.SubF Bool := fun x rec =>
  rec x.lhs (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]) &&
  rec x.rhs (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
def noLitDhPk : DY.Bytes.PartialFunction DY.DiffieHellman.DhPk.SubF Bool :=
  fun x rec => rec x.sk (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
def noLitDh : DY.Bytes.PartialFunction DY.DiffieHellman.Dh.SubF Bool := fun x rec =>
  rec x.pk (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]) &&
  rec x.sk (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
def noLitKdf0 : DY.Bytes.PartialFunction DY.KdfExtract.KdfExtract.SubF Bool := fun x rec =>
  rec x.salt (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]) &&
  rec x.ikm (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
def noLitSym0 : DY.Bytes.PartialFunction DY.SymEnc.Enc.SubF Bool := fun x rec =>
  rec x.key (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]; omega) &&
  rec x.iv (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]; omega) &&
  rec x.msg (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
def noLitTrunc0 : DY.Bytes.PartialFunction DY.Trunc.Trunc8.SubF Bool :=
  fun x rec => rec x.input (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
def noLitVariant0 : DY.Bytes.PartialFunction DY.X25519.Variant.SubF Bool :=
  fun x rec => rec x.key (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf])
def noLitFalse {SubF : Type → Type} [SubBytesFunctor SubF] : DY.Bytes.PartialFunction SubF Bool :=
  fun _ _ => false
def noLitLitFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.Literal.SubF.internal id) Bool | 0 => noLitLit0
def noLitConcatFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.Concat.SubF.internal id) Bool | 0 => noLitConcat0
def noLitDhFuns : (id : Fin 2) → DY.Bytes.PartialFunction (DY.DiffieHellman.SubF.internal id) Bool | 0 => noLitDhPk | 1 => noLitDh
def noLitKdfFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.KdfExtract.SubF.internal id) Bool | 0 => noLitKdf0
def noLitSymFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.SymEnc.SubF.internal id) Bool | 0 => noLitSym0
def noLitTruncFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.Trunc.SubF.internal id) Bool | 0 => noLitTrunc0
def noLitX25519Funs : (id : Fin 1) → DY.Bytes.PartialFunction (DY.X25519.SubF.internal id) Bool | 0 => noLitVariant0
def noLitSpqrFuns : (id : Fin 7) → DY.Bytes.PartialFunction (DY.Spqr.SubF.internal id) Bool
  | 0 => noLitFalse | 1 => noLitFalse | 2 => noLitFalse | 3 => noLitFalse
  | 4 => noLitFalse | 5 => noLitFalse | 6 => noLitFalse
def noLitTrWireFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.TrWire.SubF.internal id) Bool | 0 => noLitFalse
def noLitKemFuns : (id : Fin 4) → DY.Bytes.PartialFunction (DY.PQKem.SubF.internal id) Bool
  | 0 => noLitFalse | 1 => noLitFalse | 2 => noLitFalse | 3 => noLitFalse
def noLitSigFuns : (id : Fin 2) → DY.Bytes.PartialFunction (DY.Signature.SubF.internal id) Bool
  | 0 => noLitFalse | 1 => noLitFalse
def noLitAllFuns : (id : Fin 12) →
    DY.Bytes.PartialFunction (DY.Libsignal.Composed.SubF.internal id) Bool
  | 0 => noLitRandom
  | 1 => DY.Bytes.PartialFunction.combine noLitLitFuns
  | 2 => DY.Bytes.PartialFunction.combine noLitConcatFuns
  | 3 => DY.Bytes.PartialFunction.combine noLitDhFuns
  | 4 => DY.Bytes.PartialFunction.combine noLitKdfFuns
  | 5 => DY.Bytes.PartialFunction.combine noLitSymFuns
  | 6 => DY.Bytes.PartialFunction.combine noLitTruncFuns
  | 7 => DY.Bytes.PartialFunction.combine noLitX25519Funs
  | 8 => DY.Bytes.PartialFunction.combine noLitKemFuns
  | 9 => DY.Bytes.PartialFunction.combine noLitSigFuns
  | 10 => DY.Bytes.PartialFunction.combine noLitSpqrFuns
  | 11 => DY.Bytes.PartialFunction.combine noLitTrWireFuns
def noLitAll : DY.Bytes.Function Bool := DY.Bytes.PartialFunction.combine noLitAllFuns
def noLitBool (u : DY.Bytes) : Bool := u.rec noLitAll

section SubFunsCR
unseal DY.Bytes
private instance subNoLitRandom : DY.Bytes.SubFunction noLitRandom noLitAll := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subNoLitLit0 : DY.Bytes.SubFunction noLitLit0 noLitAll := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subNoLitConcat0 : DY.Bytes.SubFunction noLitConcat0 noLitAll := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subNoLitDhPk : DY.Bytes.SubFunction noLitDhPk noLitAll := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subNoLitDh : DY.Bytes.SubFunction noLitDh noLitAll := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subNoLitKdf0 : DY.Bytes.SubFunction noLitKdf0 noLitAll := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subNoLitSym0 : DY.Bytes.SubFunction noLitSym0 noLitAll := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subNoLitTrunc0 : DY.Bytes.SubFunction noLitTrunc0 noLitAll := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subNoLitVariant0 : DY.Bytes.SubFunction noLitVariant0 noLitAll := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subNoLitTrWire0 : DY.Bytes.SubFunction (noLitFalse (SubF := DY.TrWire.TrWireMsg.SubF)) noLitAll := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subNoLitKemEncap : DY.Bytes.SubFunction (noLitFalse (SubF := DY.PQKem.Encap.SubF)) noLitAll := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subNoLitKemSS : DY.Bytes.SubFunction (noLitFalse (SubF := DY.PQKem.SharedSecret.SubF)) noLitAll := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subNoLitKemRej : DY.Bytes.SubFunction (noLitFalse (SubF := DY.PQKem.RejKey.SubF)) noLitAll := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subRandomCR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subLit0CR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction concretizeLit (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subConcat0CR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction concretizeConcat (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subDhPkCR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeDhPk i) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subDhCR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeDh i) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subKdf0CR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subSym0CR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSym i) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subTrunc0CR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction concretizeTrunc (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subVariant0CR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subSpqrInitCR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrInit S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subSpqrSendStateCR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrSendState S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subSpqrSendKeyCR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrSendKey S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subSpqrSendMsgCR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrSendMsg S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subSpqrRecvStateCR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrRecvState S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subSpqrRecvKeyCR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrRecvKey S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subSpqrChainKeyCR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrChainKey S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subTrWire0CR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
private instance subKemRejCR (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeKemRej S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩
end SubFunsCR

/-- No subterm of `u` is `Literal`, `randTerm _ 0`, `PQKem`, `Signature`, `SPQR`, or `TrWireMsg`. -/
def NoLitSubterm (u : DY.Bytes) : Prop :=
  noLitBool u = true

/-- A term `u` is `ShapeRigid` if `TermShapeId u` and `NoLitSubterm u` hold. -/
def ShapeRigid (u : DY.Bytes) : Prop :=
  TermShapeId u ∧ NoLitSubterm u

/-- The stripped key `normalizeX25519Key pk` is `ShapeRigid` and `dhPk`-headed. -/
def CaseA' (pk : DY.Bytes) : Prop :=
  ShapeRigid (DY.X25519.normalizeX25519Key pk) ∧
  ∃ a : DY.Bytes, DY.X25519.normalizeX25519Key pk = DY.DiffieHellman.dhPk a

/-- Complement of `CaseA'`. -/
def CaseB' (pk : DY.Bytes) : Prop :=
  ¬ CaseA' pk

theorem dhPk_eq_pack_tr (a : DY.Bytes) :
    ∃ s, DY.DiffieHellman.dhPk a = ({ sk := s } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack :=
  ⟨a, rfl⟩

theorem assumedInjective_dhPk_tr (a : DY.Bytes) :
    assumedInjective (DY.DiffieHellman.dhPk a) = true := by
  obtain ⟨s, heq⟩ := dhPk_eq_pack_tr a
  rw [heq]
  simp only [assumedInjective, BytesView.view_pack, Option.isSome_some, Bool.true_or, Bool.or_true]

theorem noLitBool_literalToBytes (b : ByteArray) :
    noLitBool (Literal.literalToBytes b) = false := by
  unfold noLitBool
  show ((({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).rec noLitAll) = false
  rw [DY.Bytes.rec_eq noLitLit0 noLitAll]
  rfl

theorem noLitBool_litOf (bs : HwBytes) : noLitBool (litOf bs) = false :=
  noLitBool_literalToBytes _

theorem noLitBool_randTerm32 (t : Nat) : noLitBool (randTerm t 32) = true := by
  unfold noLitBool randTerm
  rw [DY.Bytes.rec_eq noLitRandom noLitAll]
  rfl

theorem noLitBool_dhPk (sk : DY.Bytes) : noLitBool (dhPk sk) = noLitBool sk := by
  unfold noLitBool
  show ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec noLitAll) = _
  rw [DY.Bytes.rec_eq noLitDhPk noLitAll]
  rfl

theorem noLitBool_trWireMsg_pack (x : DY.TrWire.TrWireMsg.SubF DY.Bytes) :
    noLitBool x.pack = false := by
  unfold noLitBool
  rw [DY.Bytes.rec_eq (noLitFalse (SubF := DY.TrWire.TrWireMsg.SubF)) noLitAll]
  rfl

theorem noLitBool_kemEncap_pack (x : DY.PQKem.Encap.SubF DY.Bytes) :
    noLitBool x.pack = false := by
  unfold noLitBool
  rw [DY.Bytes.rec_eq (noLitFalse (SubF := DY.PQKem.Encap.SubF)) noLitAll]
  rfl

theorem noLitBool_kemSS_pack (x : DY.PQKem.SharedSecret.SubF DY.Bytes) :
    noLitBool x.pack = false := by
  unfold noLitBool
  rw [DY.Bytes.rec_eq (noLitFalse (SubF := DY.PQKem.SharedSecret.SubF)) noLitAll]
  rfl

theorem noLitBool_kemRej_pack (x : DY.PQKem.RejKey.SubF DY.Bytes) :
    noLitBool x.pack = false := by
  unfold noLitBool
  rw [DY.Bytes.rec_eq (noLitFalse (SubF := DY.PQKem.RejKey.SubF)) noLitAll]
  rfl

theorem shapeRigid_randTerm32 (t : Nat) : ShapeRigid (randTerm t 32) :=
  ⟨termShapeId_randTerm32 t, noLitBool_randTerm32 t⟩

theorem shapeRigid_dhPk {sk : DY.Bytes} (h : ShapeRigid sk) : ShapeRigid (dhPk sk) :=
  ⟨termShapeId_dhPk h.1, (noLitBool_dhPk sk).trans h.2⟩

theorem shapeRigid_dhPk_randTerm32 (t : Nat) : ShapeRigid (dhPk (randTerm t 32)) :=
  shapeRigid_dhPk (shapeRigid_randTerm32 t)

/-! ## Unique shape preimage for `ShapeRigid` terms -/

unseal DY.Bytes in
private theorem partialFunDep_spqr_noLit
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hleaf : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm),
      (gF x rec).shape = litOf (gF x rec).bytes) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        NoLitSubterm (gamma' i S g u).shape → (gamma' i S g u).shape = u) := by
  intro x _ hnl
  change NoLitSubterm ((BytesView.pack x).rec (concretizeAll i S g)).shape at hnl
  rw [DY.Bytes.rec_eq gF (concretizeAll i S g) x, hleaf x _] at hnl
  unfold NoLitSubterm at hnl
  rw [noLitBool_litOf] at hnl
  cases hnl

unseal DY.Bytes in
private theorem partialFunDep_noLit_step
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hstep : ∀ (x : SubF DY.Bytes)
      (_ih : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x →
        NoLitSubterm (gamma' i S g y).shape → (gamma' i S g y).shape = y),
      NoLitSubterm (gF x (fun y _ => gamma' i S g y)).shape →
      (gF x (fun y _ => gamma' i S g y)).shape = BytesView.pack x) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        NoLitSubterm (gamma' i S g u).shape → (gamma' i S g u).shape = u) := by
  intro x ih hnl
  change NoLitSubterm ((BytesView.pack x).rec (concretizeAll i S g)).shape at hnl
  change ((BytesView.pack x).rec (concretizeAll i S g)).shape = BytesView.pack x
  rw [DY.Bytes.rec_eq gF (concretizeAll i S g) x] at hnl ⊢
  exact hstep x ih hnl

unseal DY.Bytes in
theorem shape_eq_self_of_noLitSubterm_shape
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (u : DY.Bytes) :
    NoLitSubterm (gamma' i S g u).shape → (gamma' i S g u).shape = u := by
  refine DY.ALaCarte.Container.rec (f := DY.BytesF)
    (motive := fun u : DY.Bytes =>
      NoLitSubterm (gamma' i S g u).shape → (gamma' i S g u).shape = u) ?_ u
  rintro ⟨⟨id, hid⟩, val⟩ rec
  match id with
  | 0 =>
    refine partialFunDep_noLit_step i S g (concretizeRandom g) (fun x _ hnl => ?_) val rec
    dsimp only [concretizeRandom] at hnl ⊢
    split at hnl
    · unfold NoLitSubterm at hnl; rw [noLitBool_litOf] at hnl; cases hnl
    · next h0 => simp only [h0, ↓reduceIte, node]
  | 1 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      refine partialFunDep_noLit_step i S g concretizeLit (fun x _ hnl => ?_) v rec
      dsimp only [concretizeLit, node] at hnl; unfold NoLitSubterm at hnl
      change noLitBool (Literal.literalToBytes x.lit) = true at hnl
      rw [noLitBool_literalToBytes] at hnl; cases hnl
    | n + 1 => omega
  | 2 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      refine partialFunDep_noLit_step i S g concretizeConcat (fun x ih hnl => ?_) v rec
      dsimp only [concretizeConcat, node] at hnl ⊢; unfold NoLitSubterm noLitBool at hnl
      rw [DY.Bytes.rec_eq noLitConcat0 noLitAll] at hnl; dsimp only [noLitConcat0] at hnl
      rw [Bool.and_eq_true] at hnl
      rw [ih x.lhs (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]) hnl.1,
          ih x.rhs (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]) hnl.2]
    | n + 1 => omega
  | 3 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      refine partialFunDep_noLit_step i S g (concretizeDhPk i) (fun x ih hnl => ?_) v rec
      dsimp only [concretizeDhPk, node] at hnl ⊢; unfold NoLitSubterm noLitBool at hnl
      rw [DY.Bytes.rec_eq noLitDhPk noLitAll] at hnl; dsimp only [noLitDhPk] at hnl
      rw [ih x.sk (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]) hnl]
    | 1 =>
      refine partialFunDep_noLit_step i S g (concretizeDh i) (fun x ih hnl => ?_) v rec
      dsimp only [concretizeDh, node] at hnl ⊢; unfold NoLitSubterm noLitBool at hnl
      rw [DY.Bytes.rec_eq noLitDh noLitAll] at hnl; dsimp only [noLitDh] at hnl
      rw [Bool.and_eq_true] at hnl
      rw [ih x.pk (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]) hnl.1,
          ih x.sk (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]) hnl.2]
    | n + 2 => omega
  | 4 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      refine partialFunDep_noLit_step i S g (concretizeKdf i) (fun x ih hnl => ?_) v rec
      dsimp only [concretizeKdf, node] at hnl ⊢; unfold NoLitSubterm noLitBool at hnl
      rw [DY.Bytes.rec_eq noLitKdf0 noLitAll] at hnl; dsimp only [noLitKdf0] at hnl
      rw [Bool.and_eq_true] at hnl
      rw [ih x.salt (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]) hnl.1,
          ih x.ikm (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]) hnl.2]
    | n + 1 => omega
  | 5 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      refine partialFunDep_noLit_step i S g (concretizeSym i) (fun x ih hnl => ?_) v rec
      dsimp only [concretizeSym, node] at hnl ⊢; unfold NoLitSubterm noLitBool at hnl
      rw [DY.Bytes.rec_eq noLitSym0 noLitAll] at hnl; dsimp only [noLitSym0] at hnl
      simp only [Bool.and_eq_true] at hnl
      rw [ih x.key (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]; omega) hnl.1.1,
          ih x.iv (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]; omega) hnl.1.2,
          ih x.msg (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]) hnl.2]
    | n + 1 => omega
  | 6 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      refine partialFunDep_noLit_step i S g concretizeTrunc (fun x ih hnl => ?_) v rec
      dsimp only [concretizeTrunc, node] at hnl ⊢; unfold NoLitSubterm noLitBool at hnl
      rw [DY.Bytes.rec_eq noLitTrunc0 noLitAll] at hnl; dsimp only [noLitTrunc0] at hnl
      rw [ih x.input (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]) hnl]
    | n + 1 => omega
  | 7 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      refine partialFunDep_noLit_step i S g (concretizeVariant i) (fun x ih hnl => ?_) v rec
      dsimp only [concretizeVariant, node] at hnl ⊢; unfold NoLitSubterm noLitBool at hnl
      rw [DY.Bytes.rec_eq noLitVariant0 noLitAll] at hnl; dsimp only [noLitVariant0] at hnl
      rw [ih x.key (by simp [DY.ALaCarte.FunctorSizeOf.sizeOf]) hnl]
    | n + 1 => omega
  | 8 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_spqr_noLit i S g (concretizeKemPk S) (fun _ _ => rfl) v rec
    | 1 =>
      refine partialFunDep_noLit_step i S g (concretizeKemEncap i) (fun x _ hnl => ?_) v rec
      dsimp only [concretizeKemEncap] at hnl; split at hnl
      · dsimp only [node] at hnl; unfold NoLitSubterm at hnl
        rw [noLitBool_kemEncap_pack] at hnl; cases hnl
      · dsimp only [opaqueNode] at hnl; unfold NoLitSubterm at hnl
        rw [noLitBool_litOf] at hnl; cases hnl
    | 2 =>
      refine partialFunDep_noLit_step i S g (concretizeKemSS i S) (fun x _ hnl => ?_) v rec
      dsimp only [concretizeKemSS] at hnl; split at hnl
      · dsimp only [node] at hnl; unfold NoLitSubterm at hnl
        rw [noLitBool_kemSS_pack] at hnl; cases hnl
      · dsimp only [opaqueNode] at hnl; unfold NoLitSubterm at hnl
        rw [noLitBool_litOf] at hnl; cases hnl
    | 3 =>
      refine partialFunDep_noLit_step i S g (concretizeKemRej S) (fun x _ hnl => ?_) v rec
      dsimp only [concretizeKemRej, node] at hnl; unfold NoLitSubterm at hnl
      rw [noLitBool_kemRej_pack] at hnl; cases hnl
    | n + 4 => omega
  | 9 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_spqr_noLit i S g (concretizeVk S) (fun _ _ => rfl) v rec
    | 1 => exact partialFunDep_spqr_noLit i S g (concretizeSign S) (fun _ _ => rfl) v rec
    | n + 2 => omega
  | 10 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_spqr_noLit i S g (concretizeSpqrInit S) (fun _ _ => rfl) v rec
    | 1 => exact partialFunDep_spqr_noLit i S g (concretizeSpqrSendState S) (fun _ _ => rfl) v rec
    | 2 => exact partialFunDep_spqr_noLit i S g (concretizeSpqrSendKey S) (fun _ _ => rfl) v rec
    | 3 => exact partialFunDep_spqr_noLit i S g (concretizeSpqrSendMsg S) (fun _ _ => rfl) v rec
    | 4 => exact partialFunDep_spqr_noLit i S g (concretizeSpqrRecvState S) (fun _ _ => rfl) v rec
    | 5 => exact partialFunDep_spqr_noLit i S g (concretizeSpqrRecvKey S) (fun _ _ => rfl) v rec
    | 6 => exact partialFunDep_spqr_noLit i S g (concretizeSpqrChainKey S) (fun _ _ => rfl) v rec
    | n + 7 => omega
  | 11 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      refine partialFunDep_noLit_step i S g (concretizeTrWire g) (fun x _ hnl => ?_) v rec
      dsimp only [concretizeTrWire, node] at hnl; unfold NoLitSubterm at hnl
      rw [noLitBool_trWireMsg_pack] at hnl; cases hnl
    | n + 1 => omega
  | n + 12 => omega

/-- If `ShapeRigid pk` holds and `(gamma' interpretation S g u).shape = pk`, then `u = pk`. -/
theorem eq_of_shape_eq_shapeRigid
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {u pk : DY.Bytes}
    (hrigid : ShapeRigid pk)
    (hshape : (gamma' interpretation S g u).shape = pk) :
    u = pk := by
  have hnl : NoLitSubterm (gamma' interpretation S g u).shape := hshape ▸ hrigid.2
  exact (shape_eq_self_of_noLitSubterm_shape interpretation S g u hnl).symm.trans hshape

/-! ## Self-memo under `TermShapeId` and serialization subtree lemmas -/

private theorem sid_self_memo_step
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hg : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm),
      ((BytesView.pack x : DY.Bytes), (gF x rec).shape, (gF x rec).bytes) ∈ (gF x rec).memo)
    (x : SubF DY.Bytes)
    (hSId : TermShapeId (BytesView.pack x)) :
    (BytesView.pack x, BytesView.pack x, gamma i S g (BytesView.pack x)) ∈
      (gamma' i S g (BytesView.pack x)).memo := by
  have h1 : (BytesView.pack x, (gamma' i S g (BytesView.pack x)).shape,
      gamma i S g (BytesView.pack x)) ∈ (gamma' i S g (BytesView.pack x)).memo := by
    change (BytesView.pack x, ((BytesView.pack x).rec (concretizeAll i S g)).shape,
      ((BytesView.pack x).rec (concretizeAll i S g)).bytes) ∈ ((BytesView.pack x).rec (concretizeAll i S g)).memo
    rw [DY.Bytes.rec_eq gF (concretizeAll i S g) x]
    exact hg x _
  rwa [hSId i S g] at h1

unseal DY.Bytes in
private theorem partialFunDep_sid_self_memo
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hg : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm),
      ((BytesView.pack x : DY.Bytes), (gF x rec).shape, (gF x rec).bytes) ∈ (gF x rec).memo) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        TermShapeId u → (u, u, gamma i S g u) ∈ (gamma' i S g u).memo) := by
  intro x _ hSId
  exact sid_self_memo_step i S g gF hg x hSId

unseal DY.Bytes in
private theorem spqr_sid_absurd_step
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hleaf : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm),
      (gF x rec).shape = litOf (gF x rec).bytes)
    (hnone : ∀ bs : HwBytes, DY.Bytes.view? (litOf bs) SubF = none)
    (x : SubF DY.Bytes)
    (hSId : TermShapeId (BytesView.pack x)) :
    (BytesView.pack x, BytesView.pack x, gamma i S g (BytesView.pack x)) ∈
      (gamma' i S g (BytesView.pack x)).memo := by
  exfalso
  have hsh : ((BytesView.pack x).rec (concretizeAll i S g)).shape = BytesView.pack x := hSId i S g
  rw [DY.Bytes.rec_eq gF (concretizeAll i S g) x, hleaf x _] at hsh
  have hv := congrArg (fun b : DY.Bytes => b.view? SubF) hsh
  rw [hnone, DY.BytesView.view_pack (SubF := SubF)] at hv
  cases hv

unseal DY.Bytes in
private theorem partialFunDep_spqr_sid_absurd
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hleaf : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm),
      (gF x rec).shape = litOf (gF x rec).bytes)
    (hnone : ∀ bs : HwBytes, DY.Bytes.view? (litOf bs) SubF = none) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF)
      (fun u : DY.Bytes =>
        TermShapeId u → (u, u, gamma i S g u) ∈ (gamma' i S g u).memo) := by
  intro x _ hSId
  exact spqr_sid_absurd_step i S g gF hleaf hnone x hSId

unseal DY.Bytes in
private theorem random_sid_self_memo_step
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (val : DY.Random.Random DY.Bytes)
    (hSId : TermShapeId (BytesView.pack val)) :
    (BytesView.pack val, BytesView.pack val, gamma i S g (BytesView.pack val)) ∈
      (gamma' i S g (BytesView.pack val)).memo := by
  have hsh : ((BytesView.pack val).rec (concretizeAll i S g)).shape = BytesView.pack val := hSId i S g
  change (BytesView.pack val, BytesView.pack val,
    ((BytesView.pack val).rec (concretizeAll i S g)).bytes) ∈ ((BytesView.pack val).rec (concretizeAll i S g)).memo
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g) val] at hsh ⊢
  dsimp only [concretizeRandom] at hsh ⊢
  split at hsh
  · have hv := congrArg (fun b : DY.Bytes => b.view? DY.Random.Random) hsh
    have hnone : DY.Bytes.view? (litOf []) DY.Random.Random = none := rfl
    rw [hnone, DY.BytesView.view_pack (SubF := DY.Random.Random)] at hv
    cases hv
  · next hsz =>
    simp only [hsz, ↓reduceIte, node, List.mem_cons, true_or]

unseal DY.Bytes in
private theorem partialFunDep_random_sid_self_memo
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.ALaCarte.Container.PartialFunDep DY.Random.Random (g := DY.BytesF)
      (fun u : DY.Bytes =>
        TermShapeId u → (u, u, gamma i S g u) ∈ (gamma' i S g u).memo) := by
  intro val _ hSId
  exact random_sid_self_memo_step i S g val hSId

unseal DY.Bytes in
theorem self_mem_memo_of_termShapeId
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) {u : DY.Bytes}
    (hSId : TermShapeId u) :
    (u, u, gamma i S g u) ∈ (gamma' i S g u).memo := by
  revert hSId
  refine DY.ALaCarte.Container.rec (f := DY.BytesF)
    (motive := fun u : DY.Bytes =>
      TermShapeId u → (u, u, gamma i S g u) ∈ (gamma' i S g u).memo) ?_ u
  rintro ⟨⟨id, hid⟩, val⟩ rec
  match id with
  | 0 => exact partialFunDep_random_sid_self_memo i S g val rec
  | 1 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_sid_self_memo i S g concretizeLit (fun _ _ => by simp [concretizeLit, node]) v rec
    | n + 1 => omega
  | 2 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_sid_self_memo i S g concretizeConcat (fun _ _ => by simp [concretizeConcat, node]) v rec
    | n + 1 => omega
  | 3 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_sid_self_memo i S g (concretizeDhPk i) (fun _ _ => by simp [concretizeDhPk, node]) v rec
    | 1 => exact partialFunDep_sid_self_memo i S g (concretizeDh i) (fun _ _ => by simp [concretizeDh, node]) v rec
    | n + 2 => omega
  | 4 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_sid_self_memo i S g (concretizeKdf i) (fun _ _ => by simp [concretizeKdf, node]) v rec
    | n + 1 => omega
  | 5 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_sid_self_memo i S g (concretizeSym i) (fun _ _ => by simp [concretizeSym, node]) v rec
    | n + 1 => omega
  | 6 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_sid_self_memo i S g concretizeTrunc (fun _ _ => by simp [concretizeTrunc, node]) v rec
    | n + 1 => omega
  | 7 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_sid_self_memo i S g (concretizeVariant i) (fun _ _ => by simp [concretizeVariant, node]) v rec
    | n + 1 => omega
  | 8 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_spqr_sid_absurd i S g (concretizeKemPk S) (fun _ _ => rfl) (fun _ => rfl) v rec
    | 1 => exact fun hSId => Symbolic.Swarm.CREF.Stage1Kyber.self_mem_memo_kemEncap_of_shape_eq_self i S g (hSId i S g)
    | 2 => exact fun hSId => Symbolic.Swarm.CREF.Stage1Kyber.self_mem_memo_kemSS_of_shape_eq_self i S g (hSId i S g)
    | 3 => exact partialFunDep_sid_self_memo i S g (concretizeKemRej S) (fun _ _ => by simp [concretizeKemRej, node]) v rec
    | n + 4 => omega
  | 9 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_spqr_sid_absurd i S g (concretizeVk S) (fun _ _ => rfl) (fun _ => rfl) v rec
    | 1 => exact partialFunDep_spqr_sid_absurd i S g (concretizeSign S) (fun _ _ => rfl) (fun _ => rfl) v rec
    | n + 2 => omega
  | 10 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_spqr_sid_absurd i S g (concretizeSpqrInit S) (fun _ _ => rfl) (fun _ => rfl) v rec
    | 1 => exact partialFunDep_spqr_sid_absurd i S g (concretizeSpqrSendState S) (fun _ _ => rfl) (fun _ => rfl) v rec
    | 2 => exact partialFunDep_spqr_sid_absurd i S g (concretizeSpqrSendKey S) (fun _ _ => rfl) (fun _ => rfl) v rec
    | 3 => exact partialFunDep_spqr_sid_absurd i S g (concretizeSpqrSendMsg S) (fun _ _ => rfl) (fun _ => rfl) v rec
    | 4 => exact partialFunDep_spqr_sid_absurd i S g (concretizeSpqrRecvState S) (fun _ _ => rfl) (fun _ => rfl) v rec
    | 5 => exact partialFunDep_spqr_sid_absurd i S g (concretizeSpqrRecvKey S) (fun _ _ => rfl) (fun _ => rfl) v rec
    | 6 => exact partialFunDep_spqr_sid_absurd i S g (concretizeSpqrChainKey S) (fun _ _ => rfl) (fun _ => rfl) v rec
    | n + 7 => omega
  | 11 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact partialFunDep_sid_self_memo i S g (concretizeTrWire g) (fun _ _ => by simp [concretizeTrWire, node]) v rec
    | n + 1 => omega
  | n + 12 => omega

theorem inMemo_concatPrefixes_suffix_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {e : DY.Bytes × DY.Bytes × HwBytes} :
    ∀ (ps : List DY.Bytes) {s : DY.Bytes}, e ∈ (gamma' i S g s).memo →
      e ∈ (gamma' i S g (Comparse.concatPrefixes ps s)).memo
  | [], _, h => h
  | p :: ps, _, h =>
    memo_rhs_subset_memo_concat i S g p (Comparse.concatPrefixes ps _)
      (inMemo_concatPrefixes_suffix_tr i S g ps h)

theorem inMemo_concatPrefixes_mem_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {e : DY.Bytes × DY.Bytes × HwBytes} :
    ∀ (ps : List DY.Bytes) {p s : DY.Bytes}, p ∈ ps → e ∈ (gamma' i S g p).memo →
      e ∈ (gamma' i S g (Comparse.concatPrefixes ps s)).memo
  | [], _, _, hp, _ => by cases hp
  | q :: ps, p, s, hp, h => by
    rcases List.mem_cons.mp hp with rfl | hp'
    · show e ∈ (gamma' i S g (Concat.concat p (Comparse.concatPrefixes ps s))).memo
      unfold gamma' at h ⊢
      rw [show Concat.concat p (Comparse.concatPrefixes ps s) =
          ({ lhs := p, rhs := Comparse.concatPrefixes ps s } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl,
          DY.Bytes.rec_eq concretizeConcat (concretizeAll i S g)]
      simp [concretizeConcat, node, h]
    · exact memo_rhs_subset_memo_concat i S g q (Comparse.concatPrefixes ps s)
        (inMemo_concatPrefixes_mem_tr i S g ps hp' h)

theorem inMemo_serialize_recvList_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {c : RecvChain} (hShapeId : TermShapeId c.ratchetKey) :
    ∀ (cs : List RecvChain), c ∈ cs →
      (c.ratchetKey, c.ratchetKey, gamma i S g c.ratchetKey) ∈
        (gamma' i S g
          ((Comparse.ExtensibleMessageFormat.list (ParseableSerializeableNE.mf (a := RecvChain))).serialize cs)).memo
  | [], hc => by cases hc
  | d :: cs, hc => by
    show (c.ratchetKey, c.ratchetKey, gamma i S g c.ratchetKey) ∈
      (gamma' i S g (Comparse.concatPrefixes
        ((ParseableSerializeableNE.mf (a := RecvChain)).serialize d)
        ((Comparse.ExtensibleMessageFormat.list (ParseableSerializeableNE.mf (a := RecvChain))).serialize cs))).memo
    rcases List.mem_cons.mp hc with rfl | hc'
    · have hser : (ParseableSerializeableNE.mf (a := RecvChain)).serialize c =
          Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length c.ratchetKey) ++
          ([c.ratchetKey] ++ (Comparse.NonExtensibleMessageFormat.slowBytes.serialize c.chainKey ++
          (Comparse.NonExtensibleMessageFormat.uint32.serialize c.index ++
           Comparse.NonExtensibleMessageFormat.slowNat.serialize c.rIdx))) := by
        rw [← List.append_assoc]; rfl
      rw [hser]
      exact inMemo_concatPrefixes_mem_tr i S g _
        (List.mem_append_right _ (List.mem_append_left _ (List.mem_singleton_self _)))
        (self_mem_memo_of_termShapeId i S g hShapeId)
    · exact inMemo_concatPrefixes_suffix_tr i S g _
        (inMemo_serialize_recvList_tr i S g hShapeId cs hc')

theorem rk_mem_memo_serialize_tr
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {st : TRState} {c : RecvChain} (hc : c ∈ st.recv)
    (hShapeId : TermShapeId c.ratchetKey) :
    (c.ratchetKey, c.ratchetKey, gamma interpretation S g c.ratchetKey) ∈
      (gamma' interpretation S g (Comparse.serialize st : DY.Bytes)).memo := by
  have hser : (Comparse.serialize st : DY.Bytes) =
      Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowString.serialize st.peer)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.myIk)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.peerIk)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.rk)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.dhs)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.cks)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.uint32.serialize st.ns)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.uint32.serialize st.pn)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.sid)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.bool.serialize st.initiator)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowNat.serialize st.rIdx)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.spqr)
      ((Comparse.ExtensibleMessageFormat.list (ParseableSerializeableNE.mf (a := RecvChain))).serialize
        st.recv)))))))))))) := rfl
  rw [hser]
  repeat apply inMemo_concatPrefixes_suffix_tr
  exact inMemo_serialize_recvList_tr interpretation S g hShapeId _ hc

theorem rk_mem_memo_serialize_local_tr
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {ls : PersistentLocalState.LocalState TRState} {c : RecvChain}
    (hc : c ∈ ls.state.recv) (hShapeId : TermShapeId c.ratchetKey) :
    (c.ratchetKey, c.ratchetKey, gamma interpretation S g c.ratchetKey) ∈
      (gamma' interpretation S g (Comparse.serialize ls : DY.Bytes)).memo := by
  have hser : (Comparse.serialize ls : DY.Bytes) = Comparse.concatPrefixes
      (Comparse.NonExtensibleMessageFormat.slowString.serialize ls.participant)
      (Comparse.serialize ls.state) := rfl
  rw [hser]
  exact inMemo_concatPrefixes_suffix_tr interpretation S g _
    (rk_mem_memo_serialize_tr interpretation S g hc hShapeId)

/-- Every stored receiver chain key `c.ratchetKey` with `TermShapeId c.ratchetKey` appears as a
self-memo entry in `prefixTerms`. -/
theorem rk_mem_prefixTerms_memo_tr
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {r₀ : ProtocolSetup} {tr : ExecTrace} {vis : List VisEntry}
    {st : TRState} {c : RecvChain}
    (hst : st ∈ availableStates r₀ tr) (hc : c ∈ st.recv)
    (hShapeId : TermShapeId c.ratchetKey) :
    (c.ratchetKey, c.ratchetKey, gamma interpretation S g c.ratchetKey) ∈
      (prefixTerms r₀ tr vis).flatMap (fun u => (gamma' interpretation S g u).memo) := by
  rw [List.mem_flatMap]
  have hst' : st ∈ (storedStates r₀ tr).map (·.state) := hst
  obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hst'
  refine ⟨Comparse.serialize ls, ?_, rk_mem_memo_serialize_local_tr interpretation S g hc hShapeId⟩
  unfold prefixTerms principalTerms
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hls)))

/-! ## `InstallWitnessTR` and `JunkTR` -/

/-- Every receiver chain `c ∈ st.recv` of an available state `st` has an available state `H` whose
`H.rk` was derived by a sending half-step on `c.ratchetKey` with secret key `H.dhs` and whose
`H.recv` contains a chain with `ratchetKey = c.ratchetKey`. -/
def InstallWitnessTR (r₀ : ProtocolSetup) (tr : ExecTrace) : Prop :=
  ∀ st ∈ availableStates r₀ tr, ∀ c ∈ st.recv,
    ∃ H ∈ availableStates r₀ tr, ∃ rk1,
      H.rk = (createChain rk1 c.ratchetKey H.dhs).1 ∧
      ∃ c₁ ∈ H.recv, c₁.ratchetKey = c.ratchetKey

/-- A ratchet key `pk` whose stripped X25519 key is not an honest `dhPk (randTerm i 32)`. -/
def JunkTR (pk : DY.Bytes) : Prop :=
  ∀ i : Nat, DY.X25519.normalizeX25519Key pk ≠ DY.DiffieHellman.dhPk (randTerm i 32)

theorem junkTR_of_caseB' {pk : DY.Bytes} (hB : CaseB' pk) : JunkTR pk := by
  intro i heq
  exact hB ⟨heq ▸ shapeRigid_dhPk_randTerm32 i, randTerm i 32, heq⟩

/-! ## Ratchet-key agreement under `CaseA'` -/

theorem chain_eq_of_hist_tr {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {r₀ : ProtocolSetup} {ms : List Move}
    (hHist : RecvHistInvTR interpretation S g r₀ ms) {H : TRState}
    (hH : H ∈ availableStates r₀ (runTraceMoves r₀ ms)) {c₁ c₂ : RecvChain}
    (h₁ : c₁ ∈ H.recv) (h₂ : c₂ ∈ H.recv)
    (hγ : gamma interpretation S g c₁.ratchetKey = gamma interpretation S g c₂.ratchetKey) :
    c₁ = c₂ :=
  List.inj_on_of_nodup_map (hHist H hH) h₁ h₂ hγ

theorem findRecvChain_none_of_hist_tr {interpretation : ExternInterpretation}
    {S : OpaqueSymbolSemantics} {g : Ghost} {r₀ : ProtocolSetup} {ms : List Move}
    (hHist : RecvHistInvTR interpretation S g r₀ ms) {H : TRState}
    (hH : H ∈ availableStates r₀ (runTraceMoves r₀ ms)) {c₁ : RecvChain} {pk rk : DY.Bytes}
    (h₁ : c₁ ∈ H.recv) (hc₁ : c₁.ratchetKey = pk) (hne : rk ≠ pk)
    (hγ : gamma interpretation S g rk = gamma interpretation S g pk) :
    findRecvChain H.recv rk = none := by
  cases hf : findRecvChain H.recv rk with
  | none => rfl
  | some c₂ =>
    exfalso
    obtain ⟨h₂, hc₂⟩ := mem_recv_of_findRecvChain_eq_some hf
    have heq : c₁ = c₂ := chain_eq_of_hist_tr hHist hH h₁ h₂ (by rw [hc₁, hc₂, hγ])
    exact hne (by rw [← hc₂, ← heq, hc₁])

private theorem memo_rk_subset_memo_trWireMsg (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (v : UInt8) (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes) (ev : DY.TrWire.EncodingVariation)
    {e : DY.Bytes × DY.Bytes × HwBytes}
    (he : e ∈ (gamma' i S g rk).memo) :
    e ∈ (gamma' i S g (DY.TrWire.trWireMsg v rk c pc ct pq ev)).memo := by
  unfold gamma' at he ⊢
  rw [show DY.TrWire.trWireMsg v rk c pc ct pq ev =
      ({ version := v, senderRatchetKey := rk, counter := c, previousCounter := pc,
         ciphertext := ct, pqRatchet := pq, encodingVariation := ev } :
        DY.TrWire.TrWireMsg.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (concretizeTrWire g) (concretizeAll i S g)]
  simp [concretizeTrWire, node, he]

theorem parse_rk_mem_memo_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {t : DY.Bytes} {msg : TRSignalMsg}
    (hparse : parseTrSignalMsg t = some msg)
    (hne : gamma i S g msg.ratchetKey ≠ [])
    (hns : notSpqrHeaded msg.ratchetKey) (hno : notOpaqueHeaded msg.ratchetKey) :
    (msg.ratchetKey, (gamma' i S g msg.ratchetKey).shape, gamma i S g msg.ratchetKey) ∈
      (gamma' i S g t).memo := by
  have ht := parseTrSignalMsg_eq_concat hparse
  obtain ⟨v₀, pc₀, ev₀, hwire, _⟩ := parseTrSignalMsg_eq_some_inv hparse
  rw [ht, hwire]
  exact inMemo_concatPrefixes_mem_tr i S g [DY.TrWire.trWireMsg v₀ msg.ratchetKey msg.counter pc₀ msg.ciphertext msg.pqRatchet ev₀]
    (List.mem_singleton_self _)
    (memo_rk_subset_memo_trWireMsg i S g _ _ _ _ _ _ _
      (self_mem_memo_of_notSpqrHeaded i S g msg.ratchetKey hne hns hno))

private theorem x25519Key_of_view_variant_none {pk : DY.Bytes}
    (h : pk.view? DY.X25519.Variant.SubF = none) :
    DY.X25519.normalizeX25519Key pk = pk := by
  unfold DY.X25519.normalizeX25519Key; rw [h]

private theorem gamma_dhPk_raw_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sk : DY.Bytes) :
    gamma i S g (DY.DiffieHellman.dhPk sk) =
      (i DY.Libsignal.Refinement.x25519PublicKeySymbol
        [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk)]).getD [] := by
  unfold gamma gamma'
  rw [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (concretizeDhPk i) (concretizeAll i S g)]
  rfl

private theorem gamma_dhPk_ne_nil_tr (i : ExternInterpretation)
    (hEq : ExternCryptoLawsHold i) (S : OpaqueSymbolSemantics) (g : Ghost) (a : DY.Bytes) :
    gamma i S g (DY.DiffieHellman.dhPk a) ≠ [] := by
  have hlen : (gamma i S g (DY.DiffieHellman.dhPk a)).length = 32 := by
    rw [gamma_dhPk_raw_tr]; exact hEq.x25519_public_key_length _
  intro hnil; rw [hnil] at hlen; cases hlen

private theorem gamma_dh_raw_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pk sk : DY.Bytes) :
    gamma i S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) =
      (i DY.Libsignal.Refinement.x25519AgreementSymbol
        [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk), gamma i S g pk]).getD [] := by
  unfold gamma gamma'; rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g)]; rfl

private theorem gamma_dh_eq_tr (i : ExternInterpretation) (hEq : ExternCryptoLawsHold i)
    (S : OpaqueSymbolSemantics) (g : Ghost) (pk sk : DY.Bytes) :
    gamma i S g (DY.DiffieHellman.dh pk sk) =
      (i DY.Libsignal.Refinement.x25519AgreementSymbol
        [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk), gamma i S g pk]).getD [] := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk
  simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 heq
    rw [heq] at hv; simp only at hv; subst hv
    split
    · rw [gamma_dh_raw_tr]
    · rw [gamma_dh_raw_tr]
      show (i DY.Libsignal.Refinement.x25519AgreementSymbol
          [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk2),
           gamma i S g (DY.DiffieHellman.dhPk sk)]).getD [] =
        (i DY.Libsignal.Refinement.x25519AgreementSymbol
          [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk),
           gamma i S g (DY.DiffieHellman.dhPk sk2)]).getD []
      rw [gamma_dhPk_raw_tr, gamma_dhPk_raw_tr,
        hEq.x25519_agreement_commutes
          (DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk2))
          (DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk))]
  · rw [gamma_dh_raw_tr]

private theorem dhPk_not_mem_ptAtoms_tr (r₀ : ProtocolSetup) (ms : List Move) (a : DY.Bytes) :
    DY.DiffieHellman.dhPk a ∉ plaintextTerms (runVis r₀ ms) ++ [] := by
  intro h
  exact not_mem_ptAtoms_of_view_random_isNone r₀ ms [] (by simp) _ rfl (by simpa using h)

private def NonDhPkPlain (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (u : DY.Bytes) : Prop :=
  u.view? DY.X25519.Variant.SubF = none ∧
  u.view? DY.Literal.Literal.SubF = none ∧
  u.view? DY.DiffieHellman.DhPk.SubF = none ∧
  ((gamma' i S g u).shape).view? DY.DiffieHellman.DhPk.SubF = none

unseal DY.Bytes in
private theorem nonDhPkPlain_randTerm (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (j n : Nat) : NonDhPkPlain i S g (randTerm j n) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  unfold gamma' randTerm; rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g)]
  dsimp only [concretizeRandom]; split <;> rfl

unseal DY.Bytes in
private theorem nonDhPkPlain_of_not_notSpqrHeaded (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {u : DY.Bytes} (h : ¬ notSpqrHeaded u) : NonDhPkPlain i S g u := by
  unfold notSpqrHeaded at h
  rcases hv1 : u.view? DY.Spqr.InitState.SubF with _ | x
  · rcases hv2 : u.view? DY.Spqr.SendState.SubF with _ | x
    · rcases hv3 : u.view? DY.Spqr.SendKey.SubF with _ | x
      · rcases hv4 : u.view? DY.Spqr.SendMsg.SubF with _ | x
        · rcases hv5 : u.view? DY.Spqr.RecvState.SubF with _ | x
          · rcases hv6 : u.view? DY.Spqr.RecvKey.SubF with _ | x
            · rcases hv7 : u.view? DY.Spqr.ChainKey.SubF with _ | x
              · exact False.elim (h ⟨by simp [hv1], by simp [hv2], by simp [hv3],
                  by simp [hv4], by simp [hv5], by simp [hv6], by simp [hv7]⟩)
              · have hp := DY.Bytes.pack_view? DY.Spqr.ChainKey.SubF u; rw [hv7] at hp; rw [← hp]; refine ⟨rfl, rfl, rfl, ?_⟩
                unfold gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrChainKey S) (concretizeAll i S g)]; rfl
            · have hp := DY.Bytes.pack_view? DY.Spqr.RecvKey.SubF u; rw [hv6] at hp; rw [← hp]; refine ⟨rfl, rfl, rfl, ?_⟩
              unfold gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrRecvKey S) (concretizeAll i S g)]; rfl
          · have hp := DY.Bytes.pack_view? DY.Spqr.RecvState.SubF u; rw [hv5] at hp; rw [← hp]; refine ⟨rfl, rfl, rfl, ?_⟩
            unfold gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrRecvState S) (concretizeAll i S g)]; rfl
        · have hp := DY.Bytes.pack_view? DY.Spqr.SendMsg.SubF u; rw [hv4] at hp; rw [← hp]; refine ⟨rfl, rfl, rfl, ?_⟩
          unfold gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrSendMsg S) (concretizeAll i S g)]; rfl
      · have hp := DY.Bytes.pack_view? DY.Spqr.SendKey.SubF u; rw [hv3] at hp; rw [← hp]; refine ⟨rfl, rfl, rfl, ?_⟩
        unfold gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrSendKey S) (concretizeAll i S g)]; rfl
    · have hp := DY.Bytes.pack_view? DY.Spqr.SendState.SubF u; rw [hv2] at hp; rw [← hp]; refine ⟨rfl, rfl, rfl, ?_⟩
      unfold gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrSendState S) (concretizeAll i S g)]; rfl
  · have hp := DY.Bytes.pack_view? DY.Spqr.InitState.SubF u; rw [hv1] at hp; rw [← hp]; refine ⟨rfl, rfl, rfl, ?_⟩
    unfold gamma'; rw [DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll i S g)]; rfl

unseal DY.Bytes in
private theorem nonDhPkPlain_of_not_notOpaqueHeaded (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {u : DY.Bytes} (h : ¬ notOpaqueHeaded u) : NonDhPkPlain i S g u := by
  unfold notOpaqueHeaded at h
  rcases hv1 : u.view? DY.PQKem.Pk.SubF with _ | x
  · rcases hv2 : u.view? DY.PQKem.Encap.SubF with _ | x
    · rcases hv3 : u.view? DY.PQKem.SharedSecret.SubF with _ | x
      · rcases hv4 : u.view? DY.Signature.Vk.SubF with _ | x
        · rcases hv5 : u.view? DY.Signature.Sign.SubF with _ | x
          · exact False.elim (h ⟨by simp [hv1], by simp [hv2], by simp [hv3],
              by simp [hv4], by simp [hv5]⟩)
          · have hp := DY.Bytes.pack_view? DY.Signature.Sign.SubF u; rw [hv5] at hp; rw [← hp]; refine ⟨rfl, rfl, rfl, ?_⟩
            unfold gamma'; rw [DY.Bytes.rec_eq (concretizeSign S) (concretizeAll i S g)]; rfl
        · have hp := DY.Bytes.pack_view? DY.Signature.Vk.SubF u; rw [hv4] at hp; rw [← hp]; refine ⟨rfl, rfl, rfl, ?_⟩
          unfold gamma'; rw [DY.Bytes.rec_eq (concretizeVk S) (concretizeAll i S g)]; rfl
      · have hp := DY.Bytes.pack_view? DY.PQKem.SharedSecret.SubF u; rw [hv3] at hp; rw [← hp]; refine ⟨rfl, rfl, rfl, ?_⟩
        unfold gamma'; rw [DY.Bytes.rec_eq (concretizeKemSS i S) (concretizeAll i S g)]; dsimp only [concretizeKemSS]; split <;> rfl
    · have hp := DY.Bytes.pack_view? DY.PQKem.Encap.SubF u; rw [hv2] at hp; rw [← hp]; refine ⟨rfl, rfl, rfl, ?_⟩
      unfold gamma'; rw [DY.Bytes.rec_eq (concretizeKemEncap i) (concretizeAll i S g)]; dsimp only [concretizeKemEncap]; split <;> rfl
  · have hp := DY.Bytes.pack_view? DY.PQKem.Pk.SubF u; rw [hv1] at hp; rw [← hp]; refine ⟨rfl, rfl, rfl, ?_⟩
    unfold gamma'; rw [DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll i S g)]; rfl

private theorem x25519LowOrder_of_nonDhPkPlain {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {u : DY.Bytes} (h : NonDhPkPlain i S g u) :
    x25519LowOrder u = false := by
  dsimp only [x25519LowOrder, DY.X25519.normalizeX25519Key, DY.Literal.bytesToLiteral,
    DY.Literal.CanMkLiteral.bytesToLiteral]
  rw [h.1, h.2.1]

private theorem dh_pack_of_view_dhPk_none {pk : DY.Bytes} (sk : DY.Bytes)
    (hnone : pk.view? DY.DiffieHellman.DhPk.SubF = none) :
    DY.DiffieHellman.dh pk sk = ({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
  dsimp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]; rw [hnone]

private theorem dh_dhPk_pack_exists (a sk : DY.Bytes) :
    ∃ s sk', DY.DiffieHellman.dh (DY.DiffieHellman.dhPk a) sk =
      ({ pk := DY.DiffieHellman.dhPk s, sk := sk' } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
  dsimp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh, DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk]
  rw [DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF)]
  dsimp only; split
  · exact ⟨a, sk, rfl⟩
  · exact ⟨sk, a, rfl⟩

private theorem dh_pack_exists (pk sk : DY.Bytes) :
    ∃ p s, DY.DiffieHellman.dh pk sk =
      ({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
  dsimp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  rcases pk.view? DY.DiffieHellman.DhPk.SubF with _ | p
  · exact ⟨pk, sk, rfl⟩
  · dsimp only; split <;> exact ⟨_, _, rfl⟩

private theorem shape_dh_pack_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pk sk : DY.Bytes) :
    (gamma' i S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)).shape =
      ({ pk := (gamma' i S g pk).shape, sk := (gamma' i S g sk).shape } :
        DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
  unfold gamma'; rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g)]; rfl

private theorem shape_dh_ne_of_nonDhPkPlain (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {u a sk : DY.Bytes} (hu : NonDhPkPlain i S g u) :
    (gamma' i S g (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key u) sk)).shape ≠
      (gamma' i S g (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk a) sk)).shape := by
  rw [x25519Key_of_view_variant_none hu.1, dh_pack_of_view_dhPk_none sk hu.2.2.1, shape_dh_pack_tr]
  obtain ⟨s, sk', hdh2⟩ := dh_dhPk_pack_exists a sk
  rw [hdh2, shape_dh_pack_tr, shape_dhPk_tr]
  intro heq
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.DiffieHellman.Dh.SubF) heq
  rw [DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF),
      DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF)] at hv
  injection hv with hmk; injection hmk with hpk _
  have hv2 := congrArg (fun b : DY.Bytes => b.view? DY.DiffieHellman.DhPk.SubF) hpk
  rw [hu.2.2.2, show DY.DiffieHellman.dhPk (gamma' i S g s).shape =
      ({ sk := (gamma' i S g s).shape } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
      DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF)] at hv2
  cases hv2

private theorem mem_memo_dh_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (pk sk : DY.Bytes) :
    let d := DY.DiffieHellman.dh pk sk
    (d, (gamma' i S g d).shape, gamma i S g d) ∈ (gamma' i S g d).memo := by
  intro d; dsimp only [d]; obtain ⟨p, s, heq⟩ := dh_pack_exists pk sk; rw [heq]
  change (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack,
    ((({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape,
    ((({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes) ∈
    ((({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack).rec (concretizeAll i S g)).memo
  rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g)]; exact List.Mem.head _

private theorem assumedInjective_dh_tr (pk sk : DY.Bytes) :
    assumedInjective (DY.DiffieHellman.dh pk sk) = true := by
  obtain ⟨p, s, heq⟩ := dh_pack_exists pk sk; rw [heq]
  unfold assumedInjective; rw [DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF)]; simp

private theorem dh_not_mem_ptAtoms_tr (r₀ : ProtocolSetup) (ms : List Move) (pk sk : DY.Bytes) :
    DY.DiffieHellman.dh pk sk ∉ plaintextTerms (runVis r₀ ms) ++ [] := by
  obtain ⟨p, s, heq⟩ := dh_pack_exists pk sk; rw [heq]
  intro h
  exact not_mem_ptAtoms_of_view_random_isNone r₀ ms [] (by simp) _ rfl (by simpa using h)

private theorem mem_memo_kdfExtract_left_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt ikm : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes}
    (hs : e ∈ (gamma' i S g salt).memo) :
    e ∈ (gamma' i S g (DY.KdfExtract.kdfExtract salt ikm)).memo := by
  unfold gamma' at hs ⊢
  rw [show DY.KdfExtract.kdfExtract salt ikm =
      ({ salt := salt, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (concretizeKdf i) (concretizeAll i S g)]
  simp only [concretizeKdf, node, List.mem_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
  exact Or.inr (Or.inl hs)

private theorem mem_memo_kdfExtract_right_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt ikm : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes}
    (hi : e ∈ (gamma' i S g ikm).memo) :
    e ∈ (gamma' i S g (DY.KdfExtract.kdfExtract salt ikm)).memo := by
  unfold gamma' at hi ⊢
  rw [show DY.KdfExtract.kdfExtract salt ikm =
      ({ salt := salt, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (concretizeKdf i) (concretizeAll i S g)]
  simp only [concretizeKdf, node, List.mem_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
  exact Or.inr (Or.inr hi)

private theorem createChain_snd_mem_whisperTrialTerms_tr
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (salts : List DY.Bytes)
    (H : TRState) (msg : TRSignalMsg)
    (hH : H ∈ availableStates r₀ tr) (hver : msg.version = messageVersion)
    (hfind : findRecvChain H.recv msg.ratchetKey = none)
    (hlow : x25519LowOrder msg.ratchetKey = false) :
    (createChain H.rk msg.ratchetKey H.dhs).2 ∈
      (whisperTrials interpretation r₀ S g tr msg).flatMap (trialTerms salts msg) := by
  have hrc : recvChainFor H.toDRState msg.ratchetKey =
      some ({ ratchetKey := msg.ratchetKey, chainKey := (createChain H.rk msg.ratchetKey H.dhs).2,
              index := 0, rIdx := H.rIdx + 2 }, true) := by
    unfold recvChainFor
    have hfind' : findRecvChain H.toDRState.recv msg.ratchetKey = none := hfind
    simp only [hfind', hlow, Bool.false_eq_true, ↓reduceIte]
  exact Symbolic.Swarm.CREF.Stage1Trials.chainKey_mem_whisperTrialTerms_of_recvChainFor hver hH hrc

/-- The new terms `RecvCollision` compares at a parsed received term `t` (`parseTrSignalMsg t = some msg`):
`t` and all expanded `whisperTrials` terms. -/
abbrev recvNewTerms (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (t : DY.Bytes) (msg : TRSignalMsg) : List DY.Bytes :=
  t :: (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg).flatMap
    (trialTerms (honestSalts r₀ ms) msg)

private theorem false_of_noncolliding_nonDhPkPlain
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (hHist : RecvHistInvTR interpretation S g r₀ ms)
    (hIW : InstallWitnessTR r₀ (runTraceMoves r₀ ms))
    {st : TRState} {c : RecvChain} {t : DY.Bytes} {msg : TRSignalMsg} {a : DY.Bytes}
    (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms)) (hc : c ∈ st.recv)
    (hca : c.ratchetKey = DY.DiffieHellman.dhPk a)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hu : NonDhPkPlain interpretation S g msg.ratchetKey)
    (hγ : gamma interpretation S g msg.ratchetKey = gamma interpretation S g c.ratchetKey)
    (hNotCol : ¬RecvCollision interpretation r₀ S g ms t) :
    False := by
  obtain ⟨H, hH, rk1, hHrk, c₁, h₁, hc₁⟩ := hIW st hst c hc
  have hne : msg.ratchetKey ≠ c.ratchetKey := by
    intro heq
    have hv := hu.2.2.1
    rw [heq, hca, show DY.DiffieHellman.dhPk a =
        ({ sk := a } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
        DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF)] at hv
    cases hv
  have hfind : findRecvChain H.recv msg.ratchetKey = none :=
    findRecvChain_none_of_hist_tr hHist hH h₁ hc₁ hne hγ
  have hlow : x25519LowOrder msg.ratchetKey = false :=
    x25519LowOrder_of_nonDhPkPlain hu
  let d1 := DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key msg.ratchetKey) H.dhs
  let d2 := DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key c.ratchetKey) H.dhs
  let x₁ : DY.Bytes × DY.Bytes × HwBytes :=
    (d1, (gamma' interpretation S g d1).shape, gamma interpretation S g d1)
  let x₂ : DY.Bytes × DY.Bytes × HwBytes :=
    (d2, (gamma' interpretation S g d2).shape, gamma interpretation S g d2)
  let ckr := (createChain H.rk msg.ratchetKey H.dhs).2
  have hckr_entry : ckr ∈ recvNewTerms interpretation r₀ S g ms t msg :=
    List.mem_cons_of_mem _ (createChain_snd_mem_whisperTrialTerms_tr interpretation r₀ S g
      (runTraceMoves r₀ ms) (honestSalts r₀ ms) H msg hH hver hfind hlow)
  have hx1_memo : x₁ ∈ (gamma' interpretation S g ckr).memo := by
    dsimp only [ckr, createChain, DY.X25519.agree, kdfRk, hkdfBlock2, hmac]
    exact mem_memo_kdfExtract_left_tr interpretation S g _ _
      (mem_memo_kdfExtract_right_tr interpretation S g _ _
        (mem_memo_dh_tr interpretation S g (DY.X25519.normalizeX25519Key msg.ratchetKey) H.dhs))
  have hx2_memo : x₂ ∈ (gamma' interpretation S g ckr).memo := by
    dsimp only [ckr, createChain, DY.X25519.agree, kdfRk, hkdfBlock2, hmac]
    refine mem_memo_kdfExtract_left_tr interpretation S g _ _
      (mem_memo_kdfExtract_left_tr interpretation S g _ _ ?_)
    rw [hHrk]
    dsimp only [createChain, DY.X25519.agree, kdfRk, hkdfBlock1, hmac]
    exact mem_memo_kdfExtract_left_tr interpretation S g _ _
      (mem_memo_kdfExtract_right_tr interpretation S g _ _
        (mem_memo_dh_tr interpretation S g (DY.X25519.normalizeX25519Key c.ratchetKey) H.dhs))
  have hx1_new : x₁ ∈ (recvNewTerms interpretation r₀ S g ms t msg).flatMap
      (fun u => (gamma' interpretation S g u).memo) :=
    List.mem_flatMap.mpr ⟨ckr, hckr_entry, hx1_memo⟩
  have hx2_terms : x₂ ∈
      ((prefixTerms r₀ (runTraceMoves r₀ ms) (runVis r₀ ms)).flatMap
        (fun u => (gamma' interpretation S g u).memo)) ++
      (recvNewTerms interpretation r₀ S g ms t msg).flatMap
        (fun u => (gamma' interpretation S g u).memo) :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨ckr, hckr_entry, hx2_memo⟩)
  have hsh_ne : x₁.2.1 ≠ x₂.2.1 := by
    dsimp only [x₁, x₂, d1, d2]
    rw [hca, show DY.X25519.normalizeX25519Key (DY.DiffieHellman.dhPk a) = DY.DiffieHellman.dhPk a from rfl]
    exact shape_dh_ne_of_nonDhPkPlain interpretation S g hu
  have hγeq : x₁.2.2 = x₂.2.2 := by
    dsimp only [x₁, x₂, d1, d2]
    rw [x25519Key_of_view_variant_none hu.1, hca,
        show DY.X25519.normalizeX25519Key (DY.DiffieHellman.dhPk a) = DY.DiffieHellman.dhPk a from rfl,
        gamma_dh_eq_tr interpretation hEq S g msg.ratchetKey H.dhs,
        gamma_dh_eq_tr interpretation hEq S g (DY.DiffieHellman.dhPk a) H.dhs,
        hγ, hca]
  apply hNotCol
  unfold RecvCollision; simp only [hparse]
  left
  refine ⟨x₁, hx1_new, x₂, hx2_terms, hsh_ne, Or.inl (assumedInjective_dh_tr _ _),
    fun hpt => False.elim (dh_not_mem_ptAtoms_tr r₀ ms _ _ hpt),
    fun hpt => False.elim (dh_not_mem_ptAtoms_tr r₀ ms _ _ hpt),
    hγeq⟩

/-- When `c ∈ st.recv` of an available state `st` has `CaseA' c.ratchetKey` and is non-`Variant`,
any non-colliding representation `t` with `parseTrSignalMsg t = some msg`,
`msg.version = messageVersion`, and `gamma msg.ratchetKey = gamma c.ratchetKey` satisfies
`msg.ratchetKey = c.ratchetKey`. -/
theorem rk_eq_of_noncolliding_caseA'
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (hHist : RecvHistInvTR interpretation S g r₀ ms)
    (hIW : InstallWitnessTR r₀ (runTraceMoves r₀ ms))
    {st : TRState} {c : RecvChain} {t : DY.Bytes} {msg : TRSignalMsg}
    (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms)) (hc : c ∈ st.recv)
    (hCaseA' : CaseA' c.ratchetKey)
    (hPlain : c.ratchetKey.view? DY.X25519.Variant.SubF = none)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hγ : gamma interpretation S g msg.ratchetKey = gamma interpretation S g c.ratchetKey)
    (hNotCol : ¬RecvCollision interpretation r₀ S g ms t) :
    msg.ratchetKey = c.ratchetKey := by
  have hxk : DY.X25519.normalizeX25519Key c.ratchetKey = c.ratchetKey :=
    x25519Key_of_view_variant_none hPlain
  have hrigid : ShapeRigid c.ratchetKey := hxk ▸ hCaseA'.1
  obtain ⟨a, hca⟩ : ∃ a, c.ratchetKey = DY.DiffieHellman.dhPk a := by
    obtain ⟨a, ha⟩ := hCaseA'.2
    exact ⟨a, hxk.symm.trans ha⟩
  refine eq_of_shape_eq_shapeRigid interpretation S g hrigid ?_
  by_contra hsh_ne
  by_cases hns : notSpqrHeaded msg.ratchetKey
  · by_cases hpt : msg.ratchetKey ∈ plaintextTerms (runVis r₀ ms) ++ []
    · obtain ⟨j, hjn⟩ := ptAtoms_runVis_mem_inv_tr32 r₀ ms [] (by simp)
        (p := msg.ratchetKey) (by simpa using hpt)
      exact false_of_noncolliding_nonDhPkPlain interpretation hEq r₀ S g ms hHist hIW
        hst hc hca hparse hver (hjn ▸ nonDhPkPlain_randTerm interpretation S g j 32) hγ hNotCol
    by_cases hno : notOpaqueHeaded msg.ratchetKey
    swap
    · exact false_of_noncolliding_nonDhPkPlain interpretation hEq r₀ S g ms hHist hIW
        hst hc hca hparse hver (nonDhPkPlain_of_not_notOpaqueHeaded interpretation S g hno) hγ hNotCol
    · apply hNotCol
      unfold RecvCollision; simp only [hparse]
      left
      have hne_nil : gamma interpretation S g msg.ratchetKey ≠ [] := by
        rw [hγ, hca]
        exact gamma_dhPk_ne_nil_tr interpretation hEq S g a
      have hx₁ : (msg.ratchetKey, (gamma' interpretation S g msg.ratchetKey).shape,
          gamma interpretation S g msg.ratchetKey) ∈
          (recvNewTerms interpretation r₀ S g ms t msg).flatMap
            (fun u => (gamma' interpretation S g u).memo) := by
        rw [List.mem_flatMap]
        exact ⟨t, List.mem_cons_self .., parse_rk_mem_memo_tr interpretation S g hparse hne_nil hns hno⟩
      have hx₂ : (c.ratchetKey, c.ratchetKey, gamma interpretation S g c.ratchetKey) ∈
          (prefixTerms r₀ (runTraceMoves r₀ ms) (runVis r₀ ms)).flatMap
            (fun u => (gamma' interpretation S g u).memo) :=
        rk_mem_prefixTerms_memo_tr interpretation S g hst hc hrigid.1
      have hinj : assumedInjective c.ratchetKey = true :=
        hca ▸ assumedInjective_dhPk_tr a
      have hc_not_pt : c.ratchetKey ∉ plaintextTerms (runVis r₀ ms) ++ [] :=
        hca ▸ dhPk_not_mem_ptAtoms_tr r₀ ms a
      exact ⟨_, hx₁, _, List.mem_append_left _ hx₂, hsh_ne, Or.inr hinj,
        fun h1 => False.elim (hpt h1),
        fun h2 => False.elim (hc_not_pt h2),
        hγ⟩
  · exact false_of_noncolliding_nonDhPkPlain interpretation hEq r₀ S g ms hHist hIW
      hst hc hca hparse hver (nonDhPkPlain_of_not_notSpqrHeaded interpretation S g hns) hγ hNotCol

end Symbolic.Swarm.CREF.TR.G1
