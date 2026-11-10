/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTRStrong
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTR
public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import DY.ALaCarte.Basic
import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
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
import Symbolic.Specifications.Model.MsgKeys
import Symbolic.Specifications.Model.TripleRatchet
import Symbolic.Specifications.Model.PQXDH
import Symbolic.Specifications.Model.Composed
import Init.Data.String.Defs
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkInvCons
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeIdInv
public import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.X25519 -- shake: keep
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.Literal
import Symbolic.DYBridge.DY.EquationalTheory.Concat
import Symbolic.DYBridge.DY.EquationalTheory.DiffieHellman
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.EquationalTheory.Sign

/-!
# Root-Key KDF Safety and Stored Root-Key Tree Invariant

Defines the root-key tree `RkTree` and the KDF safety predicate `KdfRkSafe` over
`DY.Libsignal.Composed`, and proves `JRk_reachable` and `kdfRkSafe_of_attackerKnows_reachable` on
all reachable traces.
-/

@[expose] public section

set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.Swarm.CREF.TR.G1
cref_open
open DY DY.Comparse DY.DiffieHellman DY.Libsignal.TripleRatchet Symbolic.Swarm.CREF.TR
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo KeyDir KeyComponent createChain
  consumeMessageKey computeMac findRecvChain setRecvChain recvChainFor chainKeyAt hmac hkdfBlock1
  hkdfBlock2 kdfCk lit litByte messageVersion)
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles PreKeyMsgHandles
  pqxdhKdf pqxdhIkm pqxdhLabel opkUsedB registerIdentity registerCorruptIdentity genSignedPrekey
  genPQPrekey genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK compromiseOPK invertDH
  invertKEM)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompPresPQXDH
open Symbolic.Swarm.COMPOSED.CompInv (SpqrInv spqrInv_of_reachable EvE)

attribute [local instance 2000] DY.Libsignal.Composed.instHasExecBytes DY.Libsignal.Composed.instHasExecTrace

unseal DY.Bytes in
instance subRandomSRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subLit0SRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction concretizeLit (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subConcat0SRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction concretizeConcat (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subDhPkSRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeDhPk i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subDhSRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeDh i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subKdf0SRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSym0SRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSym i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, symFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subTrunc0SRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction concretizeTrunc (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subVariant0SRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrInitSRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrInit S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrSendStateSRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrSendState S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrSendKeySRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrSendKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrSendMsgSRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrSendMsg S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrRecvStateSRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrRecvState S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrRecvKeySRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrRecvKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrChainKeySRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSpqrChainKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subTrWire0SRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, trWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subKemPkSRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeKemPk S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subKemEncapSRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeKemEncap i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subKemSSSRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeKemSS i S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemRejSRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeKemRej S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subVkSRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeVk S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSignSRK (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) : DY.Bytes.SubFunction (concretizeSign S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem recvSeed_eq_of_findRecvChain_some {st₀ : TRState} {msg₀ : TRSignalMsg} {c : RecvChain} {mkSeed : DY.Bytes}
    (hfind : findRecvChain st₀.recv msg₀.ratchetKey = some c) (hseed : recvSeed st₀ msg₀ = some mkSeed) :
    c ∈ st₀.recv ∧ c.ratchetKey = msg₀.ratchetKey ∧ mkSeed = (kdfCk (chainKeyAt c.chainKey (msg₀.counter.toNat - c.index.toNat))).2 := by
  obtain ⟨hmem, hrk_eq⟩ := mem_recv_of_findRecvChain_eq_some hfind; refine ⟨hmem, hrk_eq, ?_⟩; unfold recvSeed at hseed; split at hseed <;> [skip; cases hseed]
  rcases hrc : recvChainFor st₀.toDRState msg₀.ratchetKey with _ | ⟨c₀, b⟩ <;> rw [hrc] at hseed; · cases hseed
  simp only [Option.map_eq_some_iff] at hseed; obtain ⟨⟨s, c'⟩, hcmk, rfl⟩ := hseed
  unfold recvChainFor at hrc; have hfind' : findRecvChain st₀.toDRState.recv msg₀.ratchetKey = some c := hfind
  rw [hfind'] at hrc; injection hrc with hrc; injection hrc with hc_eq _; subst hc_eq; unfold consumeMessageKey at hcmk
  split at hcmk <;> [cases hcmk; (split at hcmk <;> [cases hcmk; (split at hcmk <;> [cases hcmk; skip])])]
  injection hcmk with hcmk; injection hcmk with h1 _; exact h1.symm
theorem recvSeed_eq_of_findRecvChain_none {st₀ : TRState} {msg₀ : TRSignalMsg} {mkSeed : DY.Bytes}
    (hfind : findRecvChain st₀.recv msg₀.ratchetKey = none) (hseed : recvSeed st₀ msg₀ = some mkSeed) :
    mkSeed = (kdfCk (chainKeyAt (createChain st₀.rk msg₀.ratchetKey st₀.dhs).2 msg₀.counter.toNat)).2 := by
  unfold recvSeed at hseed; split at hseed <;> [skip; cases hseed]
  rcases hrc : recvChainFor st₀.toDRState msg₀.ratchetKey with _ | ⟨c, b⟩ <;> rw [hrc] at hseed; · cases hseed
  simp only [Option.map_eq_some_iff] at hseed; obtain ⟨⟨s, c'⟩, hcmk, rfl⟩ := hseed
  unfold recvChainFor at hrc; have hfind' : findRecvChain st₀.toDRState.recv msg₀.ratchetKey = none := hfind
  rw [hfind'] at hrc; dsimp only at hrc; split at hrc; · cases hrc
  injection hrc with hrc; injection hrc with hc_eq _; subst hc_eq; unfold consumeMessageKey at hcmk
  split at hcmk <;> [cases hcmk; (split at hcmk <;> [cases hcmk; (split at hcmk <;> [cases hcmk; skip])])]
  injection hcmk with hcmk; injection hcmk with h1 _
  change (kdfCk (chainKeyAt (createChain st₀.rk msg₀.ratchetKey st₀.dhs).2 (msg₀.counter.toNat - 0))).2 = s at h1; rw [Nat.sub_zero] at h1; exact h1.symm
private theorem srk_container_pack_inj_sub (f g : Type → Type) [DY.ALaCarte.FunctorSizeOf f] [DY.ALaCarte.FunctorSizeOf g]
    [DY.ALaCarte.SubFunctorTC f g] [DY.ALaCarte.Representable g] (x : f (DY.ALaCarte.ContainerFor g)) :
    DY.ALaCarte.Container.pack g (DY.ALaCarte.SubFunctorTC.inj (g := g) x) = DY.ALaCarte.Container.pack f x := by
  have hv := DY.ALaCarte.Container.pack_view g (DY.ALaCarte.Container.pack f x)
  rw [Symbolic.DYBridge.DY.ALaCarte.Container.view_pack_cross f g x] at hv; exact hv
private theorem srk_lift_partialFunDep {f g : Type → Type} [DY.ALaCarte.FunctorSizeOf f] [DY.ALaCarte.FunctorSizeOf g]
    [DY.ALaCarte.SubFunctorTC f g] [DY.ALaCarte.Representable g] {motive : DY.ALaCarte.ContainerFor g → Prop}
    (h : DY.ALaCarte.Container.PartialFunDep f (g := g) motive) (x : f (DY.ALaCarte.ContainerFor g))
    (rec : ∀ y : DY.ALaCarte.ContainerFor g, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf (DY.ALaCarte.SubFunctorTC.inj (g := g) x) → motive y) :
    motive (DY.ALaCarte.Container.pack g (DY.ALaCarte.SubFunctorTC.inj (g := g) x)) := by
  rw [srk_container_pack_inj_sub f g x]; exact h x fun y hy => rec y (DY.ALaCarte.SubFunctorTC.sizeOf_inj (g := g) x ▸ hy)
unseal DY.Bytes in
theorem partialFunDep_not_dh {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sh_pk sh_sk : DY.Bytes) (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll i S g)]
    (hg : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm), DY.Bytes.view? (gF x rec).shape DY.DiffieHellman.Dh.SubF = none) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF) (fun u : DY.Bytes => DY.Bytes.view? (gamma' i S g u).shape DY.DiffieHellman.Dh.SubF = some { pk := sh_pk, sk := sh_sk } →
      ∃ pk₀ sk₀ : DY.Bytes, u = ({ pk := pk₀, sk := sk₀ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack ∧ (gamma' i S g pk₀).shape = sh_pk ∧ (gamma' i S g sk₀).shape = sh_sk) := by
  intro x _ hview; rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview
  change DY.Bytes.view? ((BytesView.pack x).rec (concretizeAll i S g)).shape DY.DiffieHellman.Dh.SubF = _ at hview
  rw [DY.Bytes.rec_eq gF (concretizeAll i S g) x, hg x _] at hview; contradiction
unseal DY.Bytes in
theorem partialFunDep_dh (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sh_pk sh_sk : DY.Bytes) :
    DY.ALaCarte.Container.PartialFunDep DY.DiffieHellman.Dh.SubF (g := DY.BytesF) (fun u : DY.Bytes => DY.Bytes.view? (gamma' i S g u).shape DY.DiffieHellman.Dh.SubF = some { pk := sh_pk, sk := sh_sk } →
      ∃ pk₀ sk₀ : DY.Bytes, u = ({ pk := pk₀, sk := sk₀ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack ∧ (gamma' i S g pk₀).shape = sh_pk ∧ (gamma' i S g sk₀).shape = sh_sk) := by
  intro x _ hview; rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview ⊢
  change DY.Bytes.view? ((BytesView.pack x).rec (concretizeAll i S g)).shape DY.DiffieHellman.Dh.SubF = _ at hview
  rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g) x] at hview; dsimp only [concretizeDh, node] at hview
  rw [DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF)] at hview; injection hview with h1; cases h1; exact ⟨x.pk, x.sk, rfl, rfl, rfl⟩
unseal DY.Bytes in
theorem view?_dh_shape_eq_some_inv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (u sh_pk sh_sk : DY.Bytes)
    (h : DY.Bytes.view? (gamma' i S g u).shape DY.DiffieHellman.Dh.SubF = some { pk := sh_pk, sk := sh_sk }) :
    ∃ pk₀ sk₀ : DY.Bytes, u = ({ pk := pk₀, sk := sk₀ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack ∧ (gamma' i S g pk₀).shape = sh_pk ∧ (gamma' i S g sk₀).shape = sh_sk := by
  refine DY.ALaCarte.Container.rec (f := DY.BytesF) (motive := fun u : DY.Bytes => DY.Bytes.view? (gamma' i S g u).shape DY.DiffieHellman.Dh.SubF = some { pk := sh_pk, sk := sh_sk } →
    ∃ pk₀ sk₀ : DY.Bytes, u = ({ pk := pk₀, sk := sk₀ } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack ∧ (gamma' i S g pk₀).shape = sh_pk ∧ (gamma' i S g sk₀).shape = sh_sk) ?_ u h
  rintro ⟨⟨id, hid⟩, val⟩ rec; match id with
  | 0 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeRandom g) (fun _ _ => by dsimp only [concretizeRandom]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) val rec
  | 1 => rcases val with ⟨⟨sid, h⟩, v⟩; match sid with | 0 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk concretizeLit (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | n + 1 => omega
  | 2 => rcases val with ⟨⟨sid, h⟩, v⟩; match sid with | 0 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk concretizeConcat (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | n + 1 => omega
  | 3 => rcases val with ⟨⟨sid, h⟩, v⟩; match sid with | 0 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeDhPk i) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | 1 => exact srk_lift_partialFunDep (partialFunDep_dh i S g sh_pk sh_sk) v rec | n + 2 => omega
  | 4 => rcases val with ⟨⟨sid, h⟩, v⟩; match sid with | 0 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeKdf i) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | n + 1 => omega
  | 5 => rcases val with ⟨⟨sid, h⟩, v⟩; match sid with | 0 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeSym i) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | n + 1 => omega
  | 6 => rcases val with ⟨⟨sid, h⟩, v⟩; match sid with | 0 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk concretizeTrunc (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | n + 1 => omega
  | 7 => rcases val with ⟨⟨sid, h⟩, v⟩; match sid with | 0 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeVariant i) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | n + 1 => omega
  | 8 => rcases val with ⟨⟨sid, h⟩, v⟩; match sid with | 0 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeKemPk S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | 1 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeKemEncap i) (fun _ _ => by dsimp only [concretizeKemEncap]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | 2 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeKemSS i S) (fun _ _ => by dsimp only [concretizeKemSS]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | 3 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeKemRej S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | n + 4 => omega
  | 9 => rcases val with ⟨⟨sid, h⟩, v⟩; match sid with | 0 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeVk S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | 1 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeSign S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | n + 2 => omega
  | 10 => rcases val with ⟨⟨sid, h⟩, v⟩; match sid with | 0 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeSpqrInit S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | 1 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeSpqrSendState S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | 2 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeSpqrSendKey S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | 3 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeSpqrSendMsg S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | 4 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeSpqrRecvState S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | 5 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeSpqrRecvKey S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | 6 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeSpqrChainKey S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | n + 7 => omega
  | 11 => rcases val with ⟨⟨sid, h⟩, v⟩; match sid with | 0 => exact srk_lift_partialFunDep (partialFunDep_not_dh i S g sh_pk sh_sk (concretizeTrWire g) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)) v rec | n + 1 => omega
  | n + 12 => omega
section UnsealedRkHelpers
unseal DY.Bytes
theorem pack_inj_rk {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF] {x₁ x₂ : SubF DY.Bytes} (h : BytesView.pack x₁ = BytesView.pack x₂) : x₁ = x₂ := by
  have h1 : DY.Bytes.view? (BytesView.pack x₁) SubF = some x₁ := DY.BytesView.view_pack (SubF := SubF) x₁
  have h2 : DY.Bytes.view? (BytesView.pack x₂) SubF = some x₂ := DY.BytesView.view_pack (SubF := SubF) x₂
  rw [h, h2] at h1; injection h1 with h1; exact h1.symm
theorem symEnc_inj_rk {k₁ iv₁ m₁ k₂ iv₂ m₂ : DY.Bytes} (h : SymEnc.symEnc k₁ iv₁ m₁ = SymEnc.symEnc k₂ iv₂ m₂) : k₁ = k₂ ∧ iv₁ = iv₂ ∧ m₁ = m₂ := by
  have hinj : ({ key := k₁, iv := iv₁, msg := m₁ } : DY.SymEnc.Enc.SubF DY.Bytes) = { key := k₂, iv := iv₂, msg := m₂ } := pack_inj_rk h; injection hinj with h1 h2 h3; exact ⟨h1, h2, h3⟩
theorem concat_inj_rk {l₁ r₁ l₂ r₂ : DY.Bytes} (h : Concat.concat l₁ r₁ = Concat.concat l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  have hinj : ({ lhs := l₁, rhs := r₁ } : DY.Concat.Concat.SubF DY.Bytes) = { lhs := l₂, rhs := r₂ } := pack_inj_rk h; injection hinj with h1 h2; exact ⟨h1, h2⟩
theorem kdfExtract_inj_rk {s₁ i₁ s₂ i₂ : DY.Bytes} (h : KdfExtract.kdfExtract s₁ i₁ = KdfExtract.kdfExtract s₂ i₂) : s₁ = s₂ ∧ i₁ = i₂ := by
  have hinj : ({ salt := s₁, ikm := i₁ } : DY.KdfExtract.KdfExtract.SubF DY.Bytes) = { salt := s₂, ikm := i₂ } := pack_inj_rk h; injection hinj with h1 h2; exact ⟨h1, h2⟩
theorem dhPk_inj_rk {sk₁ sk₂ : DY.Bytes} (h : DiffieHellman.dhPk sk₁ = DiffieHellman.dhPk sk₂) : sk₁ = sk₂ := by
  have hinj : ({ sk := sk₁ } : DY.DiffieHellman.DhPk.SubF DY.Bytes) = { sk := sk₂ } := pack_inj_rk h; injection hinj
theorem dh_eq_pack_rk (p s : DY.Bytes) : ∃ pk' sk', DiffieHellman.dh p s = ({ pk := pk', sk := sk' } : DiffieHellman.Dh.SubF DY.Bytes).pack := by
  dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh]; split <;> [split <;> exact ⟨_, _, rfl⟩; exact ⟨_, _, rfl⟩]
theorem spqrSend_snd_fst_eq_rk (st coins : DY.Bytes) :
    (∃ k p i, (Spqr.spqrSend st coins).2.1 = Spqr.spqrChainKey k p i) ∨ (∃ x : Spqr.SendKey.SubF DY.Bytes, (Spqr.spqrSend st coins).2.1 = x.pack) := by
  dsimp only [Spqr.spqrSend]; split <;> [exact .inl ⟨_, _, _, rfl⟩; exact .inr ⟨_, rfl⟩]
theorem spqrRecv_snd_eq_rk {st msg : DY.Bytes} {idx : UInt32} {r : DY.Bytes × DY.Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r) :
    r.2 = Spqr.zeroKey ∨ (∃ k p i, r.2 = Spqr.spqrChainKey k p i) ∨ (∃ x : Spqr.RecvKey.SubF DY.Bytes, r.2 = x.pack) := by
  unfold Spqr.spqrRecv at hrecv; split at hrecv; · cases hrecv
  split at hrecv <;> [(split at hrecv <;> [skip; cases hrecv]; injection hrecv with hr; rw [← hr]; dsimp only; split <;> [exact .inl rfl; exact .inr (.inl ⟨_, _, _, rfl⟩)]); (injection hrecv with hr; rw [← hr]; exact .inr (.inr ⟨_, rfl⟩))]
theorem kemPk_inj_rk {sk₁ sk₂ : DY.Bytes} (h : PQKem.kemPk sk₁ = PQKem.kemPk sk₂) : sk₁ = sk₂ := by
  have hinj : ({ sk := sk₁ } : DY.PQKem.Pk.SubF DY.Bytes) = { sk := sk₂ } := pack_inj_rk h; injection hinj
end UnsealedRkHelpers
inductive KdfRkSafe (T : ExecTrace) : DY.Bytes → Prop
  | atom {b : DY.Bytes} : DY.Bytes.view? b DY.DiffieHellman.DhPk.SubF = none → DY.Bytes.view? b DY.DiffieHellman.Dh.SubF = none →
      DY.Bytes.view? b DY.Concat.Concat.SubF = none → DY.Bytes.view? b DY.KdfExtract.KdfExtract.SubF = none →
      DY.Bytes.view? b DY.SymEnc.Enc.SubF = none →
      DY.Bytes.view? b DY.TrWire.TrWireMsg.SubF = none → DY.Bytes.view? b DY.X25519.Variant.SubF = none →
      DY.Bytes.view? b DY.Spqr.InitState.SubF = none → DY.Bytes.view? b DY.Spqr.SendState.SubF = none →
      DY.Bytes.view? b DY.Spqr.RecvState.SubF = none → DY.Bytes.view? b DY.PQKem.Pk.SubF = none → KdfRkSafe T b
  | dhPk {sk : DY.Bytes} : KdfRkSafe T sk → ((∃ t, sk = randTerm t 32) ∨ sk.AttackerKnows T) → KdfRkSafe T (DiffieHellman.dhPk sk)
  | kemPk {sk : DY.Bytes} : KdfRkSafe T sk → KdfRkSafe T (PQKem.kemPk sk)
  | dh (x : DiffieHellman.Dh.SubF DY.Bytes) : (∃ p0 s0, x.pack = DiffieHellman.dh p0 s0 ∧ p0.AttackerKnows T ∧ s0.AttackerKnows T) → KdfRkSafe T x.pack
  | concat {l r : DY.Bytes} : KdfRkSafe T l → KdfRkSafe T r → KdfRkSafe T (Concat.concat l r)
  | kdfExtract_ak {s i : DY.Bytes} : s.AttackerKnows T → i.AttackerKnows T → KdfRkSafe T s → KdfRkSafe T i → KdfRkSafe T (KdfExtract.kdfExtract s i)
  | kdfExtract_01 {s : DY.Bytes} : KdfRkSafe T s → KdfRkSafe T (KdfExtract.kdfExtract s (litByte 0x01))
  | kdfExtract_02 {s : DY.Bytes} : KdfRkSafe T s → KdfRkSafe T (KdfExtract.kdfExtract s (litByte 0x02))
  | kdfExtract_rk {s i : DY.Bytes} : i = Concat.concat (lit "WhisperRatchet") (litByte 1) →
      (∃ p st idx, TRStateStoredAt p st idx T ∧ KdfExtract.kdfExtract s i = st.rk) → KdfRkSafe T (KdfExtract.kdfExtract s i)
  | kdfExtract_dhPk {s i : DY.Bytes} : (∃ p st0 idx t_a t_sk, TRStateStoredAt p st0 idx T ∧ KdfExtract.kdfExtract s i = (createChain st0.rk (dhPk (randTerm t_a 32)) (randTerm t_sk 32)).2) → KdfRkSafe T (KdfExtract.kdfExtract s i)
  | kdfExtract_step {s i : DY.Bytes} : (∃ rk0 pk t_old t_new, t_old < t_new ∧ ((∃ p st0 idx, TRStateStoredAt p st0 idx T ∧ rk0 = st0.rk) ∨ ∃ ikm, rk0 = (DY.Libsignal.PQXDH.pqxdhKdf ikm).rk) ∧
      KdfExtract.kdfExtract s i = (createChain (createChain rk0 pk (randTerm t_old 32)).1 pk (randTerm t_new 32)).2) → KdfRkSafe T (KdfExtract.kdfExtract s i)
  | kdfExtract_pqxdh23 {s i : DY.Bytes} : (∃ b1, i = Concat.concat b1 (Concat.concat DY.Libsignal.PQXDH.pqxdhLabel (litByte 2)) ∨
      i = Concat.concat b1 (Concat.concat DY.Libsignal.PQXDH.pqxdhLabel (litByte 3))) → KdfRkSafe T (KdfExtract.kdfExtract s i)
  | kdfExtract_alice {s i : DY.Bytes} : (∃ ikm pk sk, KdfExtract.kdfExtract s i = (createChain (DY.Libsignal.PQXDH.pqxdhKdf ikm).rk pk sk).2) → KdfRkSafe T (KdfExtract.kdfExtract s i)
  | symEnc {k iv m : DY.Bytes} : KdfRkSafe T m → KdfRkSafe T (SymEnc.symEnc k iv m)
  | trWireMsg (x : TrWire.TrWireMsg.SubF DY.Bytes) : KdfRkSafe T x.senderRatchetKey → KdfRkSafe T x.ciphertext → KdfRkSafe T x.pqRatchet → KdfRkSafe T x.pack
  | variant (x : X25519.Variant.SubF DY.Bytes) : ¬(x.variation = 0 ∧ x.torsion = 0) → DY.Bytes.view? x.key DY.X25519.Variant.SubF = none → KdfRkSafe T x.key → KdfRkSafe T x.pack
  | spqrInit (x : Spqr.InitState.SubF DY.Bytes) : KdfRkSafe T x.authKey → KdfRkSafe T x.params → KdfRkSafe T x.pack
  | spqrSendState (x : Spqr.SendState.SubF DY.Bytes) : KdfRkSafe T x.st → KdfRkSafe T x.coins → KdfRkSafe T x.pack
  | spqrRecvState (x : Spqr.RecvState.SubF DY.Bytes) : KdfRkSafe T x.st → KdfRkSafe T x.msg → KdfRkSafe T x.pack
section UnsealedKdfRkLemmas
unseal DY.Bytes
theorem kdfRkSafe_random (T : ExecTrace) (r : DY.Random.SubF DY.Bytes) : KdfRkSafe T (DY.Random.Random.pack r) := by
  refine KdfRkSafe.atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem kdfRkSafe_literal (T : ExecTrace) (b : ByteArray) : KdfRkSafe T (Literal.literalToBytes b) := by
  refine KdfRkSafe.atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem kdfRkSafe_trunc8 (T : ExecTrace) (inp : DY.Bytes) : KdfRkSafe T (Trunc.trunc8 inp) := by
  refine KdfRkSafe.atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem kdfRkSafe_kemEncap_fst (T : ExecTrace) (pk e : DY.Bytes) : KdfRkSafe T (PQKem.kemEncap pk e).1 := by
  refine KdfRkSafe.atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem kdfRkSafe_kemEncap_snd (T : ExecTrace) (pk e : DY.Bytes) : KdfRkSafe T (PQKem.kemEncap pk e).2 := by
  refine KdfRkSafe.atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
private theorem kdfRkSafe_kemRejKey (T : ExecTrace) (sk ct : DY.Bytes) : KdfRkSafe T (PQKem.kemRejKey sk ct) := by
  refine KdfRkSafe.atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem kdfRkSafe_vk (T : ExecTrace) (sk : DY.Bytes) : KdfRkSafe T (Signature.vk sk) := by
  refine KdfRkSafe.atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem kdfRkSafe_sign (T : ExecTrace) (sk m r : DY.Bytes) : KdfRkSafe T (Signature.sign sk m r) := by
  refine KdfRkSafe.atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem kdfRkSafe_spqrChainKey (T : ExecTrace) (k p i : DY.Bytes) : KdfRkSafe T (Spqr.spqrChainKey k p i) := by
  refine KdfRkSafe.atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem kdfRkSafe_spqrSend_state {T : ExecTrace} {st coins : DY.Bytes} (hst : KdfRkSafe T st) (hc : KdfRkSafe T coins) : KdfRkSafe T (Spqr.spqrSend st coins).1 := KdfRkSafe.spqrSendState { st := st, coins := coins } hst hc
theorem kdfRkSafe_spqrSend_key (T : ExecTrace) (st coins : DY.Bytes) : KdfRkSafe T (Spqr.spqrSend st coins).2.1 := by
  rcases spqrSend_snd_fst_eq_rk st coins with ⟨k, p, i, heq⟩ | ⟨x, heq⟩ <;> rw [heq]
  · exact kdfRkSafe_spqrChainKey T k p i
  · refine KdfRkSafe.atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem kdfRkSafe_spqrSend_msg (T : ExecTrace) (st coins : DY.Bytes) : KdfRkSafe T (Spqr.spqrSend st coins).2.2 := by
  refine KdfRkSafe.atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem kdfRkSafe_spqrRecv_state {T : ExecTrace} {st msg : DY.Bytes} {idx : UInt32} {r : DY.Bytes × DY.Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r) (hst : KdfRkSafe T st) (hmsg : KdfRkSafe T msg) : KdfRkSafe T r.1 := by
  rw [Spqr.spqrRecv_state st msg idx r hrecv]; exact KdfRkSafe.spqrRecvState { st := st, msg := msg } hst hmsg
theorem kdfRkSafe_spqrRecv_key {T : ExecTrace} {st msg : DY.Bytes} {idx : UInt32} {r : DY.Bytes × DY.Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r) : KdfRkSafe T r.2 := by
  rcases spqrRecv_snd_eq_rk hrecv with heq | ⟨k, p, i, heq⟩ | ⟨x, heq⟩ <;> rw [heq]
  · exact kdfRkSafe_literal T _
  · exact kdfRkSafe_spqrChainKey T k p i
  · refine KdfRkSafe.atom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem kdfRkSafe_dhPk_iff {T : ExecTrace} (sk : DY.Bytes) : KdfRkSafe T (DiffieHellman.dhPk sk) ↔ KdfRkSafe T sk ∧ ((∃ t, sk = randTerm t 32) ∨ sk.AttackerKnows T) := by
  refine ⟨fun hs => ?_, fun ⟨hsk, h⟩ => KdfRkSafe.dhPk hsk h⟩; generalize hx : DiffieHellman.dhPk sk = x at hs
  have hview : DY.Bytes.view? x DY.DiffieHellman.DhPk.SubF = some { sk := sk } := by rw [← hx]; exact DY.BytesView.view_pack _
  cases hs
  case atom hdp _ _ _ _ _ _ _ _ _ _ => rw [hdp] at hview; contradiction
  case dhPk hsk h => obtain rfl := dhPk_inj_rk hx; exact ⟨hsk, h⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem kdfRkSafe_kemPk_iff {T : ExecTrace} (sk : DY.Bytes) : KdfRkSafe T (PQKem.kemPk sk) ↔ KdfRkSafe T sk := by
  refine ⟨fun hs => ?_, KdfRkSafe.kemPk⟩; generalize hx : PQKem.kemPk sk = x at hs
  have hview : DY.Bytes.view? x DY.PQKem.Pk.SubF = some { sk := sk } := by rw [← hx]; exact DY.BytesView.view_pack _
  cases hs
  case atom _ _ _ _ _ _ _ _ _ _ hkp => rw [hkp] at hview; contradiction
  case kemPk h => obtain rfl := kemPk_inj_rk hx; exact h
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem kdfRkSafe_dh_iff {T : ExecTrace} (d : DiffieHellman.Dh.SubF DY.Bytes) : KdfRkSafe T d.pack ↔ (∃ p0 s0, d.pack = DiffieHellman.dh p0 s0 ∧ p0.AttackerKnows T ∧ s0.AttackerKnows T) := by
  refine ⟨fun hs => ?_, KdfRkSafe.dh d⟩; generalize hx : d.pack = x at hs
  have hview : DY.Bytes.view? x DY.DiffieHellman.Dh.SubF = some d := by rw [← hx]; exact DY.BytesView.view_pack d
  cases hs
  case atom _ hd _ _ _ _ _ _ _ _ _ => rw [hd] at hview; contradiction
  case dh d' h => obtain rfl := pack_inj_rk hx; exact h
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem kdfRkSafe_concat_iff {T : ExecTrace} (l r : DY.Bytes) : KdfRkSafe T (Concat.concat l r) ↔ KdfRkSafe T l ∧ KdfRkSafe T r := by
  refine ⟨fun hs => ?_, fun ⟨hl, hr⟩ => KdfRkSafe.concat hl hr⟩; generalize hx : Concat.concat l r = x at hs
  have hview : DY.Bytes.view? x DY.Concat.Concat.SubF = some { lhs := l, rhs := r } := by rw [← hx]; exact DY.BytesView.view_pack _
  cases hs
  case atom _ _ hc _ _ _ _ _ _ _ _ => rw [hc] at hview; contradiction
  case concat hl hr => rcases concat_inj_rk hx with ⟨rfl, rfl⟩; exact ⟨hl, hr⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem kdfRkSafe_symEnc_iff {T : ExecTrace} (k iv m : DY.Bytes) : KdfRkSafe T (SymEnc.symEnc k iv m) ↔ KdfRkSafe T m := by
  refine ⟨fun hs => ?_, KdfRkSafe.symEnc⟩; generalize hx : SymEnc.symEnc k iv m = x at hs
  have hview : DY.Bytes.view? x DY.SymEnc.Enc.SubF = some { key := k, iv := iv, msg := m } := by rw [← hx]; exact DY.BytesView.view_pack _
  cases hs
  case atom _ _ _ _ he _ _ _ _ _ _ => rw [he] at hview; contradiction
  case symEnc hm => rcases symEnc_inj_rk hx with ⟨_, _, rfl⟩; exact hm
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem kdfRkSafe_trWireMsg_iff {T : ExecTrace} (w : TrWire.TrWireMsg.SubF DY.Bytes) :
    KdfRkSafe T w.pack ↔ KdfRkSafe T w.senderRatchetKey ∧ KdfRkSafe T w.ciphertext ∧ KdfRkSafe T w.pqRatchet := by
  refine ⟨fun hs => ?_, fun ⟨h1, h2, h3⟩ => KdfRkSafe.trWireMsg w h1 h2 h3⟩; generalize hx : w.pack = x at hs
  have hview : DY.Bytes.view? x DY.TrWire.TrWireMsg.SubF = some w := by rw [← hx]; exact DY.BytesView.view_pack w
  cases hs
  case atom _ _ _ _ _ htw _ _ _ _ _ => rw [htw] at hview; contradiction
  case trWireMsg w' h1 h2 h3 => obtain rfl := pack_inj_rk hx; exact ⟨h1, h2, h3⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem kdfRkSafe_variant_iff {T : ExecTrace} (v : X25519.Variant.SubF DY.Bytes) :
    KdfRkSafe T v.pack ↔ ¬(v.variation = 0 ∧ v.torsion = 0) ∧ DY.Bytes.view? v.key DY.X25519.Variant.SubF = none ∧ KdfRkSafe T v.key := by
  refine ⟨fun hs => ?_, fun ⟨hvar, hkv, hk⟩ => KdfRkSafe.variant v hvar hkv hk⟩; generalize hx : v.pack = x at hs
  have hview : DY.Bytes.view? x DY.X25519.Variant.SubF = some v := by rw [← hx]; exact DY.BytesView.view_pack v
  cases hs
  case atom _ _ _ _ _ _ hv _ _ _ _ => rw [hv] at hview; contradiction
  case variant v' hvar hkv hk => obtain rfl := pack_inj_rk hx; exact ⟨hvar, hkv, hk⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem kdfRkSafe_spqrInit_iff {T : ExecTrace} (x : Spqr.InitState.SubF DY.Bytes) : KdfRkSafe T x.pack ↔ KdfRkSafe T x.authKey ∧ KdfRkSafe T x.params := by
  refine ⟨fun hs => ?_, fun ⟨hk, hp⟩ => KdfRkSafe.spqrInit x hk hp⟩; generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.InitState.SubF = some x := by rw [← hx]; exact DY.BytesView.view_pack x
  cases hs
  case atom _ _ _ _ _ _ _ hi _ _ _ => rw [hi] at hview; contradiction
  case spqrInit x' hk hp => obtain rfl := pack_inj_rk hx; exact ⟨hk, hp⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem kdfRkSafe_spqrSendState_iff {T : ExecTrace} (x : Spqr.SendState.SubF DY.Bytes) : KdfRkSafe T x.pack ↔ KdfRkSafe T x.st ∧ KdfRkSafe T x.coins := by
  refine ⟨fun hs => ?_, fun ⟨hst, hc⟩ => KdfRkSafe.spqrSendState x hst hc⟩; generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.SendState.SubF = some x := by rw [← hx]; exact DY.BytesView.view_pack x
  cases hs
  case atom _ _ _ _ _ _ _ _ hs' _ _ => rw [hs'] at hview; contradiction
  case spqrSendState x' hst hc => obtain rfl := pack_inj_rk hx; exact ⟨hst, hc⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem kdfRkSafe_spqrRecvState_iff {T : ExecTrace} (x : Spqr.RecvState.SubF DY.Bytes) : KdfRkSafe T x.pack ↔ KdfRkSafe T x.st ∧ KdfRkSafe T x.msg := by
  refine ⟨fun hs => ?_, fun ⟨hst, hm⟩ => KdfRkSafe.spqrRecvState x hst hm⟩; generalize hx : x.pack = y at hs
  have hview : DY.Bytes.view? y DY.Spqr.RecvState.SubF = some x := by rw [← hx]; exact DY.BytesView.view_pack x
  cases hs
  case atom _ _ _ _ _ _ _ _ _ hr _ => rw [hr] at hview; contradiction
  case spqrRecvState x' hst hm => obtain rfl := pack_inj_rk hx; exact ⟨hst, hm⟩
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
end UnsealedKdfRkLemmas
theorem kdfRkSafe_x25519Key {T : ExecTrace} {pk : DY.Bytes} (h : KdfRkSafe T pk) : KdfRkSafe T (X25519.normalizeX25519Key pk) := by
  unfold X25519.normalizeX25519Key; have hpack := DY.Bytes.pack_view? X25519.Variant.SubF pk
  rcases hv : pk.view? X25519.Variant.SubF with _ | x; · exact h
  rw [hv] at hpack; dsimp only at hpack; rw [← hpack] at h; exact ((kdfRkSafe_variant_iff x).mp h).2.2
theorem x25519Key_view_variant_eq_none_of_kdfRkSafe {T : ExecTrace} {pk : DY.Bytes} (h : KdfRkSafe T pk) : DY.Bytes.view? (X25519.normalizeX25519Key pk) DY.X25519.Variant.SubF = none := by
  unfold X25519.normalizeX25519Key; have hpack := DY.Bytes.pack_view? X25519.Variant.SubF pk
  rcases hv : pk.view? X25519.Variant.SubF with _ | x; · exact hv
  rw [hv] at hpack; dsimp only at hpack; rw [← hpack] at h; exact ((kdfRkSafe_variant_iff x).mp h).2.1
theorem kdfRkSafe_x25519TorsionVariant {T : ExecTrace} {key : DY.Bytes} (v : Fin 4) (t : Fin 8) (h : KdfRkSafe T key) : KdfRkSafe T (X25519.x25519TorsionVariant key v t) := by
  change KdfRkSafe T (if v = 0 ∧ t = 0 then X25519.normalizeX25519Key key else ({ key := X25519.normalizeX25519Key key, variation := v, torsion := t } : X25519.Variant.SubF DY.Bytes).pack)
  split <;> [exact kdfRkSafe_x25519Key h; (rename_i hvt; exact KdfRkSafe.variant _ hvt (x25519Key_view_variant_eq_none_of_kdfRkSafe h) (kdfRkSafe_x25519Key h))]
section UnsealedPeeling
unseal DY.Bytes
theorem concat_ne_literal_rk (l r : DY.Bytes) (b : ByteArray) : Concat.concat l r ≠ Literal.literalToBytes b :=
  fun h => Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h
theorem kdfExtract_ne_literal_rk (s i : DY.Bytes) (b : ByteArray) : KdfExtract.kdfExtract s i ≠ Literal.literalToBytes b :=
  fun h => Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h
theorem kdfExtract_ne_concat_rk (s i l r : DY.Bytes) : KdfExtract.kdfExtract s i ≠ Concat.concat l r :=
  fun h => Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h
theorem trWireMsg_pack_ne_literal_rk (x : TrWire.TrWireMsg.SubF DY.Bytes) (b : ByteArray) : x.pack ≠ Literal.literalToBytes b :=
  fun h => Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h
theorem pqxdhLabel_ne_whisperRatchet_rk : DY.Libsignal.PQXDH.pqxdhLabel ≠ lit "WhisperRatchet" := by
  intro h
  have h1 : DY.Libsignal.PQXDH.pqxdhLabel.length = 46 := by
    unfold DY.Libsignal.PQXDH.pqxdhLabel lit
    rw [Literal.length_literalToBytes, String.toUTF8_eq_toByteArray,
      ← String.ofList_toList (s := "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"), String.toByteArray_ofList]
    decide
  have h2 : (lit "WhisperRatchet").length = 14 := by
    unfold lit
    rw [Literal.length_literalToBytes, String.toUTF8_eq_toByteArray,
      ← String.ofList_toList (s := "WhisperRatchet"), String.toByteArray_ofList]
    decide
  rw [h, h2] at h1; cases h1
theorem kdfRkSafe_kdfExtract_litByte_only {T : ExecTrace} {s : DY.Bytes} {b : UInt8} (hs : KdfRkSafe T (KdfExtract.kdfExtract s (litByte b))) : KdfRkSafe T s := by
  generalize hx : KdfExtract.kdfExtract s (litByte b) = x at hs
  have hview : DY.Bytes.view? x DY.KdfExtract.KdfExtract.SubF = some { salt := s, ikm := litByte b } := by rw [← hx]; exact DY.BytesView.view_pack _
  cases hs
  case atom _ _ _ hk _ _ _ _ _ _ _ => rw [hk] at hview; contradiction
  case kdfExtract_ak _ _ hs_s _ => exact (kdfExtract_inj_rk hx).1 ▸ hs_s
  case kdfExtract_01 hs_s => exact (kdfExtract_inj_rk hx).1 ▸ hs_s
  case kdfExtract_02 hs_s => exact (kdfExtract_inj_rk hx).1 ▸ hs_s
  case kdfExtract_rk hi _ => exact False.elim (concat_ne_literal_rk _ _ _ (hi.symm.trans (kdfExtract_inj_rk hx).2.symm))
  case kdfExtract_dhPk h => rcases h with ⟨_, _, _, _, _, _, heq⟩; exact False.elim (concat_ne_literal_rk _ _ _ (kdfExtract_inj_rk (hx.trans heq)).2.symm)
  case kdfExtract_step h => rcases h with ⟨_, _, _, _, _, _, heq⟩; exact False.elim (concat_ne_literal_rk _ _ _ (kdfExtract_inj_rk (hx.trans heq)).2.symm)
  case kdfExtract_pqxdh23 h => rcases h with ⟨b1, hi | hi⟩ <;> exact False.elim (concat_ne_literal_rk _ _ _ (hi.symm.trans (kdfExtract_inj_rk hx).2.symm))
  case kdfExtract_alice h => rcases h with ⟨ikm, pk, sk, heq⟩; exact False.elim (concat_ne_literal_rk _ _ _ (kdfExtract_inj_rk (hx.trans heq)).2.symm)
  all_goals erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hview; cases hview
theorem kdfRkSafe_kdfCk_fst_iff {T : ExecTrace} (ck : DY.Bytes) : KdfRkSafe T (kdfCk ck).1 ↔ KdfRkSafe T ck := ⟨kdfRkSafe_kdfExtract_litByte_only, KdfRkSafe.kdfExtract_02⟩
theorem kdfRkSafe_kdfCk_snd_iff {T : ExecTrace} (ck : DY.Bytes) : KdfRkSafe T (kdfCk ck).2 ↔ KdfRkSafe T ck := ⟨kdfRkSafe_kdfExtract_litByte_only, KdfRkSafe.kdfExtract_01⟩
theorem kdfRkSafe_chainKeyAt_iff {T : ExecTrace} (ck : DY.Bytes) (k : Nat) : KdfRkSafe T (chainKeyAt ck k) ↔ KdfRkSafe T ck := by
  induction k generalizing ck with | zero => rfl | succ k ih => exact (ih (kdfCk ck).1).trans (kdfRkSafe_kdfCk_fst_iff ck)
theorem consumeMessageKey_eq_and_kdfRkSafe {T : ExecTrace} {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes} (h : consumeMessageKey c counter = some (seed, c')) :
    seed = KdfExtract.kdfExtract (chainKeyAt c.chainKey (counter.toNat - c.index.toNat)) (litByte 0x01) ∧
    (KdfRkSafe T seed ↔ KdfRkSafe T c.chainKey) ∧ (KdfRkSafe T c'.chainKey ↔ KdfRkSafe T c.chainKey) := by
  unfold consumeMessageKey at h; split at h <;> [cases h; (split at h <;> [cases h; (split at h <;> [cases h; skip])])]
  injection h with h; injection h with h1 h2; subst h1; subst h2
  exact ⟨rfl, (kdfRkSafe_kdfCk_snd_iff _).trans (kdfRkSafe_chainKeyAt_iff c.chainKey _), (kdfRkSafe_kdfCk_fst_iff _).trans (kdfRkSafe_chainKeyAt_iff c.chainKey _)⟩
theorem messageDecrypt_dhPk_or_seed_attackerKnows {tr : ExecTrace} (hreach : ReachableTrace tr)
    {t pqSalt seed ck peerIk myIk : DY.Bytes} {msg : TRSignalMsg} (ht_ak : t.AttackerKnows tr) (hparse : parseTrSignalMsg t = some msg)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey peerIk myIk msg.wire) (hseed : seed = KdfExtract.kdfExtract ck (litByte 0x01)) :
    (∃ t_a, msg.ratchetKey = dhPk (randTerm t_a 32)) ∨ seed.AttackerKnows tr := by
  obtain ⟨x, hsplit, _, hpack, hrk_eq, _, _⟩ := parseTrSignalMsg_unpack hparse
  have hsp_ak := Concat.attacker_knows_split t (t.length - Trunc.trunc8Length) tr ht_ak; rw [hsplit] at hsp_ak
  have hmac_ak : (computeMac (trMsgKeys pqSalt seed).macKey peerIk myIk msg.wire).AttackerKnows tr := hmac_eq ▸ hsp_ak.2
  let inp₀ := hmac (trMsgKeys pqSalt seed).macKey (Concat.concat peerIk (Concat.concat myIk msg.wire))
  rcases (truncSafeStrong_trunc8_iff inp₀).mp (truncSafeStrong_of_attackerKnows_reachable hreach hmac_ak) with
    hinp_ak | ⟨pqSalt', seed', myIk', peerIk', a, ns, pn, m, pqMsg, t_s, _, _, _, hinp_eq, _, _, rfl, _, _, _, _⟩
  · right; rcases (macKdfSafeTR_kdfExtract_iff _ _).mp (macKdfSafeTR_of_attackerKnows_reachable hreach hinp_ak) with ⟨hmackey_ak, _⟩ | ⟨h01, _⟩ | h02 | hwr1 | ⟨b1, hwr2⟩
    · have hmackey_s := macKdfSafeTR_of_attackerKnows_reachable hreach hmackey_ak; dsimp [trMsgKeys, hkdfBlock2, hmac] at hmackey_s
      rcases (macKdfSafeTR_kdfExtract_iff _ _).mp hmackey_s with ⟨hprk_ak, _⟩ | ⟨h01, _⟩ | h02 | hwr1 | ⟨b1, hwr2⟩
      · rcases (macKdfSafeTR_kdfExtract_iff _ _).mp (macKdfSafeTR_of_attackerKnows_reachable hreach hprk_ak) with ⟨_, hseed_ak⟩ | ⟨h01, _⟩ | h02 | hwr1 | ⟨b1, hwr2⟩
        · exact hseed_ak
        · rw [hseed] at h01; exact False.elim (kdfExtract_ne_literal_rk _ _ _ h01)
        · rw [hseed] at h02; exact False.elim (kdfExtract_ne_literal_rk _ _ _ h02)
        · rw [hseed] at hwr1; exact False.elim (kdfExtract_ne_concat_rk _ _ _ _ hwr1)
        · rw [hseed] at hwr2; exact False.elim hwr2.ne_kdfExtract
      · exact False.elim (concat_ne_literal_rk _ _ _ h01)
      · exact False.elim (concat_ne_literal_rk _ _ _ h02)
      · exact False.elim (concat_ne_literal_rk _ _ _ (concat_inj_rk hwr1).2)
      · exact False.elim hwr2.ne_whisperMessageKeys
    · exact False.elim (concat_ne_literal_rk _ _ _ h01)
    · exact False.elim (concat_ne_literal_rk _ _ _ h02)
    · exact False.elim (concat_ne_literal_rk _ _ _ (concat_inj_rk hwr1).2)
    · rcases hwr2 with hwr2 | hwr2 | hwr2 <;> (have hwire_lit := (concat_inj_rk (concat_inj_rk hwr2).2).2; rw [hpack] at hwire_lit; exact False.elim (trWireMsg_pack_ne_literal_rk x _ hwire_lit))
  · left; refine ⟨t_s, ?_⟩
    have hwire_eq : msg.wire = trHonestWireMsg (dhPk (randTerm t_s 32)) ns pn (SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m) pqMsg :=
      (concat_inj_rk (concat_inj_rk (kdfExtract_inj_rk hinp_eq).2).2).2
    rw [hpack] at hwire_eq; exact hrk_eq.trans (congrArg TrWire.TrWireMsg.SubF.senderRatchetKey (pack_inj_rk hwire_eq))
end UnsealedPeeling
def ValidRkPk (T : ExecTrace) (pk : DY.Bytes) : Prop := (∃ t_sk : Nat, pk = dhPk (randTerm t_sk 32)) ∨ pk.AttackerKnows T
inductive RkTree (T : ExecTrace) : DY.Bytes → Prop
  | rand (t : Nat) : RkTree T (randTerm t 32)
  | pqxdh (dh1 dh2 dh3 : DY.Bytes) (dh4 : Option DY.Bytes) (ss : DY.Bytes) : RkTree T (DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 dh4 ss)).rk
  | create {rk pk : DY.Bytes} (t_dhs : Nat) : RkTree T rk → ValidRkPk T pk → RkTree T (createChain rk pk (randTerm t_dhs 32)).1
def StRkDhsInv (T : ExecTrace) (bound : Nat) (st : TRState) : Prop :=
  RkTree T st.rk ∧ ∃ t < bound, st.dhs = randTerm t 32 ∧ ((∃ t_rk, st.rk = randTerm t_rk 32) ∨ ∃ rk_p pk_p, st.rk = (createChain rk_p pk_p (randTerm t 32)).1)
theorem stRkDhsInv_mono {T : ExecTrace} {bound bound' : Nat} {st : TRState} (hle : bound ≤ bound') (h : StRkDhsInv T bound st) : StRkDhsInv T bound' st := by
  rcases h with ⟨hrk, t, ht, hdhs, hform⟩; exact ⟨hrk, t, Nat.lt_of_lt_of_le ht hle, hdhs, hform⟩
theorem kdfRkSafe_dhs_of_stRkDhsInv {T : ExecTrace} {bound : Nat} {st : TRState} (h : StRkDhsInv T bound st) : KdfRkSafe T st.dhs ∧ KdfRkSafe T (dhPk st.dhs) := by
  rcases h with ⟨_, t, _, hdhs, _⟩; rw [hdhs]; have hr : KdfRkSafe T (randTerm t 32) := kdfRkSafe_random T { timestamp := t, size := 32 }; exact ⟨hr, KdfRkSafe.dhPk hr (.inl ⟨t, rfl⟩)⟩
theorem kdfRkSafe_rk_of_stRkDhsInv {T : ExecTrace} {bound : Nat} {p : Participant} {st : TRState} {idx : Nat} (h : StRkDhsInv T bound st) (hstored : TRStateStoredAt p st idx T) : KdfRkSafe T st.rk := by
  rcases h with ⟨_, t, _, _, ⟨t_rk, hrk⟩ | ⟨rk_p, pk_p, hrk⟩⟩; · rw [hrk]; exact kdfRkSafe_random T { timestamp := t_rk, size := 32 }
  have hcc : (createChain rk_p pk_p (randTerm t 32)).1 = KdfExtract.kdfExtract (hmac rk_p (DiffieHellman.dh (X25519.normalizeX25519Key pk_p) (randTerm t 32))) (Concat.concat (lit "WhisperRatchet") (litByte 1)) := rfl
  rw [hrk, hcc]; exact KdfRkSafe.kdfExtract_rk rfl ⟨p, st, idx, hstored, (hrk.trans hcc).symm⟩
def StSafeRk (T : ExecTrace) (bound : Nat) (st : TRState) : Prop := StRkDhsInv T bound st ∧ KdfRkSafe T st.cks ∧ KdfRkSafe T st.spqr ∧ ∀ c ∈ st.recv, KdfRkSafe T c.chainKey
theorem stSafeRk_mono {T : ExecTrace} {bound bound' : Nat} {st : TRState} (hle : bound ≤ bound') (h : StSafeRk T bound st) : StSafeRk T bound' st := ⟨stRkDhsInv_mono hle h.1, h.2⟩
def JRk (T tr : ExecTrace) : Prop :=
  (∀ b, Trace.BaseAttackerKnows tr b → KdfRkSafe T b) ∧ (∀ p st i, TRStateStoredAt p st i tr → StSafeRk T tr.length st) ∧
  (∀ i s pk n seed rIdx src, tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i → KdfRkSafe T seed)
theorem parseTrSignalMsg_fields_rk {T tr : ExecTrace} {t : DY.Bytes} {msg : TRSignalMsg} (ht_ak : t.AttackerKnows tr) (ht : KdfRkSafe T t) (hparse : parseTrSignalMsg t = some msg) :
    KdfRkSafe T msg.pqRatchet ∧ msg.ratchetKey.AttackerKnows tr := by
  obtain ⟨x, hsplit, _, hpack, hrk_eq, _, hpq_eq⟩ := parseTrSignalMsg_unpack hparse
  have hsp_ak := Concat.attacker_knows_split t (t.length - Trunc.trunc8Length) tr ht_ak; rw [hsplit] at hsp_ak
  rw [← Concat.concat_split t (t.length - Trunc.trunc8Length) msg.wire msg.mac hsplit] at ht
  have hwire : KdfRkSafe T msg.wire := ((kdfRkSafe_concat_iff msg.wire msg.mac).mp ht).1; rw [hpack] at hwire; have hwire_ak := hsp_ak.1; rw [hpack] at hwire_ak
  have hrk_ak : x.senderRatchetKey.AttackerKnows tr := DY.Bytes.AttackerKnows.prove TrWire.trWireMsgArg.attackerKnowledge x.senderRatchetKey tr ⟨x, hwire_ak, Or.inl rfl⟩
  exact ⟨hpq_eq ▸ ((kdfRkSafe_trWireMsg_iff x).mp hwire).2.2, hrk_eq ▸ hrk_ak⟩
set_option maxHeartbeats 400000 in
theorem attackerKnows_imp_kdfRkSafe {tr T : ExecTrace} (hle : tr ≤ T) (h_base : ∀ msg, Trace.BaseAttackerKnows tr msg → KdfRkSafe T msg) {b : DY.Bytes} (hak : b.AttackerKnows tr) : KdfRkSafe T b := by
  suffices h : b.AttackerKnows tr ∧ KdfRkSafe T b from h.2
  refine DY.Bytes.AttackerKnows.is_least_fixpoint (fun x => x.AttackerKnows tr ∧ KdfRkSafe T x) b tr ?_ ?_ hak
  · change SubAttackerKnowledge.Implies DY.Libsignal.Composed.attackerKnowledge (fun x => x.AttackerKnows tr ∧ KdfRkSafe T x)
    dsimp [DY.Libsignal.Composed.attackerKnowledge]; apply SubAttackerKnowledge.combine.implies
    rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, _⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Random.attackerKnowledge]
      intro x hx; rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at hx; exact hx.elim
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Literal.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | n, _⟩ <;> [skip; omega]
      intro x hx; dsimp [Literal.attackerKnowledge.internal] at hx
      rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at hx
      rcases hx with ⟨bs, rfl⟩; exact ⟨Literal.attacker_knows_literalToBytes bs tr, kdfRkSafe_literal T bs⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Concat.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | n, _⟩ <;> try omega
      · intro x hx; dsimp [Concat.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at hx
        rcases hx with ⟨lhs, rhs, rfl, ⟨hl_ak, hl_s⟩, ⟨hr_ak, hr_s⟩⟩; exact ⟨Concat.attacker_knows_concat lhs rhs tr hl_ak hr_ak, KdfRkSafe.concat hl_s hr_s⟩
      · intro x hx; dsimp [Concat.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at hx
        rcases hx with ⟨inp, rhs, i, hsplit, ⟨hinp_ak, hinp_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Concat.splitLeft.attackerKnowledge x tr (by rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred]; exact ⟨inp, rhs, i, hsplit, hinp_ak⟩), ((kdfRkSafe_concat_iff x rhs).mp (Concat.concat_split inp i x rhs hsplit.symm ▸ hinp_s)).1⟩
      · intro x hx; dsimp [Concat.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hx
        rcases hx with ⟨inp, lhs, i, hsplit, ⟨hinp_ak, hinp_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove Concat.splitRight.attackerKnowledge x tr (by rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred]; exact ⟨inp, lhs, i, hsplit, hinp_ak⟩), ((kdfRkSafe_concat_iff lhs x).mp (Concat.concat_split inp i lhs x hsplit.symm ▸ hinp_s)).2⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DiffieHellman.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
      · intro x hx; dsimp [DiffieHellman.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hx
        rcases hx with ⟨sk, rfl, ⟨hsk_ak, hsk_s⟩⟩; exact ⟨DiffieHellman.attacker_knows_dhPk sk tr hsk_ak, KdfRkSafe.dhPk hsk_s (.inr (DY.Bytes.AttackerKnows_le sk tr T hle hsk_ak))⟩
      · intro x hx; dsimp [DiffieHellman.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at hx
        rcases hx with ⟨pk, sk, rfl, ⟨hpk_ak, _⟩, ⟨hsk_ak, _⟩⟩; obtain ⟨p₀, s₀, hdheq⟩ := dh_eq_pack_rk pk sk
        refine ⟨DiffieHellman.attacker_knows_dh pk sk tr hpk_ak hsk_ak, ?_⟩; rw [hdheq]
        exact KdfRkSafe.dh { pk := p₀, sk := s₀ } ⟨pk, sk, hdheq.symm, DY.Bytes.AttackerKnows_le pk tr T hle hpk_ak, DY.Bytes.AttackerKnows_le sk tr T hle hsk_ak⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, KdfExtract.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | n, _⟩ <;> [skip; omega]
      intro x hx; dsimp [KdfExtract.attackerKnowledge.internal] at hx
      rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at hx
      rcases hx with ⟨salt, ikm, rfl, ⟨hs_ak, hs_s⟩, ⟨hi_ak, hi_s⟩⟩
      exact ⟨KdfExtract.attacker_knows_kdfExtract salt ikm tr hs_ak hi_ak, KdfRkSafe.kdfExtract_ak (DY.Bytes.AttackerKnows_le salt tr T hle hs_ak) (DY.Bytes.AttackerKnows_le ikm tr T hle hi_ak) hs_s hi_s⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, SymEnc.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
      · rintro x ⟨k, iv, msg, rfl, ⟨hk_ak, _⟩, ⟨hiv_ak, _⟩, ⟨hm_ak, hm_s⟩⟩; exact ⟨SymEnc.attacker_knows_symEnc k iv msg tr hk_ak hiv_ak hm_ak, KdfRkSafe.symEnc hm_s⟩
      · rintro x ⟨key, iv, ct, hdec, ⟨hk_ak, _⟩, ⟨hiv_ak, _⟩, ⟨hct_ak, hct_s⟩⟩; have heq := SymEnc.symDec_eq_some key iv ct x hdec.symm; rw [heq] at hct_s
        exact ⟨SymEnc.attacker_knows_symDec key iv ct x tr hk_ak hiv_ak hct_ak hdec.symm, (kdfRkSafe_symEnc_iff key iv x).mp hct_s⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Trunc.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | n, _⟩ <;> [skip; omega]; rintro x ⟨m, rfl, ⟨hm_ak, _⟩⟩; exact ⟨Trunc.attacker_knows_trunc8 m tr hm_ak, kdfRkSafe_trunc8 T m⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, X25519.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
      · rintro x ⟨key, v, t, rfl, ⟨hk_ak, hk_s⟩⟩; exact ⟨DY.Bytes.AttackerKnows.prove X25519.x25519Variant.attackerKnowledge _ tr ⟨key, v, t, rfl, hk_ak⟩, kdfRkSafe_x25519TorsionVariant v t hk_s⟩
      · rintro x ⟨v, ⟨hv_ak, hv_s⟩, rfl⟩; exact ⟨DY.Bytes.AttackerKnows.prove X25519.normalizeX25519Key.attackerKnowledge _ tr ⟨v, hv_ak, rfl⟩, ((kdfRkSafe_variant_iff v).mp hv_s).2.2⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, PQKem.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | _ | _ | n, _⟩ <;> try omega
      · rintro x ⟨sk, rfl, ⟨hsk_ak, hsk_s⟩⟩; exact ⟨DY.Bytes.AttackerKnows.prove PQKem.kemPk.attackerKnowledge _ tr ⟨sk, rfl, hsk_ak⟩, KdfRkSafe.kemPk hsk_s⟩
      · rintro x ⟨pk, e, rhs, heq, ⟨hpk_ak, _⟩, ⟨he_ak, _⟩⟩; refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemEncapCipher.attackerKnowledge x tr ⟨pk, e, rhs, heq, hpk_ak, he_ak⟩, ?_⟩
        have h1 : x = (PQKem.kemEncap pk e).1 := congrArg Prod.fst heq; rw [h1]; exact kdfRkSafe_kemEncap_fst T pk e
      · rintro x ⟨pk, e, lhs, heq, ⟨hpk_ak, _⟩, ⟨he_ak, _⟩⟩; refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemEncapSS.attackerKnowledge x tr ⟨pk, e, lhs, heq, hpk_ak, he_ak⟩, ?_⟩
        have h2 : x = (PQKem.kemEncap pk e).2 := congrArg Prod.snd heq; rw [h2]; exact kdfRkSafe_kemEncap_snd T pk e
      · rintro x ⟨sk, ct, hdec, ⟨hsk_ak, _⟩, ⟨hct_ak, _⟩⟩; refine ⟨DY.Bytes.AttackerKnows.prove PQKem.kemDecap.attackerKnowledge x tr ⟨sk, ct, hdec, hsk_ak, hct_ak⟩, ?_⟩
        obtain ⟨e, _, rfl⟩ := Symbolic.Swarm.COMPOSED.CompTermAlgebra.kemDecap_eq_some_iff.mp hdec.symm; exact kdfRkSafe_kemEncap_snd T (PQKem.kemPk sk) e
      · rintro x ⟨sk, ct, rfl, ⟨hsk_ak, _⟩, ⟨hct_ak, _⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove PQKem.kemRejKey.attackerKnowledge _ tr ⟨sk, ct, rfl, hsk_ak, hct_ak⟩, kdfRkSafe_kemRejKey T sk ct⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Signature.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
      · intro x hx; dsimp [Signature.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at hx
        rcases hx with ⟨sk, rfl, ⟨hsk_ak, _⟩⟩; exact ⟨Signature.attacker_knows_vk sk tr hsk_ak, kdfRkSafe_vk T sk⟩
      · intro x hx; dsimp [Signature.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hx
        rcases hx with ⟨sk, nonce, msg, rfl, ⟨hsk_ak, _⟩, ⟨hnonce_ak, _⟩, ⟨hmsg_ak, _⟩⟩; exact ⟨Signature.attacker_knows_sign sk nonce msg tr hsk_ak hnonce_ak hmsg_ak, kdfRkSafe_sign T sk nonce msg⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Spqr.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, _⟩ <;> try omega
      · rintro x ⟨authKey, params, rfl, ⟨hk_ak, hk_s⟩, ⟨hp_ak, hp_s⟩⟩; exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrInit.attackerKnowledge _ tr ⟨authKey, params, rfl, hk_ak, hp_ak⟩, KdfRkSafe.spqrInit { authKey := authKey, params := params } hk_s hp_s⟩
      · rintro x ⟨authKey, params, idx, rfl, ⟨hk_ak, _⟩, ⟨hp_ak, _⟩, ⟨hi_ak, _⟩⟩; exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrChainKey.attackerKnowledge _ tr ⟨authKey, params, idx, rfl, hk_ak, hp_ak, hi_ak⟩, kdfRkSafe_spqrChainKey T authKey params idx⟩
      · rintro x ⟨st, coins, rfl, ⟨hst_ak, hst_s⟩, ⟨hc_ak, hc_s⟩⟩; exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendState.attackerKnowledge _ tr ⟨st, coins, rfl, hst_ak, hc_ak⟩, kdfRkSafe_spqrSend_state hst_s hc_s⟩
      · rintro x ⟨st, coins, rfl, ⟨hst_ak, _⟩, ⟨hc_ak, _⟩⟩; exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendKey.attackerKnowledge _ tr ⟨st, coins, rfl, hst_ak, hc_ak⟩, kdfRkSafe_spqrSend_key T st coins⟩
      · rintro x ⟨st, coins, rfl, ⟨hst_ak, _⟩, ⟨hc_ak, _⟩⟩; exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrSendMsg.attackerKnowledge _ tr ⟨st, coins, rfl, hst_ak, hc_ak⟩, kdfRkSafe_spqrSend_msg T st coins⟩
      · rintro x ⟨st, msg, idx, r, hrecv, rfl, ⟨hst_ak, hst_s⟩, ⟨hm_ak, hm_s⟩⟩; exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrRecvState.attackerKnowledge _ tr ⟨st, msg, idx, r, hrecv, rfl, hst_ak, hm_ak⟩, kdfRkSafe_spqrRecv_state hrecv hst_s hm_s⟩
      · rintro x ⟨st, msg, idx, r, hrecv, rfl, ⟨hst_ak, _⟩, ⟨hm_ak, _⟩⟩; exact ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrRecvKey.attackerKnowledge _ tr ⟨st, msg, idx, r, hrecv, rfl, hst_ak, hm_ak⟩, kdfRkSafe_spqrRecv_key hrecv⟩
      · rintro x (⟨s, ⟨hs_ak, hs_s⟩, harg⟩ | ⟨s, ⟨hs_ak, hs_s⟩, harg⟩ | ⟨s, ⟨hs_ak, hs_s⟩, harg⟩)
        · have hargs := (kdfRkSafe_spqrInit_iff s).mp hs_s; refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge x tr (.inl ⟨s, hs_ak, harg⟩), ?_⟩; rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
        · have hargs := (kdfRkSafe_spqrSendState_iff s).mp hs_s; refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge x tr (.inr (.inl ⟨s, hs_ak, harg⟩)), ?_⟩; rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
        · have hargs := (kdfRkSafe_spqrRecvState_iff s).mp hs_s; refine ⟨DY.Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge x tr (.inr (.inr ⟨s, hs_ak, harg⟩)), ?_⟩; rcases harg with rfl | rfl <;> [exact hargs.1; exact hargs.2]
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, TrWire.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, _⟩ <;> try omega
      · rintro x ⟨w, rfl, ⟨h1_ak, h1_s⟩, ⟨h2_ak, h2_s⟩, ⟨h3_ak, h3_s⟩⟩
        exact ⟨DY.Bytes.AttackerKnows.prove TrWire.trWireMsg.attackerKnowledge _ tr ⟨w, rfl, h1_ak, h2_ak, h3_ak⟩, KdfRkSafe.trWireMsg w h1_s h2_s h3_s⟩
      · rintro x ⟨w, ⟨hw_ak, hw_s⟩, hmem⟩; have hargs_s := (kdfRkSafe_trWireMsg_iff w).mp hw_s
        refine ⟨DY.Bytes.AttackerKnows.prove TrWire.trWireMsgArg.attackerKnowledge x tr ⟨w, hw_ak, hmem⟩, ?_⟩
        rcases hmem with rfl | rfl | rfl; exacts [hargs_s.1, hargs_s.2.1, hargs_s.2.2]
    · omega
  · intro x hx; simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, SubAttackerKnowledge.fromPred] at hx; exact ⟨DY.Bytes.AttackerKnows.prove_from_base x tr hx, h_base x hx⟩
theorem kdfRkSafe_pqxdhKdf_ck (T : ExecTrace) (ikm : DY.Bytes) : KdfRkSafe T (pqxdhKdf ikm).ck := KdfRkSafe.kdfExtract_pqxdh23 ⟨_, .inl rfl⟩
theorem kdfRkSafe_pqxdhKdf_pqr (T : ExecTrace) (ikm : DY.Bytes) : KdfRkSafe T (pqxdhKdf ikm).pqr := KdfRkSafe.kdfExtract_pqxdh23 ⟨_, .inr rfl⟩
theorem kdfRkSafe_alice_cks (T : ExecTrace) (ikm spk dhsA : DY.Bytes) :
    KdfRkSafe T (createChain (pqxdhKdf ikm).rk spk dhsA).2 := KdfRkSafe.kdfExtract_alice ⟨ikm, spk, dhsA, rfl⟩
theorem JRk_nil (T : ExecTrace) : JRk T Trace.nil := by
  refine ⟨fun b h => False.elim (Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1 b ▸ h), fun _ _ _ hst => ?_, fun _ _ _ _ _ _ _ hk => ?_⟩
  · unfold TRStateStoredAt at hst; rw [Trace.at?_eq_some] at hst; exact False.elim (Symbolic.DYBridge.DY.Trace.nil_length_not_lt _ hst.1)
  · rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?_eq_some] at hk; exact False.elim (Symbolic.DYBridge.DY.Trace.nil_length_not_lt _ hk.1)
theorem JRk_append_other {T tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] {e : E}
    (hdr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.TREntry) = none)
    (hst : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.TRStEntry) = none)
    (hbase : ∀ b, Trace.BaseAttackerKnows (tr.append e) b → KdfRkSafe T b) (h : JRk T tr) : JRk T (tr.append e) :=
  ⟨hbase, fun p st i hs => stSafeRk_mono (Trace.length_le _ _ (Trace.append_le tr _)) (h.2.1 p st i (CompTrace.trStateStoredAt_append_other hst hs)),
   fun i s pk n seed rIdx src hev => h.2.2 i s pk n seed rIdx src (CompTrace.eventLoggedAt_append_other hdr hev)⟩
theorem JRk_append_noop {T tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] {e : E} (h : JRk T tr)
    (hdr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.TREntry) = none := by rfl)
    (hst : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.TRStEntry) = none := by rfl)
    (hbk : ∀ b, Trace.BaseAttackerKnows (tr.append e) b → Trace.BaseAttackerKnows tr b := by intro _; exact (iff_of_eq (false_or _)).1) :
    JRk T (tr.append e) := JRk_append_other hdr hst (fun b hb => h.1 b (hbk b hb)) h
private theorem jrk_append_pqEv {T tr : ExecTrace} (ev : PQXDHEvent) (h : JRk T tr) : JRk T (tr.append (EvE ev)) :=
  JRk_append_noop h rfl rfl fun b hb => (CompTrace.baseAttackerKnows_append_pqEv tr ev b).mp hb
private theorem jrk_append_cEv {T tr : ExecTrace} (ev : ComposedEvent) (h : JRk T tr) : JRk T (tr.append (CEvE ev)) :=
  JRk_append_noop h rfl rfl fun b hb => (CompTrace.baseAttackerKnows_append_cEv tr ev b).mp hb
private theorem jrk_append_pqSt {T tr : ExecTrace} (me : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) (h : JRk T tr) : JRk T (tr.append (CompInv.StE me st)) :=
  JRk_append_noop h rfl rfl fun b hb => (CompTrace.baseAttackerKnows_append_pqSt tr me st b).mp hb
theorem JRk_append_rand {T tr : ExecTrace} (n : Nat) (h : JRk T tr) : JRk T (tr.append (RndE n)) :=
  JRk_append_noop h rfl rfl fun b hb => (CompTrace.baseAttackerKnows_append_rnd tr n b).mp hb
theorem JRk_append_net {T tr : ExecTrace} {m : DY.Bytes} (hm : KdfRkSafe T m) (h : JRk T tr) : JRk T (tr.append (NetE m)) :=
  JRk_append_other rfl rfl (fun b hb => by rcases (CompTrace.baseAttackerKnows_append_net tr m b).mp hb with rfl | hb <;> [exact hm; exact h.1 b hb]) h
theorem JRk_append_ev {T tr : ExecTrace} (ev : TREvent)
    (hev : ∀ s pk n seed rIdx src, ev = .SkippedKeyStored s pk n seed rIdx src → KdfRkSafe T seed) (h : JRk T tr) : JRk T (tr.append (TREvE ev)) := by
  refine ⟨fun b hb => h.1 b ((CompTrace.baseAttackerKnows_append_trEv tr ev b).mp hb),
    fun p st i hs => stSafeRk_mono (Trace.length_le _ _ (Trace.append_le tr _)) (h.2.1 p st i (CompTrace.trStateStoredAt_append_other rfl hs)), fun i s pk n seed rIdx src hevl => ?_⟩
  rcases CompTrace.eventLoggedAt_append_same hevl with ⟨_, hevl⟩ | ⟨_, hp⟩ <;> [exact h.2.2 i s pk n seed rIdx src hevl; exact hev s pk n seed rIdx src hp]
theorem JRk_append_st {T tr : ExecTrace} (p : Participant) {st : TRState} (hst : StSafeRk T tr.length st) (h : JRk T tr) : JRk T (tr.append (TRStE p st)) := by
  refine ⟨fun b hb => h.1 b ((CompTrace.baseAttackerKnows_append_trSt tr p st b).mp hb), fun p' st' i hs => ?_,
    fun i s pk n seed rIdx src hevl => h.2.2 i s pk n seed rIdx src (CompTrace.eventLoggedAt_append_other rfl hevl)⟩
  rcases CompTrace.trStateStoredAt_append_same hs with ⟨_, hs⟩ | ⟨_, rfl, rfl⟩ <;> [exact stSafeRk_mono (Trace.length_le _ _ (Trace.append_le tr _)) (h.2.1 p' st' i hs); exact stSafeRk_mono (Trace.length_le _ _ (Trace.append_le tr _)) hst]
def PQRkAt (T tr : ExecTrace) {α : Type} (Q : ExecTrace → α → Prop) (x : Traceful α) : Prop :=
  JRk T tr → (x.run tr).2.val ≤ T → JRk T (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q (x.run tr).2.val a
theorem PQRkAt.bind {T tr : ExecTrace} {α β : Type} {Q : ExecTrace → α → Prop} {R : ExecTrace → β → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : PQRkAt T tr Q x) (hf : ∀ tr1 a, tr ≤ tr1 → Q tr1 a → PQRkAt T tr1 R (f a)) : PQRkAt T tr R (x >>= f) := by
  intro hJ hle; rw [CompTrace.run_bind_snd] at hle; rw [Traceful.run_bind]; have hx0 := hx hJ
  rcases h : x.run tr with ⟨_ | a, trMid, hmid⟩ <;> rw [h] at hle hx0 <;> [exact ⟨(hx0 hle).1, fun b hb => by cases hb⟩; (have hx' := hx0 (Trace.le_trans _ _ _ ((f a).run trMid).2.property hle); exact hf trMid a hmid (hx'.2 a rfl) hx'.1 hle)]
theorem PQRkAt.of_id {T tr : ExecTrace} {α : Type} {x : Traceful α} (hx : (x.run tr).2.val = tr) : PQRkAt T tr (fun _ _ => True) x := by intro hJ _; rw [hx]; exact ⟨hJ, fun _ _ => trivial⟩
theorem PQRkAt.pure {T tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop} (a : α) (ha : Q tr a) : PQRkAt T tr Q (Pure.pure a : Traceful α) := by
  intro hJ _; rw [Traceful.run_pure]; refine ⟨hJ, fun b hb => ?_⟩; cases hb; exact ha
theorem PQRkAt.failure {T tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop} : PQRkAt T tr Q (Alternative.failure : Traceful α) := by
  intro hJ _; rw [Traceful.run_failure]; exact ⟨hJ, fun _ hb => by cases hb⟩
theorem PQRkAt.guardP {T tr : ExecTrace} (p : Prop) [Decidable p] : PQRkAt T tr (fun _ _ => p) (_root_.guard p : Traceful Unit) := by unfold _root_.guard; split <;> [ (rename_i hp; exact PQRkAt.pure () hp); exact PQRkAt.failure ]
theorem PQRkAt.guardTrace {T tr : ExecTrace} (p : ExecTrace → Bool) : PQRkAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.guardTrace p) :=
  PQRkAt.of_id (by unfold DY.Libsignal.TripleRatchet.guardTrace; erw [Traceful.run_mk])
theorem PQRkAt.traceLength {T tr : ExecTrace} : PQRkAt T tr (fun _ _ => True) DY.Libsignal.TripleRatchet.traceLength :=
  PQRkAt.of_id (by unfold DY.Libsignal.TripleRatchet.traceLength; erw [Traceful.run_mk])
theorem PQRkAt.genRand {T tr : ExecTrace} (n : Nat) : PQRkAt T tr (fun tr1 r => r = randTerm tr.length n ∧ tr.length < tr1.length ∧ KdfRkSafe T r) (Random.genRand n) := by
  intro hJ _; simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_bind, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
  refine ⟨JRk_append_rand n hJ, fun b hb => ?_⟩; cases hb; refine ⟨rfl, ?_, kdfRkSafe_random T { timestamp := tr.length, size := n }⟩
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; exact Nat.lt_succ_self _
theorem PQRkAt.sendMessage {T tr : ExecTrace} {m : DY.Bytes} (hm : KdfRkSafe T m) : PQRkAt T tr (fun _ _ => True) (Network.sendMessage m) := by
  intro hJ _; rw [CompPresTRExp.run_sendMessage_snd]
  exact ⟨JRk_append_net hm hJ, fun _ _ => trivial⟩
theorem PQRkAt.logEvent {T tr : ExecTrace} (ev : TREvent) (hev : ∀ s pk n seed rIdx src, ev = .SkippedKeyStored s pk n seed rIdx src → KdfRkSafe T seed) :
    PQRkAt T tr (fun _ _ => True) (ProtocolEvent.logEvent ev) := by
  intro hJ _; simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
  exact ⟨JRk_append_ev ev hev hJ, fun _ _ => trivial⟩
theorem PQRkAt.storeLocalState {T tr : ExecTrace} (p : Participant) {st : TRState} (hst : StSafeRk T tr.length st) :
    PQRkAt T tr (fun _ _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro hJ _; simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact ⟨JRk_append_st p hst hJ, fun _ _ => trivial⟩
theorem PQRkAt.getLocalState {T tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQRkAt T tr (fun tr1 st => tr1 = tr ∧ StSafeRk T tr1.length st ∧ KdfRkSafe T st.rk ∧ TRStateStoredAt me st stH T) (PersistentLocalState.getLocalState me stH) := by
  intro hJ hle; rw [CompTrace.getLocalState_tr_snd] at hle ⊢; refine ⟨hJ, fun st hst => ?_⟩; rw [CompTrace.getLocalState_tr_fst] at hst
  rcases he : (tr.at? stH : Option CompTrace.TRStEntry) with _ | ⟨⟨p, st'⟩⟩; · rw [he] at hst; cases hst
  rw [he] at hst; dsimp only at hst; by_cases hp : p = me
  · subst hp; simp only [↓reduceIte] at hst; cases hst; have hsafe := hJ.2.1 _ _ stH he; exact ⟨rfl, hsafe, kdfRkSafe_rk_of_stRkDhsInv hsafe.1 (trStateStoredAt_mono hle he), trStateStoredAt_mono hle he⟩
  · simp only [hp, ↓reduceIte] at hst; cases hst
def SkSafeRk (T : ExecTrace) (e : CompTrace.TREntry) : Prop := ∀ s pk n seed rIdx src, e.ev = .SkippedKeyStored s pk n seed rIdx src → KdfRkSafe T seed
theorem PQRkAt.getEntryTR {T tr : ExecTrace} (evH : Nat) : PQRkAt T tr (fun _ => SkSafeRk T) (DY.getEntry evH : Traceful CompTrace.TREntry) := by
  intro hJ _; simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; refine ⟨hJ, fun e he s pk n seed rIdx src hev => ?_⟩
  have hlog : tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) evH := by
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; have he' : (tr.at? evH : Option CompTrace.TREntry) = some e := he; rw [he']; rcases e with ⟨ev⟩; dsimp only at hev; rw [hev]
  exact hJ.2.2 evH s pk n seed rIdx src hlog
theorem PQRkAt.receiveMessage {T tr : ExecTrace} (msgH : Nat) : PQRkAt T tr (fun _ b => b.AttackerKnows tr ∧ KdfRkSafe T b) (Network.receiveMessage msgH) := by
  intro hJ hle; rw [CompTrace.receiveMessage_snd] at hle ⊢; refine ⟨hJ, fun a ha => ?_⟩; rw [CompTrace.receiveMessage_fst] at ha
  rcases hat : (tr.at? msgH : Option CompTrace.NetEntry) with _ | ⟨⟨b⟩⟩ <;> rw [hat] at ha <;>
    [cases ha; (injection ha with ha; subst ha; have hak := Trace.MessageSentAt_implies_AttackerKnows tr b msgH ((Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1 tr b msgH).mpr hat); exact ⟨hak, attackerKnows_imp_kdfRkSafe hle hJ.1 hak⟩)]
theorem PQRkAt.receiveSignalMsg {T tr : ExecTrace} (msgH : Nat) :
    PQRkAt T tr (fun _ msg => KdfRkSafe T msg.pqRatchet ∧ msg.ratchetKey.AttackerKnows tr ∧ ∃ t : DY.Bytes, t.AttackerKnows tr ∧ parseTrSignalMsg t = some msg) (DY.Libsignal.TripleRatchet.receiveSignalMsg msgH) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; refine PQRkAt.bind (PQRkAt.receiveMessage msgH) fun _ t _ ⟨ht_ak, ht_s⟩ => ?_
  rcases hp : parseTrSignalMsg t with _ | msg; · exact PQRkAt.failure
  have hf := parseTrSignalMsg_fields_rk ht_ak ht_s hp; exact PQRkAt.bind (PQRkAt.guardP _) fun _ _ _ _ => PQRkAt.pure msg ⟨hf.1, hf.2, t, ht_ak, hp⟩
theorem PQRkAt.verifyMacAndDecrypt {T tr : ExecTrace} (st : TRState) (msg : TRSignalMsg) (pqSalt seed : DY.Bytes) :
    PQRkAt T tr (fun _ _ => msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire) (DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  refine PQRkAt.bind (PQRkAt.guardP _) fun _ _ _ hmac hJ _ => ?_
  dsimp only [liftM, monadLift, MonadLift.monadLift]; erw [Traceful.run_mk]
  exact ⟨hJ, fun _ _ => hmac⟩
theorem PQRkAt.logSkippedKeys {T : ExecTrace} (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32) {tr : ExecTrace}, KdfRkSafe T ck → PQRkAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k)
  | 0, _, _, _, _ => by simp only [DY.Libsignal.TripleRatchet.logSkippedKeys]; exact PQRkAt.pure () trivial
  | k + 1, ck, n, _, hck => by
    simp only [DY.Libsignal.TripleRatchet.logSkippedKeys]
    refine PQRkAt.bind (PQRkAt.logEvent _ ?_) fun _ _ _ _ => PQRkAt.logSkippedKeys s pk rIdx src k _ _ ((kdfRkSafe_kdfCk_fst_iff ck).mpr hck)
    intro s' pk' n' seed' rIdx' src' h; cases h; exact (kdfRkSafe_kdfCk_snd_iff ck).mpr hck
theorem PQRkAt.logMessageKeyAndStore {T tr : ExecTrace} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx p : Nat) {st : TRState} (hst : StSafeRk T tr.length st) :
    PQRkAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx p st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact PQRkAt.bind (PQRkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun tr2 _ hle2 _ =>
    PQRkAt.storeLocalState me (stSafeRk_mono (Trace.length_le _ _ hle2) hst)
theorem stSafeRk_setRecvChain {T : ExecTrace} {bound : Nat} {st : TRState} {c : RecvChain} {spqr' : DY.Bytes}
    (hst : StSafeRk T bound st) (hc : KdfRkSafe T c.chainKey) (hspqr : KdfRkSafe T spqr') : StSafeRk T bound { st with recv := setRecvChain st.recv c, spqr := spqr' } := by
  refine ⟨hst.1, hst.2.1, hspqr, fun c0 hc0 => ?_⟩; unfold setRecvChain at hc0; rw [List.mem_map] at hc0; obtain ⟨c1, hc1, rfl⟩ := hc0
  by_cases hk : (c1.ratchetKey == c.ratchetKey) = true <;> [simp only [hk, ↓reduceIte]; simp only [hk, Bool.false_eq_true, ↓reduceIte]] <;> [exact hc; exact hst.2.2.2 c1 hc1]
def PreVerifyRk (T : ExecTrace) (bound : Nat) (st0 : TRState) (pk : DY.Bytes) (st : TRState) (c : RecvChain) : Prop :=
  StRkDhsInv T bound st ∧ KdfRkSafe T st.cks ∧ KdfRkSafe T st.spqr ∧ (∀ c0 ∈ st.recv, KdfRkSafe T c.chainKey → KdfRkSafe T c0.chainKey) ∧
  (KdfRkSafe T c.chainKey ∨ c.chainKey = (createChain st0.rk pk st0.dhs).2) ∧ st.peerIk = st0.peerIk ∧ st.myIk = st0.myIk
theorem PQRkAt.dhRatchetStep {T tr : ExecTrace} {st0 : TRState} {pk : DY.Bytes} (hst0 : StSafeRk T tr.length st0) (hstored0 : ∃ p idx, TRStateStoredAt p st0 idx T) (hpk : ValidRkPk T pk) :
    PQRkAt T tr (fun tr1 (r : TRState × RecvChain) => PreVerifyRk T tr1.length st0 pk r.1 r.2) (DY.Libsignal.TripleRatchet.dhRatchetStep st0 pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]; refine PQRkAt.bind (PQRkAt.guardP _) fun tr1 _ hle1 _ => ?_
  have hst1 := stSafeRk_mono (Trace.length_le _ _ hle1) hst0; rcases hst1.1 with ⟨hrk0, t_old, ht_old, hdhs0, _⟩
  rcases hc1 : createChain st0.rk pk st0.dhs with ⟨rk1, ckr⟩; dsimp only
  have hrk1_eq : rk1 = (createChain st0.rk pk (randTerm t_old 32)).1 := by rw [← hdhs0, hc1]
  have hckr_eq : ckr = (createChain st0.rk pk st0.dhs).2 := by rw [hc1]
  have hrk1 : RkTree T rk1 := hrk1_eq ▸ RkTree.create t_old hrk0 hpk
  refine PQRkAt.bind (PQRkAt.genRand 32) fun tr2 dhs _ ⟨hdhs_eq, ht2_lt, _⟩ => ?_
  rcases hc2 : createChain rk1 pk dhs with ⟨rk2, cks⟩; dsimp only
  have hrk2_eq : rk2 = (createChain rk1 pk (randTerm tr1.length 32)).1 := by rw [← hdhs_eq, hc2]
  have hrk2 : RkTree T rk2 := hrk2_eq ▸ RkTree.create tr1.length hrk1 hpk
  have hcks : KdfRkSafe T cks := by
    obtain ⟨p0, idx0, hst0_at⟩ := hstored0
    have hstep : KdfRkSafe T (createChain rk1 pk dhs).2 := KdfRkSafe.kdfExtract_step ⟨st0.rk, pk, t_old, tr1.length, ht_old, .inl ⟨p0, st0, idx0, hst0_at, rfl⟩, by rw [hdhs_eq, hrk1_eq]; rfl⟩
    rw [hc2] at hstep; exact hstep
  refine PQRkAt.pure _ ⟨⟨hrk2, tr1.length, ht2_lt, hdhs_eq, .inr ⟨rk1, pk, hrk2_eq⟩⟩, hcks, hst1.2.2.1, ?_, .inr hckr_eq, rfl, rfl⟩
  intro c0 hc0 hckr_s; have hmem := List.mem_of_mem_drop hc0; rw [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | rfl <;> [exact hst1.2.2.2 c0 hmem; exact hckr_s]
theorem PQRkAt.ensureReceiverChain {T tr : ExecTrace} {st0 : TRState} {pk : DY.Bytes} (hst0 : StSafeRk T tr.length st0) (hstored0 : ∃ p idx, TRStateStoredAt p st0 idx T) (hpk : ValidRkPk T pk) :
    PQRkAt T tr (fun tr1 (r : TRState × RecvChain × Bool) => PreVerifyRk T tr1.length st0 pk r.1 r.2.1) (DY.Libsignal.TripleRatchet.ensureReceiverChain st0 pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · rename_i c hrc; refine PQRkAt.pure _ ⟨hst0.1, hst0.2.1, hst0.2.2.1, fun c0 hc0 _ => hst0.2.2.2 c0 hc0, .inl ?_, rfl, rfl⟩
    unfold recvChainFor at hrc; split at hrc
    · rename_i c0 hfind; injection hrc with hrc; injection hrc with hrc _; subst hrc; exact hst0.2.2.2 c0 (List.mem_of_find?_eq_some hfind)
    · split at hrc <;> [cases hrc; (injection hrc with hrc; injection hrc with _ hb; cases hb)]
  · refine PQRkAt.bind (PQRkAt.dhRatchetStep hst0 hstored0 hpk) fun _ ⟨st', c⟩ _ hr => PQRkAt.pure _ hr
  · exact PQRkAt.failure
theorem PQRkAt.messageEncryptAbort {T tr : ExecTrace} (me : Participant) (stH : Nat) : PQRkAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; exact PQRkAt.bind (PQRkAt.getLocalState me stH) fun _ _ _ _ => PQRkAt.bind (PQRkAt.genRand 32) fun _ _ _ _ => PQRkAt.failure
theorem PQRkAt.messageEncrypt {T tr : ExecTrace} (me : Participant) (stH coinsLen pqIdx : Nat) : PQRkAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine PQRkAt.bind (PQRkAt.getLocalState me stH) fun tr1 st _ ⟨_, hst, _, _⟩ => PQRkAt.bind (PQRkAt.guardP _) fun tr2 _ hle2 _ =>
    PQRkAt.bind (PQRkAt.genRand 32) fun tr3 m hle3 ⟨_, _, hm⟩ => PQRkAt.bind (PQRkAt.genRand coinsLen) fun tr4 coins hle4 ⟨_, _, hcoins⟩ => ?_
  rcases hspqr : Spqr.spqrSend st.spqr coins with ⟨spqr', key, pqMsg⟩; dsimp only
  have hspqr' : KdfRkSafe T spqr' := by have := kdfRkSafe_spqrSend_state hst.2.2.1 hcoins; rw [hspqr] at this; exact this
  have hkey : KdfRkSafe T key := by have := kdfRkSafe_spqrSend_key T st.spqr coins; rw [hspqr] at this; exact this
  have hpqMsg : KdfRkSafe T pqMsg := by have := kdfRkSafe_spqrSend_msg T st.spqr coins; rw [hspqr] at this; exact this
  refine PQRkAt.bind (PQRkAt.sendMessage hkey) fun tr5 _ hle5 _ => ?_
  rcases hck : kdfCk st.cks with ⟨ck', seed⟩; dsimp only
  have hck' : KdfRkSafe T ck' := by have := (kdfRkSafe_kdfCk_fst_iff st.cks).mpr hst.2.1; rw [hck] at this; exact this
  refine PQRkAt.bind (PQRkAt.receiveMessage pqIdx) fun tr6 pqSalt hle6 _ => PQRkAt.bind (PQRkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun tr7 _ hle7 _ => ?_
  have hle17 : tr1 ≤ tr7 := Trace.le_trans _ _ _ hle2 (Trace.le_trans _ _ _ hle3 (Trace.le_trans _ _ _ hle4 (Trace.le_trans _ _ _ hle5 (Trace.le_trans _ _ _ hle6 hle7))))
  have hst' : StSafeRk T tr7.length { st with cks := ck', ns := st.ns + 1, spqr := spqr' } := ⟨stRkDhsInv_mono (Trace.length_le _ _ hle17) hst.1, hck', hspqr', hst.2.2.2⟩
  refine PQRkAt.bind (PQRkAt.logMessageKeyAndStore me _ _ _ _ _ _ _ hst') fun _ _ _ _ => ?_
  exact PQRkAt.sendMessage (KdfRkSafe.concat (KdfRkSafe.trWireMsg
    { version := messageVersion, senderRatchetKey := dhPk st.dhs, counter := st.ns, previousCounter := st.pn,
      ciphertext := SymEnc.symEnc (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv m, pqRatchet := pqMsg, encodingVariation := DY.TrWire.canonicalVariation }
    (kdfRkSafe_dhs_of_stRkDhsInv hst.1).2 (KdfRkSafe.symEnc hm) hpqMsg) (kdfRkSafe_trunc8 T _))
theorem PQRkAt.exposeKey {T tr : ExecTrace} (me : Participant) (stH : Nat) (k : KeyComponent) : PQRkAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey; refine PQRkAt.bind (PQRkAt.getLocalState me stH) fun _ st _ ⟨_, hst, hrk_s, _⟩ => ?_
  cases k with
  | rk => exact PQRkAt.bind (PQRkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQRkAt.sendMessage hrk_s
  | dhs => exact PQRkAt.bind (PQRkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQRkAt.sendMessage (kdfRkSafe_dhs_of_stRkDhsInv hst.1).1
  | cks => exact PQRkAt.bind (PQRkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQRkAt.sendMessage hst.2.1
  | ckr pk => dsimp only; rcases hfind : findRecvChain st.recv pk with _ | c <;> [exact PQRkAt.failure; exact PQRkAt.bind (PQRkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQRkAt.sendMessage (hst.2.2.2 c (List.mem_of_find?_eq_some hfind))]
theorem PQRkAt.exposeSpqr {T tr : ExecTrace} (me : Participant) (stH : Nat) : PQRkAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  exact PQRkAt.bind (PQRkAt.getLocalState me stH) fun _ st _ ⟨_, hst, _, _⟩ => PQRkAt.bind (PQRkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQRkAt.sendMessage hst.2.2.1
theorem PQRkAt.exposeSkipped {T tr : ExecTrace} (evH : Nat) : PQRkAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped; refine PQRkAt.bind (PQRkAt.getEntryTR evH) fun _ ⟨ev⟩ _ he => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src => exact PQRkAt.bind (PQRkAt.guardTrace _) fun _ _ _ _ => PQRkAt.bind (PQRkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQRkAt.sendMessage (he s pk n seed rIdx src rfl)
  | _ => exact PQRkAt.failure
theorem PQRkAt.messageDecryptSkipped {T tr : ExecTrace} (me : Participant) (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    PQRkAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine PQRkAt.bind (PQRkAt.getLocalState me stH) fun tr1 st _ ⟨_, hst, _, _⟩ => PQRkAt.bind (PQRkAt.receiveSignalMsg msgH) fun tr2 msg hle2 ⟨hmsg_pq, _, _⟩ =>
    PQRkAt.bind (PQRkAt.getEntryTR evH) fun tr3 ⟨ev⟩ hle3 _ => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    refine PQRkAt.bind (PQRkAt.guardP _) fun tr4 _ hle4 _ => PQRkAt.bind (PQRkAt.guardTrace _) fun tr5 _ hle5 _ => ?_
    rcases hrecv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · exact PQRkAt.failure
    refine PQRkAt.bind (PQRkAt.sendMessage (kdfRkSafe_spqrRecv_key hrecv)) fun tr6 _ hle6 _ => PQRkAt.bind (PQRkAt.receiveMessage pqIdx) fun tr7 pqSalt hle7 _ =>
      PQRkAt.bind (PQRkAt.verifyMacAndDecrypt st msg pqSalt seed) fun tr8 _ hle8 _ => PQRkAt.bind (PQRkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun tr9 _ hle9 _ =>
      PQRkAt.bind (PQRkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun tr10 _ hle10 _ => ?_
    have hle1_10 : tr1 ≤ tr10 := Trace.le_trans _ _ _ hle2 (Trace.le_trans _ _ _ hle3 (Trace.le_trans _ _ _ hle4 (Trace.le_trans _ _ _ hle5
      (Trace.le_trans _ _ _ hle6 (Trace.le_trans _ _ _ hle7 (Trace.le_trans _ _ _ hle8 (Trace.le_trans _ _ _ hle9 hle10)))))))
    exact PQRkAt.logMessageKeyAndStore me _ _ _ _ _ _ _ ⟨stRkDhsInv_mono (Trace.length_le _ _ hle1_10) hst.1, hst.2.1, kdfRkSafe_spqrRecv_state hrecv hst.2.2.1 hmsg_pq, hst.2.2.2⟩
  | _ => exact PQRkAt.failure
theorem PQRkAt.messageDecrypt {T tr : ExecTrace} (hreach : ReachableTrace tr) (hle_tr_T : tr ≤ T) (me : Participant) (stH msgH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    PQRkAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  intro hJ_init hle_end; refine (?_ : PQRkAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx)) hJ_init hle_end
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine PQRkAt.bind (PQRkAt.getLocalState me stH) fun tr1 st0 _ ⟨rfl, hst0, _, hstored0⟩ =>
    PQRkAt.bind (PQRkAt.receiveSignalMsg msgH) fun tr2 msg hle2 ⟨hmsg_pq, hrk_ak, t, ht_ak, hparse⟩ => ?_
  have hst0_tr2 : StSafeRk T tr2.length st0 := stSafeRk_mono (Trace.length_le _ _ hle2) hst0
  have hpk_valid : ValidRkPk T msg.ratchetKey := .inr (DY.Bytes.AttackerKnows_le _ _ T hle_tr_T hrk_ak)
  refine PQRkAt.bind (PQRkAt.ensureReceiverChain hst0_tr2 ⟨me, stH, hstored0⟩ hpk_valid) fun tr3 ⟨st, c, ratcheted⟩ hle3 hpre => ?_
  dsimp only; rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · exact PQRkAt.failure
  dsimp only; rcases hrecv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · exact PQRkAt.failure
  refine PQRkAt.bind (PQRkAt.sendMessage (kdfRkSafe_spqrRecv_key hrecv)) fun tr4 _ hle4 _ =>
    PQRkAt.bind (PQRkAt.receiveMessage pqIdx) fun tr5 pqSalt hle5 _ => PQRkAt.bind (PQRkAt.verifyMacAndDecrypt st msg pqSalt seed) fun tr6 m hle6 hmac => ?_
  have hcons_iff := consumeMessageKey_eq_and_kdfRkSafe (T := T) hcons
  have hck_safe : KdfRkSafe T c.chainKey := by
    rcases messageDecrypt_dhPk_or_seed_attackerKnows hreach ht_ak hparse hmac hcons_iff.1 with ⟨a, hrk_dhPk⟩ | hseed_ak
    · rcases hpre.2.2.2.2.1 with hck_s | hck_eq; · exact hck_s
      obtain ⟨_, t_old, _, hdhs0, _⟩ := hst0.1; rw [hck_eq, hrk_dhPk, hdhs0]; exact KdfRkSafe.kdfExtract_dhPk ⟨me, st0, stH, a, t_old, hstored0, rfl⟩
    · exact hcons_iff.2.1.mp (attackerKnows_imp_kdfRkSafe hle_tr_T hJ_init.1 hseed_ak)
  have hle3_6 : tr3 ≤ tr6 := Trace.le_trans _ _ _ hle4 (Trace.le_trans _ _ _ hle5 hle6)
  have hst_safe : StSafeRk T tr6.length st := ⟨stRkDhsInv_mono (Trace.length_le _ _ hle3_6) hpre.1, hpre.2.1, hpre.2.2.1, fun c0 hc0 => hpre.2.2.2.1 c0 hc0 hck_safe⟩
  have hc'_safe : KdfRkSafe T c'.chainKey := hcons_iff.2.2.mpr hck_safe
  have hspqr'_safe : KdfRkSafe T spqr' := kdfRkSafe_spqrRecv_state hrecv hpre.2.2.1 hmsg_pq
  have htail : ∀ {tr_t : ExecTrace}, tr6 ≤ tr_t → PQRkAt T tr_t (fun _ _ => True) (do
      DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stH c.chainKey c.index (msg.counter.toNat - c.index.toNat)
      ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) KeyDir.receiver seed pqSalt msg.counter c.rIdx stH
        { st with recv := setRecvChain st.recv c', spqr := spqr' }) := fun {tr_t} hle_t =>
    PQRkAt.bind (PQRkAt.logSkippedKeys _ _ _ _ _ _ _ hck_safe) fun tr_a _ hle_a _ =>
      PQRkAt.bind (PQRkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun tr_b _ hle_b _ =>
      PQRkAt.logMessageKeyAndStore me _ _ _ _ _ _ _
        (stSafeRk_setRecvChain (stSafeRk_mono (Trace.length_le _ _ (Trace.le_trans _ _ _ hle_t (Trace.le_trans _ _ _ hle_a hle_b))) hst_safe) hc'_safe hspqr'_safe)
  split
  · refine PQRkAt.bind (PQRkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun tr7 _ hle7 _ =>
      PQRkAt.bind (PQRkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun tr8 _ hle8 _ => htail (Trace.le_trans _ _ _ hle7 hle8)
  · exact htail (Trace.le_refl _)
theorem JRk_preserves_aliceStart {T tr : ExecTrace} (hle_tr_T : tr ≤ T) (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles) (hJ : JRk T tr) :
    JRk T ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]; refine CompTrace.bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hJ (JRk_append_rand 32 hJ) fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ hspk _ _ _ _ _ _ _ _ => ?_
  let hs := CompPresPQXDH.aliceOut tr ikA ikBPk spkPk pqPk opk; let tr1 := tr.append (RndE 32); let tr2 := tr1.append (RndE 32); let dhsA := randTerm tr2.length 32
  let stA : TRState :=
    { peer := b, myIk := DY.Libsignal.PQXDH.serializedIk hs.ikA, peerIk := DY.Libsignal.PQXDH.serializedIk hs.ikB,
      rk := (createChain hs.keys.rk hs.spk dhsA).1, dhs := dhsA, cks := (createChain hs.keys.rk hs.spk dhsA).2,
      ns := 0, pn := 0,
      sid := Concat.concat (DiffieHellman.dhPk dhsA) hs.keys.rk,
      initiator := true, rIdx := 1,
      recv := [{ ratchetKey := hs.spk, chainKey := hs.keys.ck, index := 0, rIdx := 1 }], spqr := Spqr.spqrInit hs.keys.pqr spqrA2B }
  let tr3 := tr2.append (RndE 32); let tr4 := tr3.append (NetE hs.ek); let tr5 := tr4.append (NetE hs.ct)
  let tr6 := tr5.append (EvE (PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys))
  let tr7 := tr6.append (TREvE (TREvent.InitSession a b (DiffieHellman.dhPk dhsA) hs.spk))
  let tr8 := tr7.append (CEvE (ComposedEvent.HandshakeSession (stA.sessionInfo a) tr5.length))
  have htl : ∀ {α : Type} (g : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= g).run t).2.val = ((g t.length).run t).2.val := fun g t => by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [CompTrace.run_bind_snd, Traceful.run_mk]
  rw [CompTrace.run_genRand_bind_snd]; dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, htl,
    CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  change JRk T (tr8.append (TRStE a stA))
  have hJ3 : JRk T tr3 := JRk_append_rand 32 (JRk_append_rand 32 (JRk_append_rand 32 hJ))
  have hJ4 : JRk T tr4 := JRk_append_net (.dhPk (kdfRkSafe_random T _) (.inl ⟨tr.length, rfl⟩)) hJ3
  have hJ5 : JRk T tr5 := JRk_append_net (kdfRkSafe_kemEncap_fst T pqPk _) hJ4
  have hJ8 : JRk T tr8 := jrk_append_cEv _ (JRk_append_ev _ (by intro _ _ _ _ _ _ h; cases h) (jrk_append_pqEv _ hJ5))
  have hspk_valid : ValidRkPk T hs.spk := .inr (DY.Bytes.AttackerKnows_le _ tr T hle_tr_T (CompTrace.NetMsgAt.attackerKnows hspk))
  have hrk0 : RkTree T hs.keys.rk := by dsimp [hs, CompPresPQXDH.aliceOut, DY.Libsignal.PQXDH.aliceAgreement]; exact RkTree.pqxdh _ _ _ _ _
  have hrkA : RkTree T stA.rk := RkTree.create tr2.length hrk0 hspk_valid
  have hlen : tr2.length < tr8.length := by simp [tr8, tr7, tr6, tr5, tr4, tr3, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  have hcks : KdfRkSafe T stA.cks := by dsimp [stA, hs, CompPresPQXDH.aliceOut, DY.Libsignal.PQXDH.aliceAgreement]; exact kdfRkSafe_alice_cks T _ _ _
  have hspqr : KdfRkSafe T stA.spqr := .spqrInit { authKey := hs.keys.pqr, params := spqrA2B } (by dsimp [hs, CompPresPQXDH.aliceOut, DY.Libsignal.PQXDH.aliceAgreement]; exact kdfRkSafe_pqxdhKdf_pqr T _) (kdfRkSafe_literal T _)
  refine JRk_append_st a ⟨⟨hrkA, tr2.length, hlen, rfl, .inr ⟨hs.keys.rk, hs.spk, rfl⟩⟩, hcks, hspqr, fun c hc => ?_⟩ hJ8
  rw [List.mem_singleton] at hc; subst hc; dsimp [hs, CompPresPQXDH.aliceOut, DY.Libsignal.PQXDH.aliceAgreement]; exact kdfRkSafe_pqxdhKdf_ck T _
theorem JRk_logSkippedKeys_preserves {T : ExecTrace} (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) : ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32) (tr : ExecTrace), KdfRkSafe T ck →
      JRk T tr → JRk T ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k).run tr).2.val
  | 0, _, _, _, _, hJ => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [Traceful.run_pure]; exact hJ
  | k + 1, ck, n, tr, hck, hJ => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    refine JRk_logSkippedKeys_preserves s pk rIdx src k (kdfCk ck).1 (n + 1) _ ((kdfRkSafe_kdfCk_fst_iff ck).mpr hck) (JRk_append_ev _ ?_ hJ)
    intro _ _ _ _ _ _ h; cases h; exact (kdfRkSafe_kdfCk_snd_iff ck).mpr hck
theorem JRk_bobStart_commit {T tr : ExecTrace} (hJ : JRk T tr)
    (b a : Participant) (sB sS sQ : DY.Bytes) (o : Option DY.Bytes) (ikA ek ct : DY.Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (dhs spqr' seed pqSalt m : DY.Bytes) (c' : RecvChain)
    (hck_safe : KdfRkSafe T (CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS).chainKey)
    (hst_safe : StSafeRk T tr.length { CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs with
      recv := setRecvChain (CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs).recv c', spqr := spqr' }) :
    let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    JRk T (((do
      let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
      ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys)
      if true then
        ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
        ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
      ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
      let skipped := msg.counter.toNat - c.index.toNat; let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
      DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx
        { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr).2.val) := by
  intro st c; let doneIdx := tr.length
  have htl : ∀ {α : Type} (g : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= g).run t).2.val = ((g t.length).run t).2.val := fun g t => by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let tr₁ := tr.append (EvE (.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys))
  let tr₂ := tr₁.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
  let tr₃ := tr₂.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))); let tr₄ := tr₃.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
  have hJ₄ : JRk T tr₄ := jrk_append_cEv _ (JRk_append_ev _ (by intro _ _ _ _ _ _ h; cases h) (JRk_append_ev _ (by intro _ _ _ _ _ _ h; cases h) (jrk_append_pqEv _ hJ)))
  have hle₀₄ : tr ≤ tr₄ := Trace.le_trans _ _ _ (Trace.append_le tr _) (Trace.le_trans _ _ _ (Trace.append_le tr₁ _) (Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le tr₃ _)))
  let skipped := msg.counter.toNat - c.index.toNat; let childIdx := tr₄.length + skipped + 2
  let skipAct := DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
  let restAct : Unit → Traceful Nat := fun _ => do
    ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
    DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }
  rw [htl, CompPresTRExp.run_logEvent_bind_snd]; simp only [↓reduceIte]
  rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, htl]
  change JRk T (((skipAct >>= restAct).run tr₄).2.val); rw [CompInv.CompPresBob.run_logSkippedKeys_bind_snd]
  let tr₅ := (skipAct.run tr₄).2.val; have hle₄₅ : tr₄ ≤ tr₅ := (skipAct.run tr₄).2.property
  have hJ₅ : JRk T tr₅ := JRk_logSkippedKeys_preserves (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx skipped c.chainKey c.index tr₄ hck_safe hJ₄
  let tr₆ := tr₅.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
  let tr₇ := tr₆.append (TREvE (.MessageKey (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx))
  have hJ₇ : JRk T tr₇ := JRk_append_ev _ (by intro _ _ _ _ _ _ h; cases h) (JRk_append_ev _ (by intro _ _ _ _ _ _ h; cases h) hJ₅)
  have hle₀₇ : tr ≤ tr₇ := Trace.le_trans _ _ _ hle₀₄ (Trace.le_trans _ _ _ hle₄₅ (Trace.le_trans _ _ _ (Trace.append_le tr₅ _) (Trace.append_le tr₆ _)))
  dsimp only [restAct]; rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logMessageKeyAndStore_snd]
  exact JRk_append_st b (stSafeRk_mono (Trace.length_le _ _ hle₀₇) hst_safe) hJ₇
theorem JRk_preserves_bobStart {T tr : ExecTrace} (_hreach : ReachableTrace tr) (hle_tr_T : tr ≤ T)
    (hinv : SpqrInv tr) (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat) (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (hJ : JRk T tr) :
    JRk T ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]; refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hJ fun sB sS sQ o ikA _ ek ct _ keys _ hspk _ _ _ _ _ _ hbob => ?_
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at mh.msg tr hJ fun raw _ hraw_ak => ?_
  rcases hparse : parseTrSignalMsg raw with _ | msg; · dsimp only; rw [Traceful.run_bind, Traceful.run_failure]; exact hJ
  dsimp only; rw [CompTrace.run_bind_assoc_snd]; refine CompTrace.bind_guardP_at _ tr hJ fun _ => ?_
  refine CompInv.CompPresBob.bind_ensureReceiverChain_bobInitSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey tr hJ fun _ => ?_
  let dhs := CompKeyInversion.rnd tr.length 32; let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
  let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS; let tr₁ := tr.append (RndE 32); have hJ₁ : JRk T tr₁ := JRk_append_rand 32 hJ
  rcases hConsume : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hJ₁
  dsimp only; rcases hSpqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hJ₁
  dsimp only; have hf_msg := parseTrSignalMsg_fields_rk hraw_ak (attackerKnows_imp_kdfRkSafe hle_tr_T hJ.1 hraw_ak) hparse
  have hkeys_eq : keys = DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm
      (DY.Libsignal.PQXDH.agree ikA sS) (DY.Libsignal.PQXDH.agree ek sB)
      (DY.Libsignal.PQXDH.agree ek sS) (o.map (DY.Libsignal.PQXDH.agree ek ·))
      ((DY.Libsignal.PQXDH.errToOption (PQKem.kemDecap sQ ct)).getD (PQKem.kemRejKey sQ ct))) := by
    dsimp only [DY.Libsignal.PQXDH.bobAgreement, Option.pure_def] at hbob
    injection hbob with h; exact h.symm
  have hpqr : KdfRkSafe T keys.pqr := by rw [hkeys_eq]; exact kdfRkSafe_pqxdhKdf_pqr T _
  have hspqr' : KdfRkSafe T spqr' := kdfRkSafe_spqrRecv_state hSpqr (.spqrInit { authKey := keys.pqr, params := spqrB2A } hpqr (kdfRkSafe_literal T _)) hf_msg.1
  let tr₂ := tr₁.append (NetE key); have hJ₂ : JRk T tr₂ := JRk_append_net (kdfRkSafe_spqrRecv_key hSpqr) hJ₁
  rw [CompPresTRExp.run_sendMessage_bind_snd]
  change JRk T (((Network.receiveMessage pqIdx >>= fun pqSalt => DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed >>= fun m => _).run tr₂).2.val)
  refine CompTrace.bind_receiveMessage_at pqIdx tr₂ hJ₂ fun pqSalt _ _ => CompInv.CompPresBob.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr₂ hJ₂ fun m _ => ?_
  obtain ⟨t_sS, rfl, ht_sS, _, _⟩ := hinv.stOK b { kind := .signedPrekey, sk := sS } kh.spk hspk
  have hck_safe : KdfRkSafe T c.chainKey := by change KdfRkSafe T (createChain keys.rk msg.ratchetKey _).2; rw [hkeys_eq]; exact kdfRkSafe_alice_cks T _ _ _
  have hc'_safe : KdfRkSafe T c'.chainKey := (consumeMessageKey_eq_and_kdfRkSafe (T := T) hConsume).2.2.mpr hck_safe
  have hpk_valid : ValidRkPk T msg.ratchetKey := .inr (DY.Bytes.AttackerKnows_le _ tr T hle_tr_T hf_msg.2)
  have hrk0 : RkTree T keys.rk := by rw [hkeys_eq]; exact RkTree.pqxdh _ _ _ _ _
  have hrk2 : RkTree T st.rk := RkTree.create tr.length (RkTree.create t_sS hrk0 hpk_valid) hpk_valid
  have ht_lt : t_sS < tr.length := by unfold CompInv.RandAt at ht_sS; rw [Trace.at?_eq_some] at ht_sS; exact ht_sS.1
  have hcks : KdfRkSafe T st.cks := KdfRkSafe.kdfExtract_step ⟨keys.rk, msg.ratchetKey, t_sS, tr.length, ht_lt, .inr ⟨_, congrArg HandshakeKeys.rk hkeys_eq⟩, rfl⟩
  have hlen : tr.length < tr₂.length := by simp [tr₂, tr₁, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hst_base : StSafeRk T tr₂.length st :=
    ⟨⟨hrk2, tr.length, hlen, rfl, .inr ⟨_, msg.ratchetKey, rfl⟩⟩, hcks, .spqrInit { authKey := keys.pqr, params := spqrB2A } hpqr (kdfRkSafe_literal T _),
     fun c0 hc0 => by dsimp [st, CompInv.CompPresBob.bobRatchetedSt] at hc0; rw [List.mem_singleton] at hc0; subst hc0; exact hck_safe⟩
  have hst_final := stSafeRk_setRecvChain hst_base hc'_safe hspqr'
  cases o with
  | none =>
    dsimp only [Option.map]
    exact JRk_bobStart_commit hJ₂ b a sB (randTerm t_sS 32) sQ none ikA ek ct keys msg dhs spqr' seed pqSalt m c' hck_safe hst_final
  | some oSk =>
    dsimp only [Option.map]; rw [CompTrace.run_bind_snd]; unfold DY.Libsignal.PQXDH.guardTrace; erw [Traceful.run_mk]; dsimp only
    by_cases hused : (!opkUsedB tr₂ b (DiffieHellman.dhPk oSk)) = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hused h]; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd]
      exact JRk_bobStart_commit (jrk_append_pqEv _ hJ₂) b a sB (randTerm t_sS 32) sQ (some oSk) ikA ek ct keys msg dhs spqr' seed pqSalt m c' hck_safe (stSafeRk_mono (Trace.length_le _ _ (Trace.append_le _ _)) hst_final)
    · rw [ite_eq_right_iff.mpr fun h => absurd h hused]; dsimp only; exact hJ₂
theorem JRk_reachable {T tr : ExecTrace} (hreach : ReachableTrace tr) (hle : tr ≤ T) : JRk T tr := by
  induction hreach with
  | Base => exact JRk_nil T
  | @Step tr_prev input hPre hReachPre ih =>
    have hprev_le : tr_prev ≤ T := Trace.le_trans _ _ _ ((reachability.step input).snd.run _).2.property hle
    have hJ : JRk T tr_prev := ih hprev_le; have hinv : SpqrInv tr_prev := spqrInv_of_reachable _ hReachPre
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
    · let msg : DY.Bytes := inp
      change JRk T ((Network.sendMessage msg).run tr_prev).2.val
      rw [CompPresTRExp.run_sendMessage_snd]
      exact JRk_append_net (attackerKnows_imp_kdfRkSafe hprev_le hJ.1 hPre) hJ
    · change Participant at inp; change JRk T ((registerIdentity inp).run _).2.val; unfold registerIdentity; refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, hst_snd]
      exact jrk_append_pqSt inp _ (JRk_append_net (kdfRkSafe_vk T _) (JRk_append_net (.dhPk (kdfRkSafe_random T _) (.inl ⟨tr_prev.length, rfl⟩)) (jrk_append_pqEv _ (JRk_append_rand 32 hJ))))
    · rcases inp with ⟨p, skIdx⟩; change JRk T ((registerCorruptIdentity p skIdx).run _).2.val; unfold registerCorruptIdentity
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ => CompTrace.bind_receiveMessage_at skIdx _ hJ fun _ _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, hlog_snd]
      exact jrk_append_pqEv _ (jrk_append_pqEv _ hJ)
    · rcases inp with ⟨b, idStateIdx⟩; change JRk T ((genSignedPrekey b idStateIdx).run _).2.val; unfold genSignedPrekey
      refine CompPresPQXDH.bind_getKey_at b idStateIdx .identity _ hJ fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact JRk_append_net (kdfRkSafe_sign T _ _ _) (JRk_append_net (.dhPk (kdfRkSafe_random T _) (.inl ⟨tr_prev.length, rfl⟩)) (jrk_append_pqSt b _ (jrk_append_pqEv _ (JRk_append_rand 64 (JRk_append_rand 32 hJ)))))
    · rcases inp with ⟨b, idStateIdx⟩; change JRk T ((genPQPrekey b idStateIdx).run _).2.val; unfold genPQPrekey
      refine CompPresPQXDH.bind_getKey_at b idStateIdx .identity _ hJ fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact JRk_append_net (kdfRkSafe_sign T _ _ _) (JRk_append_net (.kemPk (kdfRkSafe_random T _)) (jrk_append_pqSt b _ (jrk_append_pqEv _ (JRk_append_rand 64 (JRk_append_rand 64 hJ)))))
    · change Participant at inp; change JRk T ((genOneTimePrekey inp).run _).2.val; unfold genOneTimePrekey
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd, hst_bind,
        CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact JRk_append_net (.dhPk (kdfRkSafe_random T _) (.inl ⟨tr_prev.length, rfl⟩)) (jrk_append_pqSt inp _ (jrk_append_pqEv _ (JRk_append_rand 32 hJ)))
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩; exact JRk_preserves_aliceStart hprev_le a b idStateIdx regIdxB bh hJ
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩; exact JRk_preserves_bobStart hReachPre hprev_le hinv b a kh regIdxA mh pqIdx spqrMsgIdx hJ
    · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩; exact (PQRkAt.messageEncrypt me stateIdx coinsLen pqIdx hJ hle).1
    · rcases inp with ⟨me, stateIdx⟩; exact (PQRkAt.messageEncryptAbort me stateIdx hJ hle).1
    · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩; exact (PQRkAt.messageDecrypt hReachPre hprev_le me stateIdx msgIdx pqIdx spqrMsgIdx hJ hle).1
    · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩; exact (PQRkAt.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx hJ hle).1
    · rcases inp with ⟨me, stateIdx, k⟩; exact (PQRkAt.exposeKey me stateIdx k hJ hle).1
    · rcases inp with ⟨me, stateIdx⟩; exact (PQRkAt.exposeSpqr me stateIdx hJ hle).1
    · exact (PQRkAt.exposeSkipped inp hJ hle).1
    · rcases inp with ⟨p, stateIdx⟩; change JRk T ((compromiseIK p stateIdx).run _).2.val; unfold compromiseIK
      refine CompPresPQXDH.bind_getKey_at p stateIdx .identity _ hJ fun sk hst => ?_
      obtain ⟨t, rfl, _, _⟩ := hinv.stOK p { kind := .identity, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact JRk_append_net (kdfRkSafe_random T _) (jrk_append_pqEv _ hJ)
    · rcases inp with ⟨b, stateIdx⟩; change JRk T ((compromiseSPK b stateIdx).run _).2.val; unfold compromiseSPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .signedPrekey _ hJ fun sk hst => ?_
      obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .signedPrekey, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact JRk_append_net (kdfRkSafe_random T _) (jrk_append_pqEv _ hJ)
    · rcases inp with ⟨b, stateIdx⟩; change JRk T ((compromisePQSPK b stateIdx).run _).2.val; unfold compromisePQSPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .pqPrekey _ hJ fun sk hst => ?_
      obtain ⟨t, rfl, _, _, _⟩ := hinv.stOK b { kind := .pqPrekey, sk := sk } stateIdx hst
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact JRk_append_net (kdfRkSafe_random T _) (jrk_append_pqEv _ hJ)
    · rcases inp with ⟨b, stateIdx⟩; change JRk T ((compromiseOPK b stateIdx).run _).2.val; unfold compromiseOPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .oneTimePrekey _ hJ fun sk hst => ?_
      obtain ⟨t, rfl, _, _⟩ := hinv.stOK b { kind := .oneTimePrekey, sk := sk } stateIdx hst
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact JRk_append_net (kdfRkSafe_random T _) (jrk_append_pqEv _ hJ)
    · change JRk T ((DY.Libsignal.PQXDH.breakDH).run _).2.val; unfold DY.Libsignal.PQXDH.breakDH
      rw [hlog_snd]; exact jrk_append_pqEv _ hJ
    · change JRk T ((DY.Libsignal.PQXDH.breakKEM).run _).2.val; unfold DY.Libsignal.PQXDH.breakKEM
      rw [hlog_snd]; exact jrk_append_pqEv _ hJ
    · change JRk T ((invertDH inp).run _).2.val; unfold invertDH; refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ => CompTrace.bind_receiveMessage_at inp tr_prev hJ fun pk _ hpk => ?_
      have hpk_safe : KdfRkSafe T (X25519.normalizeX25519Key pk) := kdfRkSafe_x25519Key (attackerKnows_imp_kdfRkSafe hprev_le hJ.1 hpk)
      rcases hdh : DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
      · dsimp only; rw [Traceful.run_failure]; exact hJ
      · dsimp only; rw [CompPresTRExp.run_sendMessage_snd]; rw [dhSkOf_eq_some hdh] at hpk_safe
        exact JRk_append_net ((kdfRkSafe_dhPk_iff sk).mp hpk_safe).1 hJ
    · change JRk T ((invertKEM inp).run _).2.val; unfold invertKEM; refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ => CompTrace.bind_receiveMessage_at inp tr_prev hJ fun pk _ hpk => ?_
      have hpk_safe : KdfRkSafe T pk := attackerKnows_imp_kdfRkSafe hprev_le hJ.1 hpk
      rcases hkem : PQKem.invertKemPublicKey pk with _ | sk
      · dsimp only [liftM, monadLift, MonadLift.monadLift]; rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; exact hJ
      · dsimp only [liftM, monadLift, MonadLift.monadLift]
        rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [CompPresTRExp.run_sendMessage_snd]
        rw [kemPkInvert_eq_some hkem] at hpk_safe
        exact JRk_append_net ((kdfRkSafe_kemPk_iff sk).mp hpk_safe) hJ
    · omega
theorem kdfRkSafe_of_attackerKnows_reachable {T : ExecTrace} (hT : ReachableTrace T) {b : DY.Bytes} (hAK : b.AttackerKnows T) : KdfRkSafe T b :=
  attackerKnows_imp_kdfRkSafe (Trace.le_refl T) (JRk_reachable hT (Trace.le_refl T)).1 hAK

/-! ## Shape-Equality and Attacker-Knowledge Helpers -/
unseal DY.Bytes in
theorem shape_dh_pack_hsb (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (x : DY.DiffieHellman.Dh.SubF DY.Bytes) :
    (gamma' i S g x.pack).shape = ({ pk := (gamma' i S g x.pk).shape, sk := (gamma' i S g x.sk).shape } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
  unfold gamma'; rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g)]; rfl
private theorem attackerKnows_hkdfBlock1_srk {tr : ExecTrace} {prk info : DY.Bytes} (hp : prk.AttackerKnows tr) (hi : info.AttackerKnows tr) : (hkdfBlock1 prk info).AttackerKnows tr :=
  KdfExtract.attacker_knows_kdfExtract prk _ tr hp (Concat.attacker_knows_concat info (litByte 1) tr hi (Literal.attacker_knows_literalToBytes _ tr))
private theorem attackerKnows_hkdfBlock2_srk {tr : ExecTrace} {prk info : DY.Bytes} (hp : prk.AttackerKnows tr) (hi : info.AttackerKnows tr) : (hkdfBlock2 prk info).AttackerKnows tr :=
  KdfExtract.attacker_knows_kdfExtract prk _ tr hp (Concat.attacker_knows_concat _ _ tr (attackerKnows_hkdfBlock1_srk hp hi) (Concat.attacker_knows_concat info (litByte 2) tr hi (Literal.attacker_knows_literalToBytes _ tr)))
theorem attackerKnows_createChain_of_prk {tr : ExecTrace} {rk pk sk : DY.Bytes} (hprk : (hmac rk (DiffieHellman.dh (X25519.normalizeX25519Key pk) sk)).AttackerKnows tr) :
    (createChain rk pk sk).1.AttackerKnows tr ∧ (createChain rk pk sk).2.AttackerKnows tr :=
  have hinfo : (lit "WhisperRatchet").AttackerKnows tr := Literal.attacker_knows_literalToBytes _ tr
  ⟨attackerKnows_hkdfBlock1_srk hprk hinfo, attackerKnows_hkdfBlock2_srk hprk hinfo⟩
theorem eq_randTerm32_of_shape_eq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (t : Nat) {u : DY.Bytes} (hsh : (gamma' i S g (randTerm t 32)).shape = (gamma' i S g u).shape) : randTerm t 32 = u := by
  rw [termShapeId_randTerm32 t i S g] at hsh; exact (view?_random32_shape_eq_some_inv i S g u t (hsh ▸ DY.BytesView.view_pack (SubF := DY.Random.Random) { timestamp := t, size := 32 })).symm
section UnsealedSection3Helpers
unseal DY.Bytes
theorem trStateStoredAt_of_mem_availableStates {r₀ : ProtocolSetup} {ms : List Move} {st : TRState} (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms)) : ∃ p j, TRStateStoredAt p st j (runTraceMoves r₀ ms) := by
  unfold availableStates storedStates DY.ExecTrace.getLocalStateAt at hst; obtain ⟨⟨p, st'⟩, hls, rfl⟩ := List.mem_map.mp hst; obtain ⟨j, _, he⟩ := List.mem_filterMap.mp hls
  simp only [Option.map_eq_some_iff] at he; obtain ⟨⟨⟨p', st''⟩⟩, hat, heq⟩ := he; cases heq; exact ⟨p, j, hat⟩
end UnsealedSection3Helpers
end Symbolic.Swarm.CREF.TR.G1
