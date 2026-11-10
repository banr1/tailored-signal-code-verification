/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
import Init.Data.String.Defs
import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import Comparse.Basic
import DY.Comparse
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
public import Symbolic.Specifications.Refinement.Concretization
public import Symbolic.Specifications.Refinement.ModelTraces
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import VCVio.Prelude.Core
import Symbolic.Proofs.Tests.CliNonvacuity.Witness -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.Comparse.Basic
import Symbolic.DYBridge.DY.Comparse
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
# Trace-Randomness Constructors, Serialization, and `TRand` Primitives

Defines `RandAt`, `MemoRandAt`, `TermRandAt`, and `TraceEntriesRand`, proves constructor,
attacker-knowledge, and Comparse serialization preservation (`termRandAt_serialize_tr`,
`termRandAt_serialize_pq`), and provides `TRand` combinators for composed protocol transitions.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet
  (SessionInfo KeyDir KeyComponent RecvChain TRState TREvent TRSignalMsg parseTrSignalMsg
   lit hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 kdfRk createChain kdfCk chainKeyAt spqrB2A
   trMsgKeys computeMac trHonestWireMsg findRecvChain setRecvChain recvChainFor consumeMessageKey)
open DY.Libsignal.PQXDH
  (KeyKind PQXDHState PQXDHEvent BundleHandles BobKeyHandles PreKeyMsgHandles
   HandshakeKeys AliceHandshakeOut BobHandshakeOut zeroSalt pqxdhLabel
   serializedIk agree pqxdhIkm pqxdhKdf aliceAgreement bobAgreement extractDhSecretKey)
open DY.Libsignal.Composed (ComposedEvent aliceStart bobStart reachability)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber (kemDecap_eq_some_iff assumedInjective_eq_true_iff)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myInterp length_hmacWith_32 length_myInterp_dhPk length_myInterp_dh le_length_myInterp_aesEnc
   length_myInterp_kyberEncap_take length_myInterp_kyberEncap_drop)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost ConcretizedTerm
   node opaqueNode spqrKeyNode
   concretizeRandom concretizeLit concretizeConcat concretizeDhPk concretizeDh
   concretizeKdf concretizeSym concretizeTrunc concretizeVariant
   concretizeKemPk concretizeKemEncap concretizeKemSS concretizeKemRej concretizeVk concretizeSign
   concretizeSpqrInit concretizeSpqrSendState concretizeSpqrSendKey concretizeSpqrSendMsg
   concretizeSpqrRecvState concretizeSpqrRecvKey concretizeSpqrChainKey concretizeTrWire
   concretizeAll gamma' gamma randTerm assumedInjective)

/-! ## `RandAt`, `MemoRandAt`, and `TermRandAt` Constructor Lemmas -/

def RandAt (tr : ExecTrace) (ts sz : Nat) : Prop :=
  (tr.at? ts : Option DY.Random.ExecEntryT) = some ⟨sz⟩

theorem RandAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {ts sz : Nat} (h : RandAt tr ts sz) :
    RandAt tr' ts sz := by
  have hat := DY.Trace.at?_le (EntryT := DY.Random.ExecEntryT) tr tr' ts hle
  unfold RandAt at h ⊢; rw [h] at hat; exact hat

def MemoRandAt (tr : ExecTrace) (ct : ConcretizedTerm) : Prop :=
  ∀ (t sh : DY.Bytes) (v : HwBytes) (r : DY.Random.Random DY.Bytes),
    (t, sh, v) ∈ ct.memo → t.view? DY.Random.Random = some r → RandAt tr r.timestamp r.size

def TermRandAt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (b : DY.Bytes) : Prop :=
  MemoRandAt tr (gamma' i S g b)

theorem TermRandAt.mono {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : DY.Bytes} (h : TermRandAt i S g tr b) :
    TermRandAt i S g tr' b :=
  fun t sh v r hm hv => RandAt.mono hle (h t sh v r hm hv)

private theorem memoRandAt_node {tr : ExecTrace} {v : HwBytes} {self sh : DY.Bytes}
    {cs : List ConcretizedTerm} (hself : self.view? DY.Random.Random = none) :
    MemoRandAt tr (node v self sh cs) ↔ ∀ c ∈ cs, MemoRandAt tr c := by
  refine ⟨fun h c hc t sh' v' r hm hv =>
    h t sh' v' r (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c, hc, hm⟩)) hv, fun h t sh' v' r hm hv => ?_⟩
  rcases List.mem_cons.mp hm with ⟨rfl, rfl, rfl⟩ | hm'
  · rw [hself] at hv; cases hv
  · obtain ⟨c, hc, hcm⟩ := List.mem_flatMap.mp hm'; exact h c hc t sh' v' r hcm hv

private theorem memoRandAt_opaqueNode {tr : ExecTrace} {v : HwBytes} {cs : List ConcretizedTerm} :
    MemoRandAt tr (opaqueNode v cs) ↔ ∀ c ∈ cs, MemoRandAt tr c :=
  ⟨fun h c hc t sh' v' r hm hv => h t sh' v' r (List.mem_flatMap.mpr ⟨c, hc, hm⟩) hv,
   fun h t sh' v' r hm hv => by obtain ⟨c, hc, hcm⟩ := List.mem_flatMap.mp hm; exact h c hc t sh' v' r hcm hv⟩

private theorem memoRandAt_spqrKeyNode {tr : ExecTrace} {v : HwBytes} {cs : List ConcretizedTerm} :
    MemoRandAt tr (spqrKeyNode v cs) ↔ ∀ c ∈ cs, MemoRandAt tr c := memoRandAt_opaqueNode

section UnsealedRandAt
unseal DY.Bytes
variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

private theorem rec_eq_concretizeAll
    {F : Type → Type} [DY.SubBytesFunctor F] [DY.BytesFunctor.Has F]
    (pf : DY.Bytes.PartialFunction F ConcretizedTerm) (x : F DY.Bytes)
    (hsub : DY.Bytes.SubFunction pf (concretizeAll i S g) := by
      refine @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => ?_⟩
      simp -failIfUnchanged only [concretizeAll,
        DY.Libsignal.Composed.Refinement.allFuns,
        DY.Libsignal.Composed.Refinement.litFuns,
        DY.Libsignal.Composed.Refinement.concatFuns,
        DY.Libsignal.Composed.Refinement.dhFuns,
        DY.Libsignal.Composed.Refinement.kdfFuns,
        DY.Libsignal.Composed.Refinement.symFuns,
        DY.Libsignal.Composed.Refinement.truncFuns,
        DY.Libsignal.Composed.Refinement.x25519Funs,
        DY.Libsignal.Composed.Refinement.kemFuns,
        DY.Libsignal.Composed.Refinement.sigFuns,
        DY.Libsignal.Composed.Refinement.spqrFuns,
        DY.Libsignal.Composed.Refinement.trWireFuns,
        Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
      rfl) :
    DY.Bytes.rec (concretizeAll i S g) (DY.BytesView.pack x) =
      pf x (fun y _ => DY.Bytes.rec (concretizeAll i S g) y) := by
  have := hsub
  exact DY.Bytes.rec_eq pf (concretizeAll i S g) x

theorem termRandAt_rand {tr : ExecTrace} {ts sz : Nat} (h : RandAt tr ts sz) :
    TermRandAt i S g tr (randTerm ts sz) := by
  unfold TermRandAt gamma' randTerm
  rw [rec_eq_concretizeAll i S g (concretizeRandom g) ({ timestamp := ts, size := sz } : DY.Random.Random DY.Bytes)]
  dsimp only [concretizeRandom]; split
  · intro _ _ _ _ hm _; cases hm
  · intro t sh v r hm hv; rcases List.mem_singleton.mp hm with ⟨rfl, _, _⟩
    rw [BytesView.view_pack ({ timestamp := ts, size := sz } : DY.Random.Random DY.Bytes)] at hv
    injection hv with hr; subst hr; exact h

private theorem termRandAt_lit (tr : ExecTrace) (x : DY.Literal.Literal.SubF DY.Bytes) : TermRandAt i S g tr x.pack := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g concretizeLit x]
  exact (memoRandAt_node (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)).mpr fun _ hc => nomatch hc
private theorem termRandAt_concat_pack (tr : ExecTrace) (x : DY.Concat.Concat.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.lhs ∧ TermRandAt i S g tr x.rhs := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g concretizeConcat x]; dsimp only [concretizeConcat]; rw [memoRandAt_node (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp
theorem termRandAt_dhPk_pack (tr : ExecTrace) (x : DY.DiffieHellman.DhPk.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.sk := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeDhPk i) x]; dsimp only [concretizeDhPk]; rw [memoRandAt_node (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp
private theorem termRandAt_dh_pack (tr : ExecTrace) (x : DY.DiffieHellman.Dh.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.pk ∧ TermRandAt i S g tr x.sk := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeDh i) x]; dsimp only [concretizeDh]; rw [memoRandAt_node (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp
private theorem termRandAt_kdf_pack (tr : ExecTrace) (x : DY.KdfExtract.KdfExtract.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.salt ∧ TermRandAt i S g tr x.ikm := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeKdf i) x]; dsimp only [concretizeKdf]; rw [memoRandAt_node (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp
private theorem termRandAt_sym_pack (tr : ExecTrace) (x : DY.SymEnc.Enc.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.key ∧ TermRandAt i S g tr x.iv ∧ TermRandAt i S g tr x.msg := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeSym i) x]; dsimp only [concretizeSym]; rw [memoRandAt_node (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp
private theorem termRandAt_trunc_pack (tr : ExecTrace) (x : DY.Trunc.Trunc8.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.input := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g concretizeTrunc x]; dsimp only [concretizeTrunc]; rw [memoRandAt_node (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp
private theorem termRandAt_variant_pack (tr : ExecTrace) (x : DY.X25519.Variant.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.key := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeVariant i) x]; dsimp only [concretizeVariant]; rw [memoRandAt_node (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp
theorem termRandAt_kemPk_pack (tr : ExecTrace) (x : DY.PQKem.Pk.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.sk := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeKemPk S) x]; dsimp only [concretizeKemPk]; rw [memoRandAt_opaqueNode]; simp
private theorem termRandAt_kemEncap_pack (tr : ExecTrace) (x : DY.PQKem.Encap.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.pk ∧ TermRandAt i S g tr x.entropy := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeKemEncap i) x]; dsimp only [concretizeKemEncap]; split
  · rw [memoRandAt_node (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp
  · rw [memoRandAt_opaqueNode]; simp
private theorem termRandAt_kemSS_pack (tr : ExecTrace) (x : DY.PQKem.SharedSecret.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.pk ∧ TermRandAt i S g tr x.entropy := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeKemSS i S) x]; dsimp only [concretizeKemSS]; split
  · rw [memoRandAt_node (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp
  · rw [memoRandAt_opaqueNode]; simp
theorem termRandAt_kemRej_pack (tr : ExecTrace) (x : DY.PQKem.RejKey.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.sk ∧ TermRandAt i S g tr x.cipher := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeKemRej S) x]; dsimp only [concretizeKemRej]; rw [memoRandAt_node (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp
private theorem termRandAt_vk_pack (tr : ExecTrace) (x : DY.Signature.Vk.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.sk := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeVk S) x]; dsimp only [concretizeVk]; rw [memoRandAt_opaqueNode]; simp
private theorem termRandAt_sign_pack (tr : ExecTrace) (x : DY.Signature.Sign.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.sk ∧ TermRandAt i S g tr x.nonce ∧ TermRandAt i S g tr x.msg := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeSign S) x]; dsimp only [concretizeSign]; rw [memoRandAt_opaqueNode]; simp
private theorem termRandAt_spqrInit_pack (tr : ExecTrace) (x : DY.Spqr.InitState.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.authKey ∧ TermRandAt i S g tr x.params := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeSpqrInit S) x]; dsimp only [concretizeSpqrInit]; rw [memoRandAt_opaqueNode]; simp
private theorem termRandAt_spqrSendState_pack (tr : ExecTrace) (x : DY.Spqr.SendState.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.st ∧ TermRandAt i S g tr x.coins := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeSpqrSendState S) x]; dsimp only [concretizeSpqrSendState]; rw [memoRandAt_opaqueNode]; simp
private theorem termRandAt_spqrSendKey_pack (tr : ExecTrace) (x : DY.Spqr.SendKey.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.st ∧ TermRandAt i S g tr x.coins := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeSpqrSendKey S) x]; dsimp only [concretizeSpqrSendKey]; rw [memoRandAt_spqrKeyNode]; simp
private theorem termRandAt_spqrSendMsg_pack (tr : ExecTrace) (x : DY.Spqr.SendMsg.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.st ∧ TermRandAt i S g tr x.coins := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeSpqrSendMsg S) x]; dsimp only [concretizeSpqrSendMsg]; rw [memoRandAt_opaqueNode]; simp
private theorem termRandAt_spqrRecvState_pack (tr : ExecTrace) (x : DY.Spqr.RecvState.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.st ∧ TermRandAt i S g tr x.msg := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeSpqrRecvState S) x]; dsimp only [concretizeSpqrRecvState]; rw [memoRandAt_opaqueNode]; simp
private theorem termRandAt_spqrRecvKey_pack (tr : ExecTrace) (x : DY.Spqr.RecvKey.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.st ∧ TermRandAt i S g tr x.msg := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeSpqrRecvKey S) x]; dsimp only [concretizeSpqrRecvKey]; rw [memoRandAt_spqrKeyNode]; simp
private theorem termRandAt_spqrChainKey_pack (tr : ExecTrace) (x : DY.Spqr.ChainKey.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.authKey ∧ TermRandAt i S g tr x.params ∧ TermRandAt i S g tr x.idx := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeSpqrChainKey S) x]; dsimp only [concretizeSpqrChainKey]; rw [memoRandAt_spqrKeyNode]; simp
private theorem termRandAt_trWire_pack (tr : ExecTrace) (x : DY.TrWire.TrWireMsg.SubF DY.Bytes) : TermRandAt i S g tr x.pack ↔ TermRandAt i S g tr x.senderRatchetKey ∧ TermRandAt i S g tr x.ciphertext ∧ TermRandAt i S g tr x.pqRatchet := by
  unfold TermRandAt gamma'; rw [rec_eq_concretizeAll i S g (concretizeTrWire g) x]; dsimp only [concretizeTrWire]; rw [memoRandAt_node (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x)]; simp
end UnsealedRandAt

/-! ## Derived Constructors, `AttackerKnows`, and Serialization -/

section Core
variable {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {T : ExecTrace}

theorem termRandAt_x25519Key {pk : DY.Bytes} (h : TermRandAt i S g T pk) :
    TermRandAt i S g T (DY.X25519.normalizeX25519Key pk) := by
  have hpv := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk; unfold DY.X25519.normalizeX25519Key; split
  · next x hx => rw [hx] at hpv; rw [← hpv] at h; exact (termRandAt_variant_pack i S g T x).mp h
  · exact h
theorem termRandAt_dh {pk sk : DY.Bytes} (hpk : TermRandAt i S g T pk) (hsk : TermRandAt i S g T sk) :
    TermRandAt i S g T (DY.DiffieHellman.dh pk sk) := by
  have hpv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk; dsimp [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]; split
  · next sk2 hx =>
    rw [hx] at hpv; rw [← hpv] at hpk; have hsk2 := (termRandAt_dhPk_pack i S g T ⟨sk2⟩).mp hpk; split
    · exact (termRandAt_dh_pack i S g T ⟨({ sk := sk2 } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack, sk⟩).mpr ⟨(termRandAt_dhPk_pack i S g T ⟨sk2⟩).mpr hsk2, hsk⟩
    · exact (termRandAt_dh_pack i S g T ⟨({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack, sk2⟩).mpr ⟨(termRandAt_dhPk_pack i S g T ⟨sk⟩).mpr hsk, hsk2⟩
  · exact (termRandAt_dh_pack i S g T ⟨pk, sk⟩).mpr ⟨hpk, hsk⟩
theorem termRandAt_literalToBytes (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (T : ExecTrace) (b : ByteArray) :
    TermRandAt i S g T (DY.Literal.literalToBytes b) := termRandAt_lit i S g T ⟨b⟩
theorem termRandAt_concat {a b : DY.Bytes} (ha : TermRandAt i S g T a) (hb : TermRandAt i S g T b) :
    TermRandAt i S g T (DY.Concat.concat a b) := (termRandAt_concat_pack i S g T ⟨a, b⟩).mpr ⟨ha, hb⟩
theorem termRandAt_dhPk {sk : DY.Bytes} (hsk : TermRandAt i S g T sk) :
    TermRandAt i S g T (DY.DiffieHellman.dhPk sk) := (termRandAt_dhPk_pack i S g T ⟨sk⟩).mpr hsk
theorem termRandAt_kemPk {sk : DY.Bytes} (hsk : TermRandAt i S g T sk) :
    TermRandAt i S g T (DY.PQKem.kemPk sk) := (termRandAt_kemPk_pack i S g T ⟨sk⟩).mpr hsk
theorem termRandAt_kemEncap {pk e : DY.Bytes} (hpk : TermRandAt i S g T pk) (he : TermRandAt i S g T e) :
    TermRandAt i S g T (DY.PQKem.kemEncap pk e).1 ∧ TermRandAt i S g T (DY.PQKem.kemEncap pk e).2 :=
  ⟨(termRandAt_kemEncap_pack i S g T ⟨pk, e⟩).mpr ⟨hpk, he⟩, (termRandAt_kemSS_pack i S g T ⟨pk, e⟩).mpr ⟨hpk, he⟩⟩
theorem termRandAt_kemDecap {sk ct ss : DY.Bytes} (hdec : DY.PQKem.kemDecap sk ct = some ss) (hct : TermRandAt i S g T ct) : TermRandAt i S g T ss := by
  obtain ⟨e, rfl, rfl⟩ := kemDecap_eq_some_iff.mp hdec
  obtain ⟨hpk, he⟩ := (termRandAt_kemEncap_pack i S g T ⟨DY.PQKem.kemPk sk, e⟩).mp hct
  exact (termRandAt_kemSS_pack i S g T ⟨DY.PQKem.kemPk sk, e⟩).mpr ⟨hpk, he⟩
theorem termRandAt_kemRej {sk ct : DY.Bytes} (hsk : TermRandAt i S g T sk) (hct : TermRandAt i S g T ct) : TermRandAt i S g T (DY.PQKem.kemRejKey sk ct) :=
  (termRandAt_kemRej_pack i S g T ⟨sk, ct⟩).mpr ⟨hsk, hct⟩
theorem termRandAt_vk {sk : DY.Bytes} (hsk : TermRandAt i S g T sk) : TermRandAt i S g T (DY.Signature.vk sk) := (termRandAt_vk_pack i S g T ⟨sk⟩).mpr hsk
theorem termRandAt_sign {sk n m : DY.Bytes} (hsk : TermRandAt i S g T sk) (hn : TermRandAt i S g T n) (hm : TermRandAt i S g T m) :
    TermRandAt i S g T (DY.Signature.sign sk n m) := (termRandAt_sign_pack i S g T ⟨sk, n, m⟩).mpr ⟨hsk, hn, hm⟩
private theorem termRandAt_kdfExtract {s ikm : DY.Bytes} (hs : TermRandAt i S g T s) (hikm : TermRandAt i S g T ikm) :
    TermRandAt i S g T (DY.KdfExtract.kdfExtract s ikm) := (termRandAt_kdf_pack i S g T ⟨s, ikm⟩).mpr ⟨hs, hikm⟩
theorem termRandAt_symEnc {k iv m : DY.Bytes} (hk : TermRandAt i S g T k) (hiv : TermRandAt i S g T iv) (hm : TermRandAt i S g T m) :
    TermRandAt i S g T (DY.SymEnc.symEnc k iv m) := (termRandAt_sym_pack i S g T ⟨k, iv, m⟩).mpr ⟨hk, hiv, hm⟩
private theorem termRandAt_symDec {k iv ct m : DY.Bytes} (hdec : DY.SymEnc.symDec k iv ct = some m) (hct : TermRandAt i S g T ct) : TermRandAt i S g T m := by
  rw [DY.SymEnc.symDec_eq_some k iv ct m hdec] at hct; exact ((termRandAt_sym_pack i S g T ⟨k, iv, m⟩).mp hct).2.2
private theorem termRandAt_trunc8 {x : DY.Bytes} (hx : TermRandAt i S g T x) : TermRandAt i S g T (DY.Trunc.trunc8 x) := (termRandAt_trunc_pack i S g T ⟨x⟩).mpr hx
private theorem termRandAt_trWireMsg {v : UInt8} {rk : DY.Bytes} {c pc : UInt32} {ct pq : DY.Bytes} {ev : DY.TrWire.EncodingVariation}
    (hrk : TermRandAt i S g T rk) (hct : TermRandAt i S g T ct) (hpq : TermRandAt i S g T pq) :
    TermRandAt i S g T (DY.TrWire.trWireMsg v rk c pc ct pq ev) := (termRandAt_trWire_pack i S g T ⟨v, rk, c, pc, ct, pq, ev⟩).mpr ⟨hrk, hct, hpq⟩
theorem termRandAt_spqrParams (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (T : ExecTrace) (dir : DY.Spqr.Direction) :
    TermRandAt i S g T (DY.Spqr.encodeSpqrDirectionParams dir) := termRandAt_literalToBytes i S g T _
private theorem termRandAt_spqrIdx (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (T : ExecTrace) (idx : UInt32) :
    TermRandAt i S g T (DY.Spqr.encodeSpqrIndexTerm idx) := termRandAt_literalToBytes i S g T _
private theorem termRandAt_zeroKey (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (T : ExecTrace) :
    TermRandAt i S g T DY.Spqr.zeroKey := termRandAt_literalToBytes i S g T _
theorem termRandAt_spqrInit {authKey params : DY.Bytes} (ha : TermRandAt i S g T authKey) (hp : TermRandAt i S g T params) :
    TermRandAt i S g T (DY.Spqr.spqrInit authKey params) := (termRandAt_spqrInit_pack i S g T ⟨authKey, params⟩).mpr ⟨ha, hp⟩
private theorem termRandAt_spqrChainKey {authKey params idx : DY.Bytes} (ha : TermRandAt i S g T authKey) (hp : TermRandAt i S g T params) (hi : TermRandAt i S g T idx) :
    TermRandAt i S g T (DY.Spqr.spqrChainKey authKey params idx) := (termRandAt_spqrChainKey_pack i S g T ⟨authKey, params, idx⟩).mpr ⟨ha, hp, hi⟩
theorem termRandAt_spqrSend {st coins : DY.Bytes} (hst : TermRandAt i S g T st) (hc : TermRandAt i S g T coins) :
    TermRandAt i S g T (DY.Spqr.spqrSend st coins).1 ∧ TermRandAt i S g T (DY.Spqr.spqrSend st coins).2.1 ∧ TermRandAt i S g T (DY.Spqr.spqrSend st coins).2.2 := by
  refine ⟨(termRandAt_spqrSendState_pack i S g T ⟨st, coins⟩).mpr ⟨hst, hc⟩, ?_, (termRandAt_spqrSendMsg_pack i S g T ⟨st, coins⟩).mpr ⟨hst, hc⟩⟩
  have hpv := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st; unfold DY.Spqr.spqrSend; dsimp only; split
  · next authKey params hx =>
    have hst' := hst; rw [hx] at hpv; rw [← hpv] at hst'; obtain ⟨ha, hp⟩ := (termRandAt_spqrInit_pack i S g T ⟨authKey, params⟩).mp hst'
    exact termRandAt_spqrChainKey ha hp (termRandAt_spqrIdx i S g T 1)
  · exact (termRandAt_spqrSendKey_pack i S g T ⟨st, coins⟩).mpr ⟨hst, hc⟩
theorem termRandAt_spqrRecv {st msg st' key : DY.Bytes} {idx : UInt32}
    (hst : TermRandAt i S g T st) (hmsg : TermRandAt i S g T msg) (hrecv : DY.Spqr.spqrRecv st msg idx = some (st', key)) :
    TermRandAt i S g T st' ∧ TermRandAt i S g T key := by
  have hpv := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st; unfold DY.Spqr.spqrRecv at hrecv; split at hrecv
  · cases hrecv
  · dsimp only at hrecv; split at hrecv
    · next authKey params hx =>
      have hst' := hst; rw [hx] at hpv; rw [← hpv] at hst'; obtain ⟨ha, _⟩ := (termRandAt_spqrInit_pack i S g T ⟨authKey, params⟩).mp hst'
      split at hrecv
      · next dir _ =>
        injection hrecv with hrecv; injection hrecv with hst_eq hkey; subst hst_eq hkey
        refine ⟨(termRandAt_spqrRecvState_pack i S g T ⟨st, msg⟩).mpr ⟨hst, hmsg⟩, ?_⟩
        split
        · exact termRandAt_zeroKey i S g T
        · exact termRandAt_spqrChainKey ha (termRandAt_spqrParams i S g T dir.flip) (termRandAt_spqrIdx i S g T idx)
      · cases hrecv
    · injection hrecv with hrecv; injection hrecv with hst_eq hkey; subst hst_eq hkey
      exact ⟨(termRandAt_spqrRecvState_pack i S g T ⟨st, msg⟩).mpr ⟨hst, hmsg⟩, (termRandAt_spqrRecvKey_pack i S g T ⟨st, msg⟩).mpr ⟨hst, hmsg⟩⟩

private theorem attackerKnowledge_implies_termRandAt (i : ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (T : ExecTrace) :
    DY.SubAttackerKnowledge.Implies DY.AttackerKnowledge.attackerKnowledge (TermRandAt i S g T) := by
  change DY.SubAttackerKnowledge.Implies (DY.SubAttackerKnowledge.combine _) (TermRandAt i S g T)
  apply DY.SubAttackerKnowledge.combine.implies; intro id; match id with
  | ⟨0, _⟩ =>
    intro _ h; dsimp [DY.Libsignal.Composed.attackerKnowledge.internal] at h
    rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at h; exact h.elim
  | ⟨1, _⟩ =>
    apply DY.SubAttackerKnowledge.combine'.implies; intro ⟨0, _⟩ _ h
    dsimp [DY.Literal.attackerKnowledge.internal] at h
    rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at h
    rcases h with ⟨lit, rfl⟩; exact termRandAt_lit i S g T ⟨lit⟩
  | ⟨2, _⟩ => apply DY.SubAttackerKnowledge.combine'.implies; intro id2; match id2 with
    | ⟨0, _⟩ =>
      intro _ h; dsimp [DY.Concat.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at h
      rcases h with ⟨l, r, rfl, hl, hr⟩; exact (termRandAt_concat_pack i S g T ⟨l, r⟩).mpr ⟨hl, hr⟩
    | ⟨1, _⟩ =>
      intro b h; dsimp [DY.Concat.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at h
      rcases h with ⟨inp, r, idx, hsp, hinp⟩; rw [← DY.Concat.concat_split inp idx b r hsp.symm] at hinp
      exact ((termRandAt_concat_pack i S g T ⟨b, r⟩).mp hinp).1
    | ⟨2, _⟩ =>
      intro b h; dsimp [DY.Concat.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at h
      rcases h with ⟨inp, l, idx, hsp, hinp⟩; rw [← DY.Concat.concat_split inp idx l b hsp.symm] at hinp
      exact ((termRandAt_concat_pack i S g T ⟨l, b⟩).mp hinp).2
  | ⟨3, _⟩ => apply DY.SubAttackerKnowledge.combine'.implies; intro id2; match id2 with
    | ⟨0, _⟩ =>
      intro _ h; dsimp [DY.DiffieHellman.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at h
      rcases h with ⟨sk, rfl, hsk⟩; exact (termRandAt_dhPk_pack i S g T ⟨sk⟩).mpr hsk
    | ⟨1, _⟩ =>
      intro _ h; dsimp [DY.DiffieHellman.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at h
      rcases h with ⟨pk, sk, rfl, hpk, hsk⟩; exact termRandAt_dh hpk hsk
  | ⟨4, _⟩ =>
    apply DY.SubAttackerKnowledge.combine'.implies; intro ⟨0, _⟩ _ h
    dsimp [DY.KdfExtract.attackerKnowledge.internal] at h
    rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at h
    rcases h with ⟨salt, ikm, rfl, ha, hb⟩; exact (termRandAt_kdf_pack i S g T ⟨salt, ikm⟩).mpr ⟨ha, hb⟩
  | ⟨5, _⟩ => apply DY.SubAttackerKnowledge.combine'.implies; intro id2; match id2 with
    | ⟨0, _⟩ => rintro _ ⟨k, iv, msg, rfl, hk, hiv, hm⟩; exact (termRandAt_sym_pack i S g T ⟨k, iv, msg⟩).mpr ⟨hk, hiv, hm⟩
    | ⟨1, _⟩ => rintro b ⟨k, iv, ct, hdec, _, _, hct⟩; rw [DY.SymEnc.symDec_eq_some k iv ct b hdec.symm] at hct; exact ((termRandAt_sym_pack i S g T ⟨k, iv, b⟩).mp hct).2.2
  | ⟨6, _⟩ => apply DY.SubAttackerKnowledge.combine'.implies; intro ⟨0, _⟩; rintro _ ⟨inp, rfl, ha⟩; exact (termRandAt_trunc_pack i S g T ⟨inp⟩).mpr ha
  | ⟨7, _⟩ => apply DY.SubAttackerKnowledge.combine'.implies; intro id2; match id2 with
    | ⟨0, _⟩ =>
      rintro _ ⟨key, v, t, rfl, hk⟩; have hk' := termRandAt_x25519Key hk; dsimp only [DY.X25519.x25519TorsionVariant]; split
      · exact hk'
      · exact (termRandAt_variant_pack i S g T ⟨DY.X25519.normalizeX25519Key key, v, t⟩).mpr hk'
    | ⟨1, _⟩ => rintro _ ⟨x, hx, rfl⟩; exact (termRandAt_variant_pack i S g T x).mp hx
  | ⟨8, _⟩ => apply DY.SubAttackerKnowledge.combine'.implies; intro id2; match id2 with
    | ⟨0, _⟩ => rintro _ ⟨sk, rfl, hsk⟩; exact termRandAt_kemPk hsk
    | ⟨1, _⟩ =>
      rintro b ⟨pk, e, _, heq, hpk, he⟩
      have hb : b = (DY.PQKem.kemEncap pk e).1 := congrArg Prod.fst heq
      rw [hb]; exact (termRandAt_kemEncap hpk he).1
    | ⟨2, _⟩ =>
      rintro b ⟨pk, e, _, heq, hpk, he⟩
      have hb : b = (DY.PQKem.kemEncap pk e).2 := congrArg Prod.snd heq
      rw [hb]; exact (termRandAt_kemEncap hpk he).2
    | ⟨3, _⟩ => rintro _ ⟨sk, ct, hdec, _, hct⟩; exact termRandAt_kemDecap hdec.symm hct
    | ⟨4, _⟩ => rintro _ ⟨sk, ct, rfl, hsk, hct⟩; exact termRandAt_kemRej hsk hct
  | ⟨9, _⟩ => apply DY.SubAttackerKnowledge.combine'.implies; intro id2; match id2 with
    | ⟨0, _⟩ =>
      intro _ h; dsimp [DY.Signature.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at h
      rcases h with ⟨sk, rfl, hsk⟩; exact termRandAt_vk hsk
    | ⟨1, _⟩ =>
      intro _ h; dsimp [DY.Signature.attackerKnowledge.internal] at h
      rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at h
      rcases h with ⟨sk, nonce, msg, rfl, hsk, hn, hm⟩; exact termRandAt_sign hsk hn hm
  | ⟨10, _⟩ => apply DY.SubAttackerKnowledge.combine'.implies; intro id2; match id2 with
    | ⟨0, _⟩ => rintro _ ⟨authKey, params, rfl, ha, hp⟩; exact termRandAt_spqrInit ha hp
    | ⟨1, _⟩ => rintro _ ⟨authKey, params, idx, rfl, ha, hp, hi⟩; exact termRandAt_spqrChainKey ha hp hi
    | ⟨2, _⟩ => rintro _ ⟨st, coins, rfl, hst, hc⟩; exact (termRandAt_spqrSend hst hc).1
    | ⟨3, _⟩ => rintro _ ⟨st, coins, rfl, hst, hc⟩; exact (termRandAt_spqrSend hst hc).2.1
    | ⟨4, _⟩ => rintro _ ⟨st, coins, rfl, hst, hc⟩; exact (termRandAt_spqrSend hst hc).2.2
    | ⟨5, _⟩ => rintro _ ⟨st, msg, idx, ⟨st', key⟩, hrecv, rfl, hst, hmsg⟩; exact (termRandAt_spqrRecv hst hmsg hrecv).1
    | ⟨6, _⟩ => rintro _ ⟨st, msg, idx, ⟨st', key⟩, hrecv, rfl, hst, hmsg⟩; exact (termRandAt_spqrRecv hst hmsg hrecv).2
    | ⟨7, _⟩ =>
      rintro _ (⟨x, hx, rfl | rfl⟩ | ⟨x, hx, rfl | rfl⟩ | ⟨x, hx, rfl | rfl⟩)
      · exact ((termRandAt_spqrInit_pack i S g T x).mp hx).1
      · exact ((termRandAt_spqrInit_pack i S g T x).mp hx).2
      · exact ((termRandAt_spqrSendState_pack i S g T x).mp hx).1
      · exact ((termRandAt_spqrSendState_pack i S g T x).mp hx).2
      · exact ((termRandAt_spqrRecvState_pack i S g T x).mp hx).1
      · exact ((termRandAt_spqrRecvState_pack i S g T x).mp hx).2
  | ⟨11, _⟩ => apply DY.SubAttackerKnowledge.combine'.implies; intro id2; match id2 with
    | ⟨0, _⟩ => rintro _ ⟨x, rfl, hrk, hct, hpq⟩; exact (termRandAt_trWire_pack i S g T x).mpr ⟨hrk, hct, hpq⟩
    | ⟨1, _⟩ =>
      rintro _ ⟨x, hx, rfl | rfl | rfl⟩
      · exact ((termRandAt_trWire_pack i S g T x).mp hx).1
      · exact ((termRandAt_trWire_pack i S g T x).mp hx).2.1
      · exact ((termRandAt_trWire_pack i S g T x).mp hx).2.2
theorem attackerKnows_termRandAt {tr : ExecTrace} (hbase : ∀ m, tr.BaseAttackerKnows m → TermRandAt i S g T m)
    {b : DY.Bytes} (hkn : b.AttackerKnows tr) : TermRandAt i S g T b := by
  refine DY.Bytes.AttackerKnows.is_least_fixpoint (TermRandAt i S g T) b tr
    (attackerKnowledge_implies_termRandAt i S g T) (fun m hm => ?_) hkn
  simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, DY.SubAttackerKnowledge.fromPred] at hm
  exact hbase m hm

theorem composed_attackerKnows_ind {tr : ExecTrace} {Q : DY.Bytes → Prop}
    (hlit : ∀ bs, DY.Bytes.AttackerKnows (DY.Literal.literalToBytes bs) tr → Q (DY.Literal.literalToBytes bs))
    (hconcat : ∀ a c, DY.Bytes.AttackerKnows (DY.Concat.concat a c) tr → Q a → Q c → Q (DY.Concat.concat a c))
    (hconcat_elim : ∀ a c, Q (DY.Concat.concat a c) → Q a ∧ Q c)
    (hdhPk : ∀ sk, DY.Bytes.AttackerKnows (DY.DiffieHellman.dhPk sk) tr → Q sk → Q (DY.DiffieHellman.dhPk sk))
    (hdh_pack : ∀ pk sk, DY.Bytes.AttackerKnows (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) tr → Q pk → Q sk → Q (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack))
    (hdhPk_elim : ∀ sk, Q (DY.DiffieHellman.dhPk sk) → Q sk)
    (hkdf : ∀ salt ikm, DY.Bytes.AttackerKnows (DY.KdfExtract.kdfExtract salt ikm) tr → Q salt → Q ikm → Q (DY.KdfExtract.kdfExtract salt ikm))
    (hsymEnc : ∀ k iv msg, DY.Bytes.AttackerKnows (DY.SymEnc.symEnc k iv msg) tr → Q k → Q iv → Q msg → Q (DY.SymEnc.symEnc k iv msg))
    (hsymEnc_elim : ∀ e : DY.SymEnc.Enc.SubF DY.Bytes, Q e.pack → Q e.msg)
    (htrunc8 : ∀ m, DY.Bytes.AttackerKnows (DY.Trunc.trunc8 m) tr → Q m → Q (DY.Trunc.trunc8 m))
    (hx25519Key : ∀ key, Q key → Q (DY.X25519.normalizeX25519Key key))
    (hvariant_pack : ∀ v : DY.X25519.Variant.SubF DY.Bytes, DY.Bytes.AttackerKnows v.pack tr → Q v.key → Q v.pack)
    (hvariant_elim : ∀ v : DY.X25519.Variant.SubF DY.Bytes, Q v.pack → Q v.key)
    (hkemPk : ∀ sk, Q sk → Q (DY.PQKem.kemPk sk))
    (hkemEncap_fst : ∀ pk e, DY.Bytes.AttackerKnows (DY.PQKem.kemEncap pk e).1 tr → Q pk → Q e → Q (DY.PQKem.kemEncap pk e).1)
    (hkemEncap_fst_elim : ∀ c : DY.PQKem.Encap.SubF DY.Bytes, Q c.pack → Q c.pk ∧ Q c.entropy)
    (hkemEncap_snd : ∀ pk e, DY.Bytes.AttackerKnows (DY.PQKem.kemEncap pk e).2 tr → Q pk → Q e → Q (DY.PQKem.kemEncap pk e).2)
    (hkemRej : ∀ sk ct, DY.Bytes.AttackerKnows (DY.PQKem.kemRejKey sk ct) tr → Q sk → Q ct → Q (DY.PQKem.kemRejKey sk ct))
    (hvk : ∀ sk, Q sk → Q (DY.Signature.vk sk))
    (hsign : ∀ sk n m, Q sk → Q n → Q m → Q (DY.Signature.sign sk n m))
    (hspqrInit : ∀ authKey params, Q authKey → Q params → Q (DY.Spqr.spqrInit authKey params))
    (hspqrInit_elim : ∀ s : DY.Spqr.InitState.SubF DY.Bytes, Q s.pack → Q s.authKey ∧ Q s.params)
    (hspqrChainKey : ∀ authKey params idx, Q authKey → Q params → Q idx → Q (DY.Spqr.spqrChainKey authKey params idx))
    (hspqrSendState : ∀ st coins, Q st → Q coins → Q (DY.Spqr.spqrSend st coins).1)
    (hspqrSendState_elim : ∀ s : DY.Spqr.SendState.SubF DY.Bytes, Q s.pack → Q s.st ∧ Q s.coins)
    (hspqrSendKey_pack : ∀ st coins, Q st → Q coins → Q (({ st := st, coins := coins } : DY.Spqr.SendKey.SubF DY.Bytes).pack))
    (hspqrSendMsg : ∀ st coins, Q st → Q coins → Q (DY.Spqr.spqrSend st coins).2.2)
    (hspqrRecvState_pack : ∀ st msg, Q st → Q msg → Q (({ st := st, msg := msg } : DY.Spqr.RecvState.SubF DY.Bytes).pack))
    (hspqrRecvState_elim : ∀ s : DY.Spqr.RecvState.SubF DY.Bytes, Q s.pack → Q s.st ∧ Q s.msg)
    (hspqrRecvKey_pack : ∀ st msg, Q st → Q msg → Q (({ st := st, msg := msg } : DY.Spqr.RecvKey.SubF DY.Bytes).pack))
    (hlit_uncond : ∀ bs, Q (DY.Literal.literalToBytes bs))
    (htrWire : ∀ (v : UInt8) (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes) (ev : DY.TrWire.EncodingVariation),
      DY.Bytes.AttackerKnows (DY.TrWire.trWireMsg v rk c pc ct pq ev) tr → Q rk → Q ct → Q pq → Q (DY.TrWire.trWireMsg v rk c pc ct pq ev))
    (htrWire_elim : ∀ w : DY.TrWire.TrWireMsg.SubF DY.Bytes, Q w.pack → Q w.senderRatchetKey ∧ Q w.ciphertext ∧ Q w.pqRatchet)
    (hbase : ∀ y, tr.BaseAttackerKnows y → Q y)
    {t : DY.Bytes} (ht : DY.Bytes.AttackerKnows t tr) : Q t := by
  suffices hgood : t.AttackerKnows tr ∧ Q t from hgood.2
  refine DY.Bytes.AttackerKnows.is_least_fixpoint (fun x => x.AttackerKnows tr ∧ Q x) t tr ?_ ?_ ht
  · change DY.SubAttackerKnowledge.Implies DY.Libsignal.Composed.attackerKnowledge (fun x => x.AttackerKnows tr ∧ Q x)
    dsimp [DY.Libsignal.Composed.attackerKnowledge]
    apply DY.SubAttackerKnowledge.combine.implies
    intro id b hr
    have hpred : DY.AttackerKnowledge.attackerKnowledge.pred (fun x => x.AttackerKnows tr ∧ Q x) b :=
      (inferInstance : DY.AttackerKnowledge.HasStep (DY.Libsignal.Composed.attackerKnowledge.internal id)
        (DY.SubAttackerKnowledge.combine DY.Libsignal.Composed.attackerKnowledge.internal)).pf _ b hr
    have hak : b.AttackerKnows tr := DY.Bytes.AttackerKnows.prove DY.AttackerKnowledge.attackerKnowledge b tr
      (DY.AttackerKnowledge.attackerKnowledge.pred_isMonotonic (fun x => x.AttackerKnows tr ∧ Q x) (·.AttackerKnows tr) (fun _ h => h.1) b hpred)
    refine ⟨hak, ?_⟩
    rcases id with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, hlt⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal] at hr
      rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at hr; exact hr.elim
    · simp only [DY.Libsignal.Composed.attackerKnowledge.internal, DY.Literal.attackerKnowledge, Symbolic.DYBridge.DY.SubAttackerKnowledge.combine'_pred, DY.Fixpoint.combine] at hr
      rcases hr with ⟨⟨_ | n, hlt'⟩, hr⟩ <;> [skip; omega]
      dsimp [DY.Literal.attackerKnowledge.internal] at hr
      rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at hr
      rcases hr with ⟨bs, rfl⟩; exact hlit bs hak
    · simp only [DY.Libsignal.Composed.attackerKnowledge.internal, DY.Concat.attackerKnowledge, Symbolic.DYBridge.DY.SubAttackerKnowledge.combine'_pred, DY.Fixpoint.combine] at hr
      rcases hr with ⟨⟨_ | _ | _ | n, hlt'⟩, hr⟩ <;> try omega
      · dsimp [DY.Concat.attackerKnowledge.internal] at hr
        rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at hr
        rcases hr with ⟨lhs, rhs, rfl, hlhs, hrhs⟩; exact hconcat lhs rhs hak hlhs.2 hrhs.2
      · dsimp [DY.Concat.attackerKnowledge.internal] at hr
        rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at hr
        rcases hr with ⟨inp, rhs, idx, hsplit, hinp⟩; exact (hconcat_elim b rhs (DY.Concat.concat_split inp idx b rhs hsplit.symm ▸ hinp.2)).1
      · dsimp [DY.Concat.attackerKnowledge.internal] at hr
        rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hr
        rcases hr with ⟨inp, lhs, idx, hsplit, hinp⟩; exact (hconcat_elim lhs b (DY.Concat.concat_split inp idx lhs b hsplit.symm ▸ hinp.2)).2
    · simp only [DY.Libsignal.Composed.attackerKnowledge.internal, DY.DiffieHellman.attackerKnowledge, Symbolic.DYBridge.DY.SubAttackerKnowledge.combine'_pred, DY.Fixpoint.combine] at hr
      rcases hr with ⟨⟨_ | _ | n, hlt'⟩, hr⟩ <;> try omega
      · dsimp [DY.DiffieHellman.attackerKnowledge.internal] at hr
        rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hr
        rcases hr with ⟨sk, rfl, hsk⟩; exact hdhPk sk hak hsk.2
      · dsimp [DY.DiffieHellman.attackerKnowledge.internal] at hr
        rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at hr
        rcases hr with ⟨pk, sk, rfl, hpk, hsk⟩
        have hp := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk
        cases hv : pk.view? DY.DiffieHellman.DhPk.SubF with
        | none =>
          have h_eq : DY.DiffieHellman.dh pk sk = ({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by simp [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh, hv]
          rw [h_eq] at hak ⊢; exact hdh_pack pk sk hak hpk.2 hsk.2
        | some x =>
          rcases x with ⟨sk2⟩; rw [hv] at hp; dsimp only at hp; rw [← hp] at hpk
          have hsk2 : Q sk2 := hdhPk_elim sk2 hpk.2
          have hdhpk_sk_ak : (DY.DiffieHellman.dhPk sk).AttackerKnows tr := by
            refine DY.Bytes.AttackerKnows.prove DY.DiffieHellman.attackerKnowledge (DY.DiffieHellman.dhPk sk) tr ?_
            rw [DY.DiffieHellman.attackerKnowledge, Symbolic.DYBridge.DY.SubAttackerKnowledge.combine'_pred]
            refine ⟨⟨0, by decide⟩, ?_⟩
            dsimp [DY.DiffieHellman.attackerKnowledge.internal]
            rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred]
            exact ⟨sk, rfl, hsk.1⟩
          have hdhpk_sk : Q (DY.DiffieHellman.dhPk sk) := hdhPk sk hdhpk_sk_ak hsk.2
          by_cases hle : sk ≤ sk2
          · have h_eq : DY.DiffieHellman.dh pk sk =
                ({ pk := ({ sk := sk2 } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
              simp [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh, hv, hle]
            rw [h_eq] at hak ⊢; exact hdh_pack _ sk hak hpk.2 hsk.2
          · have h_eq : DY.DiffieHellman.dh pk sk =
                ({ pk := ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack, sk := sk2 } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
              simp [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh, hv, hle]
            rw [h_eq] at hak ⊢; exact hdh_pack _ sk2 hak hdhpk_sk hsk2
    · simp only [DY.Libsignal.Composed.attackerKnowledge.internal, DY.KdfExtract.attackerKnowledge, Symbolic.DYBridge.DY.SubAttackerKnowledge.combine'_pred, DY.Fixpoint.combine] at hr
      rcases hr with ⟨⟨_ | n, hlt'⟩, hr⟩ <;> [skip; omega]
      dsimp [DY.KdfExtract.attackerKnowledge.internal] at hr
      rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at hr
      rcases hr with ⟨salt, ikm, rfl, hs, hm⟩
      exact hkdf salt ikm hak hs.2 hm.2
    · simp only [DY.Libsignal.Composed.attackerKnowledge.internal, DY.SymEnc.attackerKnowledge, Symbolic.DYBridge.DY.SubAttackerKnowledge.combine'_pred, DY.Fixpoint.combine] at hr
      rcases hr with ⟨⟨_ | _ | n, hlt'⟩, hr⟩ <;> try omega
      · rcases hr with ⟨k, iv, msg, rfl, hk, hiv, hmsg⟩; exact hsymEnc k iv msg hak hk.2 hiv.2 hmsg.2
      · rcases hr with ⟨key, iv, ct, hdec, _, _, hct⟩
        rw [DY.SymEnc.symDec_eq_some key iv ct b hdec.symm] at hct
        exact hsymEnc_elim ⟨key, iv, b⟩ hct.2
    · simp only [DY.Libsignal.Composed.attackerKnowledge.internal, DY.Trunc.attackerKnowledge, Symbolic.DYBridge.DY.SubAttackerKnowledge.combine'_pred, DY.Fixpoint.combine] at hr
      rcases hr with ⟨⟨_ | n, hlt'⟩, hr⟩ <;> [rcases hr with ⟨m, rfl, hm⟩; omega]
      exact htrunc8 m hak hm.2
    · simp only [DY.Libsignal.Composed.attackerKnowledge.internal, DY.X25519.attackerKnowledge, Symbolic.DYBridge.DY.SubAttackerKnowledge.combine'_pred, DY.Fixpoint.combine] at hr
      rcases hr with ⟨⟨_ | _ | n, hlt'⟩, hr⟩ <;> try omega
      · rcases hr with ⟨key, v, t, rfl, hkey⟩
        dsimp [DY.X25519.x25519TorsionVariant] at hak ⊢
        by_cases hvt : v = 0 ∧ t = 0 <;> simp only [hvt, ↓reduceIte] at hak ⊢
        · exact hx25519Key key hkey.2
        · exact hvariant_pack ⟨DY.X25519.normalizeX25519Key key, v, t⟩ hak (hx25519Key key hkey.2)
      · rcases hr with ⟨x, hpack, rfl⟩; exact hvariant_elim x hpack.2
    · simp only [DY.Libsignal.Composed.attackerKnowledge.internal, DY.PQKem.attackerKnowledge, Symbolic.DYBridge.DY.SubAttackerKnowledge.combine'_pred, DY.Fixpoint.combine] at hr
      rcases hr with ⟨⟨_ | _ | _ | _ | _ | n, hlt'⟩, hr⟩ <;> try omega
      · rcases hr with ⟨sk, rfl, hsk⟩; exact hkemPk sk hsk.2
      · rcases hr with ⟨pk, e, rhs, heq, hpk, he⟩
        have h1 := congrArg Prod.fst heq; dsimp only at h1; subst h1; exact hkemEncap_fst pk e hak hpk.2 he.2
      · rcases hr with ⟨pk, e, lhs, heq, hpk, he⟩
        have h1 := congrArg Prod.snd heq; dsimp only at h1; subst h1; exact hkemEncap_snd pk e hak hpk.2 he.2
      · rcases hr with ⟨sk, ct, hdec, hsk, hct⟩
        obtain ⟨e, rfl, rfl⟩ := kemDecap_eq_some_iff.mp hdec.symm
        exact hkemEncap_snd (DY.PQKem.kemPk sk) e hak (hkemPk sk hsk.2) (hkemEncap_fst_elim ⟨DY.PQKem.kemPk sk, e⟩ hct.2).2
      · rcases hr with ⟨sk, ct, rfl, hsk, hct⟩
        exact hkemRej sk ct hak hsk.2 hct.2
    · simp only [DY.Libsignal.Composed.attackerKnowledge.internal, DY.Signature.attackerKnowledge, Symbolic.DYBridge.DY.SubAttackerKnowledge.combine'_pred, DY.Fixpoint.combine] at hr
      rcases hr with ⟨⟨_ | _ | n, hlt'⟩, hr⟩ <;> try omega
      · dsimp [DY.Signature.attackerKnowledge.internal] at hr
        rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at hr
        rcases hr with ⟨sk, rfl, hsk⟩; exact hvk sk hsk.2
      · dsimp [DY.Signature.attackerKnowledge.internal] at hr
        rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hr
        rcases hr with ⟨sk, nonce, msg, rfl, hsk, hn, hm⟩; exact hsign sk nonce msg hsk.2 hn.2 hm.2
    · simp only [DY.Libsignal.Composed.attackerKnowledge.internal, DY.Spqr.attackerKnowledge, Symbolic.DYBridge.DY.SubAttackerKnowledge.combine'_pred, DY.Fixpoint.combine] at hr
      rcases hr with ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hlt'⟩, hr⟩ <;> try omega
      · rcases hr with ⟨authKey, params, rfl, hk, hp⟩; exact hspqrInit authKey params hk.2 hp.2
      · rcases hr with ⟨authKey, params, idx, rfl, hk, hp, hidx⟩; exact hspqrChainKey authKey params idx hk.2 hp.2 hidx.2
      · rcases hr with ⟨st, coins, rfl, hst, hc⟩; exact hspqrSendState st coins hst.2 hc.2
      · rcases hr with ⟨st, coins, rfl, hst, hc⟩
        unfold DY.Spqr.spqrSend; dsimp only; have hp := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
        cases hv : st.view? DY.Spqr.InitState.SubF with
        | none => exact hspqrSendKey_pack st coins hst.2 hc.2
        | some x =>
          rw [hv] at hp; rw [← hp] at hst; obtain ⟨hk, hpar⟩ := hspqrInit_elim x hst.2; exact hspqrChainKey x.authKey x.params _ hk hpar (hlit_uncond _)
      · rcases hr with ⟨st, coins, rfl, hst, hc⟩; exact hspqrSendMsg st coins hst.2 hc.2
      · rcases hr with ⟨st, msg, idx, ⟨st', key⟩, hrecv, hbeq, hst, hm⟩
        dsimp only at hbeq
        have hst_eq : st' = ({ st := st, msg := msg } : DY.Spqr.RecvState.SubF DY.Bytes).pack := by
          unfold DY.Spqr.spqrRecv at hrecv; split at hrecv
          · cases hrecv
          · dsimp only at hrecv; split at hrecv
            · split at hrecv
              · injection hrecv with hrecv; injection hrecv with h1 _; exact h1.symm
              · cases hrecv
            · injection hrecv with hrecv; injection hrecv with h1 _; exact h1.symm
        rw [hbeq, hst_eq]; exact hspqrRecvState_pack st msg hst.2 hm.2
      · rcases hr with ⟨st, msg, idx, r, hrecv, rfl, hst, hm⟩
        unfold DY.Spqr.spqrRecv at hrecv
        split at hrecv
        · cases hrecv
        · have hp := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
          cases hv : st.view? DY.Spqr.InitState.SubF with
          | none =>
            rw [hv] at hrecv; injection hrecv with hrecv'; subst hrecv'; exact hspqrRecvKey_pack st msg hst.2 hm.2
          | some x =>
            rw [hv] at hrecv hp; rcases x with ⟨authKey, params⟩; dsimp only at hrecv hp
            rw [← hp] at hst; obtain ⟨hk, _⟩ := hspqrInit_elim ⟨authKey, params⟩ hst.2
            cases hd : DY.Spqr.spqrParamsDir? params with
            | none => rw [hd] at hrecv; cases hrecv
            | some dir =>
              rw [hd] at hrecv; injection hrecv with hrecv'; subst hrecv'; dsimp only
              split <;> [exact hlit_uncond _; exact hspqrChainKey authKey _ _ hk (hlit_uncond _) (hlit_uncond _)]
      · rcases hr with (⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩)
        exacts [(hspqrInit_elim x hpack.2).1, (hspqrInit_elim x hpack.2).2, (hspqrSendState_elim x hpack.2).1, (hspqrSendState_elim x hpack.2).2, (hspqrRecvState_elim x hpack.2).1, (hspqrRecvState_elim x hpack.2).2]
    · simp only [DY.Libsignal.Composed.attackerKnowledge.internal, DY.TrWire.attackerKnowledge, Symbolic.DYBridge.DY.SubAttackerKnowledge.combine'_pred, DY.Fixpoint.combine] at hr
      rcases hr with ⟨⟨_ | _ | n, hlt'⟩, hr⟩ <;> try omega
      · rcases hr with ⟨⟨v, rk, c, pc, ct, pq, ev⟩, rfl, hrk, hct, hpq⟩; exact htrWire v rk c pc ct pq ev hak hrk.2 hct.2 hpq.2
      · rcases hr with ⟨w, hw, hmem⟩
        obtain ⟨hrk, hct, hpq⟩ := htrWire_elim w hw.2
        rcases hmem with rfl | rfl | rfl <;> assumption
    · omega
  · intro y hy
    simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, DY.SubAttackerKnowledge.fromPred] at hy
    exact ⟨DY.Bytes.AttackerKnows.prove_from_base y tr hy, hbase y hy⟩
local instance termRandAt_compat (i : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (T : ExecTrace) : Comparse.BytesCompatiblePred (TermRandAt i S g T) where
  pred_empty := by simp only [Comparse.BytesLike.empty]; exact termRandAt_literalToBytes i S g T _
  pred_concat := by simp only [Comparse.BytesLike.concat]; intro _ _ h1 h2; exact termRandAt_concat h1 h2
  pred_split := by
    intro buf j hbuf; simp only [Comparse.BytesLike.split]; rcases hsp : DY.Concat.split buf j with _ | ⟨b1, b2⟩
    · trivial
    · rw [← DY.Concat.concat_split buf j b1 b2 hsp] at hbuf; exact (termRandAt_concat_pack i S g T ⟨b1, b2⟩).mp hbuf
  pred_fromByteArray := by intro b; simp only [Comparse.BytesLike.fromByteArray]; exact termRandAt_literalToBytes i S g T b

/-! ## Trace-Entry Invariant and `TRand` Primitives -/
abbrev StEntry := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
abbrev TREntry := DY.ProtocolEvent.ExecEntryT TREvent
abbrev PQStEntry := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState PQXDHState)
abbrev PQEvEntry := DY.ProtocolEvent.ExecEntryT PQXDHEvent
abbrev CEvEntry := DY.ProtocolEvent.ExecEntryT ComposedEvent
def StateRandAt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (T : ExecTrace) (st : TRState) : Prop :=
  TermRandAt i S g T st.myIk ∧ TermRandAt i S g T st.peerIk ∧ TermRandAt i S g T st.rk ∧
  TermRandAt i S g T st.dhs ∧ TermRandAt i S g T st.cks ∧ TermRandAt i S g T st.sid ∧
  TermRandAt i S g T st.spqr ∧ ∀ c ∈ st.recv, TermRandAt i S g T c.ratchetKey ∧ TermRandAt i S g T c.chainKey
theorem termRandAt_serialize_tr (ls : PersistentLocalState.LocalState TRState)
    (hst : StateRandAt i S g T ls.state) : TermRandAt i S g T (Comparse.serialize ls) := by
  rw [Symbolic.DYBridge.DY.Comparse.serialize_eq_1, ← Comparse.ExtensibleMessageFormat.wf_eq _ (TermRandAt i S g T) ls]
  obtain ⟨hmy, hpeer, hrk, hdhs, hcks, hsid, hspqr, hrecv⟩ := hst
  simp [Comparse.ParseableSerializeable.mf, Comparse.ParseableSerializeableNE.mf]
  exact ⟨hmy, hpeer, hrk, hdhs, hcks, hsid, hspqr, hrecv⟩
theorem termRandAt_serialize_pq (ls : PersistentLocalState.LocalState PQXDHState)
    (hsk : TermRandAt i S g T ls.state.sk) : TermRandAt i S g T (Comparse.serialize ls) := by
  rw [Symbolic.DYBridge.DY.Comparse.serialize_eq_1, ← Comparse.ExtensibleMessageFormat.wf_eq _ (TermRandAt i S g T) ls]
  simp [Comparse.ParseableSerializeable.mf]; exact hsk
def EventRandAt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (T : ExecTrace) : TREvent → Prop
  | .SkippedKeyStored _ pk _ seed _ _ => TermRandAt i S g T seed ∧ TermRandAt i S g T pk
  | .ExposedMK _ seed _ _ => TermRandAt i S g T seed
  | .ExposedSpqr _ spqr _ => TermRandAt i S g T spqr
  | .Received _ _ _ _ m => TermRandAt i S g T m
  | _ => True
def PQEventRandAt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (T : ExecTrace) : PQXDHEvent → Prop
  | .IdentityRegistered _ ikPk vk _ => TermRandAt i S g T ikPk ∧ TermRandAt i S g T vk
  | .BobDone _ _ _ _ _ _ _ ek _ _ => TermRandAt i S g T ek
  | _ => True
def EntryRandAt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (T : ExecTrace) (ent : ExecTrace.Entry) : Prop :=
  (∀ e : Network.ExecEntryT, TraceEntryHas.proj ent = some e → TermRandAt i S g T e.msg) ∧
  (∀ e : StEntry, TraceEntryHas.proj ent = some e → StateRandAt i S g T e.st.state) ∧
  (∀ e : TREntry, TraceEntryHas.proj ent = some e → EventRandAt i S g T e.ev) ∧
  (∀ e : PQStEntry, TraceEntryHas.proj ent = some e → TermRandAt i S g T e.st.state.sk) ∧
  (∀ e : PQEvEntry, TraceEntryHas.proj ent = some e → PQEventRandAt i S g T e.ev)
def TraceEntriesRand (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (T tr : ExecTrace) : Prop :=
  (∀ b, tr.BaseAttackerKnows b → TermRandAt i S g T b) ∧ (∀ j (hj : j < tr.length), EntryRandAt i S g T (tr.at j hj))
theorem traceEntriesRand_nil : TraceEntriesRand i S g T (DY.Trace.nil : ExecTrace) :=
  ⟨fun _ h => by rw [Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1] at h; exact h.elim,
   fun _ hj => by simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at hj⟩
theorem traceEntriesRand_knows {tr : ExecTrace} (htr : TraceEntriesRand i S g T tr) {b : DY.Bytes} (hkn : b.AttackerKnows tr) : TermRandAt i S g T b :=
  attackerKnows_termRandAt htr.1 hkn
private theorem traceEntriesRand_append {tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] {e : E}
    (hbase : ∀ b, (tr.append e).BaseAttackerKnows b → TermRandAt i S g T b)
    (hent : EntryRandAt i S g T (TraceEntryHas.inj e)) (htr : TraceEntriesRand i S g T tr) : TraceEntriesRand i S g T (tr.append e) := by
  refine ⟨hbase, fun j hj => ?_⟩; by_cases hlt : j < tr.length
  · rw [← DY.Trace.at_le tr (tr.append e) j hlt (DY.Trace.append_le tr e)]; exact htr.2 j hlt
  · have heq : j = tr.length := by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hj; omega
    subst heq; simpa [Symbolic.DYBridge.DY.Trace.append_eq_1, DY.Trace.snoc, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] using hent

theorem traceEntriesRand_at?_net {tr : ExecTrace} (htr : TraceEntriesRand i S g T tr)
    {j : Nat} {e : Network.ExecEntryT} (h : (tr.at? j : Option Network.ExecEntryT) = some e) : TermRandAt i S g T e.msg := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).1 e h
  · cases h
theorem traceEntriesRand_at?_st {tr : ExecTrace} (htr : TraceEntriesRand i S g T tr)
    {j : Nat} {e : StEntry} (h : (tr.at? j : Option StEntry) = some e) : StateRandAt i S g T e.st.state := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).2.1 e h
  · cases h
private theorem traceEntriesRand_at?_tr {tr : ExecTrace} (htr : TraceEntriesRand i S g T tr)
    {j : Nat} {e : TREntry} (h : (tr.at? j : Option TREntry) = some e) : EventRandAt i S g T e.ev := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).2.2.1 e h
  · cases h
theorem traceEntriesRand_at?_pqst {tr : ExecTrace} (htr : TraceEntriesRand i S g T tr)
    {j : Nat} {e : PQStEntry} (h : (tr.at? j : Option PQStEntry) = some e) : TermRandAt i S g T e.st.state.sk := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).2.2.2.1 e h
  · cases h
private theorem traceEntriesRand_at?_pqev {tr : ExecTrace} (htr : TraceEntriesRand i S g T tr)
    {j : Nat} {e : PQEvEntry} (h : (tr.at? j : Option PQEvEntry) = some e) : PQEventRandAt i S g T e.ev := by
  unfold DY.Trace.at? at h; split at h
  · next hj => exact (htr.2 j hj).2.2.2.2 e h
  · cases h
private theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 = match (x.run tr).1 with | some a => ((f a).run (x.run tr).2.val).1 | none => none := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl
private theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val = match (x.run tr).1 with | some a => ((f a).run (x.run tr).2.val).2.val | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl
def TRand {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, (x.run tr).2.val ≤ T → TraceEntriesRand i S g T tr →
    TraceEntriesRand i S g T (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q a
theorem TRand.pure {α : Type} {Q : α → Prop} {a : α} (ha : Q a) : TRand (i := i) (S := S) (g := g) (T := T) Q (pure a) := by
  intro tr _ htr; rw [Traceful.run_pure]; exact ⟨htr, fun _ hb => Option.some.inj hb ▸ ha⟩
theorem TRand.failure {α : Type} {Q : α → Prop} : TRand (i := i) (S := S) (g := g) (T := T) Q (failure : Traceful α) := by
  intro tr _ htr; rw [Traceful.run_failure]; exact ⟨htr, fun _ hb => by cases hb⟩
theorem TRand.bind {α β : Type} {Q₁ : α → Prop} {Q₂ : β → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : TRand (i := i) (S := S) (g := g) (T := T) Q₁ x) (hf : ∀ a, Q₁ a → TRand (i := i) (S := S) (g := g) (T := T) Q₂ (f a)) :
    TRand (i := i) (S := S) (g := g) (T := T) Q₂ (x >>= f) := by
  intro tr hle htr; rw [run_bind_snd] at hle ⊢; rw [run_bind_fst]; revert hle
  cases h1 : (x.run tr).1 with
  | none => intro hle; exact ⟨(hx tr hle htr).1, fun _ hb => by cases hb⟩
  | some a =>
    intro hle; have h1' := hx tr (DY.Trace.le_trans _ _ _ ((f a).run (x.run tr).2.val).2.property hle) htr
    exact hf a (h1'.2 a h1) (x.run tr).2.val hle h1'.1
theorem TRand.guardP (p : Prop) {_ : Decidable p} :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (@_root_.guard Traceful _ p _) := by
  unfold _root_.guard; split
  · exact TRand.pure trivial
  · exact TRand.failure
theorem TRand.guardTrace (p : ExecTrace → Bool) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.TripleRatchet.guardTrace p) := by
  intro tr _ htr; unfold DY.Libsignal.TripleRatchet.guardTrace; erw [Traceful.run_mk]; exact ⟨htr, fun _ _ => trivial⟩
theorem TRand.requireTracePredicate (p : ExecTrace → Bool) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.PQXDH.guardTrace p) := by
  intro tr _ htr; unfold DY.Libsignal.PQXDH.guardTrace; simp only [Traceful.run_mk]; split <;> exact ⟨htr, fun _ _ => trivial⟩
theorem TRand.traceLength : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) DY.Libsignal.TripleRatchet.traceLength := by
  intro tr _ htr; unfold DY.Libsignal.TripleRatchet.traceLength; erw [Traceful.run_mk]; exact ⟨htr, fun _ _ => trivial⟩
private theorem TRand.getEntry_net (j : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (fun e : Network.ExecEntryT => TermRandAt i S g T e.msg) (DY.getEntry j) := by
  intro tr _ htr; rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ⟨htr, fun _ he => traceEntriesRand_at?_net htr he⟩
private theorem TRand.getEntry_st (j : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (fun e : StEntry => StateRandAt i S g T e.st.state) (DY.getEntry j) := by
  intro tr _ htr; rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ⟨htr, fun _ he => traceEntriesRand_at?_st htr he⟩
theorem TRand.getEntry_tr (j : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (fun e : TREntry => EventRandAt i S g T e.ev) (DY.getEntry j) := by
  intro tr _ htr; rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ⟨htr, fun _ he => traceEntriesRand_at?_tr htr he⟩
private theorem TRand.getEntry_pqst (j : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (fun e : PQStEntry => TermRandAt i S g T e.st.state.sk) (DY.getEntry j) := by
  intro tr _ htr; rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ⟨htr, fun _ he => traceEntriesRand_at?_pqst htr he⟩
private theorem TRand.getEntry_pqev (j : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (fun e : PQEvEntry => PQEventRandAt i S g T e.ev) (DY.getEntry j) := by
  intro tr _ htr; rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ⟨htr, fun _ he => traceEntriesRand_at?_pqev htr he⟩
theorem TRand.receiveMessage (j : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (TermRandAt i S g T) (Network.receiveMessage j) := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact TRand.bind (TRand.getEntry_net j) fun _ he => TRand.pure he
theorem TRand.getLocalState (p : Participant) (j : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (StateRandAt i S g T) (PersistentLocalState.getLocalState p j) := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact TRand.bind (TRand.bind (TRand.getEntry_st j) fun _ he => TRand.pure (Q := fun ls : PersistentLocalState.LocalState TRState => StateRandAt i S g T ls.state) he) fun _ hst => TRand.bind (TRand.guardP _) fun _ _ => TRand.pure hst
private theorem TRand.getPQLocalState (p : Participant) (j : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (fun s : PQXDHState => TermRandAt i S g T s.sk) (PersistentLocalState.getLocalState p j) := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact TRand.bind (TRand.bind (TRand.getEntry_pqst j) fun _ he => TRand.pure (Q := fun ls : PersistentLocalState.LocalState PQXDHState => TermRandAt i S g T ls.state.sk) he) fun _ hst => TRand.bind (TRand.guardP _) fun _ _ => TRand.pure hst
theorem TRand.getKey (p : Participant) (stateIdx : Nat) (kind : KeyKind) : TRand (i := i) (S := S) (g := g) (T := T) (TermRandAt i S g T) (DY.Libsignal.PQXDH.getKey p stateIdx kind) :=
  TRand.bind (TRand.getPQLocalState p stateIdx) fun _ hst => TRand.bind (TRand.guardP _) fun _ _ => TRand.pure hst
theorem TRand.lookupIdentity (p : Participant) (regIdx : Nat) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun kv : DY.Bytes × DY.Bytes => TermRandAt i S g T kv.1 ∧ TermRandAt i S g T kv.2) (DY.Libsignal.PQXDH.lookupIdentity p regIdx) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity; refine TRand.bind (TRand.getEntry_pqev regIdx) fun e he => ?_
  cases hev : e.ev with
  | IdentityRegistered p' _ _ _ => rw [hev] at he; exact TRand.bind (TRand.guardP (p' = p)) fun _ _ => TRand.pure he
  | _ => exact TRand.failure
private theorem proj_inj {E : Type} [ExecTraceTypes.Has E] (e : E) : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by rw [TraceEntryHas.inj_proj_eq]
private theorem randAt_append_self (tr : ExecTrace) (n : Nat) : RandAt (tr.append (DY.Random.ExecEntryT.mk n)) tr.length n := by
  have hlt : tr.length < (tr.append (DY.Random.ExecEntryT.mk n)).length := by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  unfold RandAt; simp only [DY.Trace.at?, hlt, ↓reduceDIte]
  simpa [Symbolic.DYBridge.DY.Trace.append_eq_1, DY.Trace.snoc, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] using proj_inj (DY.Random.ExecEntryT.mk n)
theorem TRand.genRand (n : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (TermRandAt i S g T) (DY.Random.genRand n) := by
  intro tr hle htr
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk] at hle ⊢
  dsimp only at hle ⊢; rw [Traceful.run_pure] at hle ⊢
  have hrnd : RandAt T tr.length n := RandAt.mono hle (randAt_append_self tr n)
  refine ⟨traceEntriesRand_append (fun b hb => ?_)
    ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr, ?_⟩
  · rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
    rcases hb with h0 | hb'
    · have h1 := (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        DY.Libsignal.Composed.baseAttackerKnowledge.internal tr (TraceEntryHas.inj (DY.Random.ExecEntryT.mk n) : ExecTrace.Entry) b).trans
        (Symbolic.DYBridge.DY.Random.baseAttackerKnowledge_attackerKnows tr (DY.Random.ExecEntryT.mk n) b)
      exact False.elim (Eq.mp h1 h0)
    · exact htr.1 b hb'
  · intro a ha; injection ha with ha; subst ha; exact termRandAt_rand i S g hrnd
theorem TRand.sendMessage {msg : DY.Bytes} (hm : TermRandAt i S g T msg) : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (Network.sendMessage msg) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceEntriesRand_append (fun b hb => ?_)
    ⟨(fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hm), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr, fun _ _ => trivial⟩
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
  rcases hb with h0 | hb'
  · have h1 := (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr (TraceEntryHas.inj (Network.ExecEntryT.mk msg) : ExecTrace.Entry) b).trans
      (Symbolic.DYBridge.DY.Network.baseAttackerKnowledge_attackerKnows tr (Network.ExecEntryT.mk msg) b)
    exact (Eq.mp h1 h0) ▸ hm
  · exact htr.1 b hb'
theorem TRand.storeLocalState (p : Participant) {st : TRState} (hst : StateRandAt i S g T st) : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceEntriesRand_append (fun b hb => ?_)
    ⟨(fun _ h => by cases h), (fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hst), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr, fun _ _ => trivial⟩
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
  rcases hb with h0 | hb'
  · let e : ExecTrace.Entry := TraceEntryHas.inj (⟨⟨p, st⟩⟩ : StEntry)
    have h1 := (((Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.CompromisableState.baseAttackerKnowledge.internal TRState) tr e.entry b)).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.State.baseAttackerKnowledge.internal TRState) tr e.entry.entry b)).trans
      (Symbolic.DYBridge.DY.PersistentGlobalState.State.baseAttackerKnowledge_attackerKnows (PersistentLocalState.LocalState TRState) tr ⟨⟨p, st⟩⟩ b)
    exact False.elim (Eq.mp h1 h0)
  · exact htr.1 b hb'
theorem TRand.storePQLocalState (p : Participant) {st : PQXDHState} (hsk : TermRandAt i S g T st.sk) : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceEntriesRand_append (fun b hb => ?_)
    ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hsk), (fun _ h => by cases h)⟩ htr, fun _ _ => trivial⟩
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
  rcases hb with h0 | hb'
  · let e : ExecTrace.Entry := TraceEntryHas.inj (⟨⟨p, st⟩⟩ : PQStEntry)
    have h1 := (((Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.CompromisableState.baseAttackerKnowledge.internal PQXDHState) tr e.entry b)).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.State.baseAttackerKnowledge.internal PQXDHState) tr e.entry.entry b)).trans
      (Symbolic.DYBridge.DY.PersistentGlobalState.State.baseAttackerKnowledge_attackerKnows (PersistentLocalState.LocalState PQXDHState) tr ⟨⟨p, st⟩⟩ b)
    exact False.elim (Eq.mp h1 h0)
  · exact htr.1 b hb'
theorem TRand.logEvent {ev : TREvent} (hev : EventRandAt i S g T ev) : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  refine ⟨traceEntriesRand_append (fun b hb => ?_)
    ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hev), (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr, fun _ _ => trivial⟩
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
  rcases hb with h0 | hb'
  · have h1 := (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr (TraceEntryHas.inj (⟨ev⟩ : TREntry) : ExecTrace.Entry) b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows TREvent tr ⟨ev⟩ b)
    exact False.elim (Eq.mp h1 h0)
  · exact htr.1 b hb'
theorem TRand.logPQEvent {ev : PQXDHEvent} (hev : PQEventRandAt i S g T ev) : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  refine ⟨traceEntriesRand_append (fun b hb => ?_)
    ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hev)⟩ htr, fun _ _ => trivial⟩
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
  rcases hb with h0 | hb'
  · have h1 := (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr (TraceEntryHas.inj (⟨ev⟩ : PQEvEntry) : ExecTrace.Entry) b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows PQXDHEvent tr ⟨ev⟩ b)
    exact False.elim (Eq.mp h1 h0)
  · exact htr.1 b hb'
theorem TRand.logCEvent (ev : ComposedEvent) : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro tr _ htr
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  refine ⟨traceEntriesRand_append (fun b hb => ?_)
    ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr, fun _ _ => trivial⟩
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2] at hb
  rcases hb with h0 | hb'
  · have h1 := (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr (TraceEntryHas.inj (⟨ev⟩ : CEvEntry) : ExecTrace.Entry) b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows ComposedEvent tr ⟨ev⟩ b)
    exact False.elim (Eq.mp h1 h0)
  · exact htr.1 b hb'

/-! ## Protocol Helpers and Ratchet Operations -/
theorem termRandAt_hmac {k m : DY.Bytes} (hk : TermRandAt i S g T k) (hm : TermRandAt i S g T m) : TermRandAt i S g T (hmac k m) := termRandAt_kdfExtract hk hm
theorem termRandAt_hkdfBlock1 {prk info : DY.Bytes} (hp : TermRandAt i S g T prk) (hi : TermRandAt i S g T info) : TermRandAt i S g T (hkdfBlock1 prk info) := termRandAt_hmac hp (termRandAt_concat hi (termRandAt_literalToBytes i S g T _))
theorem termRandAt_hkdfBlock2 {prk info : DY.Bytes} (hp : TermRandAt i S g T prk) (hi : TermRandAt i S g T info) : TermRandAt i S g T (hkdfBlock2 prk info) := termRandAt_hmac hp (termRandAt_concat (termRandAt_hkdfBlock1 hp hi) (termRandAt_concat hi (termRandAt_literalToBytes i S g T _)))
theorem termRandAt_hkdfBlock3 {prk info : DY.Bytes} (hp : TermRandAt i S g T prk) (hi : TermRandAt i S g T info) : TermRandAt i S g T (hkdfBlock3 prk info) := termRandAt_hmac hp (termRandAt_concat (termRandAt_hkdfBlock2 hp hi) (termRandAt_concat hi (termRandAt_literalToBytes i S g T _)))
private theorem termRandAt_kdfRk {rk dhOut : DY.Bytes} (hrk : TermRandAt i S g T rk) (hdh : TermRandAt i S g T dhOut) : TermRandAt i S g T (kdfRk rk dhOut).1 ∧ TermRandAt i S g T (kdfRk rk dhOut).2 :=
  ⟨termRandAt_hkdfBlock1 (termRandAt_hmac hrk hdh) (termRandAt_literalToBytes i S g T _), termRandAt_hkdfBlock2 (termRandAt_hmac hrk hdh) (termRandAt_literalToBytes i S g T _)⟩
theorem termRandAt_createChain {rk pk sk : DY.Bytes} (hrk : TermRandAt i S g T rk) (hpk : TermRandAt i S g T pk) (hsk : TermRandAt i S g T sk) : TermRandAt i S g T (createChain rk pk sk).1 ∧ TermRandAt i S g T (createChain rk pk sk).2 :=
  termRandAt_kdfRk hrk (termRandAt_dh (termRandAt_x25519Key hpk) hsk)
theorem termRandAt_kdfCk {ck : DY.Bytes} (hck : TermRandAt i S g T ck) : TermRandAt i S g T (kdfCk ck).1 ∧ TermRandAt i S g T (kdfCk ck).2 :=
  ⟨termRandAt_hmac hck (termRandAt_literalToBytes i S g T _), termRandAt_hmac hck (termRandAt_literalToBytes i S g T _)⟩
private theorem termRandAt_chainKeyAt : ∀ {ck : DY.Bytes} (n : Nat), TermRandAt i S g T ck → TermRandAt i S g T (chainKeyAt ck n)
  | _, 0, hck => hck
  | _, n + 1, hck => termRandAt_chainKeyAt n (termRandAt_kdfCk hck).1
theorem termRandAt_trMsgKeys {pqSalt seed : DY.Bytes} (hpq : TermRandAt i S g T pqSalt) (hs : TermRandAt i S g T seed) :
    TermRandAt i S g T (trMsgKeys pqSalt seed).cipherKey ∧ TermRandAt i S g T (trMsgKeys pqSalt seed).macKey ∧ TermRandAt i S g T (trMsgKeys pqSalt seed).iv := by
  have hp : TermRandAt i S g T (hmac pqSalt seed) := termRandAt_hmac hpq hs
  have hi : TermRandAt i S g T (lit "WhisperMessageKeys") := termRandAt_literalToBytes i S g T ("WhisperMessageKeys".toUTF8)
  exact ⟨termRandAt_hkdfBlock1 hp hi, termRandAt_hkdfBlock2 hp hi, termRandAt_hkdfBlock3 hp hi⟩
theorem termRandAt_computeMac {mk sik rik w : DY.Bytes} (hmk : TermRandAt i S g T mk) (hsik : TermRandAt i S g T sik) (hrik : TermRandAt i S g T rik) (hw : TermRandAt i S g T w) :
    TermRandAt i S g T (computeMac mk sik rik w) := termRandAt_trunc8 (termRandAt_hmac hmk (termRandAt_concat hsik (termRandAt_concat hrik hw)))
theorem termRandAt_trHonestWireMsg {rk ct pq : DY.Bytes} (hrk : TermRandAt i S g T rk) (c pc : UInt32) (hct : TermRandAt i S g T ct) (hpq : TermRandAt i S g T pq) :
    TermRandAt i S g T (trHonestWireMsg rk c pc ct pq) := termRandAt_trWireMsg hrk hct hpq
def TRSignalMsgRandAt (msg : TRSignalMsg) : Prop :=
  TermRandAt i S g T msg.wire ∧ TermRandAt i S g T msg.mac ∧ TermRandAt i S g T msg.ratchetKey ∧ TermRandAt i S g T msg.ciphertext ∧ TermRandAt i S g T msg.pqRatchet
private theorem termRandAt_parseTrSignalMsg {t : DY.Bytes} {msg : TRSignalMsg} (ht : TermRandAt i S g T t) (hp : parseTrSignalMsg t = some msg) :
    TRSignalMsgRandAt (i := i) (S := S) (g := g) (T := T) msg := by
  unfold parseTrSignalMsg at hp; simp only [bind, Option.bind] at hp; split at hp <;> try cases hp
  next p hsp =>
  rcases p with ⟨wire, mac⟩; rw [← DY.Concat.concat_split t (t.length - DY.Trunc.trunc8Length) wire mac hsp] at ht
  obtain ⟨hw, hm⟩ := (termRandAt_concat_pack i S g T ⟨wire, mac⟩).mp ht; dsimp only at hp; split at hp <;> try cases hp
  next x hx =>
  have hpv := DY.Bytes.pack_view? DY.TrWire.TrWireMsg.SubF wire
  change wire.view? DY.TrWire.TrWireMsg.SubF = some x at hx; rw [hx] at hpv
  have hwf := hw; rw [← hpv] at hwf; have h3 := (termRandAt_trWire_pack i S g T x).mp hwf; exact ⟨hw, hm, h3.1, h3.2.1, h3.2.2⟩
theorem TRand.receiveSignalMsg (msgIdx : Nat) :
    TRand (i := i) (S := S) (g := g) (T := T) (TRSignalMsgRandAt (i := i) (S := S) (g := g) (T := T)) (DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; refine TRand.bind (TRand.receiveMessage msgIdx) fun t ht => ?_; split
  · next msg hp => exact TRand.bind (TRand.guardP _) fun _ _ => TRand.pure (termRandAt_parseTrSignalMsg ht hp)
  · exact TRand.failure
def ChainRandAt (c : RecvChain) : Prop := TermRandAt i S g T c.ratchetKey ∧ TermRandAt i S g T c.chainKey
theorem termRandAt_findRecvChain {st : TRState} {pk : DY.Bytes} {c : RecvChain} (hst : StateRandAt i S g T st) (hf : findRecvChain st.recv pk = some c) :
    ChainRandAt (i := i) (S := S) (g := g) (T := T) c := hst.2.2.2.2.2.2.2 c (List.mem_of_find?_eq_some hf)
private theorem termRandAt_recvChainFor {st : TRState} {pk : DY.Bytes} {c : RecvChain} {b : Bool} (hst : StateRandAt i S g T st) (hpk : TermRandAt i S g T pk)
    (hr : recvChainFor st.toDRState pk = some (c, b)) : ChainRandAt (i := i) (S := S) (g := g) (T := T) c := by
  unfold recvChainFor at hr; split at hr
  · next c' hf => injection hr with hr; injection hr with hc _; subst hc; exact termRandAt_findRecvChain hst hf
  · split at hr
    · cases hr
    · injection hr with hr; injection hr with hc _; subst hc; exact ⟨hpk, (termRandAt_createChain hst.2.2.1 hpk hst.2.2.2.1).2⟩
private theorem TRand.dhRatchetStep {st : TRState} {pk : DY.Bytes} (hst : StateRandAt i S g T st) (hpk : TermRandAt i S g T pk) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun p : TRState × RecvChain => StateRandAt i S g T p.1 ∧ ChainRandAt (i := i) (S := S) (g := g) (T := T) p.2)
      (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine TRand.bind (TRand.guardP _) fun _ _ => TRand.bind (TRand.genRand 32) fun dhs hdhs => ?_
  have hc1 := termRandAt_createChain hst.2.2.1 hpk hst.2.2.2.1; have hc2 := termRandAt_createChain hc1.1 hpk hdhs
  have hc_new : ChainRandAt (i := i) (S := S) (g := g) (T := T) { ratchetKey := pk, chainKey := (createChain st.rk pk st.dhs).2, index := 0, rIdx := st.rIdx + 2 } := ⟨hpk, hc1.2⟩
  refine TRand.pure ⟨⟨hst.1, hst.2.1, hc2.1, hdhs, hc2.2, hst.2.2.2.2.2.1, hst.2.2.2.2.2.2.1, fun c' hc' => ?_⟩, hc_new⟩
  rcases List.mem_append.mp (List.mem_of_mem_drop hc') with hmem | hmem
  · exact hst.2.2.2.2.2.2.2 c' hmem
  · rcases List.mem_singleton.mp hmem with rfl; exact hc_new
theorem TRand.ensureReceiverChain {st : TRState} {pk : DY.Bytes} (hst : StateRandAt i S g T st) (hpk : TermRandAt i S g T pk) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun p : TRState × RecvChain × Bool => StateRandAt i S g T p.1 ∧ ChainRandAt (i := i) (S := S) (g := g) (T := T) p.2.1)
      (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · next c hr => exact TRand.pure ⟨hst, termRandAt_recvChainFor hst hpk hr⟩
  · exact TRand.bind (TRand.dhRatchetStep hst hpk) fun ⟨_, _⟩ h => TRand.pure h
  · exact TRand.failure
theorem termRandAt_consumeMessageKey {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (hc : ChainRandAt (i := i) (S := S) (g := g) (T := T) c) (hcm : consumeMessageKey c counter = some (seed, c')) :
    TermRandAt i S g T seed ∧ ChainRandAt (i := i) (S := S) (g := g) (T := T) c' := by
  unfold consumeMessageKey at hcm; split at hcm <;> try cases hcm
  split at hcm <;> try cases hcm
  split at hcm <;> try cases hcm
  have hck := termRandAt_kdfCk (termRandAt_chainKeyAt (counter.toNat - c.index.toNat) hc.2); exact ⟨hck.2, hc.1, hck.1⟩
theorem stateRandAt_setRecvChain {st : TRState} {c' : RecvChain} {spqr' : DY.Bytes}
    (hst : StateRandAt i S g T st) (hc' : ChainRandAt (i := i) (S := S) (g := g) (T := T) c') (hspqr' : TermRandAt i S g T spqr') :
    StateRandAt i S g T { st with recv := setRecvChain st.recv c', spqr := spqr' } := by
  refine ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2.1, hst.2.2.2.2.2.1, hspqr', fun c hc => ?_⟩
  unfold setRecvChain at hc; obtain ⟨c₀, hc₀, heq⟩ := List.mem_map.mp hc; split at heq <;> subst heq
  · exact hc'
  · exact hst.2.2.2.2.2.2.2 c₀ hc₀
theorem TRand.verifyMacAndDecrypt {st : TRState} {msg : TRSignalMsg} {pqSalt seed : DY.Bytes}
    (hmsg : TRSignalMsgRandAt (i := i) (S := S) (g := g) (T := T) msg) :
    TRand (i := i) (S := S) (g := g) (T := T) (TermRandAt i S g T) (DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  refine TRand.bind (TRand.guardP _) fun _ _ tr _ htr => by
    erw [Traceful.run_mk]; exact ⟨htr, fun _ hm => termRandAt_symDec hm hmsg.2.2.2.1⟩
theorem TRand.logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) (hpk : TermRandAt i S g T pk) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat), TermRandAt i S g T ck →
      TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0, _ => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact TRand.pure trivial
  | ck, n, k + 1, hck => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys; have hkdf := termRandAt_kdfCk hck
    exact TRand.bind (TRand.logEvent ⟨hkdf.2, hpk⟩) fun _ _ => TRand.logSkippedKeys s pk rIdx src hpk (kdfCk ck).1 (n + 1) k hkdf.1
theorem TRand.logMessageKeyAndStore (me : Participant) (s : SessionInfo) (dir : KeyDir)
    (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) {st : TRState} (hst : StateRandAt i S g T st) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) :=
  TRand.bind (TRand.logEvent trivial) fun _ _ => TRand.storeLocalState me hst

end Core

end Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase

-- AUTO-BRIDGE BEGIN
namespace Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (RandAt MemoRandAt TermRandAt termRandAt_rand termRandAt_dhPk_pack)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (termRandAt_kemPk_pack termRandAt_x25519Key termRandAt_dh)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (termRandAt_literalToBytes termRandAt_concat termRandAt_dhPk termRandAt_kemPk)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (termRandAt_kemEncap termRandAt_kemDecap termRandAt_kemRej termRandAt_vk termRandAt_sign)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (termRandAt_symEnc termRandAt_spqrParams termRandAt_spqrInit termRandAt_spqrSend)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (termRandAt_spqrRecv attackerKnows_termRandAt termRandAt_compat StEntry TREntry)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (PQStEntry PQEvEntry CEvEntry StateRandAt termRandAt_serialize_tr)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (termRandAt_serialize_pq EventRandAt PQEventRandAt EntryRandAt TraceEntriesRand)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (traceEntriesRand_nil traceEntriesRand_knows traceEntriesRand_at?_net)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (traceEntriesRand_at?_st traceEntriesRand_at?_pqst TRand termRandAt_hmac)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (termRandAt_hkdfBlock1 termRandAt_hkdfBlock2 termRandAt_hkdfBlock3)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (termRandAt_createChain termRandAt_kdfCk termRandAt_trMsgKeys)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (termRandAt_computeMac termRandAt_trHonestWireMsg TRSignalMsgRandAt ChainRandAt)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase (termRandAt_findRecvChain termRandAt_consumeMessageKey stateRandAt_setRecvChain)
end Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
namespace Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux.RandAt
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase.RandAt (mono)
end Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux.RandAt
namespace Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux.TermRandAt
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase.TermRandAt (mono)
end Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux.TermRandAt
namespace Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux.TRand
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase.TRand (pure failure bind guardP guardTrace requireTracePredicate traceLength)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase.TRand (getEntry_tr receiveMessage getLocalState getKey lookupIdentity genRand)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase.TRand (sendMessage storeLocalState storePQLocalState logEvent logPQEvent logCEvent)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase.TRand (receiveSignalMsg ensureReceiverChain verifyMacAndDecrypt logSkippedKeys)
export Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase.TRand (logMessageKeyAndStore)
end Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux.TRand
-- AUTO-BRIDGE END
