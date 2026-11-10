/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators
import Symbolic.BugInjection.Proofs.Common443.CompC2KdfInjRest

/-!
# Per-Constructor `TermAt` and `SafeMemo` Lemmas

Proves `TermAt` closure for all `DagOp` constructors and `SafeMemo` preservation for opaque PKI,
SPQR, and receiver-trial operations.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTermAt

open DY
open scoped DY.Libsignal.Composed
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (canonicalVariation)
open DY.Libsignal.TripleRatchet
  (trHonestWireMsg messageVersion spqrA2B spqrB2A lit litByte
   hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 trMsgKeys kdfCk computeMac TRSignalMsg)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compKyberEncaps)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost ConcretizedTerm TrialCtx trialTerms
   node concretizeRandom
   gRandom gLit0 gConcat0 gDhPk gDh gKdf0 gSym0 gTrunc0 gTrWire0
   gamma' gamma randTerm litOf clamp trWireBytes assumedInjective)
open Symbolic.BugInjection.Proofs.Common443.Census443Memo
  (memoOK_kemPk memoOK_spqrInit memoOK_spqrInit_elim memoOK_spqrChainKey
   memoOK_spqrSendState memoOK_spqrSendKey_pack memoOK_spqrSendMsg memoOK_spqrRecvState_pack)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
  (ms_pack_random ms_pack_lit ms_pack_concat ms_pack_dhPk ms_pack_dh
   ms_pack_kdf ms_pack_sym ms_pack_trunc ms_pack_trWire)
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
  (assumedInjective_lit memoOK_vk memoOK_sign memoOK_spqrRecvKey_pack)
open Symbolic.BugInjection.Proofs.Common443.CompC2KdfInjRest
  (assumedInjective_concat assumedInjective_trWire)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
  (gamma'_kemEncap_of_len32 gamma'_kemSS_of_len32)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedLookupPub evictedLookupDh evictedAesPerm)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
  (evictedLookupDh_comm)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
  (DagOp dagOpBytesOk dagNodeOk evalDagShapeAux)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators
  (dagShape dagShape_unfold SafeEntry SafeMemo TermAt
   safeMemo_plaintext safeMemo_symDec safeMemo_lit_short safeMemo_randTerm_zero)

section Combinators

variable {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
variable {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}

private theorem topo_of_nodes (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true) :
    ∀ i < dagSize, (opOf i).childrenLt i = true := by
  intro i hi
  have h := hNodes i hi
  unfold dagNodeOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

private theorem bytesOk_of_nodes (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {id : Nat} (hid : id < dagSize) :
    dagOpBytesOk bytesOf id (opOf id) = true := by
  have h := hNodes id hid
  unfold dagNodeOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

private theorem termAt_of_node {b : Bytes} {id : Nat} {cs : List ConcretizedTerm}
    (hid : id < dagSize)
    (hg : gamma' evictedI0 S g b = node (bytesOf id) b (dagShape opOf dagSize id) cs)
    (hai : assumedInjective b = true → (opOf id).isAI = true)
    (hcs : ∀ c ∈ cs, ∀ x ∈ c.memo, SafeEntry dagSize opOf bytesOf pts x) :
    TermAt dagSize opOf bytesOf S g pts b id := by
  refine ⟨hid, by rw [hg]; rfl, by rw [hg]; rfl, ?_⟩
  intro x hx
  rw [hg] at hx
  simp only [node, List.mem_cons, List.mem_flatMap] at hx
  rcases hx with rfl | ⟨c, hc, hxc⟩
  · exact Or.inr (Or.inr ⟨id, hid, rfl, rfl, hai⟩)
  · exact hcs c hc x hxc

theorem termAt_lit (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {ba : ByteArray} {id : Nat} (hid : id < dagSize)
    (hop : opOf id = .lit (DY.Libsignal.Composed.Refinement.ofByteArray ba)) :
    TermAt dagSize opOf bytesOf S g pts (DY.Literal.literalToBytes ba) id := by
  set v := DY.Libsignal.Composed.Refinement.ofByteArray ba
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id = litOf v := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]
  have hba : DY.Literal.literalToBytes ba = litOf v := by
    unfold litOf DY.Literal.literalToBytes
    congr 1; apply ByteArray.ext
    change ba.data = (v.map UInt8.ofBitVec).toArray
    rw [← Array.toList_inj, List.toList_toArray]
    change ba.data.toList = (ba.data.toList.map UInt8.toBitVec).map UInt8.ofBitVec
    induction ba.data.toList with
    | nil => rfl
    | cons u us ih => exact congrArg (u :: ·) ih
  have hg := ms_pack_lit evictedI0 S g { lit := ba }
  change gamma' evictedI0 S g (DY.Literal.literalToBytes ba) = _ at hg
  apply termAt_of_node hid (cs := [])
  · rw [hg]; unfold gLit0 DY.Libsignal.Composed.Refinement.concretizeLit
    change node v (DY.Literal.literalToBytes ba) (DY.Literal.literalToBytes ba) [] = _
    rw [← hbok, hsh, ← hba]
  · intro h; rw [assumedInjective_lit ba] at h; cases h
  · intro _ hc; cases hc

theorem termAt_litOf (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {v : HwBytes} {id : Nat} (hid : id < dagSize) (hop : opOf id = .lit v) :
    TermAt dagSize opOf bytesOf S g pts (litOf v) id := by
  have hv_aux : ∀ l : HwBytes, (l.map UInt8.ofBitVec).map UInt8.toBitVec = l := by
    intro l; induction l with
    | nil => rfl
    | cons b bs ih => exact congrArg (b :: ·) ih
  let ba := ByteArray.mk (v.map UInt8.ofBitVec).toArray
  have hv : DY.Libsignal.Composed.Refinement.ofByteArray ba = v := hv_aux v
  exact termAt_lit hNodes hid (hop.trans (congrArg DagOp.lit hv.symm))

theorem randTerm_eq_dagShape (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {ts sz id : Nat} (hid : id < dagSize) (hop : opOf id = .rand ts sz) :
    randTerm ts sz = dagShape opOf dagSize id := by
  rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]

theorem termAt_rand (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {ts sz id : Nat} (hid : id < dagSize) (hop : opOf id = .rand ts sz)
    (hσ : g.σ ts sz = bytesOf id) :
    TermAt dagSize opOf bytesOf S g pts (randTerm ts sz) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, decide_eq_true_eq] at hbok
  have hsh : dagShape opOf dagSize id = randTerm ts sz := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]
  have hg := ms_pack_random evictedI0 S g ⟨ts, sz⟩
  change gamma' evictedI0 S g (randTerm ts sz) = _ at hg
  apply termAt_of_node hid (cs := [])
  · rw [hg]; dsimp only [gRandom, concretizeRandom]
    simp only [hbok, ↓reduceIte, hσ, hsh]; rfl
  · intro _; rw [hop]; rfl
  · intro _ hc; cases hc

theorem termAt_concat (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {a b : Bytes} {l r id : Nat} (hid : id < dagSize) (hop : opOf id = .concat l r)
    (ha : TermAt dagSize opOf bytesOf S g pts a l)
    (hb : TermAt dagSize opOf bytesOf S g pts b r) :
    TermAt dagSize opOf bytesOf S g pts (DY.Concat.concat a b) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id = DY.Concat.concat (dagShape opOf dagSize l) (dagShape opOf dagSize r) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hg := ms_pack_concat evictedI0 S g ⟨a, b⟩
  change gamma' evictedI0 S g (DY.Concat.concat a b) = _ at hg
  apply termAt_of_node hid (cs := [gamma' evictedI0 S g a, gamma' evictedI0 S g b])
  · rw [hg]; unfold gConcat0 DY.Libsignal.Composed.Refinement.concretizeConcat; dsimp only
    rw [ha.2.1, hb.2.1, ← hbok, ha.2.2.1, hb.2.2.1, hsh]; rfl
  · intro h; rw [assumedInjective_concat] at h; cases h
  · intro c hc x hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha.2.2.2 x hxc
    · exact hb.2.2.2 x hxc

theorem termAt_dhPk (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {sk : Bytes} {s id : Nat} (hid : id < dagSize) (hop : opOf id = .dhPk s)
    (hs : TermAt dagSize opOf bytesOf S g pts sk s) :
    TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id = DY.DiffieHellman.dhPk (dagShape opOf dagSize s) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hg := ms_pack_dhPk evictedI0 S g ⟨sk⟩
  change gamma' evictedI0 S g (DY.DiffieHellman.dhPk sk) = _ at hg
  apply termAt_of_node hid (cs := [gamma' evictedI0 S g sk])
  · rw [hg]; unfold gDhPk DY.Libsignal.Composed.Refinement.concretizeDhPk; dsimp only
    rw [hs.2.1, hs.2.2.1, hsh]
    change node (evictedLookupPub (clamp (bytesOf s))) _ _ _ = _
    rw [← hbok]; rfl
  · intro _; rw [hop]; rfl
  · intro c hc x hxc
    simp only [List.mem_singleton] at hc; subst hc
    exact hs.2.2.2 x hxc

/-- Order-independent `TermAt` for `dh (dhPk sk1) sk2` against a single canonical `.dh pk1_id s2_id` node. -/
theorem termAt_dh (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {sk1 sk2 : Bytes} {s1_id pk1_id s2_id pk2_id id : Nat}
    (hid : id < dagSize) (hop : opOf id = .dh pk1_id s2_id)
    (hop_pk1 : opOf pk1_id = .dhPk s1_id)
    (hop_pk2 : opOf pk2_id = .dhPk s2_id)
    (hsh1 : sk1 = dagShape opOf dagSize s1_id)
    (hsh2 : sk2 = dagShape opOf dagSize s2_id)
    (hs1 : TermAt dagSize opOf bytesOf S g pts sk1 s1_id)
    (hp1 : TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk1) pk1_id)
    (hs2 : TermAt dagSize opOf bytesOf S g pts sk2 s2_id)
    (hp2 : TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk2) pk2_id) :
    TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk sk1) sk2) id := by
  subst hsh1 hsh2
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hbpk1 := bytesOk_of_nodes hNodes hp1.1
  rw [hop_pk1] at hbpk1; simp only [dagOpBytesOk, beq_iff_eq] at hbpk1
  have hbpk2 := bytesOk_of_nodes hNodes hp2.1
  rw [hop_pk2] at hbpk2; simp only [dagOpBytesOk, beq_iff_eq] at hbpk2
  have hsh_pk1 : dagShape opOf dagSize pk1_id = DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hp1.1]; simp only [evalDagShapeAux, hop_pk1]; rfl
  have hsh_pk2 : dagShape opOf dagSize pk2_id = DY.DiffieHellman.dhPk (dagShape opOf dagSize s2_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hp2.1]; simp only [evalDagShapeAux, hop_pk2]; rfl
  have hsh_id : dagShape opOf dagSize id =
      DY.DiffieHellman.dh (DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id))
        (dagShape opOf dagSize s2_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]
    change DY.DiffieHellman.dh (dagShape opOf dagSize pk1_id) (dagShape opOf dagSize s2_id) = _
    rw [hsh_pk1]
  by_cases hge : dagShape opOf dagSize s2_id ≤ dagShape opOf dagSize s1_id
  · have heq : DY.DiffieHellman.dh (DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id))
        (dagShape opOf dagSize s2_id) =
        ({ pk := DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id),
           sk := dagShape opOf dagSize s2_id } : DY.DiffieHellman.Dh.SubF Bytes).pack := by
      simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh,
        DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk, DY.BytesView.view_pack, hge, ↓reduceIte]
    have hsh := hsh_id.trans heq
    rw [heq]
    have hg := ms_pack_dh evictedI0 S g
      ⟨DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id), dagShape opOf dagSize s2_id⟩
    apply termAt_of_node hid
      (cs := [gamma' evictedI0 S g (DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id)),
              gamma' evictedI0 S g (dagShape opOf dagSize s2_id)])
    · rw [hg]; unfold gDh DY.Libsignal.Composed.Refinement.concretizeDh; dsimp only
      rw [hp1.2.1, hs2.2.1, hp1.2.2.1, hs2.2.2.1, hsh_pk1, hsh]
      change node (evictedLookupDh (clamp (bytesOf s2_id)) (bytesOf pk1_id)) _ _ _ = _
      rw [← hbok]
    · intro _; rw [hop]; rfl
    · intro c hc x hxc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hp1.2.2.2 x hxc
      · exact hs2.2.2.2 x hxc
  · have heq : DY.DiffieHellman.dh (DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id))
        (dagShape opOf dagSize s2_id) =
        ({ pk := DY.DiffieHellman.dhPk (dagShape opOf dagSize s2_id),
           sk := dagShape opOf dagSize s1_id } : DY.DiffieHellman.Dh.SubF Bytes).pack := by
      simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh,
        DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk, DY.BytesView.view_pack, hge, ↓reduceIte]
    have hsh := hsh_id.trans heq
    rw [heq]
    have hg := ms_pack_dh evictedI0 S g
      ⟨DY.DiffieHellman.dhPk (dagShape opOf dagSize s2_id), dagShape opOf dagSize s1_id⟩
    apply termAt_of_node hid
      (cs := [gamma' evictedI0 S g (DY.DiffieHellman.dhPk (dagShape opOf dagSize s2_id)),
              gamma' evictedI0 S g (dagShape opOf dagSize s1_id)])
    · rw [hg]; unfold gDh DY.Libsignal.Composed.Refinement.concretizeDh; dsimp only
      rw [hp2.2.1, hs1.2.1, hp2.2.2.1, hs1.2.2.1, hsh_pk2, hsh]
      change node (evictedLookupDh (clamp (bytesOf s1_id)) (bytesOf pk2_id)) _ _ _ = _
      rw [hbpk2, evictedLookupDh_comm, ← hbpk1, ← hbok]
    · intro _; rw [hop]; rfl
    · intro c hc x hxc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hp2.2.2.2 x hxc
      · exact hs1.2.2.2 x hxc

theorem termAt_dh_symm (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {sk1 sk2 : Bytes} {s1_id pk1_id s2_id pk2_id id : Nat}
    (hid : id < dagSize) (hop : opOf id = .dh pk1_id s2_id)
    (hop_pk1 : opOf pk1_id = .dhPk s1_id)
    (hop_pk2 : opOf pk2_id = .dhPk s2_id)
    (hsh1 : sk1 = dagShape opOf dagSize s1_id)
    (hsh2 : sk2 = dagShape opOf dagSize s2_id)
    (hs1 : TermAt dagSize opOf bytesOf S g pts sk1 s1_id)
    (hp1 : TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk1) pk1_id)
    (hs2 : TermAt dagSize opOf bytesOf S g pts sk2 s2_id)
    (hp2 : TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk2) pk2_id) :
    TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk sk2) sk1) id := by
  rw [DY.DiffieHellman.dh_commutes]
  exact termAt_dh hNodes hid hop hop_pk1 hop_pk2 hsh1 hsh2 hs1 hp1 hs2 hp2

theorem termAt_kdf (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {a b : Bytes} {a_id b_id id : Nat} (hid : id < dagSize) (hop : opOf id = .kdf a_id b_id)
    (ha : TermAt dagSize opOf bytesOf S g pts a a_id)
    (hb : TermAt dagSize opOf bytesOf S g pts b b_id) :
    TermAt dagSize opOf bytesOf S g pts (DY.KdfExtract.kdfExtract a b) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id =
      DY.KdfExtract.kdfExtract (dagShape opOf dagSize a_id) (dagShape opOf dagSize b_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hg := ms_pack_kdf evictedI0 S g ⟨a, b⟩
  change gamma' evictedI0 S g (DY.KdfExtract.kdfExtract a b) = _ at hg
  apply termAt_of_node hid (cs := [gamma' evictedI0 S g a, gamma' evictedI0 S g b])
  · rw [hg]; unfold gKdf0 DY.Libsignal.Composed.Refinement.concretizeKdf; dsimp only
    rw [ha.2.1, hb.2.1, ← hbok, ha.2.2.1, hb.2.2.1, hsh]; rfl
  · intro _; rw [hop]; rfl
  · intro c hc x hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha.2.2.2 x hxc
    · exact hb.2.2.2 x hxc

theorem termAt_trunc8 (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {a : Bytes} {a_id id : Nat} (hid : id < dagSize) (hop : opOf id = .trunc8 a_id)
    (ha : TermAt dagSize opOf bytesOf S g pts a a_id) :
    TermAt dagSize opOf bytesOf S g pts (DY.Trunc.trunc8 a) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id = DY.Trunc.trunc8 (dagShape opOf dagSize a_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hg := ms_pack_trunc evictedI0 S g ⟨a⟩
  change gamma' evictedI0 S g (DY.Trunc.trunc8 a) = _ at hg
  apply termAt_of_node hid (cs := [gamma' evictedI0 S g a])
  · rw [hg]; unfold gTrunc0 DY.Libsignal.Composed.Refinement.concretizeTrunc; dsimp only
    rw [ha.2.1, ← hbok, ha.2.2.1, hsh]; rfl
  · intro _; rw [hop]; rfl
  · intro c hc x hxc
    simp only [List.mem_singleton] at hc; subst hc
    exact ha.2.2.2 x hxc

theorem termAt_symEncPt (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {k iv : Bytes} {k_id iv_id ptTs id : Nat} {ptBs : HwBytes}
    (hid : id < dagSize) (hop : opOf id = .symEncPt k_id iv_id ptTs ptBs)
    (hk : TermAt dagSize opOf bytesOf S g pts k k_id)
    (hiv : TermAt dagSize opOf bytesOf S g pts iv iv_id)
    (hpt_mem : randTerm ptTs 32 ∈ pts)
    (hσ : g.σ ptTs 32 = ptBs)
    (hlen : ptBs.length < 8) :
    TermAt dagSize opOf bytesOf S g pts (DY.SymEnc.symEnc k iv (randTerm ptTs 32)) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id =
      DY.SymEnc.symEnc (dagShape opOf dagSize k_id) (dagShape opOf dagSize iv_id) (randTerm ptTs 32) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hgpt := ms_pack_random evictedI0 S g ⟨ptTs, 32⟩
  change gamma' evictedI0 S g (randTerm ptTs 32) = _ at hgpt
  have hpt_bs : (gamma' evictedI0 S g (randTerm ptTs 32)).bytes = ptBs := by
    rw [hgpt]; dsimp only [gRandom, concretizeRandom]; simp only [Nat.reduceEqDiff, ↓reduceIte, node]; exact hσ
  have hpt_sh : (gamma' evictedI0 S g (randTerm ptTs 32)).shape = randTerm ptTs 32 := by
    rw [hgpt]; dsimp only [gRandom, concretizeRandom]; simp only [Nat.reduceEqDiff, ↓reduceIte, node]; rfl
  have hpt_sm : SafeMemo dagSize opOf bytesOf S g pts (randTerm ptTs 32) :=
    safeMemo_plaintext hpt_mem (by rw [hσ]; exact hlen)
  have hg := ms_pack_sym evictedI0 S g ⟨k, iv, randTerm ptTs 32⟩
  change gamma' evictedI0 S g (DY.SymEnc.symEnc k iv (randTerm ptTs 32)) = _ at hg
  apply termAt_of_node hid
    (cs := [gamma' evictedI0 S g k, gamma' evictedI0 S g iv, gamma' evictedI0 S g (randTerm ptTs 32)])
  · rw [hg]; unfold gSym0 DY.Libsignal.Composed.Refinement.concretizeSym; dsimp only
    rw [hk.2.1, hiv.2.1, hpt_bs, hk.2.2.1, hiv.2.2.1, hpt_sh, hsh]
    change node (evictedAesPerm (bytesOf k_id) ((bytesOf iv_id).take 16) ptBs) _ _ _ = _
    rw [← hbok]; rfl
  · intro _; rw [hop]; rfl
  · intro c hc x hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hk.2.2.2 x hxc
    · exact hiv.2.2.2 x hxc
    · exact hpt_sm x hxc

theorem termAt_trWire (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {rk ct pq : Bytes} {cnt prev : UInt32} {rk_id ct_id pq_id id : Nat} {addr : HwBytes}
    (hid : id < dagSize) (hop : opOf id = .trWire messageVersion rk_id cnt prev ct_id pq_id addr)
    (hrk : TermAt dagSize opOf bytesOf S g pts rk rk_id)
    (hct : TermAt dagSize opOf bytesOf S g pts ct ct_id)
    (hpq : TermAt dagSize opOf bytesOf S g pts pq pq_id)
    (haddr : g.addr (trHonestWireMsg rk cnt prev ct pq) = addr) :
    TermAt dagSize opOf bytesOf S g pts (trHonestWireMsg rk cnt prev ct pq) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id =
      DY.TrWire.trWireMsg messageVersion (dagShape opOf dagSize rk_id) cnt prev
        (dagShape opOf dagSize ct_id) (dagShape opOf dagSize pq_id)
        { canonicalVariation with fields := .extra 6 (.bytes addr) 0 0 :: canonicalVariation.fields } := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have haddr' : g.addr (DY.BytesView.pack (SubF := DY.TrWire.TrWireMsg.SubF)
      ⟨messageVersion, rk, cnt, prev, ct, pq, canonicalVariation⟩) = addr := haddr
  have hg := ms_pack_trWire evictedI0 S g ⟨messageVersion, rk, cnt, prev, ct, pq, canonicalVariation⟩
  change gamma' evictedI0 S g (trHonestWireMsg rk cnt prev ct pq) = _ at hg
  apply termAt_of_node hid
    (cs := [gamma' evictedI0 S g rk, gamma' evictedI0 S g ct, gamma' evictedI0 S g pq])
  · rw [hg]; unfold gTrWire0 DY.Libsignal.Composed.Refinement.concretizeTrWire; dsimp only
    rw [haddr', hrk.2.1, hct.2.1, hpq.2.1, ← hbok, hrk.2.2.1, hct.2.2.1, hpq.2.2.1, hsh]
    rfl
  · intro h
    have hw := assumedInjective_trWire messageVersion rk cnt prev ct pq canonicalVariation
    change assumedInjective (trHonestWireMsg rk cnt prev ct pq) = false at hw
    rw [hw] at h; cases h
  · intro c hc x hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hrk.2.2.2 x hxc
    · exact hct.2.2.2 x hxc
    · exact hpq.2.2.2 x hxc

theorem termAt_kemEncap (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {pk e : Bytes} {p_id e_id id1 id2 : Nat}
    (hid1 : id1 < dagSize) (hop1 : opOf id1 = .kemEncap p_id e_id)
    (hid2 : id2 < dagSize) (hop2 : opOf id2 = .kemSS p_id e_id)
    (hp : TermAt dagSize opOf bytesOf S g pts pk p_id)
    (he : TermAt dagSize opOf bytesOf S g pts e e_id) :
    TermAt dagSize opOf bytesOf S g pts (DY.PQKem.kemEncap pk e).1 id1 ∧
      TermAt dagSize opOf bytesOf S g pts (DY.PQKem.kemEncap pk e).2 id2 := by
  have hbok1 := bytesOk_of_nodes hNodes hid1
  rw [hop1] at hbok1
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hbok1
  have hbok2 := bytesOk_of_nodes hNodes hid2
  rw [hop2] at hbok2
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hbok2
  have he_g : gamma evictedI0 S g e = bytesOf e_id := he.2.1
  have helen : (gamma evictedI0 S g e).length = 32 := by rw [he_g, hbok1.1]
  have hsh1 : dagShape opOf dagSize id1 =
      ({ pk := dagShape opOf dagSize p_id, entropy := dagShape opOf dagSize e_id } :
        DY.PQKem.Encap.SubF Bytes).pack := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid1]; simp only [evalDagShapeAux, hop1]; rfl
  have hsh2 : dagShape opOf dagSize id2 =
      ({ pk := dagShape opOf dagSize p_id, entropy := dagShape opOf dagSize e_id } :
        DY.PQKem.SharedSecret.SubF Bytes).pack := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid2]; simp only [evalDagShapeAux, hop2]; rfl
  constructor
  · apply termAt_of_node hid1 (cs := [gamma' evictedI0 S g pk, gamma' evictedI0 S g e])
    · rw [gamma'_kemEncap_of_len32 (i := evictedI0) (S := S) (g := g) helen]
      rw [he_g, hp.2.2.1, he.2.2.1, hsh1]
      change node ((compKyberEncaps (bytesOf e_id)).take 1568) _ _ _ = _
      rw [← hbok1.2]
    · intro _; rw [hop1]; rfl
    · intro c hc x hxc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hp.2.2.2 x hxc
      · exact he.2.2.2 x hxc
  · apply termAt_of_node hid2 (cs := [gamma' evictedI0 S g pk, gamma' evictedI0 S g e])
    · rw [gamma'_kemSS_of_len32 (i := evictedI0) (S := S) (g := g) helen]
      rw [he_g, hp.2.2.1, he.2.2.1, hsh2]
      change node ((compKyberEncaps (bytesOf e_id)).drop 1568) _ _ _ = _
      rw [← hbok2.2]
    · intro _; rw [hop2]; rfl
    · intro c hc x hxc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hp.2.2.2 x hxc
      · exact he.2.2.2 x hxc

/-- Maps an opaque term `b` with `(gamma' evictedI0 S g b).bytes = v`, `.shape = litOf v`, and
`SafeMemo` to a `.lit v` DAG node. -/
theorem termAt_of_opaque (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {b : Bytes} {v : HwBytes} {id : Nat} (hid : id < dagSize) (hop : opOf id = .lit v)
    (hbs : (gamma' evictedI0 S g b).bytes = v)
    (hsh_b : (gamma' evictedI0 S g b).shape = litOf v)
    (hsm : SafeMemo dagSize opOf bytesOf S g pts b) :
    TermAt dagSize opOf bytesOf S g pts b id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id = litOf v := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]
  exact ⟨hid, hbs.trans hbok.symm, hsh_b.trans hsh.symm, hsm⟩

theorem safeMemo_kemPk {sk : Bytes} (hsk : SafeMemo dagSize opOf bytesOf S g pts sk) :
    SafeMemo dagSize opOf bytesOf S g pts (DY.PQKem.kemPk sk) :=
  memoOK_kemPk hsk

theorem safeMemo_vk {sk : Bytes} (hsk : SafeMemo dagSize opOf bytesOf S g pts sk) :
    SafeMemo dagSize opOf bytesOf S g pts (DY.Signature.vk sk) :=
  memoOK_vk hsk

theorem safeMemo_sign {sk nonce msg : Bytes}
    (hsk : SafeMemo dagSize opOf bytesOf S g pts sk)
    (hn : SafeMemo dagSize opOf bytesOf S g pts nonce)
    (hm : SafeMemo dagSize opOf bytesOf S g pts msg) :
    SafeMemo dagSize opOf bytesOf S g pts (DY.Signature.sign sk nonce msg) :=
  memoOK_sign hsk hn hm

theorem safeMemo_spqrInit {k p : Bytes}
    (hk : SafeMemo dagSize opOf bytesOf S g pts k)
    (hp : SafeMemo dagSize opOf bytesOf S g pts p) :
    SafeMemo dagSize opOf bytesOf S g pts (DY.Spqr.spqrInit k p) :=
  memoOK_spqrInit hk hp

theorem safeMemo_spqrSend {st coins : Bytes}
    (hst : SafeMemo dagSize opOf bytesOf S g pts st)
    (hc : SafeMemo dagSize opOf bytesOf S g pts coins) :
    SafeMemo dagSize opOf bytesOf S g pts (DY.Spqr.spqrSend st coins).1 ∧
      SafeMemo dagSize opOf bytesOf S g pts (DY.Spqr.spqrSend st coins).2.1 ∧
      SafeMemo dagSize opOf bytesOf S g pts (DY.Spqr.spqrSend st coins).2.2 := by
  refine ⟨memoOK_spqrSendState hst hc, ?_, memoOK_spqrSendMsg hst hc⟩
  have hpv := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
  unfold DY.Spqr.spqrSend; dsimp only
  split
  · next authKey params hx =>
    have hst' := hst
    rw [hx] at hpv; rw [← hpv] at hst'
    obtain ⟨ha, hp⟩ := memoOK_spqrInit_elim (s := ⟨authKey, params⟩) hst'
    refine memoOK_spqrChainKey ha hp ?_
    cases DY.Spqr.spqrParamsDir? params with
    | none => exact safeMemo_lit_short (by decide)
    | some d => cases d <;> exact safeMemo_lit_short (by decide)
  · exact memoOK_spqrSendKey_pack hst hc

theorem safeMemo_spqrRecv
    (hZero : SafeMemo dagSize opOf bytesOf S g pts DY.Spqr.zeroKey)
    {st msg st' key : Bytes} {idx : UInt32}
    (hst : SafeMemo dagSize opOf bytesOf S g pts st)
    (hmsg : SafeMemo dagSize opOf bytesOf S g pts msg)
    (hrecv : DY.Spqr.spqrRecv st msg idx = some (st', key)) :
    SafeMemo dagSize opOf bytesOf S g pts st' ∧ SafeMemo dagSize opOf bytesOf S g pts key := by
  unfold DY.Spqr.spqrRecv at hrecv
  split at hrecv
  · cases hrecv
  · have hp := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
    cases hv : st.view? DY.Spqr.InitState.SubF with
    | none =>
      rw [hv] at hrecv
      injection hrecv with hrecv'; injection hrecv' with hst_eq hkey
      subst hst_eq hkey
      exact ⟨memoOK_spqrRecvState_pack hst hmsg, memoOK_spqrRecvKey_pack hst hmsg⟩
    | some x =>
      rw [hv] at hrecv hp
      rcases x with ⟨authKey, params⟩
      dsimp only at hrecv hp
      have hst' := hst; rw [← hp] at hst'
      obtain ⟨hk, _⟩ := memoOK_spqrInit_elim (s := ⟨authKey, params⟩) hst'
      cases hd : DY.Spqr.spqrParamsDir? params with
      | none => rw [hd] at hrecv; cases hrecv
      | some dir =>
        rw [hd] at hrecv
        injection hrecv with hrecv'; injection hrecv' with hst_eq hkey
        subst hst_eq hkey
        refine ⟨memoOK_spqrRecvState_pack hst hmsg, ?_⟩
        split
        · exact hZero
        · refine memoOK_spqrChainKey hk ?_ ?_
          · cases dir <;> exact safeMemo_lit_short (by decide)
          · unfold DY.Spqr.encodeSpqrIndexTerm; exact safeMemo_lit_short (show 4 < 8 by decide)

theorem termAt_computeMac (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {mk pIk mIk w : Bytes} {mk_id pIk_id mIk_id w_id c1_id c2_id h_id t_id : Nat}
    (hc1 : c1_id < dagSize ∧ opOf c1_id = .concat mIk_id w_id)
    (hc2 : c2_id < dagSize ∧ opOf c2_id = .concat pIk_id c1_id)
    (hh : h_id < dagSize ∧ opOf h_id = .kdf mk_id c2_id)
    (ht : t_id < dagSize ∧ opOf t_id = .trunc8 h_id)
    (hmk : TermAt dagSize opOf bytesOf S g pts mk mk_id)
    (hpIk : TermAt dagSize opOf bytesOf S g pts pIk pIk_id)
    (hmIk : TermAt dagSize opOf bytesOf S g pts mIk mIk_id)
    (hw : TermAt dagSize opOf bytesOf S g pts w w_id) :
    TermAt dagSize opOf bytesOf S g pts (computeMac mk pIk mIk w) t_id := by
  unfold computeMac hmac
  exact termAt_trunc8 hNodes ht.1 ht.2
    (termAt_kdf hNodes hh.1 hh.2 hmk
      (termAt_concat hNodes hc2.1 hc2.2 hpIk
        (termAt_concat hNodes hc1.1 hc1.2 hmIk hw)))

theorem termAt_trMsgKeys (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {salt seed : Bytes}
    {info1_id info2_id info3_id salt_id seed_id prk_id ck_id c2_id mk_id c3_id iv_id : Nat}
    (hi1 : TermAt dagSize opOf bytesOf S g pts
      (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 1)) info1_id)
    (hi2 : TermAt dagSize opOf bytesOf S g pts
      (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 2)) info2_id)
    (hi3 : TermAt dagSize opOf bytesOf S g pts
      (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 3)) info3_id)
    (hprk : prk_id < dagSize ∧ opOf prk_id = .kdf salt_id seed_id)
    (hck : ck_id < dagSize ∧ opOf ck_id = .kdf prk_id info1_id)
    (hc2 : c2_id < dagSize ∧ opOf c2_id = .concat ck_id info2_id)
    (hmk : mk_id < dagSize ∧ opOf mk_id = .kdf prk_id c2_id)
    (hc3 : c3_id < dagSize ∧ opOf c3_id = .concat mk_id info3_id)
    (hiv : iv_id < dagSize ∧ opOf iv_id = .kdf prk_id c3_id)
    (hsalt : TermAt dagSize opOf bytesOf S g pts salt salt_id)
    (hseed : TermAt dagSize opOf bytesOf S g pts seed seed_id) :
    TermAt dagSize opOf bytesOf S g pts (trMsgKeys salt seed).cipherKey ck_id ∧
      TermAt dagSize opOf bytesOf S g pts (trMsgKeys salt seed).macKey mk_id ∧
      TermAt dagSize opOf bytesOf S g pts (trMsgKeys salt seed).iv iv_id := by
  unfold trMsgKeys hkdfBlock1 hkdfBlock2 hkdfBlock3 hmac; dsimp only
  have tprk := termAt_kdf hNodes hprk.1 hprk.2 hsalt hseed
  have tck := termAt_kdf hNodes hck.1 hck.2 tprk hi1
  have tmk := termAt_kdf hNodes hmk.1 hmk.2 tprk (termAt_concat hNodes hc2.1 hc2.2 tck hi2)
  have tiv := termAt_kdf hNodes hiv.1 hiv.2 tprk (termAt_concat hNodes hc3.1 hc3.2 tmk hi3)
  exact ⟨tck, tmk, tiv⟩

theorem safeMemo_trialTerms {salts : List Bytes} {msg : TRSignalMsg} {ctx : TrialCtx}
    (hextra : ∀ t ∈ ctx.extra, SafeMemo dagSize opOf bytesOf S g pts t)
    (hct : SafeMemo dagSize opOf bytesOf S g pts msg.ciphertext)
    (hbody : ∀ seed, ctx.seed? = some seed → ∀ salt ∈ salts,
      SafeMemo dagSize opOf bytesOf S g pts (trMsgKeys salt seed).cipherKey ∧
      SafeMemo dagSize opOf bytesOf S g pts (trMsgKeys salt seed).macKey ∧
      SafeMemo dagSize opOf bytesOf S g pts (trMsgKeys salt seed).iv ∧
      SafeMemo dagSize opOf bytesOf S g pts
        (computeMac (trMsgKeys salt seed).macKey ctx.peerIk ctx.myIk msg.wire)) :
    ∀ t ∈ trialTerms salts msg ctx, SafeMemo dagSize opOf bytesOf S g pts t := by
  intro t ht
  unfold trialTerms at ht
  rw [List.mem_append] at ht
  rcases ht with ht | ht
  · exact hextra t ht
  · cases hs : ctx.seed? with
    | none => rw [hs] at ht; cases ht
    | some seed =>
      rw [hs, List.mem_flatMap] at ht
      rcases ht with ⟨salt, hsalt, ht⟩
      obtain ⟨hck, hmk, hiv, hmac_ok⟩ := hbody seed hs salt hsalt
      rw [List.mem_append] at ht
      rcases ht with ht | ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact hck
        · exact hmk
        · exact hiv
        · exact hmac_ok
      · cases hdec : DY.SymEnc.symDec (trMsgKeys salt seed).cipherKey (trMsgKeys salt seed).iv msg.ciphertext with
        | none => rw [hdec] at ht; cases ht
        | some pt =>
          rw [hdec] at ht; simp only [Option.toList, List.mem_singleton] at ht; subst ht
          exact safeMemo_symDec hdec hct

end Combinators

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTermAt
