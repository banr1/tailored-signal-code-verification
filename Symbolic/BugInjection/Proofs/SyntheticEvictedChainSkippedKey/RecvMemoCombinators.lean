/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoSetup
public import Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
import DY.Bytes.Basic
import Comparse.Basic
import DY.Comparse
import DY.Actions.PersistentLocalState
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Comparse

/-!
# Certified DAG `TermAt` and `SafeMemo` Combinators

Connects symbolic `DY.Bytes` terms under `(evictedI0, S, g)` to certified `DagOp` node IDs and
refutes `MemoCollisionOn` whenever all prefix and trial terms satisfy `SafeMemo`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators

open DY
open scoped DY.Libsignal.Composed
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (canonicalVariation sha256CompressFunction)
open DY.Libsignal.TripleRatchet
  (TRState RecvChain hmac hkdfBlock1 hkdfBlock2 hkdfBlock3
   kdfRk createChain kdfCk trMsgKeys computeMac trHonestWireMsg)
open DY.Libsignal.PQXDH (PQXDHState agree encodeEC encodeKEM serializedIk)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost VisEntry
   node concretizeRandom gRandom
   gamma' gamma randTerm
   assumedInjective MemoCollisionOn prefixTerms plaintextTerms)
open Symbolic.BugInjection.Proofs.Common443.Census443Memo
  (MemoOK memoOK_dhPk_elim memoOK_spqrInit memoOK_spqrInit_elim memoOK_spqrChainKey
   memoOK_spqrSendState memoOK_spqrSendKey_pack memoOK_spqrSendMsg memoOK_spqrRecvState_pack)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
  (ms_pack_random ms_pack_lit ms_pack_kdf)
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
  (assumedInjective_lit bytes_rec_gAll memoOK_symEnc_elim memoOK_spqrRecvKey_pack)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (recvTailTerm stateAnchorPair trStateProxyRoots serialize_localTR_memo suffix_drop_eq)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
  (gamma'_kemEncap_of_len32 gamma'_kemSS_of_len32)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedLookupPub evictedLookupDh evictedAesPerm)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
  (evictedLookupDh_comm)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (r0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
  (DagOp dagOpBytesOk dagNodeOk evalDagShapeAux evalDagShapeAux_irrel)

/-- Reconstructs the canonical `.shape` of DAG node `id` from `opOf` using fuel `dagSize`. -/
def dagShape (opOf : Nat → DagOp) (dagSize id : Nat) : Bytes :=
  evalDagShapeAux opOf dagSize id

theorem dagShape_unfold {opOf : Nat → DagOp} {dagSize id : Nat}
    (htopo : ∀ i < dagSize, (opOf i).childrenLt i = true)
    (hid : id < dagSize) :
    dagShape opOf dagSize id =
      evalDagShapeAux opOf (dagSize + 1) id := by
  let opSafe : Nat → DagOp := fun i => if i < dagSize then opOf i else .lit []
  have htopoSafe : ∀ i, (opSafe i).childrenLt i = true := by
    intro i; dsimp only [opSafe]
    split_ifs with hi
    · exact htopo i hi
    · rfl
  have heq : ∀ f j, j < dagSize → j < f → evalDagShapeAux opOf f j = evalDagShapeAux opSafe f j := by
    intro f
    induction f with
    | zero => intro j _ hj; exact absurd hj (Nat.not_lt_zero _)
    | succ f ih =>
      intro j hj hlt
      have hc := htopo j hj
      have hop : opSafe j = opOf j := by simp [opSafe, hj]
      cases hop' : opOf j <;> rw [hop'] at hc hop <;>
        simp only [DagOp.childrenLt, Bool.and_eq_true, decide_eq_true_eq] at hc <;>
        simp only [evalDagShapeAux, hop, hop']
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
  unfold dagShape
  rw [heq dagSize id hid hid, heq (dagSize + 1) id hid (by omega)]
  exact evalDagShapeAux_irrel opSafe htopoSafe dagSize (dagSize + 1) id hid (by omega)

/-- Classifies a memo entry `(term, shape, bytes)` as a short plaintext (`< 8` bytes), a
non-`assumedInjective` entry (short or ending in the local-state `[0x01, 0x00]` suffix), or a
certified DAG node below `dagSize`. -/
def SafeEntry (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (pts : List Bytes) (x : Bytes × Bytes × HwBytes) : Prop :=
  (x.1 ∈ pts ∧ x.2.2.length < 8) ∨
  (assumedInjective x.1 = false ∧
    (x.2.2.length < 8 ∨
     (38 ≤ x.2.2.length ∧ x.2.2.drop (x.2.2.length - 2) = [0x01#8, 0x00#8]))) ∨
  (∃ id < dagSize, x.2.1 = dagShape opOf dagSize id ∧ x.2.2 = bytesOf id ∧
    (assumedInjective x.1 = true → (opOf id).isAI = true))

/-- Every memo entry of `b` under `(evictedI0, S, g)` satisfies `SafeEntry`. -/
def SafeMemo (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes) (b : Bytes) : Prop :=
  MemoOK evictedI0 S g (SafeEntry dagSize opOf bytesOf pts) b

/-- Witnesses that `b` evaluates under `(evictedI0, S, g)` to DAG node `id` (matching `.bytes`
and `.shape`) and satisfies `SafeMemo`. -/
def TermAt (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes) (b : Bytes) (id : Nat) : Prop :=
  id < dagSize ∧
  (gamma' evictedI0 S g b).bytes = bytesOf id ∧
  (gamma' evictedI0 S g b).shape = dagShape opOf dagSize id ∧
  SafeMemo dagSize opOf bytesOf S g pts b

theorem TermAt.safeMemo {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {b : Bytes} {id : Nat}
    (h : TermAt dagSize opOf bytesOf S g pts b id) :
    SafeMemo dagSize opOf bytesOf S g pts b :=
  h.2.2.2

theorem TermAt.gamma_eq {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {b : Bytes} {id : Nat}
    (h : TermAt dagSize opOf bytesOf S g pts b id) :
    gamma evictedI0 S g b = bytesOf id :=
  h.2.1

/-- Refutes `MemoCollisionOn` when all DAG nodes satisfy `dagNodeOk`, `assumedInjective` node
bytes are distinct, and all prefix and new terms satisfy `SafeMemo`. -/
theorem not_memoCollisionOn_of_safeMemo
    {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    (hNodes : ∀ id < dagSize, dagNodeOk opOf bytesOf id = true)
    (hNoColl : ∀ id₁ < dagSize, ∀ id₂ < dagSize,
      ((opOf id₁).isAI = true ∨ (opOf id₂).isAI = true) →
      bytesOf id₁ = bytesOf id₂ → id₁ = id₂)
    {S : OpaqueSymbolSemantics} {g : Ghost} {known : Bytes → Prop}
    {tr : ExecTrace} {vis : List VisEntry} {newTerms newPts : List Bytes}
    (hPref : ∀ t ∈ prefixTerms r0 tr vis,
      SafeMemo dagSize opOf bytesOf S g (plaintextTerms vis ++ newPts) t)
    (hNew : ∀ t ∈ newTerms,
      SafeMemo dagSize opOf bytesOf S g (plaintextTerms vis ++ newPts) t) :
    ¬ MemoCollisionOn evictedI0 r0 S g known tr vis newTerms newPts := by
  rintro ⟨x₁, hx₁_raw, x₂, hx₂_raw, hsh, hinj, hpt₁, hpt₂, hbytes⟩
  set pts := plaintextTerms vis ++ newPts
  have hs₁ : SafeEntry dagSize opOf bytesOf pts x₁ := by
    obtain ⟨t₁, ht₁, hmx₁⟩ := List.mem_flatMap.mp hx₁_raw
    exact hNew t₁ ht₁ x₁ hmx₁
  have hs₂ : SafeEntry dagSize opOf bytesOf pts x₂ := by
    rcases List.mem_append.mp hx₂_raw with hx₂_p | hx₂_n
    · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_p
      exact hPref t₂ ht₂ x₂ hmx₂
    · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_n
      exact hNew t₂ ht₂ x₂ hmx₂
  have hAiProp : ∀ {id : Nat}, id < dagSize → (opOf id).isAI = true →
      8 ≤ (bytesOf id).length ∧
      ¬(38 ≤ (bytesOf id).length ∧ (bytesOf id).drop ((bytesOf id).length - 2) = [0x01#8, 0x00#8]) := by
    intro id hid hai
    have hn := hNodes id hid
    unfold dagNodeOk at hn
    simp only [hai, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not, beq_eq_false_iff_ne] at hn
    obtain ⟨_, h8, hnsfx⟩ := hn
    exact ⟨h8, fun ⟨h38, hd⟩ => by rcases hnsfx with h1 | h2; exact h1 h38; exact h2 hd⟩
  rcases hs₁ with ⟨hm₁, hlen₁⟩ | ⟨hnai₁, hni₁⟩ | ⟨id₁, hid₁, hsh₁, hb₁, hai₁⟩
  · rcases hs₂ with ⟨hm₂, _⟩ | ⟨hnai₂, _⟩ | ⟨id₂, hid₂, _, hb₂, hai₂⟩
    · exact (hpt₁ hm₁).1 hm₂
    · have := (hpt₁ hm₁).2.1; rw [hnai₂] at this; cases this
    · have ⟨h8, _⟩ := hAiProp hid₂ (hai₂ (hpt₁ hm₁).2.1)
      rw [hbytes, hb₂] at hlen₁; omega
  · rcases hs₂ with ⟨hm₂, _⟩ | ⟨hnai₂, _⟩ | ⟨id₂, hid₂, _, hb₂, hai₂⟩
    · have := (hpt₂ hm₂).2.1; rw [hnai₁] at this; cases this
    · rcases hinj with h | h <;> simp_all
    · have hai₂' : (opOf id₂).isAI = true := by
        rcases hinj with h | h
        · rw [hnai₁] at h; cases h
        · exact hai₂ h
      have ⟨h8, hnsfx⟩ := hAiProp hid₂ hai₂'
      rcases hni₁ with hlt₁ | ⟨h38₁, hd₁⟩
      · rw [hbytes, hb₂] at hlt₁; omega
      · rw [hbytes, hb₂] at h38₁ hd₁; exact hnsfx ⟨h38₁, hd₁⟩
  · rcases hs₂ with ⟨hm₂, hlen₂⟩ | ⟨hnai₂, hni₂⟩ | ⟨id₂, hid₂, hsh₂, hb₂, hai₂⟩
    · have ⟨h8, _⟩ := hAiProp hid₁ (hai₁ (hpt₂ hm₂).2.1)
      rw [← hbytes, hb₁] at hlen₂; omega
    · have hai₁' : (opOf id₁).isAI = true := by
        rcases hinj with h | h
        · exact hai₁ h
        · rw [hnai₂] at h; cases h
      have ⟨h8, hnsfx⟩ := hAiProp hid₁ hai₁'
      rcases hni₂ with hlt₂ | ⟨h38₂, hd₂⟩
      · rw [← hbytes, hb₁] at hlt₂; omega
      · rw [← hbytes, hb₁] at h38₂ hd₂; exact hnsfx ⟨h38₂, hd₂⟩
    · have hor : (opOf id₁).isAI = true ∨ (opOf id₂).isAI = true := by
        rcases hinj with h | h
        · exact Or.inl (hai₁ h)
        · exact Or.inr (hai₂ h)
      have hideq := hNoColl id₁ hid₁ id₂ hid₂ hor (hb₁.symm.trans (hbytes.trans hb₂))
      subst hideq
      exact hsh (hsh₁.trans hsh₂.symm)

theorem safeMemo_mono_pts {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts₁ pts₂ : List Bytes} {b : Bytes}
    (hsub : ∀ p ∈ pts₁, p ∈ pts₂)
    (h : SafeMemo dagSize opOf bytesOf S g pts₁ b) :
    SafeMemo dagSize opOf bytesOf S g pts₂ b := by
  intro x hx
  rcases h x hx with ⟨hm, hl⟩ | hsp | hdag
  · exact Or.inl ⟨hsub _ hm, hl⟩
  · exact Or.inr (Or.inl hsp)
  · exact Or.inr (Or.inr hdag)

theorem safeMemo_plaintext {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {ts : Nat}
    (hmem : randTerm ts 32 ∈ pts)
    (hlen : (g.σ ts 32).length < 8) :
    SafeMemo dagSize opOf bytesOf S g pts (randTerm ts 32) := by
  intro x hx
  unfold randTerm at hx
  rw [ms_pack_random evictedI0 S g ⟨ts, 32⟩] at hx
  dsimp only [gRandom, concretizeRandom] at hx
  simp only [Nat.reduceEqDiff, ↓reduceIte, node, List.flatMap_nil, List.mem_singleton] at hx
  subst hx
  exact Or.inl ⟨hmem, hlen⟩

theorem safeMemo_symDec {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {k iv ct m : Bytes}
    (hdec : DY.SymEnc.symDec k iv ct = some m)
    (hct : SafeMemo dagSize opOf bytesOf S g pts ct) :
    SafeMemo dagSize opOf bytesOf S g pts m := by
  dsimp only [DY.SymEnc.symDec, DY.SymEnc.instCanSymEncBytes] at hdec
  split at hdec <;> try cases hdec
  next key' iv' msg hx =>
    split_ifs at hdec
    cases hdec
    have hpv := DY.Bytes.pack_view? DY.SymEnc.Enc.SubF ct
    change ct.view? DY.SymEnc.Enc.SubF = some { key := key', iv := iv', msg := m } at hx
    rw [hx] at hpv
    rw [← hpv] at hct
    exact memoOK_symEnc_elim (e := ⟨key', iv', m⟩) hct

theorem safeMemo_serialize_localTR {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    (ls : DY.PersistentLocalState.LocalState TRState)
    (hroots : ∀ r ∈ trStateProxyRoots ls, SafeMemo dagSize opOf bytesOf S g pts r)
    (hlen : 38 ≤ (gamma evictedI0 S g (stateAnchorPair ls).1 ++
      gamma evictedI0 S g (stateAnchorPair ls).2).length)
    (hsfx : (gamma evictedI0 S g (stateAnchorPair ls).1 ++
      gamma evictedI0 S g (stateAnchorPair ls).2).drop
      ((gamma evictedI0 S g (stateAnchorPair ls).1 ++
        gamma evictedI0 S g (stateAnchorPair ls).2).length - 2) = [0x01#8, 0x00#8]) :
    SafeMemo dagSize opOf bytesOf S g pts (DY.Comparse.serialize ls) := by
  intro x hx
  rcases serialize_localTR_memo evictedI0 S g ls hx with ⟨r, hr, hmx⟩ | ⟨hnai, hsuff⟩
  · exact hroots r hr x hmx
  · refine Or.inr (Or.inl ⟨hnai, Or.inr ⟨?_, ?_⟩⟩)
    · have := hsuff.length_le; omega
    · rcases hsuff with ⟨pfx, heq⟩
      rw [← heq]
      have hsub : (pfx ++ (gamma evictedI0 S g (stateAnchorPair ls).1 ++
          gamma evictedI0 S g (stateAnchorPair ls).2)).length - 2 =
          pfx.length + ((gamma evictedI0 S g (stateAnchorPair ls).1 ++
            gamma evictedI0 S g (stateAnchorPair ls).2).length - 2) := by
        rw [List.length_append]; omega
      rw [hsub, List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right pfx.length _),
        List.nil_append, Nat.add_sub_cancel_left, hsfx]

theorem safeMemo_lit_short {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {ba : ByteArray}
    (hlen : ba.size < 8) :
    SafeMemo dagSize opOf bytesOf S g pts (DY.Literal.literalToBytes ba) := by
  intro x hx
  have hg := ms_pack_lit evictedI0 S g ⟨ba⟩
  change gamma' evictedI0 S g (DY.Literal.literalToBytes ba) = _ at hg
  rw [hg] at hx
  unfold DY.Libsignal.Composed.Refinement.gLit0 DY.Libsignal.Composed.Refinement.concretizeLit node at hx
  simp only [List.flatMap_nil, List.mem_singleton] at hx
  subst hx
  refine Or.inr (Or.inl ⟨assumedInjective_lit ba, Or.inl ?_⟩)
  dsimp only [DY.Libsignal.Composed.Refinement.ofByteArray]
  rw [List.length_map, Array.length_toList]
  exact hlen

theorem safeMemo_randTerm_zero {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} (ts : Nat) :
    SafeMemo dagSize opOf bytesOf S g pts (randTerm ts 0) := by
  intro x hx
  have hg := ms_pack_random evictedI0 S g ⟨ts, 0⟩
  change gamma' evictedI0 S g (randTerm ts 0) = _ at hg
  rw [hg] at hx
  dsimp only [gRandom, concretizeRandom] at hx
  simp only [↓reduceIte] at hx
  cases hx

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators
