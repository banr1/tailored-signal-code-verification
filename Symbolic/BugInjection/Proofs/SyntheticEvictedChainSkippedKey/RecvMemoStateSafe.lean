/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalkSend

/-!
# `TRState` Serialization Memo Safety and Honest-MAC Refutation

Defines `SafeMemo2` (an extension of `SafeMemo` to non-`assumedInjective` terms whose concretized
bytes end in `[0x01, 0x00]`) and proves `¬ MemoCollisionOn` via `dag_no_ai_0100`. Reduces
`SafeMemo2 (DY.Comparse.serialize ls)` to `SafeMemo` on `spqr`, core Double Ratchet fields, and
receiver chains (`safeMemo2_trState_of_dr`), and refutes `MacTagForgeryOrCollision` for clean sends.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoStateSafe

open scoped DY.Libsignal.Composed
attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

open DY (Bytes ExecTrace)
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (TRState RecvChain kdfCk)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost VisEntry TrialCtx MacTagForgeryOrCollision
   MemoCollisionOn assumedInjective prefixTerms plaintextTerms gamma' gamma)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4)
open Symbolic.BugInjection.Proofs.Common443.Census443Memo (MemoOK bytes_rec_gAll)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd encSig)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (trStateProxyRoots stateAnchorPair recvTailTerm serialize_localTR_memo)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (ai_concat_eq bool_serialize_singleton slowNat_serialize_zero slowNat_serialize_succ
   slowString_serialize_eq uint32_serialize_singleton concatPrefixes_cons concatPrefixes_nil
   concatPrefixes_append_eq alice_utf8_sizes bob_utf8_sizes)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue (bool_serialize_singleton_head)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0 (evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (r0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws
  (not_macTagForgeryOrCollision_of_honest_mac)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (DagOp dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagSize dagOp dagBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBuckets
  (dag_nodes_ok dag_no_collision)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators
  (dagShape SafeMemo TermAt safeMemo_lit_short)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace (pqKeyOf)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv0 (sendPtTs)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk0 (termAt_lit_b)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalkSend
  (getSendRow sendRowOk all_send_rows_ok SendStepOut)

/-- Memo entry invariant adding non-`assumedInjective` terms with byte length `< 8` or suffix
`[0x01, 0x00]` to `SafeEntry`. -/
def SafeEntry2 (pts : List Bytes) (x : Bytes × Bytes × HwBytes) : Prop :=
  (x.1 ∈ pts ∧ x.2.2.length < 8) ∨
  (assumedInjective x.1 = false ∧
    (x.2.2.length < 8 ∨ [0x01#8, 0x00#8] <:+ x.2.2)) ∨
  (∃ id < dagSize, x.2.1 = dagShape dagOp dagSize id ∧ x.2.2 = dagBytes id ∧
    (assumedInjective x.1 = true → (dagOp id).isAI = true))

def SafeMemo2 (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes) (b : Bytes) : Prop :=
  MemoOK evictedI0 S g (SafeEntry2 pts) b

theorem safeMemo_toSafeMemo2 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {b : Bytes}
    (h : SafeMemo dagSize dagOp dagBytes S g pts b) :
    SafeMemo2 S g pts b := by
  intro x hx
  rcases h x hx with hpt | ⟨hnai, hlt | ⟨_, hd⟩⟩ | hdag
  · exact Or.inl hpt
  · exact Or.inr (Or.inl ⟨hnai, Or.inl hlt⟩)
  · refine Or.inr (Or.inl ⟨hnai, Or.inr ⟨x.2.2.take (x.2.2.length - 2), ?_⟩⟩)
    rw [← hd, List.take_append_drop]
  · exact Or.inr (Or.inr hdag)

theorem safeMemo2_mono_pts {S : OpaqueSymbolSemantics} {g : Ghost} {pts₁ pts₂ : List Bytes} {b : Bytes}
    (hsub : ∀ p ∈ pts₁, p ∈ pts₂)
    (h : SafeMemo2 S g pts₁ b) :
    SafeMemo2 S g pts₂ b := by
  intro x hx
  rcases h x hx with ⟨hm, hl⟩ | hsp | hdag
  · exact Or.inl ⟨hsub _ hm, hl⟩
  · exact Or.inr (Or.inl hsp)
  · exact Or.inr (Or.inr hdag)

def endsWith0100 (bs : HwBytes) : Bool :=
  decide (2 ≤ bs.length) && (bs.drop (bs.length - 2) == [0x01#8, 0x00#8])

private theorem no_ai_0100_0 :
    (List.range 1680).all (fun i =>
      let id := i; !(dagOp id).isAI || !endsWith0100 (dagBytes id)) = true := by
  decide +kernel
private theorem no_ai_0100_1 :
    (List.range 1680).all (fun i =>
      let id := 1680 + i; !(dagOp id).isAI || !endsWith0100 (dagBytes id)) = true := by
  decide +kernel
private theorem no_ai_0100_2 :
    (List.range 1680).all (fun i =>
      let id := 3360 + i; !(dagOp id).isAI || !endsWith0100 (dagBytes id)) = true := by
  decide +kernel
private theorem no_ai_0100_3 :
    (List.range 1680).all (fun i =>
      let id := 5040 + i; !(dagOp id).isAI || !endsWith0100 (dagBytes id)) = true := by
  decide +kernel

theorem dag_no_ai_0100 {id : Nat} (hid : id < dagSize) (hai : (dagOp id).isAI = true) :
    ¬ ([0x01#8, 0x00#8] <:+ dagBytes id) := by
  have hsz : dagSize = 6720 := rfl
  have hok : (!(dagOp id).isAI || !endsWith0100 (dagBytes id)) = true := by
    by_cases h1 : id < 1680
    · exact List.all_eq_true.mp no_ai_0100_0 id (List.mem_range.mpr h1)
    · by_cases h2 : id < 3360
      · have := List.all_eq_true.mp no_ai_0100_1 (id - 1680) (List.mem_range.mpr (by omega))
        simpa [Nat.add_sub_of_le (by omega : 1680 ≤ id)] using this
      · by_cases h3 : id < 5040
        · have := List.all_eq_true.mp no_ai_0100_2 (id - 3360) (List.mem_range.mpr (by omega))
          simpa [Nat.add_sub_of_le (by omega : 3360 ≤ id)] using this
        · have := List.all_eq_true.mp no_ai_0100_3 (id - 5040) (List.mem_range.mpr (by omega))
          simpa [Nat.add_sub_of_le (by omega : 5040 ≤ id)] using this
  rw [hai, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hok
  rintro ⟨pfx, heq⟩
  have h2 : 2 ≤ (dagBytes id).length := by
    rw [← heq, List.length_append]; simp
  have hd : (dagBytes id).drop ((dagBytes id).length - 2) = [0x01#8, 0x00#8] := by
    rw [← heq]
    have hsub : (pfx ++ [0x01#8, 0x00#8]).length - 2 = pfx.length := by
      rw [List.length_append]; simp
    rw [hsub, List.drop_append, List.drop_eq_nil_of_le (Nat.le_refl pfx.length),
      List.nil_append, Nat.sub_self, List.drop_zero]
  unfold endsWith0100 at hok
  simp [h2, hd] at hok

theorem not_memoCollisionOn_of_safeMemo2
    {S : OpaqueSymbolSemantics} {g : Ghost} {known : Bytes → Prop}
    {tr : ExecTrace} {vis : List VisEntry} {newTerms newPts : List Bytes}
    (hPref : ∀ t ∈ prefixTerms r0 tr vis,
      SafeMemo2 S g (plaintextTerms vis ++ newPts) t)
    (hNew : ∀ t ∈ newTerms,
      SafeMemo2 S g (plaintextTerms vis ++ newPts) t) :
    ¬ MemoCollisionOn evictedI0 r0 S g known tr vis newTerms newPts := by
  rintro ⟨x₁, hx₁_raw, x₂, hx₂_raw, hsh, hinj, hpt₁, hpt₂, hbytes⟩
  set pts := plaintextTerms vis ++ newPts
  have hs₁ : SafeEntry2 pts x₁ := by
    obtain ⟨t₁, ht₁, hmx₁⟩ := List.mem_flatMap.mp hx₁_raw
    exact hNew t₁ ht₁ x₁ hmx₁
  have hs₂ : SafeEntry2 pts x₂ := by
    rcases List.mem_append.mp hx₂_raw with hx₂_p | hx₂_n
    · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_p
      exact hPref t₂ ht₂ x₂ hmx₂
    · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_n
      exact hNew t₂ ht₂ x₂ hmx₂
  have hAiLen : ∀ {id : Nat}, id < dagSize → (dagOp id).isAI = true → 8 ≤ (dagBytes id).length := by
    intro id hid hai
    have hn := dag_nodes_ok id hid
    unfold dagNodeOk at hn
    simp only [hai, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hn
    exact hn.2.1
  rcases hs₁ with ⟨hm₁, hlen₁⟩ | ⟨hnai₁, hni₁⟩ | ⟨id₁, hid₁, hsh₁, hb₁, hai₁⟩
  · rcases hs₂ with ⟨hm₂, _⟩ | ⟨hnai₂, _⟩ | ⟨id₂, hid₂, _, hb₂, hai₂⟩
    · exact (hpt₁ hm₁).1 hm₂
    · have := (hpt₁ hm₁).2.1; rw [hnai₂] at this; cases this
    · have h8 := hAiLen hid₂ (hai₂ (hpt₁ hm₁).2.1)
      rw [hbytes, hb₂] at hlen₁; omega
  · rcases hs₂ with ⟨hm₂, _⟩ | ⟨hnai₂, _⟩ | ⟨id₂, hid₂, _, hb₂, hai₂⟩
    · have := (hpt₂ hm₂).2.1; rw [hnai₁] at this; cases this
    · rcases hinj with h | h <;> simp_all
    · have hai₂' : (dagOp id₂).isAI = true := by
        rcases hinj with h | h
        · rw [hnai₁] at h; cases h
        · exact hai₂ h
      rcases hni₁ with hlt₁ | hsfx₁
      · have h8 := hAiLen hid₂ hai₂'
        rw [hbytes, hb₂] at hlt₁; omega
      · rw [hbytes, hb₂] at hsfx₁
        exact dag_no_ai_0100 hid₂ hai₂' hsfx₁
  · rcases hs₂ with ⟨hm₂, hlen₂⟩ | ⟨hnai₂, hni₂⟩ | ⟨id₂, hid₂, hsh₂, hb₂, hai₂⟩
    · have h8 := hAiLen hid₁ (hai₁ (hpt₂ hm₂).2.1)
      rw [← hbytes, hb₁] at hlen₂; omega
    · have hai₁' : (dagOp id₁).isAI = true := by
        rcases hinj with h | h
        · exact hai₁ h
        · rw [hnai₂] at h; cases h
      rcases hni₂ with hlt₂ | hsfx₂
      · have h8 := hAiLen hid₁ hai₁'
        rw [← hbytes, hb₁] at hlt₂; omega
      · rw [← hbytes, hb₁] at hsfx₂
        exact dag_no_ai_0100 hid₁ hai₁' hsfx₂
    · have hor : (dagOp id₁).isAI = true ∨ (dagOp id₂).isAI = true := by
        rcases hinj with h | h
        · exact Or.inl (hai₁ h)
        · exact Or.inr (hai₂ h)
      have hideq := dag_no_collision id₁ hid₁ id₂ hid₂ hor (hb₁.symm.trans (hbytes.trans hb₂))
      subst hideq
      exact hsh (hsh₁.trans hsh₂.symm)

theorem safeMemo_bool_serialize {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    (b : Bool) :
    ∀ u ∈ (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := Bytes)).serialize b,
      SafeMemo dagSize dagOp dagBytes S g pts u := by
  obtain ⟨ba, hsz, heq⟩ := bool_serialize_singleton b
  rw [heq]
  intro u hu
  rw [List.mem_singleton] at hu; subst hu
  exact safeMemo_lit_short (by omega)

theorem safeMemo_slowNat_serialize {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} :
    ∀ (n : Nat)
      (u : Bytes),
      u ∈ (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := Bytes)).serialize n →
      SafeMemo dagSize dagOp dagBytes S g pts u
  | 0, u, hu => by
    rw [slowNat_serialize_zero] at hu
    exact safeMemo_bool_serialize false u hu
  | n + 1, u, hu => by
    rw [slowNat_serialize_succ, List.mem_append] at hu
    rcases hu with hu | hu
    · exact safeMemo_bool_serialize true u hu
    · exact safeMemo_slowNat_serialize n u hu

theorem safeMemo_slowString_party {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {p : String} (hp : p = "alice" ∨ p = "bob") :
    ∀ u ∈ (_root_.Comparse.NonExtensibleMessageFormat.slowString (Bytes := Bytes)).serialize p,
      SafeMemo dagSize dagOp dagBytes S g pts u := by
  rw [slowString_serialize_eq]
  intro u hu
  rw [List.mem_append] at hu
  rcases hu with hu | hu
  · exact safeMemo_slowNat_serialize p.utf8ByteSize u hu
  · rw [List.mem_singleton] at hu; subst hu
    rcases hp with rfl | rfl
    · exact safeMemo_lit_short (by rw [alice_utf8_sizes.2]; omega)
    · exact safeMemo_lit_short (by rw [bob_utf8_sizes.2]; omega)

theorem safeMemo_uint32_serialize {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    (x : UInt32) :
    ∀ u ∈ (_root_.Comparse.NonExtensibleMessageFormat.uint32 (Bytes := Bytes)).serialize x,
      SafeMemo dagSize dagOp dagBytes S g pts u := by
  obtain ⟨ba, hsz, heq⟩ := uint32_serialize_singleton x
  rw [heq]
  intro u hu
  rw [List.mem_singleton] at hu; subst hu
  exact safeMemo_lit_short (by omega)

private theorem gamma_concat_eq (S : OpaqueSymbolSemantics) (g : Ghost) (a b : Bytes) :
    gamma evictedI0 S g (DY.Concat.concat a b) =
      gamma evictedI0 S g a ++ gamma evictedI0 S g b := by
  unfold gamma gamma'
  rw [show DY.Concat.concat a b = ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF Bytes).pack from rfl,
    DY.Bytes.rec_eq DY.Libsignal.Composed.Refinement.gConcat0
      (DY.Libsignal.Composed.Refinement.concretizeAll evictedI0 S g)]
  rfl

private theorem memo_concat_cases {S : OpaqueSymbolSemantics} {g : Ghost} {a b : Bytes}
    {x : Bytes × Bytes × HwBytes}
    (hx : x ∈ (gamma' evictedI0 S g (DY.Concat.concat a b)).memo) :
    (x.1 = DY.Concat.concat a b ∧ x.2.2 = gamma evictedI0 S g a ++ gamma evictedI0 S g b) ∨
    x ∈ (gamma' evictedI0 S g a).memo ∨
    x ∈ (gamma' evictedI0 S g b).memo := by
  unfold gamma' at hx
  rw [show DY.Concat.concat a b = ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF Bytes).pack from rfl,
    DY.Bytes.rec_eq DY.Libsignal.Composed.Refinement.gConcat0
      (DY.Libsignal.Composed.Refinement.concretizeAll evictedI0 S g)] at hx
  dsimp only [DY.Libsignal.Composed.Refinement.gConcat0,
    DY.Libsignal.Composed.Refinement.concretizeConcat,
    DY.Libsignal.Composed.Refinement.node] at hx
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxb
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl hxa)
  · exact Or.inr (Or.inr hxb)

private theorem safeMemo2_concatPrefixes_suffix {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} :
    ∀ (ps : List Bytes) {s : Bytes},
      (∀ p ∈ ps, SafeMemo2 S g pts p) →
      SafeMemo2 S g pts s →
      [0x01#8, 0x00#8] <:+ gamma evictedI0 S g s →
      SafeMemo2 S g pts (_root_.Comparse.concatPrefixes ps s) ∧
        [0x01#8, 0x00#8] <:+ gamma evictedI0 S g (_root_.Comparse.concatPrefixes ps s)
  | [], s, _, hs, hsfx => by
    rw [concatPrefixes_nil]
    exact ⟨hs, hsfx⟩
  | p :: ps, s, hps, hs, hsfx => by
    rw [concatPrefixes_cons]
    obtain ⟨ih_sm, pfx, hpfx⟩ := safeMemo2_concatPrefixes_suffix ps
      (fun q hq => hps q (List.mem_cons_of_mem p hq)) hs hsfx
    have hsfx_new :
        [0x01#8, 0x00#8] <:+ gamma evictedI0 S g (DY.Concat.concat p (_root_.Comparse.concatPrefixes ps s)) := by
      rw [gamma_concat_eq]
      exact ⟨gamma evictedI0 S g p ++ pfx, by rw [List.append_assoc, hpfx]⟩
    refine ⟨?_, hsfx_new⟩
    intro x hx
    rcases memo_concat_cases hx with ⟨hx1, hx2⟩ | hxp | hxr
    · refine Or.inr (Or.inl ⟨by rw [hx1]; exact ai_concat_eq _ _, Or.inr ?_⟩)
      rw [hx2, ← gamma_concat_eq]
      exact hsfx_new
    · exact hps p List.mem_cons_self x hxp
    · exact ih_sm x hxr

private theorem bool_ser_false :
    (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := Bytes)).serialize false =
      [DY.Libsignal.TripleRatchet.litByte 0] := by
  obtain ⟨ba, _, rfl, heq⟩ := bool_serialize_singleton_head false
  exact heq

private theorem bool_ser_true :
    (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := Bytes)).serialize true =
      [DY.Libsignal.TripleRatchet.litByte 1] := by
  obtain ⟨ba, _, rfl, heq⟩ := bool_serialize_singleton_head true
  exact heq

private theorem slowNat_pos_split :
    ∀ (r : Nat),
      ∃ mid : List Bytes,
        (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := Bytes)).serialize (r + 1) =
          mid ++ [DY.Libsignal.TripleRatchet.litByte 1, DY.Libsignal.TripleRatchet.litByte 0]
  | 0 =>
    ⟨[], by rw [slowNat_serialize_succ, slowNat_serialize_zero, bool_ser_true, bool_ser_false]; rfl⟩
  | r + 1 => by
    obtain ⟨mid, ih⟩ := slowNat_pos_split r
    exact ⟨(_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := Bytes)).serialize true ++ mid,
      by rw [slowNat_serialize_succ, ih, List.append_assoc]⟩

/-- When `1 ≤ c.rIdx`, `recvTailTerm c` concretizes with suffix `[0x01, 0x00]` and satisfies `SafeMemo2`. -/
theorem safeMemo2_recvTail {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {c : RecvChain} (hr : 1 ≤ c.rIdx) :
    SafeMemo2 S g pts (recvTailTerm c) ∧
      [0x01#8, 0x00#8] <:+ gamma evictedI0 S g (recvTailTerm c) := by
  have hr_eq : c.rIdx = (c.rIdx - 1) + 1 := by omega
  obtain ⟨mid, hmid⟩ := slowNat_pos_split (c.rIdx - 1)
  have temp : TermAt dagSize dagOp dagBytes S g pts (_root_.Comparse.BytesLike.empty : Bytes) 0 := by
    change TermAt dagSize dagOp dagBytes S g pts (DY.Literal.literalToBytes ByteArray.empty) 0
    exact termAt_lit_b (by decide +kernel)
  have tb0 : TermAt dagSize dagOp dagBytes S g pts (DY.Libsignal.TripleRatchet.litByte 0) 1 :=
    termAt_lit_b (by decide +kernel)
  have tb1 : TermAt dagSize dagOp dagBytes S g pts (DY.Libsignal.TripleRatchet.litByte 1) 2 :=
    termAt_lit_b (by decide +kernel)
  set s0 := DY.Concat.concat (DY.Libsignal.TripleRatchet.litByte 0) _root_.Comparse.BytesLike.empty
  set s1 := DY.Concat.concat (DY.Libsignal.TripleRatchet.litByte 1) s0
  have hs0_g : gamma evictedI0 S g s0 = [0x00#8] := by
    dsimp only [s0]; rw [gamma_concat_eq, tb0.gamma_eq, temp.gamma_eq]; rfl
  have hs0_sm : SafeMemo2 S g pts s0 := by
    intro x hx
    rcases memo_concat_cases hx with ⟨hx1, hx2⟩ | hxa | hxb
    · refine Or.inr (Or.inl ⟨by rw [hx1]; exact ai_concat_eq _ _, Or.inl ?_⟩)
      rw [hx2, ← gamma_concat_eq, hs0_g]; decide
    · exact safeMemo_toSafeMemo2 tb0.safeMemo x hxa
    · exact safeMemo_toSafeMemo2 temp.safeMemo x hxb
  have hs1_g : gamma evictedI0 S g s1 = [0x01#8, 0x00#8] := by
    dsimp only [s1]; rw [gamma_concat_eq, tb1.gamma_eq, hs0_g]; rfl
  have hs1_sfx : [0x01#8, 0x00#8] <:+ gamma evictedI0 S g s1 :=
    ⟨[], by rw [List.nil_append, hs1_g]⟩
  have hs1_sm : SafeMemo2 S g pts s1 := by
    intro x hx
    rcases memo_concat_cases hx with ⟨hx1, hx2⟩ | hxa | hxb
    · refine Or.inr (Or.inl ⟨by rw [hx1]; exact ai_concat_eq _ _, Or.inr ?_⟩)
      rw [hx2, ← gamma_concat_eq]; exact hs1_sfx
    · exact safeMemo_toSafeMemo2 tb1.safeMemo x hxa
    · exact hs0_sm x hxb
  have htail_eq : recvTailTerm c =
      _root_.Comparse.concatPrefixes
        ((_root_.Comparse.NonExtensibleMessageFormat.uint32 (Bytes := Bytes)).serialize c.index ++ mid) s1 := by
    unfold recvTailTerm
    rw [hr_eq, hmid, ← List.append_assoc, ← concatPrefixes_append_eq]
    simp only [concatPrefixes_cons, concatPrefixes_nil, s1, s0]
  rw [htail_eq]
  refine safeMemo2_concatPrefixes_suffix _ (fun u hu => ?_) hs1_sm hs1_sfx
  rcases List.mem_append.mp hu with hu32 | hmid_u
  · exact safeMemo_toSafeMemo2 (safeMemo_uint32_serialize c.index u hu32)
  · have hsn : u ∈ (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := Bytes)).serialize c.rIdx := by
      rw [hr_eq, hmid]
      exact List.mem_append_left _ hmid_u
    exact safeMemo_toSafeMemo2 (safeMemo_slowNat_serialize c.rIdx u hsn)

private theorem mem_of_getLast? {α : Type} : ∀ {l : List α} {a : α}, l.getLast? = some a → a ∈ l
  | [], _, h => by simp at h
  | [x], a, h => by simp at h; subst h; exact List.mem_cons_self
  | x :: y :: zs, a, h => List.mem_cons_of_mem x (mem_of_getLast? h)

/-- Reduces `SafeMemo2` of `DY.Comparse.serialize ls` to `SafeMemo` on `ls.state.spqr`, the core
Double Ratchet fields and receiver chains of a template `ls₀` with matching `toDRState`, and
`1 ≤ cLast.rIdx` on the final receiver chain. -/
theorem safeMemo2_trState_of_dr {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {ls ls₀ : DY.PersistentLocalState.LocalState TRState}
    {cLast : RecvChain}
    (hpart : ls.participant = ls₀.participant)
    (hdr : ls.state.toDRState = ls₀.state.toDRState)
    (hp_party : ls₀.participant = "alice" ∨ ls₀.participant = "bob")
    (hp_peer : ls₀.state.peer = "alice" ∨ ls₀.state.peer = "bob")
    (hspqr : SafeMemo dagSize dagOp dagBytes S g pts ls.state.spqr)
    (hcore : ∀ u ∈ [ls₀.state.myIk, ls₀.state.peerIk, ls₀.state.rk,
                     ls₀.state.dhs, ls₀.state.cks, ls₀.state.sid],
      SafeMemo dagSize dagOp dagBytes S g pts u)
    (hrecv : ∀ c ∈ ls₀.state.recv,
      SafeMemo dagSize dagOp dagBytes S g pts c.ratchetKey ∧
      SafeMemo dagSize dagOp dagBytes S g pts c.chainKey)
    (hlast : ls₀.state.recv.getLast? = some cLast)
    (hrIdx : 1 ≤ cLast.rIdx) :
    SafeMemo2 S g pts (DY.Comparse.serialize ls) := by
  have hrecv_eq : ls.state.recv = ls₀.state.recv := congrArg (·.recv) hdr
  have hanchor : stateAnchorPair ls = (cLast.chainKey, recvTailTerm cLast) := by
    unfold stateAnchorPair
    rw [hrecv_eq, hlast]
  obtain ⟨htail_sm2, pfx_tail, htail_sfx⟩ := safeMemo2_recvTail (S := S) (g := g) (pts := pts) hrIdx
  have hck_sm : SafeMemo dagSize dagOp dagBytes S g pts cLast.chainKey :=
    (hrecv cLast (mem_of_getLast? hlast)).2
  intro x hx
  rcases serialize_localTR_memo evictedI0 S g ls hx with ⟨u, hu, hmx⟩ | ⟨hnai, pfx_sp, hsp⟩
  · have hu_sm2 : SafeMemo2 S g pts u := by
      unfold trStateProxyRoots at hu
      rw [hanchor, hpart] at hu
      dsimp only at hu
      have hpeer : ls.state.peer = ls₀.state.peer := congrArg (·.peer) hdr
      have hmyIk : ls.state.myIk = ls₀.state.myIk := congrArg (·.myIk) hdr
      have hpeerIk : ls.state.peerIk = ls₀.state.peerIk := congrArg (·.peerIk) hdr
      have hrk : ls.state.rk = ls₀.state.rk := congrArg (·.rk) hdr
      have hdhs : ls.state.dhs = ls₀.state.dhs := congrArg (·.dhs) hdr
      have hcks : ls.state.cks = ls₀.state.cks := congrArg (·.cks) hdr
      have hsid : ls.state.sid = ls₀.state.sid := congrArg (·.sid) hdr
      rw [hpeer, hmyIk, hpeerIk, hrk, hdhs, hcks, hsid, hrecv_eq] at hu
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_flatMap] at hu
      rcases hu with (((((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11
      · exact safeMemo_toSafeMemo2 (safeMemo_bool_serialize true u h1)
      · exact safeMemo_toSafeMemo2 (safeMemo_bool_serialize false u h2)
      · exact safeMemo_toSafeMemo2 (safeMemo_slowString_party hp_party u h3)
      · exact safeMemo_toSafeMemo2 (safeMemo_slowString_party hp_peer u h4)
      · rcases h5 with rfl | rfl | rfl | rfl | rfl <;>
          exact safeMemo_toSafeMemo2 (hcore _ (by simp))
      · exact safeMemo_toSafeMemo2 (safeMemo_uint32_serialize ls.state.ns u h6)
      · exact safeMemo_toSafeMemo2 (safeMemo_uint32_serialize ls.state.pn u h7)
      · subst h8; exact safeMemo_toSafeMemo2 (hcore _ (by simp))
      · exact safeMemo_toSafeMemo2 (safeMemo_slowNat_serialize ls.state.rIdx u h9)
      · rcases h10 with rfl | rfl | rfl | rfl
        · exact safeMemo_toSafeMemo2 hspqr
        · exact safeMemo_toSafeMemo2 (safeMemo_lit_short (ba := ByteArray.empty) (by decide))
        · exact safeMemo_toSafeMemo2 hck_sm
        · exact htail_sm2
      · obtain ⟨c, hc_mem, hc_u⟩ := h11
        rcases hc_u with ((rfl | rfl) | hidx) | hridx
        · exact safeMemo_toSafeMemo2 (hrecv c hc_mem).1
        · exact safeMemo_toSafeMemo2 (hrecv c hc_mem).2
        · exact safeMemo_toSafeMemo2 (safeMemo_uint32_serialize c.index u hidx)
        · exact safeMemo_toSafeMemo2 (safeMemo_slowNat_serialize c.rIdx u hridx)
    exact hu_sm2 x hmx
  · rw [hanchor] at hsp
    dsimp only at hsp
    refine Or.inr (Or.inl ⟨hnai, Or.inr ⟨pfx_sp ++ gamma evictedI0 S g cLast.chainKey ++ pfx_tail, ?_⟩⟩)
    rw [List.append_assoc, List.append_assoc, htail_sfx, hsp]

theorem not_macTagForgery_of_sendStep {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List Bytes} {known : Bytes → Prop} {salts : List Bytes} {ctxs : List TrialCtx}
    {st : TRState} {j : Nat}
    (hj12 : j < 12)
    (hsalt_mem : pqKeyOf st (cls j) (sendPtTs j) ∈ salts)
    (hs : SendStepOut (cls := cls) S g pts st j) :
    ¬ MacTagForgeryOrCollision evictedI0 S g known salts
        (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32))
        ctxs := by
  have hrow := List.all_eq_true.mp all_send_rows_ok j (List.mem_range.mpr hj12)
  unfold sendRowOk at hrow
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
  have huntag : (dagBytes (getSendRow j).mac_id).take 4 ≠ compTag4 := hrow.1.2
  refine not_macTagForgeryOrCollision_of_honest_mac hsalt_mem rfl ?_
  rw [hs.mac.gamma_eq]
  exact huntag

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoStateSafe
