/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.Census443Defs
public import Symbolic.BugInjection.Proofs.Common443.CompI0Laws
public import Symbolic.BugInjection.Proofs.Common443.CompRTag
public import Symbolic.BugInjection.Proofs.Common443.CompExcuse
public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
abbrev DY.Libsignal.Composed.Refinement.ptAtoms := DY.Libsignal.Composed.Refinement.plaintextTerms
abbrev DY.Libsignal.Composed.Refinement.Layout := DY.Libsignal.Composed.Refinement.VisByteLayout
namespace Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompI0Laws
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
export DY.Libsignal.Composed.Refinement (PrefixGhosts)
export Symbolic.BugInjection.Proofs.Common443.CompExcuse (view_concat_lit)
theorem bytes_rec_gAll (i : ExternInterpretation) (S : Sem) (g : Ghost) (u : DY.Bytes) : u.rec (gAll i S g) = gamma' i S g u := rfl
theorem gamma'_randTerm (i : ExternInterpretation) (S : Sem) (g : Ghost) (ts sz : Nat) (hsz : sz ≠ 0) : gamma' i S g (randTerm ts sz) = { bytes := g.σ ts sz, shape := randTerm ts sz, memo := [(randTerm ts sz, randTerm ts sz, g.σ ts sz)] } := by
  unfold gamma' randTerm
  show ((({ timestamp := ts, size := sz } : DY.Random.Random DY.Bytes).pack).rec (gAll i S g)) = _
  rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)]; simp only [gRandom, concretizeRandom, node, List.flatMap_nil, hsz, ↓reduceIte]
export Symbolic.BugInjection.Proofs.Common443.CompExcuse (concat_inj)
def PtSplitCollisionAt (i : ExternInterpretation) (r : Records) (S : Sem) (who : List Participant) (ok : Nat → Bool) (τ : List MachineEvent) (n : Nat) : Prop := ∃ (g : Ghost) (ms : List Move) (b : HwBytes), ExplainsMoves i r S who ok g ms (τ.take n) ∧ τ[n]? = some (.pt b) ∧ EventMatchesEntry i r S g (.pt b) (ptEntryOfNextEncrypt r ms) ∧ ∀ g' ∈ PrefixGhosts i r S who g ms (τ.take n),
      MemoCollisionOn i r S g' (fun u => u.AttackerKnows (runTraceMoves r ms)) (runTraceMoves r ms) (runVis r ms) (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms
theorem not_pt_collision_of_ne_bytes {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hem : EventMatchesEntry i r S g (.pt b) (ptEntryOfNextEncrypt r ms)) (hne : ∀ t ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms), ∀ x ∈ (gamma' i S g t).memo, assumedInjective x.1 = true → x.2.2 ≠ b) : ¬ MemoCollisionOn i r S g (fun u => u.AttackerKnows (runTraceMoves r ms)) (runTraceMoves r ms) (runVis r ms) (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms := by
  dsimp only [ptEntryOfNextEncrypt, EventMatchesEntry] at hem; obtain ⟨_, hb_eq⟩ := hem; dsimp only [List.map, DY.Libsignal.Composed.Refinement.eventBytes] at hb_eq
  injection hb_eq with hb_eq'
  have hmem0 := gamma'_randTerm i S g (runTraceMoves r ms).length 32 (by decide)
  have hb_σ : b = g.σ (runTraceMoves r ms).length 32 := by rw [← hb_eq']; unfold gamma; rw [hmem0]
  rintro ⟨x₁, hx₁, x₂, hx₂, hsh_ne, _, hpt₁, _, hval_eq⟩; simp only [ptEntryOfNextEncrypt, List.flatMap_cons, List.flatMap_nil, List.append_nil, hmem0] at hx₁ hx₂ hpt₁; have hx₁_eq : x₁ = (randTerm (runTraceMoves r ms).length 32, randTerm (runTraceMoves r ms).length 32, g.σ (runTraceMoves r ms).length 32) := List.mem_singleton.mp hx₁; subst hx₁_eq
  have hx₁_pt : randTerm (runTraceMoves r ms).length 32 ∈
      ptAtoms (runVis r ms) ++ [randTerm (runTraceMoves r ms).length 32] :=
    List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨_, hinj₂, _⟩ := hpt₁ hx₁_pt
  rcases List.mem_append.mp hx₂ with hx₂_pre | hx₂_new
  · obtain ⟨t_pre, ht_pre, hx₂_mem⟩ := List.mem_flatMap.mp hx₂_pre; exact hne t_pre ht_pre x₂ hx₂_mem hinj₂ (hval_eq.symm.trans hb_σ.symm)
  · have hx₂_eq := List.mem_singleton.mp hx₂_new; subst hx₂_eq; exact hsh_ne rfl
theorem not_pt_collision_of_ne_bytes_full {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hem : EventMatchesEntry i r S g (.pt b) (ptEntryOfNextEncrypt r ms)) (hne : ∀ t ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms), ∀ x ∈ (gamma' i S g t).memo, x.1 ∉ ptAtoms (runVis r ms) → assumedInjective x.1 = true → ¬ x.1.AttackerKnows (runTraceMoves r ms) → x.2.2 ≠ b) : ¬ MemoCollisionOn i r S g (fun u => u.AttackerKnows (runTraceMoves r ms)) (runTraceMoves r ms) (runVis r ms) (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms := by
  dsimp only [ptEntryOfNextEncrypt, EventMatchesEntry] at hem; obtain ⟨_, hb_eq⟩ := hem; dsimp only [List.map, DY.Libsignal.Composed.Refinement.eventBytes] at hb_eq
  injection hb_eq with hb_eq'
  have hmem0 := gamma'_randTerm i S g (runTraceMoves r ms).length 32 (by decide)
  have hb_σ : b = g.σ (runTraceMoves r ms).length 32 := by rw [← hb_eq']; unfold gamma; rw [hmem0]
  rintro ⟨x₁, hx₁, x₂, hx₂, hsh_ne, _, hpt₁, _, hval_eq⟩; simp only [ptEntryOfNextEncrypt, List.flatMap_cons, List.flatMap_nil, List.append_nil, hmem0] at hx₁ hx₂ hpt₁; have hx₁_eq : x₁ = (randTerm (runTraceMoves r ms).length 32, randTerm (runTraceMoves r ms).length 32, g.σ (runTraceMoves r ms).length 32) := List.mem_singleton.mp hx₁; subst hx₁_eq
  have hx₁_pt : randTerm (runTraceMoves r ms).length 32 ∈
      ptAtoms (runVis r ms) ++ [randTerm (runTraceMoves r ms).length 32] :=
    List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨hnot_pts₂, hinj₂, hnot_known₂⟩ := hpt₁ hx₁_pt
  have hnot_pt₂ : x₂.1 ∉ ptAtoms (runVis r ms) :=
    fun h => hnot_pts₂ (List.mem_append_left _ h)
  rcases List.mem_append.mp hx₂ with hx₂_pre | hx₂_new
  · obtain ⟨t_pre, ht_pre, hx₂_mem⟩ := List.mem_flatMap.mp hx₂_pre; exact hne t_pre ht_pre x₂ hx₂_mem hnot_pt₂ hinj₂ hnot_known₂ (hval_eq.symm.trans hb_σ.symm)
  · have hx₂_eq := List.mem_singleton.mp hx₂_new; subst hx₂_eq; exact hsh_ne rfl
theorem not_pt_prefixGhosts_collision_of_ne_bytes {i : ExternInterpretation} {r : Records} {S : Sem} {who : List Participant} {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent} {b : HwBytes} (hmp : MatchedPrefix i r S who g ms τ₁) (hne : ∀ t ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms), ∀ x ∈ (gamma' i S g t).memo, assumedInjective x.1 = true → x.2.2 ≠ b) : ¬ (EventMatchesEntry i r S g (.pt b) (ptEntryOfNextEncrypt r ms) ∧ ∀ g' ∈ PrefixGhosts i r S who g ms τ₁, MemoCollisionOn i r S g' (fun u => u.AttackerKnows (runTraceMoves r ms)) (runTraceMoves r ms) (runVis r ms) (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms) := by rintro ⟨hem, hall⟩; exact not_pt_collision_of_ne_bytes hem hne (hall g ⟨rfl, hmp⟩)
theorem not_ptSplitCollisionAt_of_ne_bytes {i : ExternInterpretation} {r : Records} {S : Sem} {who : List Participant} {ok : Nat → Bool} {τ : List MachineEvent} {n : Nat} {b₀ : HwBytes} (hb₀ : τ[n]? = some (.pt b₀)) (hne : ∀ g ms, ExplainsMoves i r S who ok g ms (τ.take n) → ∀ t ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms), ∀ x ∈ (gamma' i S g t).memo, assumedInjective x.1 = true → x.2.2 ≠ b₀) : ¬ PtSplitCollisionAt i r S who ok τ n := by
  rintro ⟨g, ms, b, hexp, hget, hem, hcol⟩; rw [hb₀] at hget
  injection hget with hpt
  injection hpt with hb
  subst hb; exact not_pt_prefixGhosts_collision_of_ne_bytes hexp.1 (hne g ms hexp) ⟨hem, hcol⟩
inductive LitConcatTree : DY.Bytes → Prop where
  | lit (b : ByteArray) : LitConcatTree (DY.Literal.literalToBytes b)
  | concat {lhs rhs : DY.Bytes} :
      LitConcatTree lhs → LitConcatTree rhs → LitConcatTree (DY.Concat.concat lhs rhs)
theorem litConcatTree_of_concat {lhs rhs : DY.Bytes} (h : LitConcatTree (DY.Concat.concat lhs rhs)) : LitConcatTree lhs ∧ LitConcatTree rhs := by
  generalize heq : DY.Concat.concat lhs rhs = t at h; cases h with
  | lit b =>
    have hv := congrArg (fun u : DY.Bytes => u.view? DY.Concat.Concat.SubF) heq; dsimp only [DY.Concat.concat, DY.Concat.CanConcat.concat, DY.Literal.literalToBytes] at hv; rw [DY.BytesView.view_pack, view_concat_lit] at hv; cases hv
  | concat hl hr => obtain ⟨rfl, rfl⟩ := concat_inj heq; exact ⟨hl, hr⟩
instance : Comparse.BytesCompatiblePred (LitConcatTree : DY.Bytes → Prop) where
  pred_empty := .lit .empty
  pred_concat _ _ hl hr := .concat hl hr
  pred_split buf n hbuf := by
    cases hsp : Comparse.BytesLike.split buf n with
    | none => trivial
    | some p => rw [← DY.Concat.concat_split buf n p.1 p.2 hsp] at hbuf; exact litConcatTree_of_concat hbuf
  pred_fromByteArray b := .lit b
export Symbolic.BugInjection.Proofs.Common443.CompExcuse (gamma_concatPrefixes)
export Symbolic.BugInjection.Proofs.Common443.CompExcuse (concatPrefixes_append)
export Symbolic.BugInjection.Proofs.Common443.CompExcuse (mem_memo_concatPrefixes)
theorem mem_memo_serialize_recvList_tr {i : ExternInterpretation} {S : Sem} {g : Ghost} {x : DY.Bytes × DY.Bytes × HwBytes} : ∀ (cs : List DY.Libsignal.TripleRatchet.RecvChain), x ∈ (gamma' i S g ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize cs)).memo → (∃ d ∈ cs, ∃ p ∈ (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize d, x ∈ (gamma' i S g p).memo) ∨ assumedInjective x.1 = false
  | [], hx => by
    have hx' : x ∈ (gamma' i S g (DY.Literal.literalToBytes .empty)).memo := by
      rwa [recvList_serialize_nil] at hx
    unfold gamma' at hx'; rw [show DY.Literal.literalToBytes .empty = ({ lit := .empty } : DY.Literal.Literal.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gLit0 (gAll i S g)] at hx'
    rcases List.mem_singleton.mp hx' with rfl; exact Or.inr (ai_lit_pack_eq .empty)
  | d :: cs, hx => by
    have h1 : ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize (d :: cs)) = Comparse.concatPrefixes ((Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize d)
          ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize cs) :=
      recvList_serialize_cons d cs
    rw [h1] at hx
    rcases mem_memo_concatPrefixes _ _ hx with ⟨p, hp, hxp⟩ | hxs | ⟨hinj, _⟩
    · exact Or.inl ⟨d, List.mem_cons_self, p, hp, hxp⟩
    · rcases mem_memo_serialize_recvList_tr cs hxs with ⟨d', hd', p, hp, hxp⟩ | hinj
      · exact Or.inl ⟨d', List.mem_cons_of_mem d hd', p, hp, hxp⟩
      · exact Or.inr hinj
    · exact Or.inr hinj
export Symbolic.BugInjection.Proofs.Common443.CompExcuse (trStatePrefixes)
theorem memo_serialize_local_tr_decomp {i : ExternInterpretation} {S : Sem} {g : Ghost} {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (Comparse.serialize ls : DY.Bytes)).memo) : (∃ p ∈ trStatePrefixes ls, x ∈ (gamma' i S g p).memo) ∨ (∃ d ∈ ls.state.recv, ∃ p ∈ (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize d, x ∈ (gamma' i S g p).memo) ∨ (assumedInjective x.1 = false ∧ (x ∈ (gamma' i S g ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize ls.state.recv)).memo ∨ (gamma i S g ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize ls.state.recv)).length ≤ x.2.2.length)) := by
  have hser : (Comparse.serialize ls : DY.Bytes) =
      Comparse.concatPrefixes (trStatePrefixes ls) ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize ls.state.recv) :=
    serialize_local_tr_eq_bridge ls
  rw [hser] at hx
  rcases mem_memo_concatPrefixes _ _ hx with hpre | hrecv | ⟨hinj, hlen⟩
  · exact Or.inl hpre
  · rcases mem_memo_serialize_recvList_tr ls.state.recv hrecv with hchain | hinj
    · exact Or.inr (Or.inl hchain)
    · exact Or.inr (Or.inr ⟨hinj, Or.inl hrecv⟩)
  · exact Or.inr (Or.inr ⟨hinj, Or.inr hlen⟩)
def MemoInjGt (i : ExternInterpretation) (S : Sem) (g : Ghost) (k : Nat) (t : DY.Bytes) : Prop := ∀ x ∈ (gamma' i S g t).memo, assumedInjective x.1 = true → k < x.2.2.length
theorem memoInjGt_lit (i : ExternInterpretation) (S : Sem) (g : Ghost) (k : Nat) (b : ByteArray) : MemoInjGt i S g k (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack) := by
  intro x hx hinj; unfold gamma' at hx; rw [DY.Bytes.rec_eq gLit0 (gAll i S g)] at hx
  rcases List.mem_singleton.mp hx with rfl; rw [ai_lit_pack_eq] at hinj; cases hinj
theorem memoInjGt_literalToBytes (i : ExternInterpretation) (S : Sem) (g : Ghost) (k : Nat) (b : ByteArray) : MemoInjGt i S g k (DY.Literal.literalToBytes b) := memoInjGt_lit i S g k b
theorem memoInjGt_randTerm {i : ExternInterpretation} {S : Sem} {g : Ghost} {k idx sz : Nat} (h : sz = 0 ∨ k < (g.σ idx sz).length) : MemoInjGt i S g k (randTerm idx sz) := by
  intro x hx _; unfold gamma' randTerm at hx; rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)] at hx
  dsimp only [gRandom, concretizeRandom] at hx; split_ifs at hx with hsz
  · cases hx
  · rcases List.mem_singleton.mp hx with rfl; exact h.resolve_left hsz
theorem memoInjGt_concat {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {a b : DY.Bytes} (ha : MemoInjGt i S g k a) (hb : MemoInjGt i S g k b) : MemoInjGt i S g k (DY.Concat.concat a b) := by
  intro x hx hinj; unfold gamma' at hx; rw [show DY.Concat.concat a b = ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gConcat0 (gAll i S g)] at hx; simp only [gConcat0, concretizeConcat, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxb
  · rw [show ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack = DY.Concat.concat a b from rfl, ai_concat_eq] at hinj; cases hinj
  · exact ha x hxa hinj
  · exact hb x hxb hinj
theorem memoInjGt_concatPrefixes {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} : ∀ {ps : List DY.Bytes} {s : DY.Bytes}, (∀ p ∈ ps, MemoInjGt i S g k p) → MemoInjGt i S g k s → MemoInjGt i S g k (Comparse.concatPrefixes ps s)
  | [], _, _, hs => by simpa [concatPrefixes_nil] using hs
  | p :: _, _, hps, hs => by
    rw [concatPrefixes_cons]
    exact memoInjGt_concat (hps p List.mem_cons_self) (memoInjGt_concatPrefixes (fun q hq => hps q (List.mem_cons_of_mem p hq)) hs)
theorem memoInjGt_of_litConcatTree {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {t : DY.Bytes} (h : LitConcatTree t) : MemoInjGt i S g k t := by
  induction h with
  | lit b => exact memoInjGt_literalToBytes i S g k b
  | concat _ _ ih1 ih2 => exact memoInjGt_concat ih1 ih2
theorem memoInjGt_dhPk_compI0 {S : Sem} {g : Ghost} {k : Nat} {sk : DY.Bytes} (hk : k < 32) (hsk : MemoInjGt compI0 S g k sk) : MemoInjGt compI0 S g k (DY.DiffieHellman.dhPk sk) := by
  intro x hx hinj; unfold gamma' at hx; rw [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gDhPk compI0) (gAll compI0 S g)] at hx; simp only [gDhPk, concretizeDhPk, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, bytes_rec_gAll] at hx
  rcases hx with rfl | hxsk
  · change k < (compLookupPub _).length; rw [compLookupPub_length]; exact hk
  · exact hsk x hxsk hinj
theorem memoInjGt_of_dhPk {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {sk : DY.Bytes} (h : MemoInjGt i S g k (DY.DiffieHellman.dhPk sk)) : MemoInjGt i S g k sk := by
  intro x hx hinj; apply h x _ hinj; unfold gamma' at hx ⊢
  show x ∈ (((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (gAll i S g))).memo
  rw [DY.Bytes.rec_eq (gDhPk i) (gAll i S g)]; exact List.mem_cons_of_mem _ (by simpa [node] using hx)
theorem memoInjGt_dh_pack_compI0 {S : Sem} {g : Ghost} {k : Nat} {pk sk : DY.Bytes} (hk : k < 32) (hpk : MemoInjGt compI0 S g k pk) (hsk : MemoInjGt compI0 S g k sk) : MemoInjGt compI0 S g k (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by
  intro x hx hinj; unfold gamma' at hx; rw [DY.Bytes.rec_eq (gDh compI0) (gAll compI0 S g)] at hx; simp only [gDh, concretizeDh, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxpk | hxsk
  · change k < (compLookupDh _ _).length; rw [compLookupDh_length]; exact hk
  · exact hpk x hxpk hinj
  · exact hsk x hxsk hinj
theorem memoInjGt_dh_compI0 {S : Sem} {g : Ghost} {k : Nat} {pk sk : DY.Bytes} (hk : k < 32) (hpk : MemoInjGt compI0 S g k pk) (hsk : MemoInjGt compI0 S g k sk) : MemoInjGt compI0 S g k (DY.DiffieHellman.dh pk sk) := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk; simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]; split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; subst hv; have hsk2 := memoInjGt_of_dhPk hpk; split
    · exact memoInjGt_dh_pack_compI0 hk hpk hsk
    · exact memoInjGt_dh_pack_compI0 hk (memoInjGt_dhPk_compI0 hk hsk) hsk2
  · exact memoInjGt_dh_pack_compI0 hk hpk hsk
theorem memoInjGt_hmac {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {a b : DY.Bytes} (hk : k < 32) (ha : MemoInjGt i S g k a) (hb : MemoInjGt i S g k b) : MemoInjGt i S g k (DY.Libsignal.TripleRatchet.hmac a b) := by
  intro x hx hinj; unfold gamma' DY.Libsignal.TripleRatchet.hmac at hx; rw [show DY.KdfExtract.kdfExtract a b = ({ salt := a, ikm := b } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gKdf0 i) (gAll i S g)] at hx; simp only [gKdf0, concretizeKdf, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxb
  · dsimp only [ByteSpecs.hmacWith]; rw [CompRTag.sha256With_length]; exact hk
  · exact ha x hxa hinj
  · exact hb x hxb hinj
theorem memoInjGt_hkdfBlock1 {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {prk info : DY.Bytes} (hk : k < 32) (hprk : MemoInjGt i S g k prk) (hinfo : MemoInjGt i S g k info) : MemoInjGt i S g k (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) := memoInjGt_hmac hk hprk (memoInjGt_concat hinfo (memoInjGt_lit i S g k _))
theorem memoInjGt_hkdfBlock2 {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {prk info : DY.Bytes} (hk : k < 32) (hprk : MemoInjGt i S g k prk) (hinfo : MemoInjGt i S g k info) : MemoInjGt i S g k (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) := memoInjGt_hmac hk hprk (memoInjGt_concat (memoInjGt_hkdfBlock1 hk hprk hinfo) (memoInjGt_concat hinfo (memoInjGt_lit i S g k _)))
theorem memoInjGt_hkdfBlock3 {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {prk info : DY.Bytes} (hk : k < 32) (hprk : MemoInjGt i S g k prk) (hinfo : MemoInjGt i S g k info) : MemoInjGt i S g k (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) := memoInjGt_hmac hk hprk (memoInjGt_concat (memoInjGt_hkdfBlock2 hk hprk hinfo) (memoInjGt_concat hinfo (memoInjGt_lit i S g k _)))
theorem memoInjGt_kemPk {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {sk : DY.Bytes} (hsk : MemoInjGt i S g k sk) : MemoInjGt i S g k (DY.PQKem.kemPk sk) := by intro x hx hinj; unfold gamma' at hx; rw [show DY.PQKem.kemPk sk = ({ sk := sk } : DY.PQKem.Pk.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gKemPk S) (gAll i S g)] at hx; simp only [gKemPk, concretizeKemPk, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, bytes_rec_gAll] at hx; exact hsk x hx hinj
private theorem compKyberCt0_len : compKyberCt0.length = 1568 := leBytes_length 1568 _
private theorem compKyberCt1_len : compKyberCt1.length = 1568 := leBytes_length 1568 _
private theorem compKyberCt2_len : compKyberCt2.length = 1568 := leBytes_length 1568 _
private theorem compDefaultKyberCt_len : compDefaultKyberCt.length = 1568 := List.length_replicate
private theorem take_append_eq_of_len {α : Type} {l1 l2 : List α} {n : Nat} (h : l1.length = n) : (l1 ++ l2).take n = l1 := by subst h; exact List.take_left
private theorem drop_append_eq_of_len {α : Type} {l1 l2 : List α} {n : Nat} (h : l1.length = n) : (l1 ++ l2).drop n = l2 := by subst h; exact List.drop_left
theorem compKyberEncaps_take_length (e : HwBytes) : ((compKyberEncaps e).take 1568).length = 1568 := by
  unfold compKyberEncaps
  split
  · rw [take_append_eq_of_len compKyberCt0_len, compKyberCt0_len]
  · split
    · rw [take_append_eq_of_len compKyberCt1_len, compKyberCt1_len]
    · split
      · rw [take_append_eq_of_len compKyberCt2_len, compKyberCt2_len]
      · rw [take_append_eq_of_len compDefaultKyberCt_len, compDefaultKyberCt_len]
theorem compKyberEncaps_drop_length (e : HwBytes) : ((compKyberEncaps e).drop 1568).length = 32 := by
  unfold compKyberEncaps
  split
  · rw [drop_append_eq_of_len compKyberCt0_len]; rfl
  · split
    · rw [drop_append_eq_of_len compKyberCt1_len]; rfl
    · split
      · rw [drop_append_eq_of_len compKyberCt2_len]; rfl
      · rw [drop_append_eq_of_len compDefaultKyberCt_len]; rfl
theorem memoInjGt_kemEncap_snd_compI0 {S : Sem} {g : Ghost} {k : Nat} {pk e : DY.Bytes} (hk : k < 32) (hpk : MemoInjGt compI0 S g k pk) (he : MemoInjGt compI0 S g k e) : MemoInjGt compI0 S g k (DY.PQKem.kemEncap pk e).2 := by
  intro x hx hinj; unfold gamma' at hx; rw [show (DY.PQKem.kemEncap pk e).2 = ({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gKemSS compI0 S) (gAll compI0 S g)] at hx; dsimp only [gKemSS, concretizeKemSS] at hx
  split_ifs at hx with helen
  · simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
    rcases hx with rfl | hxpk | hxe
    · change k < (((compI0 DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [_, _]).getD []).drop 1568).length; rw [compI0_kyberEncaps, Option.getD_some, compKyberEncaps_drop_length]; exact hk
    · exact hpk x hxpk hinj
    · exact he x hxe hinj
  · simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx; exact hx.elim (fun h => hpk x h hinj) (fun h => he x h hinj)
theorem memoInjGt_spqrInit {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {a p : DY.Bytes} (ha : MemoInjGt i S g k a) (hp : MemoInjGt i S g k p) : MemoInjGt i S g k (DY.Spqr.spqrInit a p) := by intro x hx hinj; unfold gamma' DY.Spqr.spqrInit at hx; rw [DY.Bytes.rec_eq (gSpqrInit S) (gAll i S g)] at hx; simp only [gSpqrInit, concretizeSpqrInit, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx; exact hx.elim (fun h => ha x h hinj) (fun h => hp x h hinj)
theorem memoInjGt_mem_bool (i : ExternInterpretation) (S : Sem) (g : Ghost) (k : Nat) (b : Bool) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.bool.serialize b) : MemoInjGt i S g k p := by
  obtain ⟨ba, -, h⟩ := bool_serialize_singleton b
  rw [h, List.mem_singleton] at hp; exact hp ▸ memoInjGt_literalToBytes i S g k ba
theorem memoInjGt_mem_slowNat (i : ExternInterpretation) (S : Sem) (g : Ghost) (k : Nat) : ∀ (n : Nat) {p : DY.Bytes}, p ∈ Comparse.NonExtensibleMessageFormat.slowNat.serialize n → MemoInjGt i S g k p
  | 0, _, hp => by rw [slowNat_serialize_zero] at hp; exact memoInjGt_mem_bool i S g k false hp
  | n + 1, _, hp => by
    rw [slowNat_serialize_succ, List.mem_append] at hp
    exact hp.elim (memoInjGt_mem_bool i S g k true) (memoInjGt_mem_slowNat i S g k n)
theorem memoInjGt_mem_uint32 (i : ExternInterpretation) (S : Sem) (g : Ghost) (k : Nat) (n : UInt32) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.uint32.serialize n) : MemoInjGt i S g k p := by
  obtain ⟨ba, -, h⟩ := uint32_serialize_singleton n
  rw [h, List.mem_singleton] at hp; exact hp ▸ memoInjGt_literalToBytes i S g k ba
theorem memoInjGt_mem_slowString (i : ExternInterpretation) (S : Sem) (g : Ghost) (k : Nat) (s : String) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowString.serialize s) : MemoInjGt i S g k p := by
  rw [slowString_serialize_eq, List.mem_append, List.mem_singleton] at hp
  exact hp.elim (memoInjGt_mem_slowNat i S g k _) (· ▸ memoInjGt_literalToBytes i S g k _)
theorem memoInjGt_mem_slowBytes {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {b : DY.Bytes} (hb : MemoInjGt i S g k b) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowBytes.serialize b) : MemoInjGt i S g k p := by
  have hser := slowBytes_serialize_eq b
  rw [hser, List.mem_append, List.mem_singleton] at hp; exact hp.elim (memoInjGt_mem_slowNat i S g k _) (· ▸ hb)
theorem memoInjGt_serialize_local_pqxdh {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState} (hsk : MemoInjGt i S g k ls.state.sk) : MemoInjGt i S g k (Comparse.serialize ls) := by
  have hser : (Comparse.serialize ls : DY.Bytes) = Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowString.serialize ls.participant ++
          (Comparse.NonExtensibleMessageFormat.bool.serialize ls.state.kind.toBits.1 ++ Comparse.NonExtensibleMessageFormat.bool.serialize ls.state.kind.toBits.2)) ls.state.sk :=
    serialize_local_pqxdh_eq_bridge ls
  rw [hser]; refine memoInjGt_concatPrefixes (fun p hp => ?_) hsk; simp only [List.mem_append] at hp
  rcases hp with h1 | h2 | h3
  exacts [memoInjGt_mem_slowString i S g k _ h1, memoInjGt_mem_bool i S g k _ h2, memoInjGt_mem_bool i S g k _ h3]
theorem memoInjGt_serialize_local_tr {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hmyIk : MemoInjGt i S g k ls.state.myIk) (hpeerIk : MemoInjGt i S g k ls.state.peerIk) (hrk : MemoInjGt i S g k ls.state.rk) (hdhs : MemoInjGt i S g k ls.state.dhs) (hcks : MemoInjGt i S g k ls.state.cks) (hsid : MemoInjGt i S g k ls.state.sid) (hspqr : MemoInjGt i S g k ls.state.spqr) (hrecv : ∀ d ∈ ls.state.recv, MemoInjGt i S g k d.ratchetKey ∧ MemoInjGt i S g k d.chainKey) : MemoInjGt i S g k (Comparse.serialize ls) := by
  intro x hx hinj
  rcases memo_serialize_local_tr_decomp hx with ⟨p, hp, hxp⟩ | ⟨d, hd, p, hp, hxp⟩ | ⟨hfalse, _⟩
  · unfold trStatePrefixes at hp; simp only [List.mem_append] at hp
    rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    exacts [memoInjGt_mem_slowString i S g k _ h1 x hxp hinj, memoInjGt_mem_slowString i S g k _ h2 x hxp hinj, memoInjGt_mem_slowBytes hmyIk h3 x hxp hinj, memoInjGt_mem_slowBytes hpeerIk h4 x hxp hinj, memoInjGt_mem_slowBytes hrk h5 x hxp hinj, memoInjGt_mem_slowBytes hdhs h6 x hxp hinj, memoInjGt_mem_slowBytes hcks h7 x hxp hinj, memoInjGt_mem_uint32 i S g k _ h8 x hxp hinj, memoInjGt_mem_uint32 i S g k _ h9 x hxp hinj, memoInjGt_mem_slowBytes hsid h10 x hxp hinj, memoInjGt_mem_bool i S g k _ h11 x hxp hinj, memoInjGt_mem_slowNat i S g k _ h12 x hxp hinj, memoInjGt_mem_slowBytes hspqr h13 x hxp hinj]
  · have hser : (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize d = Comparse.NonExtensibleMessageFormat.slowBytes.serialize d.ratchetKey ++ (Comparse.NonExtensibleMessageFormat.slowBytes.serialize d.chainKey ++ (Comparse.NonExtensibleMessageFormat.uint32.serialize d.index ++ Comparse.NonExtensibleMessageFormat.slowNat.serialize d.rIdx)) := recvChain_serialize_eq d; rw [hser] at hp; simp only [List.mem_append] at hp
    rcases hp with h1 | h2 | h3 | h4
    exacts [memoInjGt_mem_slowBytes (hrecv d hd).1 h1 x hxp hinj, memoInjGt_mem_slowBytes (hrecv d hd).2 h2 x hxp hinj, memoInjGt_mem_uint32 i S g k _ h3 x hxp hinj, memoInjGt_mem_slowNat i S g k _ h4 x hxp hinj]
  · rw [hfalse] at hinj; cases hinj
theorem memoInjGt_serializedIk {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {ik : DY.Bytes} (hik : MemoInjGt i S g k ik) : MemoInjGt i S g k (DY.Libsignal.PQXDH.serializedIk ik) := memoInjGt_concat (memoInjGt_lit i S g k _) hik
theorem memoInjGt_pqxdhKdf_none {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {dh1 dh2 dh3 ss₀ : DY.Bytes} (hk : k < 32) (hdh1 : MemoInjGt i S g k dh1) (hdh2 : MemoInjGt i S g k dh2) (hdh3 : MemoInjGt i S g k dh3) (hss₀ : MemoInjGt i S g k ss₀) : let keys := DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss₀);
    MemoInjGt i S g k keys.rk ∧ MemoInjGt i S g k keys.ck ∧ MemoInjGt i S g k keys.pqr := by
  have hprk : MemoInjGt i S g k (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss₀)) := memoInjGt_hmac hk (memoInjGt_lit i S g k _) (memoInjGt_concat (memoInjGt_lit i S g k _) (memoInjGt_concat hdh1 (memoInjGt_concat hdh2 (memoInjGt_concat hdh3 hss₀)))); have hinfo : MemoInjGt i S g k DY.Libsignal.PQXDH.pqxdhLabel := memoInjGt_lit i S g k _; exact ⟨memoInjGt_hkdfBlock1 hk hprk hinfo, memoInjGt_hkdfBlock2 hk hprk hinfo, memoInjGt_hkdfBlock3 hk hprk hinfo⟩
theorem memoInjGt_createChain {S : Sem} {g : Ghost} {k : Nat} {rk pk sk : DY.Bytes} (hk : k < 32) (hrk : MemoInjGt compI0 S g k rk) (hpk : MemoInjGt compI0 S g k (DY.X25519.x25519Key pk)) (hsk : MemoInjGt compI0 S g k sk) : MemoInjGt compI0 S g k (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 ∧ MemoInjGt compI0 S g k (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 := by have hprk := memoInjGt_hmac hk hrk (memoInjGt_dh_compI0 hk hpk hsk); have hinfo : MemoInjGt compI0 S g k (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := memoInjGt_lit compI0 S g k _; exact ⟨memoInjGt_hkdfBlock1 hk hprk hinfo, memoInjGt_hkdfBlock2 hk hprk hinfo⟩
theorem memoInjGt_iniAliceStartState {S : Sem} {g : Ghost} {k : Nat} (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (hk : k < 32) (hikA : MemoInjGt compI0 S g k o.ikA) (hikB : MemoInjGt compI0 S g k o.ikB) (hspk : MemoInjGt compI0 S g k o.spk) (hspk_key : MemoInjGt compI0 S g k (DY.X25519.x25519Key o.spk)) (hrk : MemoInjGt compI0 S g k o.keys.rk) (hck : MemoInjGt compI0 S g k o.keys.ck) (hpqr : MemoInjGt compI0 S g k o.keys.pqr) (hdhsA : MemoInjGt compI0 S g k (randTerm (tr.length + 2) 32)) : MemoInjGt compI0 S g k (Comparse.serialize (⟨a, iniAliceStartState tr b o⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by
  have hcc := memoInjGt_createChain hk hrk hspk_key hdhsA
  refine memoInjGt_serialize_local_tr (memoInjGt_serializedIk hikA) (memoInjGt_serializedIk hikB) hcc.1 hdhsA hcc.2
    (memoInjGt_concat (memoInjGt_dhPk_compI0 hk hdhsA) hrk) (memoInjGt_spqrInit hpqr (memoInjGt_lit compI0 S g k _)) (fun d hd => ?_)
  simp only [iniAliceStartState, List.mem_singleton] at hd; subst hd; exact ⟨hspk, hck⟩
theorem memoInjGt_prefixTerms {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {k : Nat} {tr : ExecTrace} {vis : List VisEntry} (hsend : ∀ v ∈ vis, v.kind = .send → ∀ u ∈ v.terms, MemoInjGt i S g k u) (hstates : ∀ ls ∈ storedStates r tr, MemoInjGt i S g k (Comparse.serialize ls)) (hsecrets : ∀ u ∈ storedSecrets tr, MemoInjGt i S g k u) (hpt : ∀ v ∈ vis, v.kind = .pt → ∀ u ∈ v.terms, MemoInjGt i S g k u) : ∀ u ∈ prefixTerms r tr vis, MemoInjGt i S g k u := by
  intro u hu; unfold prefixTerms principalTerms plaintextTerms at hu; simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_map, beq_iff_eq] at hu
  rcases hu with ((⟨v, ⟨hv_mem, hv_kind⟩, hu_v⟩ | ⟨ls, hls, rfl⟩) | hsec) | ⟨v, ⟨hv_mem, hv_kind⟩, hu_v⟩
  exacts [hsend v hv_mem hv_kind u hu_v, hstates ls hls, hsecrets u hsec, hpt v hv_mem hv_kind u hu_v]
theorem memoInjGt_setup_randTerm {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {k ts sz : Nat} (hcompat : Compat i r S g) (hwf : RecordsWF r) (hk : k < sz) (hp : (ts, sz) ∈ setupRandomsAt r) : MemoInjGt i S g k (randTerm ts sz) := by refine memoInjGt_randTerm (.inr ?_); rw [hcompat.1 (ts, sz) hp, hwf.2.1 (ts, sz) hp]; exact hk
end Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt
