/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.Refinement.Composed.MatchedPrefix
public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Clean Explanations, Read-Collision Preservation, and Whisper Step Assembly

Defines `rcvMoveTerm`, `AcceptCollision`, `RecvExcuseFree`, `CBadBridgeHyp`, and `CBadG2Hyp`,
proves preservation of `¬ ReadCollision` across non-decrypt and decrypt blocks, and establishes
clean whisper reselection and step assembly (`cBad_whisper_reselect_ef`, `cBadStep_whisper_c13`).
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)

/-! ## Definitions and Compatibility Abbreviations -/

abbrev CleanBy := Clean

abbrev CollisionAtBy := CollisionAt

abbrev RecvBody := RecvMsgBody

theorem CleanBy.explains {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {τ₁ : List MachineEvent} (h : CleanBy interpretation r S who ok g ms τ₁) :
    ExplainsMoves interpretation r S who ok g ms τ₁ := h.1

theorem CleanBy.matched {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {τ₁ : List MachineEvent} (h : CleanBy interpretation r S who ok g ms τ₁) :
    MatchedPrefix interpretation r S who g ms τ₁ := h.1.1

theorem CleanBy.not_readCollision {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {τ₁ : List MachineEvent} (h : CleanBy interpretation r S who ok g ms τ₁) :
    ¬ ReadCollision interpretation r S g ms τ₁ := h.2

theorem cleanBy_prefix {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms₁ ms₂ : List Move}
    {τ₁ τ₂ : List MachineEvent} (h : CleanBy interpretation r S who ok g (ms₁ ++ ms₂) (τ₁ ++ τ₂))
    (hlen : τ₁.length = (runVis r ms₁).length) :
    CleanBy interpretation r S who ok g ms₁ τ₁ :=
  clean_prefix hlen h

/-- Network message term read by a `decrypt` or `decryptSkipped` move on `tr`, or `none` for all
other moves. -/
def rcvMoveTerm (tr : ExecTrace) (m : Move) : Option DY.Bytes :=
  m.decryptMsgIdx?.bind tr.getMessageSentAt

@[scoped simp] theorem rcvMoveTerm_decrypt (tr : ExecTrace) (me : Participant)
    (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool) :
    rcvMoveTerm tr (.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped) =
      tr.getMessageSentAt msgIdx := rfl

@[scoped simp] theorem rcvMoveTerm_decryptSkipped (tr : ExecTrace) (me : Participant)
    (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool) :
    rcvMoveTerm tr (.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped) =
      tr.getMessageSentAt msgIdx := rfl

theorem MoveReadsCollidingMsg.iff_rcvMoveTerm {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pre : List Move} {e : MachineEvent} {m : Move} :
    MoveReadsCollidingMsg interpretation r S g pre e m ↔
      ∃ (b : HwBytes) (t : DY.Bytes),
        RecvMsgBody e b ∧ rcvMoveTerm (runTraceMoves r pre) m = some t ∧
        RecvCollision interpretation r S g pre t := by
  cases m <;> simp [MoveReadsCollidingMsg, rcvMoveTerm, Move.decryptMsgIdx?]

/-- Second disjunct of `WhisperExcused`: some representation of `b` is accepted via
`ModelAcceptsTermAfterCoinSplit`, and every accepted representation suffers `RecvCollision`. -/
abbrev AcceptCollision (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost) (ms : List Move)
    (τ₁ : List MachineEvent) (e : MachineEvent) (τ₂ : List MachineEvent) (b : HwBytes) : Prop :=
  let reps := recvRepresentations interpretation r S g ms b
  let accepts := ModelAcceptsTermAfterCoinSplit interpretation r S who ok g ms τ₁ e τ₂
  (∃ t ∈ reps, accepts t) ∧ ∀ t ∈ reps, accepts t → RecvCollision interpretation r S g ms t

abbrev AcceptCollisionBy := AcceptCollision

/-- Neither `ReselectCollision` on `t` nor `AcceptCollision` on `b` occurs at `(g, ms)` on `τ₁`. -/
abbrev RecvExcuseFree (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost) (ms : List Move)
    (τ₁ : List MachineEvent) (e : MachineEvent) (τ₂ : List MachineEvent) (b : HwBytes)
    (t : DY.Bytes) : Prop :=
  ¬ ReselectCollision interpretation r S g ms t ∧
    ¬ AcceptCollision interpretation r S who ok g ms τ₁ e τ₂ b

/-! ## Preservation of `¬ ReadCollision` -/

theorem vis_length_pos_of_rcvMoveTerm_some {tr : ExecTrace} {m : Move} {t : DY.Bytes}
    (ht : rcvMoveTerm tr m = some t) : 1 ≤ (m.vis tr).length := by
  cases m <;> simp [rcvMoveTerm, Move.decryptMsgIdx?] at ht
  all_goals
    simp [Move.vis, decVis, ht]

theorem runVis_take_length_lt_of_rcvMoveTerm_some {r : ProtocolSetup} {ms : List Move} {i : Nat}
    {m : Move} {t : DY.Bytes} (hm : ms[i]? = some m)
    (ht : rcvMoveTerm (runTraceMoves r (ms.take i)) m = some t) :
    (runVis r (ms.take i)).length < (runVis r ms).length := by
  have hi : i < ms.length := (List.getElem?_eq_some_iff.mp hm).1
  have hm_eq : ms[i] = m := by
    rw [List.getElem?_eq_getElem hi] at hm
    exact Option.some.inj hm
  have hsplit : ms = ms.take i ++ m :: ms.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i ms, List.drop_eq_getElem_cons hi, hm_eq]
  have hpos := vis_length_pos_of_rcvMoveTerm_some ht
  conv_rhs => rw [hsplit, runVis_append]
  simp only [runMoves, List.length_append]
  omega

private theorem split_append_of_length_lt {α : Type} {acc blk τ₁ : List α} {e : α} {τ₂ : List α}
    (heq : acc ++ blk = τ₁ ++ e :: τ₂) (hlt : τ₁.length < acc.length) :
    ∃ τ₂_acc, acc = τ₁ ++ e :: τ₂_acc ∧ τ₂ = τ₂_acc ++ blk := by
  have h1 : τ₁ = acc.take τ₁.length := by
    have h := congrArg (List.take τ₁.length) heq
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt), List.take_left] at h
    exact h.symm
  have h2 : acc.drop τ₁.length = e :: acc.drop (τ₁.length + 1) := by
    have hdrop := congrArg (List.drop τ₁.length) heq
    rw [List.drop_left] at hdrop
    have hlen_pos : 0 < (acc.drop τ₁.length).length := by simp; omega
    cases hd : acc.drop τ₁.length with
    | nil => simp [hd] at hlen_pos
    | cons a tl =>
      rw [List.drop_append_of_le_length (Nat.le_of_lt hlt), hd] at hdrop
      simp only [List.cons_append, List.cons.injEq] at hdrop
      obtain ⟨rfl, _⟩ := hdrop
      rw [← List.drop_drop, hd]
      rfl
  refine ⟨acc.drop (τ₁.length + 1), ?_, ?_⟩
  · conv_lhs => rw [← List.take_append_drop τ₁.length acc, ← h1, h2]
  · have hdrop := congrArg (List.drop τ₁.length) heq
    rw [List.drop_append_of_le_length (Nat.le_of_lt hlt), h2, List.drop_left] at hdrop
    simpa using hdrop.symm

/-- Lifts `¬ ReadCollision` across `(ms₀ ++ δ, acc ++ blk)` when `δ` has no decrypt moves and the
first non-`rng` event of `blk` is not `.accept`. -/
theorem not_readCollision_append_of_no_decrypt {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms₀ δ : List Move} {acc blk : List MachineEvent}
    (hnd : ¬ ReadCollision interpretation r S g ms₀ acc)
    (hlen : acc.length = (runVis r ms₀).length)
    (hno_dec : ∀ m ∈ δ, ∀ tr, rcvMoveTerm tr m = none)
    (hblk : ∀ pt, (blk.filter fun e => eventKind e != .rng).head? ≠ some (.accept pt)) :
    ¬ ReadCollision interpretation r S g (ms₀ ++ δ) (acc ++ blk) := by
  rintro ⟨i, τ₁, e, τ₂, m, heq, hm, hF, ⟨pt, hpt⟩, hRd⟩
  obtain ⟨b, t, _, ht, _⟩ := MoveReadsCollidingMsg.iff_rcvMoveTerm.mp hRd
  by_cases hi : i < ms₀.length
  · have htk : (ms₀ ++ δ).take i = ms₀.take i := List.take_append_of_le_length (Nat.le_of_lt hi)
    have hm₀ : ms₀[i]? = some m := by rwa [List.getElem?_append_left hi] at hm
    rw [htk] at hF ht hRd
    have hlt : τ₁.length < acc.length := by
      rw [hF.length_eq, hlen]
      exact runVis_take_length_lt_of_rcvMoveTerm_some hm₀ ht
    obtain ⟨τ₂_acc, hacc, rfl⟩ := split_append_of_length_lt heq hlt
    rw [List.filter_append] at hpt
    cases hf : τ₂_acc.filter (fun e => eventKind e != .rng) with
    | nil =>
      rw [hf, List.nil_append] at hpt
      exact hblk pt hpt
    | cons a tl =>
      rw [hf, List.cons_append, List.head?_cons] at hpt
      exact hnd ⟨i, τ₁, e, τ₂_acc, m, hacc, hm₀, hF, ⟨pt, by simp [hf, hpt]⟩, hRd⟩
  · have hle : ms₀.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getElem?_append_right hle] at hm
    have hm_mem : m ∈ δ := List.mem_of_getElem? hm
    have hnone := hno_dec m hm_mem (runTraceMoves r ((ms₀ ++ δ).take i))
    rw [hnone] at ht
    cases ht

/-- Preserves `¬ ReadCollision` across an accepting decrypt block `pre ++ m_dec :: post` when `pre`
and `post` contain no decrypt moves and the term read by `m_dec` avoids `RecvCollision`. -/
theorem not_readCollision_snoc_decrypt {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms₀ pre post : List Move} {m_dec : Move}
    {acc τ₂_dec : List MachineEvent} {wire : HwBytes}
    (hnd : ¬ ReadCollision interpretation r S g ms₀ acc)
    (hlen : acc.length = (runVis r ms₀).length)
    (_hpre_vis : (runMoves pre (runTraceMoves r ms₀)).2 = [])
    (hpre_no_dec : ∀ m ∈ pre, ∀ tr, rcvMoveTerm tr m = none)
    (hpost_no_dec : ∀ m ∈ post, ∀ tr, rcvMoveTerm tr m = none)
    (hnc : ∀ t, rcvMoveTerm (runTraceMoves r (ms₀ ++ pre)) m_dec = some t →
      ¬ RecvCollision interpretation r S g (ms₀ ++ pre) t) :
    ¬ ReadCollision interpretation r S g
      (ms₀ ++ (pre ++ m_dec :: post)) (acc ++ (.recv wire :: τ₂_dec)) := by
  rintro ⟨i, τ₁, e, τ₂, m, heq, hm, hF, ⟨pt, hpt⟩, hRd⟩
  obtain ⟨b, t, _, ht, hC⟩ := MoveReadsCollidingMsg.iff_rcvMoveTerm.mp hRd
  by_cases hi₀ : i < ms₀.length
  · have htk : (ms₀ ++ (pre ++ m_dec :: post)).take i = ms₀.take i :=
      List.take_append_of_le_length (Nat.le_of_lt hi₀)
    have hm₀ : ms₀[i]? = some m := by rwa [List.getElem?_append_left hi₀] at hm
    rw [htk] at hF ht hRd
    have hlt : τ₁.length < acc.length := by
      rw [hF.length_eq, hlen]
      exact runVis_take_length_lt_of_rcvMoveTerm_some hm₀ ht
    obtain ⟨τ₂_acc, hacc, rfl⟩ := split_append_of_length_lt heq hlt
    rw [List.filter_append] at hpt
    cases hf : τ₂_acc.filter (fun e => eventKind e != .rng) with
    | nil =>
      rw [hf, List.nil_append] at hpt
      have hhd : ((MachineEvent.recv wire :: τ₂_dec).filter fun e => eventKind e != .rng).head? =
          some (.recv wire) := rfl
      rw [hhd] at hpt
      cases hpt
    | cons a tl =>
      rw [hf, List.cons_append, List.head?_cons] at hpt
      exact hnd ⟨i, τ₁, e, τ₂_acc, m, hacc, hm₀, hF, ⟨pt, by simp [hf, hpt]⟩, hRd⟩
  · by_cases hi₁ : i < ms₀.length + pre.length
    · have hassoc : ms₀ ++ (pre ++ m_dec :: post) = (ms₀ ++ pre) ++ (m_dec :: post) := by
        simp [List.append_assoc]
      have hge₀ : ms₀.length ≤ i := Nat.le_of_not_lt hi₀
      rw [hassoc, List.getElem?_append_left (by simp; omega), List.getElem?_append_right hge₀] at hm
      have hnone := hpre_no_dec m (List.mem_of_getElem? hm)
        (runTraceMoves r ((ms₀ ++ (pre ++ m_dec :: post)).take i))
      rw [hnone] at ht
      cases ht
    · by_cases hi_eq : i = ms₀.length + pre.length
      · subst hi_eq
        have hassoc : ms₀ ++ (pre ++ m_dec :: post) = (ms₀ ++ pre) ++ (m_dec :: post) := by
          simp [List.append_assoc]
        have hm_dec : m = m_dec := by
          rw [hassoc, List.getElem?_append_right (by simp)] at hm
          simpa using hm.symm
        subst hm_dec
        have htk : (ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length) = ms₀ ++ pre := by
          rw [hassoc]
          exact List.take_left' (by simp)
        rw [htk] at ht hC
        exact hnc t ht hC
      · have hassoc : ms₀ ++ (pre ++ m_dec :: post) = (ms₀ ++ pre ++ [m_dec]) ++ post := by
          simp [List.append_assoc]
        rw [hassoc, List.getElem?_append_right (by simp; omega)] at hm
        have hnone := hpost_no_dec m (List.mem_of_getElem? hm)
          (runTraceMoves r ((ms₀ ++ (pre ++ m_dec :: post)).take i))
        rw [hnone] at ht
        cases ht

/-- Extracts `¬ RecvCollision` on the term `t` read by `m` at `ms₀ ++ pre` from `¬ ReadCollision`
on `(ms₀ ++ (pre ++ m :: post), acc ++ .recv wire :: τ₂_dec)`. -/
theorem not_recvCollision_of_not_readCollision {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    {acc τ₂_dec : List MachineEvent} {wire b pt : HwBytes} {t : DY.Bytes}
    (hnd : ¬ ReadCollision interpretation r S g
      (ms₀ ++ (pre ++ m :: post)) (acc ++ .recv wire :: τ₂_dec))
    (hF₀ : List.Forall₂ (EventMatchesEntry interpretation r S g) acc (runVis r ms₀))
    (hpre_vis : (runMoves pre (runTraceMoves r ms₀)).2 = [])
    (hpt : (τ₂_dec.filter fun e => eventKind e != .rng).head? = some (.accept pt))
    (hrb : RecvMsgBody (.recv wire) b)
    (ht : rcvMoveTerm (runTraceMoves r (ms₀ ++ pre)) m = some t) :
    ¬ RecvCollision interpretation r S g (ms₀ ++ pre) t := by
  intro hcol
  apply hnd
  have htk : (ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length) = ms₀ ++ pre := by
    rw [← List.append_assoc]
    exact List.take_left' (by simp)
  have hm : (ms₀ ++ (pre ++ m :: post))[ms₀.length + pre.length]? = some m := by
    rw [← List.append_assoc, List.getElem?_append_right (by simp)]
    simp
  have hvis_pre : runVis r (ms₀ ++ pre) = runVis r ms₀ := by
    rw [runVis_append, hpre_vis, List.append_nil]
  refine ⟨ms₀.length + pre.length, acc, .recv wire, τ₂_dec, m, rfl, hm, ?_, ⟨pt, hpt⟩, ?_⟩
  · rw [htk, hvis_pre]
    exact hF₀
  · rw [htk, MoveReadsCollidingMsg.iff_rcvMoveTerm]
    exact ⟨b, t, hrb, ht, hcol⟩

/-! ## Clean Reselection and Step Assembly -/

/-- From `¬ CollisionAt` on `acc ++ .recv (tag :: body) :: τ₂` and an existing explanation
`(g₁, ms₁)` of `acc` with a representation of `b`, extracts a `CleanBy` explanation `(g', ms')`
and a non-colliding, `RecvExcuseFree` representation `t'`. -/
theorem cBad_whisper_reselect_ef {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {g₁ : Ghost} {ms₁ : List Move} {acc τ₂ : List MachineEvent}
    {tag : BitVec 8} {body b pt : HwBytes} {t₁ : DY.Bytes}
    (hex₁ : ExplainsMoves interpretation r S who ok g₁ ms₁ acc)
    (ht₁ : t₁ ∈ recvRepresentations interpretation r S g₁ ms₁ b)
    (hpt : (τ₂.filter fun e => eventKind e != .rng).head? = some (.accept pt))
    (hrb : (tag = wireWhisperTag ∧ b = body) ∨
      (∃ p, parsePreKeyWire (tag :: body) = some p ∧ b = p.message ∧
        KnownBaseKey interpretation r S g₁ ms₁ p))
    (hncol : ¬ CollisionAt interpretation r S who ok (acc ++ .recv (tag :: body) :: τ₂)) :
    ∃ (g' : Ghost) (ms' : List Move) (t' : DY.Bytes),
      ExplainsMoves interpretation r S who ok g' ms' acc ∧
      ¬ ReadCollision interpretation r S g' ms' acc ∧
      CleanBy interpretation r S who ok g' ms' acc ∧
      t' ∈ recvRepresentations interpretation r S g' ms' b ∧
      ¬ RecvCollision interpretation r S g' ms' t' ∧
      RecvExcuseFree interpretation r S who ok g' ms' acc (.recv (tag :: body)) τ₂ b t' := by
  have hnot_exc : ¬ WhisperExcused interpretation r S who ok g₁ ms₁ acc (.recv (tag :: body)) τ₂ b := by
    intro hexc
    apply hncol
    refine ⟨acc, .recv (tag :: body), τ₂, g₁, ms₁, rfl, hex₁, ⟨pt, hpt⟩, ?_⟩
    rcases hrb with ⟨rfl, rfl⟩ | ⟨p, hp, rfl, hkb⟩
    · exact Or.inl ⟨rfl, hexc⟩
    · exact Or.inr ⟨p, hp, Or.inl ⟨hkb, hexc⟩⟩
  refine Classical.byContradiction fun hno => hnot_exc ⟨⟨t₁, ht₁⟩, ?_⟩
  intro g' ms' hex' hnrc
  have hclean : CleanBy interpretation r S who ok g' ms' acc := ⟨hex', hnrc⟩
  by_cases hac : AcceptCollision interpretation r S who ok g' ms' acc (.recv (tag :: body)) τ₂ b
  · exact Or.inr hac
  · refine Or.inl (fun t' ht' => Classical.byContradiction fun hnc => ?_)
    exact hno ⟨g', ms', t', hex', hnrc, hclean, ht',
      fun hc => hnc (Or.inl hc), ⟨fun hrs => hnc (Or.inr hrs), hac⟩⟩

/-- Moves that read a received network or prekey message (`decrypt`, `decryptSkipped`, `bobStart`). -/
def isReadMove : Move → Bool
  | .decrypt .. => true
  | .decryptSkipped .. => true
  | .bobStart .. => true
  | _ => false

theorem rcvMoveTerm_eq_none_of_isReadMove_false {m : Move} (h : isReadMove m = false)
    (tr : ExecTrace) : rcvMoveTerm tr m = none := by
  cases m <;> simp [isReadMove, rcvMoveTerm, Move.decryptMsgIdx?] at h ⊢

theorem cleanBy_snoc_decrypt {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms₀ pre post : List Move} {m_dec : Move}
    {acc τ₂_dec : List MachineEvent} {wire b : HwBytes} {t : DY.Bytes}
    (hc₀ : CleanBy interpretation r S who ok g ms₀ acc)
    (hex : ExplainsMoves interpretation r S who ok g (ms₀ ++ (pre ++ m_dec :: post))
      (acc ++ .recv wire :: τ₂_dec))
    (hpre_vis : (runMoves pre (runTraceMoves r ms₀)).2 = [])
    (hpre_no_read : ∀ m ∈ pre, isReadMove m = false)
    (hpost_no_read : ∀ m ∈ post, isReadMove m = false)
    (hm_dec : rcvMoveTerm (runTraceMoves r (ms₀ ++ pre)) m_dec = some t)
    (_hb : RecvMsgBody (.recv wire) b)
    (_hrep : t ∈ recvRepresentations interpretation r S g (ms₀ ++ pre) b)
    (hncol : ¬ RecvCollision interpretation r S g (ms₀ ++ pre) t) :
    CleanBy interpretation r S who ok g (ms₀ ++ (pre ++ m_dec :: post))
      (acc ++ .recv wire :: τ₂_dec) := by
  refine ⟨hex, not_readCollision_snoc_decrypt hc₀.not_readCollision
    (matchedPrefix_length_eq hc₀.matched) hpre_vis
    (fun m hm => rcvMoveTerm_eq_none_of_isReadMove_false (hpre_no_read m hm))
    (fun m hm => rcvMoveTerm_eq_none_of_isReadMove_false (hpost_no_read m hm)) ?_⟩
  intro t' ht'
  cases hm_dec.symm.trans ht'
  exact hncol

/-- Existence of an accepting block `pre ++ m :: post` extending `(g₀, ms₀)` to explain
`acc ++ .recv wire :: τ₂` where `m` is the unique read move and its read term avoids `RecvCollision`. -/
def CBadBridgeHyp (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (g₀ : Ghost) (ms₀ : List Move)
    (acc : List MachineEvent) (wire b : HwBytes) (τ₂ : List MachineEvent) : Prop :=
  ∃ (pre post : List Move) (m : Move) (t : DY.Bytes),
    ExplainsMoves interpretation r S who ok g₀ (ms₀ ++ (pre ++ m :: post)) (acc ++ .recv wire :: τ₂) ∧
    (runMoves pre (runTraceMoves r ms₀)).2 = [] ∧
    (∀ m' ∈ pre, isReadMove m' = false) ∧
    (∀ m' ∈ post, isReadMove m' = false) ∧
    rcvMoveTerm (runTraceMoves r (ms₀ ++ pre)) m = some t ∧
    RecvMsgBody (.recv wire) b ∧
    t ∈ recvRepresentations interpretation r S g₀ (ms₀ ++ pre) b ∧
    ¬ RecvCollision interpretation r S g₀ (ms₀ ++ pre) t

theorem cleanBy_stitch_bridge {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g₀ : Ghost} {ms₀ : List Move}
    {acc τ₂ : List MachineEvent} {wire b : HwBytes}
    (hc : CleanBy interpretation r S who ok g₀ ms₀ acc)
    (hb : CBadBridgeHyp interpretation r S who ok g₀ ms₀ acc wire b τ₂) :
    ∃ ms, CleanBy interpretation r S who ok g₀ ms (acc ++ .recv wire :: τ₂) := by
  obtain ⟨pre, post, m, t, hex, hpre_vis, hpre_nd, hpost_nd, hm, hbody, hrep, hncol⟩ := hb
  exact ⟨ms₀ ++ (pre ++ m :: post),
    cleanBy_snoc_decrypt hc hex hpre_vis hpre_nd hpost_nd hm hbody hrep hncol⟩

theorem cBadStep_whisper_before_c13 {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {g₀ : Ghost} {ms₀ : List Move} {acc τ₂ : List MachineEvent}
    {tag : BitVec 8} {body b pt : HwBytes} {t₀ : DY.Bytes}
    (hc₀ : CleanBy interpretation r S who ok g₀ ms₀ acc)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r S g₀ ms₀ b)
    (hpt : (τ₂.filter fun e => eventKind e != .rng).head? = some (.accept pt))
    (hrb : (tag = wireWhisperTag ∧ b = body) ∨
      (∃ p, parsePreKeyWire (tag :: body) = some p ∧ b = p.message ∧
        KnownBaseKey interpretation r S g₀ ms₀ p)) :
    (∃ g_clean ms_clean t_clean,
      CleanBy interpretation r S who ok g_clean ms_clean acc ∧
      t_clean ∈ recvRepresentations interpretation r S g_clean ms_clean b ∧
      ¬ RecvCollision interpretation r S g_clean ms_clean t_clean ∧
      RecvExcuseFree interpretation r S who ok g_clean ms_clean acc (.recv (tag :: body)) τ₂ b t_clean) ∨
    CollisionAt interpretation r S who ok (acc ++ .recv (tag :: body) :: τ₂) := by
  by_cases hcol : CollisionAt interpretation r S who ok (acc ++ .recv (tag :: body) :: τ₂)
  · exact Or.inr hcol
  · obtain ⟨g', ms', t', _, _, hc', ht', hnc', hns'⟩ :=
      cBad_whisper_reselect_ef hc₀.explains ht₀ hpt hrb hcol
    exact Or.inl ⟨g', ms', t', hc', ht', hnc', hns'⟩

/-- Hypothesis that any `CleanBy` explanation `(g, ms)` with a non-colliding, `RecvExcuseFree`
representation of `b` admits a ghost `g₁` agreeing with `g` below `(runTraceMoves r ms).length`
that remains `CleanBy` on `acc` and satisfies `CBadBridgeHyp` on `mid ++ [.accept pt]`. -/
def CBadG2Hyp (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool)
    (acc mid : List MachineEvent) (pt : HwBytes) (tag : BitVec 8) (body b : HwBytes) : Prop :=
  (∀ e ∈ mid, ∀ x, e ≠ .recv x) →
  ∀ g ms t',
    CleanBy interpretation r S who ok g ms acc →
    t' ∈ recvRepresentations interpretation r S g ms b →
    ¬ RecvCollision interpretation r S g ms t' →
    RecvExcuseFree interpretation r S who ok g ms acc (.recv (tag :: body)) (mid ++ [.accept pt]) b t' →
    ∃ g₁,
      (∀ ts < (runTraceMoves r ms).length, ∀ len, g₁.σ ts len = g.σ ts len) ∧
      CleanBy interpretation r S who ok g₁ ms acc ∧
      CBadBridgeHyp interpretation r S who ok g₁ ms acc (tag :: body) b (mid ++ [.accept pt])

theorem cBadCleanStep_of_parts_c13 {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {g₀ : Ghost} {ms₀ : List Move} {acc mid : List MachineEvent}
    {tag : BitVec 8} {body b pt : HwBytes} {t₀ : DY.Bytes}
    (hc₀ : CleanBy interpretation r S who ok g₀ ms₀ acc)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r S g₀ ms₀ b)
    (hmid_no_recv : ∀ e ∈ mid, ∀ x, e ≠ .recv x)
    (hpt : ((mid ++ [MachineEvent.accept pt]).filter fun e => eventKind e != .rng).head? =
      some (.accept pt))
    (hrb : (tag = wireWhisperTag ∧ b = body) ∨
      (∃ p, parsePreKeyWire (tag :: body) = some p ∧ b = p.message ∧
        KnownBaseKey interpretation r S g₀ ms₀ p))
    (hG2 : CBadG2Hyp interpretation r S who ok acc mid pt tag body b)
    (hncol : ¬ CollisionAt interpretation r S who ok
      (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt]))) :
    ∃ (g : Ghost) (ms : List Move),
      CleanBy interpretation r S who ok g ms acc ∧
      CBadBridgeHyp interpretation r S who ok g ms acc (tag :: body) b (mid ++ [.accept pt]) := by
  obtain ⟨g_c, ms_c, t_c, _, _, hc_c, ht_c, hnc_c, hns_c⟩ :=
    cBad_whisper_reselect_ef hc₀.explains ht₀ hpt hrb hncol
  obtain ⟨g₁, _, hc₁, hbr₁⟩ := hG2 hmid_no_recv g_c ms_c t_c hc_c ht_c hnc_c hns_c
  exact ⟨g₁, ms_c, hc₁, hbr₁⟩

/-- Either `acc ++ .recv (tag :: body) :: (mid ++ [.accept pt])` admits a `CleanBy` explanation or
`CollisionAt` holds on that trace. -/
theorem cBadStep_whisper_c13 {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {g₀ : Ghost} {ms₀ : List Move} {acc mid : List MachineEvent}
    {tag : BitVec 8} {body b pt : HwBytes} {t₀ : DY.Bytes}
    (hc₀ : CleanBy interpretation r S who ok g₀ ms₀ acc)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r S g₀ ms₀ b)
    (hmid_no_recv : ∀ e ∈ mid, ∀ x, e ≠ .recv x)
    (hpt : ((mid ++ [MachineEvent.accept pt]).filter fun e => eventKind e != .rng).head? =
      some (.accept pt))
    (hrb : (tag = wireWhisperTag ∧ b = body) ∨
      (∃ p, parsePreKeyWire (tag :: body) = some p ∧ b = p.message ∧
        KnownBaseKey interpretation r S g₀ ms₀ p))
    (hG2 : CBadG2Hyp interpretation r S who ok acc mid pt tag body b) :
    (∃ g_clean ms_clean,
      CleanBy interpretation r S who ok g_clean ms_clean
        (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt]))) ∨
    CollisionAt interpretation r S who ok
      (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt])) := by
  by_cases hcol : CollisionAt interpretation r S who ok
      (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt]))
  · exact Or.inr hcol
  · obtain ⟨g₁, ms_c, hc₁, hbr₁⟩ :=
      cBadCleanStep_of_parts_c13 hc₀ ht₀ hmid_no_recv hpt hrb hG2 hcol
    obtain ⟨ms_ext, hc_ext⟩ := cleanBy_stitch_bridge hc₁ hbr₁
    exact Or.inl ⟨g₁, ms_ext, hc_ext⟩

end Symbolic.Swarm.CREF
