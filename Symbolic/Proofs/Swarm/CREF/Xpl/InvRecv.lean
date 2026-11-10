/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix

/-!
# Whisper Receive-Block Inversion

Proves `xplStep_recv` and `xplInv_recv`: under a faithful explanation, a whisper `recv_wire` block
(`recv (wireWhisperTag :: body)` followed by at most a DH ratchet draw and an `accept`) is explained
by one visible move of the caller `p` surrounded by `InvisibleNoEffect` moves, and if the block
accepts then that move satisfies `DecryptBy p`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)

/-- Event shape of a whisper `recv_wire` call: `recv (wireWhisperTag :: body)` followed by `rng` or
`accept` events with total length at most `3`. -/
structure RecvBlockShape (blk : List MachineEvent) : Prop where
  head : ∃ body, blk.head? = some (.recv (wireWhisperTag :: body))
  tail : ∀ e ∈ blk.tail, eventKind e = .rng ∨ eventKind e = .accept
  len : blk.length ≤ 3

/-- Step conclusion for a whisper `recv_wire` block: a move acting for `p` (or nobody) that either
satisfies `RecvKind` or has `NoSessionEffect`, and satisfies `DecryptBy p` when `blk` accepts. -/
def RecvStep (p : Participant) (blk : List MachineEvent) (tr : ExecTrace) (m : Move) : Prop :=
  ActorIn p m ∧ (RecvKind m ∨ NoSessionEffect tr m) ∧
    ((∃ e ∈ blk, eventKind e = .accept) → DecryptBy p m)

theorem xpl_parsePreKeyWire_whisper (body : HwBytes) :
    parsePreKeyWire (wireWhisperTag :: body) = none := by
  unfold parsePreKeyWire
  simp only []
  rfl

theorem xpl_opkMatches_whisper {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (body : HwBytes) (ts : List DY.Bytes) :
    ¬ PreKeyRecvOpkMatches interpretation r S g (wireWhisperTag :: body) ts := by
  intro h
  unfold PreKeyRecvOpkMatches at h
  split at h
  · obtain ⟨⟨p, hp, _⟩, _⟩ := h
    rw [xpl_parsePreKeyWire_whisper] at hp; cases hp
  · obtain ⟨⟨p, hp, _⟩, _⟩ := h
    rw [xpl_parsePreKeyWire_whisper] at hp; cases hp
  · exact h

theorem xpl_bobStart_head {b a : Participant} {kh : PQXDH.BobKeyHandles} {regIdxA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {n : Nat}
    {tr : ExecTrace} :
    ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx (n + 1)).vis tr).head?.map VisEntry.layout =
      some .preKeyRecv := by
  rw [xpl_vis_eq]
  simp only [xpl_ownVis, bobVis, List.cons_append, List.take_succ_cons, List.head?_cons,
    Option.map_some]

/-- `Move.bobStart` cannot match a whisper-tagged `recv` head event. -/
theorem xpl_bobStart_not_whisper {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {b a : Participant} {kh : PQXDH.BobKeyHandles} {regIdxA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat}
    {tr : ExecTrace} {body : HwBytes} {t : List MachineEvent}
    (hm : List.Forall₂ (EventMatchesEntry interpretation r S g)
      (.recv (wireWhisperTag :: body) :: t)
      ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).vis tr)) : False := by
  obtain ⟨v', l', hv', _, hvl⟩ := xpl_forall₂_cons_left hm
  cases shown with
  | zero =>
    have hmem : v' ∈ exposures tr ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx 0).next tr) := by
      have h0 := xpl_vis_eq (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx 0) tr
      simp only [xpl_ownVis, List.take_zero, List.nil_append] at h0
      rw [← h0, hvl]; exact List.mem_cons_self ..
    have h1 := xpl_exposures_kind hmem
    rw [← hv'.1] at h1
    cases h1
  | succ n =>
    have hlay :=
      xpl_bobStart_head (b := b) (a := a) (kh := kh) (regIdxA := regIdxA) (mh := mh)
        (pqIdx := pqIdx) (spqrMsgIdx := spqrMsgIdx) (n := n) (tr := tr)
    rw [hvl] at hlay
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hlay
    have h2 := hv'.2
    simp only [hlay, eventBytes] at h2
    exact xpl_opkMatches_whisper body _ h2

/-- Single-move inversion for a whisper `recv_wire` block. -/
theorem xplStep_recv {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {p : Participant} {blk : List MachineEvent} {m : Move} {tr : ExecTrace}
    (hs : m.isSetup = false) (ha : m.LogsSessionCompletion tr)
    (hm : List.Forall₂ (EventMatchesEntry interpretation r S g) blk (m.vis tr))
    (hshape : RecvBlockShape blk) (hact : ActorIn p m) : RecvStep p blk tr m := by
  obtain ⟨body, hb⟩ := hshape.head
  obtain ⟨t, rfl⟩ : ∃ t, blk = .recv (wireWhisperTag :: body) :: t := by
    cases blk with
    | nil => simp at hb
    | cons e t =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      exact ⟨t, by rw [hb]⟩
  obtain ⟨v, hv, hvk, _⟩ := xpl_head_entry hm rfl
  have hrk := xpl_recvHeadKind m tr hv hvk
  have hlen : (m.vis tr).length ≤ 3 := by
    rw [← xpl_forall₂_length hm]; exact hshape.len
  refine ⟨hact, ?_, ?_⟩
  · cases m
    case aliceStart => exact Or.inr (noSessionEffect_aliceStart_short ha (by omega))
    case bobStart => exact (xpl_bobStart_not_whisper hm).elim
    case decrypt => exact Or.inl trivial
    case decryptSkipped => exact Or.inl trivial
    case reject => exact Or.inl trivial
    all_goals exact False.elim hrk
  · rintro ⟨e, he, hek⟩
    obtain ⟨w, hw, hew⟩ := xpl_forall₂_mem_left hm e he
    have hwk : w.kind = .accept := by rw [xpl_kind_of_matches hew, hek]
    rcases xpl_accept_by m tr hw hwk hact with h | h
    · cases m <;> simp only [BobStartBy] at h
      exact (xpl_bobStart_not_whisper hm).elim
    · exact h

/-- Call-block inversion for a whisper `recv_wire` block. -/
theorem xplInv_recv {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost}
    {ms₀ δ : List Move} {acc blk : List MachineEvent} {p : Participant}
    (hB : XplBlock interpretation r S who g ms₀ δ acc blk)
    (hf : DeltaFaithful p (runTraceMoves r ms₀) δ) (hshape : RecvBlockShape blk) :
    OneMove (RecvStep p blk) (runTraceMoves r ms₀) δ := by
  obtain ⟨body, hb⟩ := hshape.head
  have hne : blk ≠ [] := by rintro rfl; simp at hb
  have hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    rw [hb, Option.mem_def, Option.some.injEq] at he
    subst he
    exact Or.inl rfl
  have htail : ∀ e ∈ blk.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he
    rcases hshape.tail e he with h | h <;> rw [h] <;> decide
  obtain ⟨pre, m, post, rfl, hpre, ⟨hs, ha, hm⟩, hpost⟩ := xpl_oneMove hB hhead hne htail
  exact ⟨pre, m, post, rfl, hpre,
    xplStep_recv hs ha hm hshape (actorIn_of_vis_ne_nil hf (vis_ne_nil_of_forall₂ hm hne)), hpost⟩

end Symbolic.Swarm.CREF
