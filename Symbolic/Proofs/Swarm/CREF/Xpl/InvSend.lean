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

/-!
# Send-Block Inversion

Proves `xplStep_send` and `xplInv_send`: under a faithful explanation, a `send_wire` block (`pt`
followed by `rng` or `send` events) is explained by one visible encrypt-family move of the caller
`p` surrounded by `InvisibleNoEffect` moves, and if the block emits a `send` event then that move
is `Move.encrypt`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)

/-- Event shape of a `send_wire` call: `pt b` followed only by `rng` or `send` events. -/
structure SendBlockShape (blk : List MachineEvent) : Prop where
  head : ∃ b, blk.head? = some (.pt b)
  tail : ∀ e ∈ blk.tail, eventKind e = .rng ∨ eventKind e = .send

/-- Encrypt-family move acting for `p`. -/
def SendBy (p : Participant) : Move → Prop
  | .encrypt me .. | .encryptAbort me _ | .encryptFail me .. => me = p
  | _ => False

/-- Step conclusion for a `send_wire` block: an encrypt-family move by `p` that is `Move.encrypt`
whenever `blk` contains a `send` event. -/
def SendStep (p : Participant) (blk : List MachineEvent) (_tr : ExecTrace) (m : Move) : Prop :=
  SendBy p m ∧ ((∃ e ∈ blk, eventKind e = .send) → ∃ me s c q w, m = .encrypt me s c q w)

/-- Single-move inversion for a `send_wire` block. -/
theorem xplStep_send {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {p : Participant} {blk : List MachineEvent} {m : Move} {tr : ExecTrace}
    (hs : m.isSetup = false)
    (hm : List.Forall₂ (EventMatchesEntry interpretation r S g) blk (m.vis tr))
    (hshape : SendBlockShape blk) (hact : ActorIn p m) : SendStep p blk tr m := by
  obtain ⟨b, hb⟩ := hshape.head
  obtain ⟨t, rfl⟩ : ∃ t, blk = .pt b :: t := by
    cases blk with
    | nil => simp at hb
    | cons e t =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      exact ⟨t, by rw [hb]⟩
  have hsk : SendKind m := by
    obtain ⟨v, l, hv, _, hvl⟩ := xpl_forall₂_cons_left hm
    have hk := xpl_kind_of_matches hv
    have hmem : v ∈ m.vis tr := by rw [hvl]; exact List.mem_cons_self ..
    rcases xpl_vis_kind m tr hmem with h | ⟨h, _⟩ | ⟨_, h⟩
    · rw [hk] at h; cases h
    · exact h
    · rw [hk] at h; rcases h with h | h | h <;> cases h
  refine ⟨?_, ?_⟩
  · cases m <;> simp only [SendKind] at hsk <;>
      rcases hact with h | h <;> simp only [moveActor, Option.some.injEq, reduceCtorEq] at h <;>
      simp only [SendBy] <;> exact h
  · rintro ⟨e, he, hk⟩
    obtain ⟨v, hv, hev⟩ := xpl_forall₂_mem_left hm e he
    have hvk := xpl_kind_of_matches hev
    rw [hk] at hvk
    rcases xpl_vis_kind m tr hv with h | ⟨_, h⟩ | ⟨_, h⟩
    · rw [hvk] at h; cases h
    · rcases h with h | h | ⟨_, h⟩
      · rw [hvk] at h; cases h
      · rw [hvk] at h; cases h
      · exact h
    · rw [hvk] at h; rcases h with h | h | h <;> cases h

/-- Call-block inversion for a `send_wire` block. -/
theorem xplInv_send {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost}
    {ms₀ δ : List Move} {acc blk : List MachineEvent} {p : Participant}
    (hB : XplBlock interpretation r S who g ms₀ δ acc blk)
    (hf : DeltaFaithful p (runTraceMoves r ms₀) δ) (hshape : SendBlockShape blk) :
    OneMove (SendStep p blk) (runTraceMoves r ms₀) δ := by
  obtain ⟨b, hb⟩ := hshape.head
  have hne : blk ≠ [] := by rintro rfl; simp at hb
  have hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    rw [hb, Option.mem_def, Option.some.injEq] at he
    subst he
    exact Or.inr rfl
  have htail : ∀ e ∈ blk.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he
    rcases hshape.tail e he with h | h <;> rw [h] <;> decide
  obtain ⟨pre, m, post, rfl, hpre, ⟨hs, _, hm⟩, hpost⟩ := xpl_oneMove hB hhead hne htail
  exact ⟨pre, m, post, rfl, hpre,
    xplStep_send hs hm hshape (actorIn_of_vis_ne_nil hf (vis_ne_nil_of_forall₂ hm hne)), hpost⟩

end Symbolic.Swarm.CREF
