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
# Pre-Key Receive-Block Inversion

Proves `xplStep_rpk` and `xplInv_rpk`: under a faithful explanation, a `recv_prekey` block (`recv b`
followed by at most a ratchet draw and an `accept`) is explained by one visible move of the caller
`p` surrounded by `InvisibleNoEffect` moves, and if the block accepts then that move satisfies
`BobStartBy p` or `DecryptBy p`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)

/-- Event shape of a `recv_prekey` call: `recv b` followed by `rng` or `accept` events with total
length at most `3`. -/
structure RpkBlockShape (blk : List MachineEvent) : Prop where
  head : ∃ b, blk.head? = some (.recv b)
  tail : ∀ e ∈ blk.tail, eventKind e = .rng ∨ eventKind e = .accept
  len : blk.length ≤ 3

/-- Step conclusion for a `recv_prekey` block: a move acting for `p` (or nobody) that either
satisfies `RpkKind` or has `NoSessionEffect`, and satisfies `BobStartBy p ∨ DecryptBy p` when `blk`
accepts. -/
def RpkStep (p : Participant) (blk : List MachineEvent) (tr : ExecTrace) (m : Move) : Prop :=
  ActorIn p m ∧ (RpkKind m ∨ NoSessionEffect tr m) ∧
    ((∃ e ∈ blk, eventKind e = .accept) → BobStartBy p m ∨ DecryptBy p m)

/-- Single-move inversion for a `recv_prekey` block. -/
theorem xplStep_rpk {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {p : Participant} {blk : List MachineEvent} {m : Move} {tr : ExecTrace}
    (hs : m.isSetup = false) (ha : m.LogsSessionCompletion tr)
    (hm : List.Forall₂ (EventMatchesEntry interpretation r S g) blk (m.vis tr))
    (hshape : RpkBlockShape blk) (hact : ActorIn p m) : RpkStep p blk tr m := by
  obtain ⟨b, hb⟩ := hshape.head
  obtain ⟨v, hv, hvk, _⟩ := xpl_head_entry hm hb
  have hrk := xpl_recvHeadKind m tr hv hvk
  have hlen : (m.vis tr).length ≤ 3 := by
    rw [← xpl_forall₂_length hm]; exact hshape.len
  refine ⟨hact, ?_, ?_⟩
  · cases m
    case aliceStart => exact Or.inr (noSessionEffect_aliceStart_short ha (by omega))
    case bobStart => exact Or.inl trivial
    case decrypt => exact Or.inl trivial
    case decryptSkipped => exact Or.inl trivial
    case reject => exact Or.inl trivial
    all_goals exact False.elim hrk
  · rintro ⟨e, he, hek⟩
    obtain ⟨w, hw, hew⟩ := xpl_forall₂_mem_left hm e he
    have hwk : w.kind = .accept := by rw [xpl_kind_of_matches hew, hek]
    exact xpl_accept_by m tr hw hwk hact

/-- Call-block inversion for a `recv_prekey` block. -/
theorem xplInv_rpk {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost}
    {ms₀ δ : List Move} {acc blk : List MachineEvent} {p : Participant}
    (hB : XplBlock interpretation r S who g ms₀ δ acc blk)
    (hf : DeltaFaithful p (runTraceMoves r ms₀) δ) (hshape : RpkBlockShape blk) :
    OneMove (RpkStep p blk) (runTraceMoves r ms₀) δ := by
  obtain ⟨b, hb⟩ := hshape.head
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
    xplStep_rpk hs ha hm hshape (actorIn_of_vis_ne_nil hf (vis_ne_nil_of_forall₂ hm hne)), hpost⟩

end Symbolic.Swarm.CREF
