/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.ReadFaithful
import Symbolic.Proofs.Swarm.CREF.Xpl.Steps

/-!
# Visible Read-Shape and `ReadCollision` Preservation Lemmas

Proves preservation of `ReadFaithful` under hidden moves (including `.attackerSend`), unpacks
`decVis` when a sent message is present, and shows `¬ ReadCollision` is preserved when appending a
block with no `.accept` event and no colliding-read moves.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)

theorem exposures_kind_ne_recv {tr tr' : ExecTrace} {v : VisEntry}
    (hv : v ∈ exposures tr tr') : v.kind ≠ .recv := by
  have hk := xpl_exposures_kind hv
  intro h; rw [h] at hk; cases hk

/-- Extending by a move with `m.vis (runTraceMoves r ms) = []` preserves `ReadFaithful`. -/
theorem readFaithful_snoc_hidden {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {m : Move} {acc : List MachineEvent}
    (hrf : ReadFaithful interpretation r S g ms acc)
    (hvis : m.vis (runTraceMoves r ms) = []) :
    ReadFaithful interpretation r S g (ms ++ [m]) acc := by
  intro ev hev hk
  rw [runVis_snoc, hvis, List.append_nil] at hev
  exact ReadOKWith.mono (recvRepresentations_append_subset interpretation r S g ms [m])
    (preKeyRepresentations_append_subset interpretation r S g ms [m]) (hrf ev hev hk)

theorem readFaithful_snoc_attackerSend {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {msg : DY.Bytes} {acc : List MachineEvent}
    (hrf : ReadFaithful interpretation r S g ms acc) :
    ReadFaithful interpretation r S g (ms ++ [.attackerSend msg]) acc :=
  readFaithful_snoc_hidden hrf (vis_attackerSend_nil msg _)

theorem decVis_cons_of_getMessageSentAt_some {tr tr' : ExecTrace} {stateIdx msgIdx : Nat}
    {wrapped : Bool} {t : DY.Bytes} (ht : tr.getMessageSentAt msgIdx = some t) :
    decVis tr tr' stateIdx msgIdx wrapped =
      ⟨.recv, [t], if wrapped then .preKeyInner (sessionBaseKeys tr stateIdx) else .whisper,
        none⟩ ::
        ((newRandoms tr tr').map (fun r => rngEntry r.1) ++
          ((receivedPlaintext tr tr').map fun m => (⟨.accept, [m], .single, none⟩ : VisEntry)).toList) := by
  simp [decVis, ht, List.cons_append]

theorem parsePreKeyWire_whisperTag_none (body : HwBytes) :
    parsePreKeyWire (wireWhisperTag :: body) = none := rfl

private theorem append_split_of_mem_not_mem {α : Type} :
    ∀ {acc blk τ₁ : List α} {e x : α} {τ₂ : List α},
      acc ++ blk = τ₁ ++ e :: τ₂ → x ∈ τ₂ → x ∉ blk → ∃ τ₂₀, acc = τ₁ ++ e :: τ₂₀ ∧ τ₂ = τ₂₀ ++ blk
  | [], _, _, _, _, _, h, hx, hnb => by
    rw [List.nil_append] at h; subst h
    exact absurd (List.mem_append_right _ (List.mem_cons_of_mem _ hx)) hnb
  | a :: acc', _, [], _, _, _, h, _, _ => by
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact ⟨acc', by rw [h.1]; rfl, h.2.symm⟩
  | a :: acc', _, b :: τ₁', _, _, _, h, hx, hnb => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨τ₂₀, hacc', hτ₂⟩ := append_split_of_mem_not_mem h.2 hx hnb
    exact ⟨τ₂₀, by rw [h.1, hacc']; rfl, hτ₂⟩

/-- Extending `(ms, acc)` by `(ms', blk)` where `blk` contains no `.accept` event and `ms'`
contains no `MoveReadsCollidingMsg`-capable move preserves `¬ ReadCollision`. -/
theorem not_readCollision_append_noAccept {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms ms' : List Move} {acc blk : List MachineEvent}
    (hnoRc : ¬ ReadCollision interpretation r S g ms acc)
    (hnoAcc : ∀ e ∈ blk, ∀ pt, e ≠ .accept pt)
    (hnoCol : ∀ m ∈ ms', ∀ pre e, ¬ MoveReadsCollidingMsg interpretation r S g pre e m) :
    ¬ ReadCollision interpretation r S g (ms ++ ms') (acc ++ blk) := by
  rintro ⟨i, τ₁, e, τ₂, m, hsplit, hmi, hF₁, ⟨pt, hpt⟩, hcol⟩
  by_cases hlt : i < ms.length
  · rw [List.getElem?_append_left hlt] at hmi
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at hF₁ hcol
    have hmem_τ₂ : MachineEvent.accept pt ∈ τ₂ := (List.mem_filter.mp (List.mem_of_head? hpt)).1
    obtain ⟨τ₂₀, hacc_eq, hτ₂_eq⟩ :=
      append_split_of_mem_not_mem hsplit hmem_τ₂ (fun hb => hnoAcc _ hb pt rfl)
    rw [hτ₂_eq, List.filter_append] at hpt
    have hpt₀ : (τ₂₀.filter fun ev => eventKind ev != .rng).head? = some (.accept pt) := by
      rcases hf : τ₂₀.filter (fun ev => eventKind ev != .rng) with _ | _
      · rw [hf, List.nil_append] at hpt
        exact absurd rfl (hnoAcc _ (List.mem_filter.mp (List.mem_of_head? hpt)).1 pt)
      · rw [hf, List.cons_append] at hpt; exact hpt
    exact hnoRc ⟨i, τ₁, e, τ₂₀, m, hacc_eq, hmi, hF₁, ⟨pt, hpt₀⟩, hcol⟩
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hmi
    exact hnoCol m (List.mem_of_getElem? hmi) _ e hcol

end Symbolic.Swarm.CREF
