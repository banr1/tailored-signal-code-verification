/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
public import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Extension and Prefix Lemmas for `ReadFaithful`

Characterizes `ReadFaithful` pointwise via `ReadOKWith` and proves that `ReadFaithful` extends
across appended blocks (`readFaithful_append`) and restricts to move-aligned prefixes
(`readFaithful_prefix`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)

/-- The read condition of one (event, entry) pair against representation sets `R`, `P` (the body
of `ReadFaithful`). -/
def ReadOKWith (R : HwBytes → Set DY.Bytes) (P : HwBytes → Set PreKeyRep)
    (e : MachineEvent) (v : VisEntry) : Prop :=
  match v.layout, v.terms, eventBytes e with
  | .whisper, [t], _ :: body => t ∈ R body
  | .preKeyInner _, [t], b => ∀ p, parsePreKeyWire b = some p → t ∈ R p.message
  | .preKeyRecv, ek :: ct :: msg :: _, b => ⟨ek, ct, msg⟩ ∈ P b
  | _, _, _ => True

theorem readFaithful_iff {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent} :
    ReadFaithful interpretation r S g ms τ₁ ↔
      ∀ ev ∈ τ₁.zip (runVis r ms), ev.2.kind = .recv →
        ReadOKWith (recvRepresentations interpretation r S g ms)
          (preKeyRepresentations interpretation r S g ms) ev.1 ev.2 := Iff.rfl

theorem ReadOKWith.mono {R R' : HwBytes → Set DY.Bytes} {P P' : HwBytes → Set PreKeyRep}
    (hR : ∀ b, R b ⊆ R' b) (hP : ∀ b, P b ⊆ P' b) {e : MachineEvent} {v : VisEntry}
    (h : ReadOKWith R P e v) : ReadOKWith R' P' e v := by
  revert h
  unfold ReadOKWith
  generalize v.layout = l
  generalize v.terms = ts
  generalize eventBytes e = b
  cases l <;> try exact id
  case whisper =>
    rcases ts with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> try exact id
    rcases b with _ | ⟨_, body⟩
    · exact id
    · exact fun h => hR _ h
  case preKeyInner =>
    rcases ts with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> try exact id
    exact fun h p hp => hR _ (h p hp)
  case preKeyRecv =>
    rcases ts with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg, _⟩⟩⟩ <;> try exact id
    exact fun h => hP _ h

theorem recvRepresentations_append_subset (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ms ms' : List Move) (b : HwBytes) :
    recvRepresentations interpretation r S g ms b ⊆
      recvRepresentations interpretation r S g (ms ++ ms') b := by
  rintro t ⟨hk, hrest⟩
  exact ⟨attackerKnows_append ms' hk, hrest⟩

theorem preKeyRepresentations_append_subset (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ms ms' : List Move) (b : HwBytes) :
    preKeyRepresentations interpretation r S g ms b ⊆
      preKeyRepresentations interpretation r S g (ms ++ ms') b := by
  rintro x ⟨h1, h2, h3, hrest⟩
  exact ⟨attackerKnows_append ms' h1, attackerKnows_append ms' h2, attackerKnows_append ms' h3,
    hrest⟩

/-- `ReadFaithful` extends by a block `(ms', blk)` whose `.recv` entries satisfy `ReadOKWith` at
`ms ++ ms'`. -/
theorem readFaithful_append {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms ms' : List Move} {acc blk : List MachineEvent}
    (hlen : acc.length = (runVis r ms).length)
    (h : ReadFaithful interpretation r S g ms acc)
    (hblk : ∀ ev ∈ blk.zip (runMoves ms' (runTraceMoves r ms)).2, ev.2.kind = .recv →
      ReadOKWith (recvRepresentations interpretation r S g (ms ++ ms'))
        (preKeyRepresentations interpretation r S g (ms ++ ms')) ev.1 ev.2) :
    ReadFaithful interpretation r S g (ms ++ ms') (acc ++ blk) := by
  intro ev hev hk
  rw [runVis_append, List.zip_append hlen] at hev
  rcases List.mem_append.mp hev with h1 | h2
  · exact ReadOKWith.mono (recvRepresentations_append_subset interpretation r S g ms ms')
      (preKeyRepresentations_append_subset interpretation r S g ms ms') (h ev h1 hk)
  · exact hblk ev h2 hk

private theorem mem_snd_of_mem_zip :
    ∀ {α β : Type} {xs : List α} {ys : List β} {p : α × β},
      p ∈ xs.zip ys → p.2 ∈ ys
  | _, _, [], _, _, h => by cases h
  | _, _, _ :: _, [], _, h => by cases h
  | _, _, _ :: _, _ :: _, _, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_snd_of_mem_zip h')

/-- A `.recv` entry visible at `ms₁` retains `ReadOKWith` when restricted from `ms₁ ++ ms₂` to `ms₁`. -/
theorem readOKWith_of_visKnown {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms₁ ms₂ : List Move} {e : MachineEvent} {v : VisEntry}
    (hk : v.kind = .recv) (hvis : VisKnown (runTraceMoves r ms₁) v)
    (hok : ReadOKWith (recvRepresentations interpretation r S g (ms₁ ++ ms₂))
      (preKeyRepresentations interpretation r S g (ms₁ ++ ms₂)) e v) :
    ReadOKWith (recvRepresentations interpretation r S g ms₁)
      (preKeyRepresentations interpretation r S g ms₁) e v := by
  have hknown : ∀ t ∈ v.terms, t.AttackerKnows (runTraceMoves r ms₁) :=
    hvis (Or.inr (Or.inl hk))
  revert hok hknown
  unfold ReadOKWith
  generalize v.layout = l
  generalize v.terms = ts
  generalize eventBytes e = b
  intro hok hknown
  cases l <;> try trivial
  case whisper =>
    rcases ts with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> try trivial
    rcases b with _ | ⟨_, body⟩
    · trivial
    · exact ⟨hknown t List.mem_cons_self, hok.2⟩
  case preKeyInner =>
    rcases ts with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> try trivial
    intro p hp
    exact ⟨hknown t List.mem_cons_self, (hok p hp).2⟩
  case preKeyRecv =>
    rcases ts with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg, rest⟩⟩⟩ <;> try trivial
    exact ⟨hknown ek List.mem_cons_self,
      hknown ct (List.mem_cons_of_mem _ List.mem_cons_self),
      hknown msg (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      hok.2.2.2⟩

/-- `ReadFaithful` restricts from `(ms₁ ++ ms₂, acc₁ ++ acc₂)` to `(ms₁, acc₁)` when
`acc₁.length = (runVis r ms₁).length`. -/
theorem readFaithful_prefix {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms₁ ms₂ : List Move} {acc₁ acc₂ : List MachineEvent}
    (hlen : acc₁.length = (runVis r ms₁).length)
    (h : ReadFaithful interpretation r S g (ms₁ ++ ms₂) (acc₁ ++ acc₂)) :
    ReadFaithful interpretation r S g ms₁ acc₁ := by
  intro ev hev hk
  have hev' : ev ∈ (acc₁ ++ acc₂).zip (runVis r (ms₁ ++ ms₂)) := by
    rw [runVis_append, List.zip_append hlen]
    exact List.mem_append_left _ hev
  have hv_mem : ev.2 ∈ runVis r ms₁ := mem_snd_of_mem_zip hev
  exact readOKWith_of_visKnown hk (runVis_known hv_mem) (h ev hev' hk)

end Symbolic.Swarm.CREF
