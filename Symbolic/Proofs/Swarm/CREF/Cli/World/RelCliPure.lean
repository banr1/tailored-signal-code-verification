/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj

/-!
# `PureCRel` Projections, Monotonicity, and Record Erasure

Provides projection lemmas for `PureCRel`, move-list monotonicity for `PureCPrevRel` and
`PureCRecRelH`, and preservation of `PureCRel` invariants when erasing a single participant's
session record.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)

theorem pureCRecRelH_single {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {p : Participant} {b : HwBytes}
    (h : PureCRecRelH interp r S g ms p b) (hs : SingleSession b) :
    PureCRecRel interp r S g ms p b := by
  rcases h with h | ⟨rr, rfl, hne, hprev⟩
  · exact h
  · obtain ⟨rr', heq, hp'⟩ := hs
    have hn := TR.recordBytes_injective heq
    have hprev_eq : (TR.normPending rr).previous = (TR.normPending rr').previous :=
      congrArg RecordRec.previous hn
    simp only [TR.normPending, hp'] at hprev_eq
    exact absurd hprev_eq hne

theorem pureCPrevRel_append {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms ms' : List Move} {p : Participant} {b : HwBytes}
    (hstep : ∀ c, PureCRecRel interp r S g ms p c → PureCRecRel interp r S g ms' p c)
    (h : PureCPrevRel interp r S g ms p b) :
    PureCPrevRel interp r S g ms' p b := by
  obtain ⟨rr, rfl, hne, hc⟩ := h
  exact ⟨rr, rfl, hne, hstep _ hc⟩

theorem pureCRecRelH_mono {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms ms' : List Move} {p : Participant} {b : HwBytes}
    (hstep : ∀ c, PureCRecRel interp r S g ms p c → PureCRecRel interp r S g ms' p c)
    (h : PureCRecRelH interp r S g ms p b) :
    PureCRecRelH interp r S g ms' p b :=
  h.elim (fun h1 => .inl (hstep b h1)) (fun h2 => .inr (pureCPrevRel_append hstep h2))

section PureCRelProjections
variable {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
  {who : List Participant} {ok : Nat → Bool}
  {records : Participant → Option HwBytes} {sent accepted : List HwBytes}
  {acc : List MachineEvent} {g : Ghost} {ms : List Move}

theorem _root_.Symbolic.Swarm.CREF.PureCRel.recs (h : PureCRel interp r S who ok records sent accepted acc)
    (hc : Clean interp r S who ok g ms acc) :
    ∀ p b, records p = some b →
      (p = r.alice ∨ p = r.bob) ∧ b ≠ [] ∧ PureCRecRelH interp r S g ms p b :=
  (h.clean g ms hc).1.1

theorem _root_.Symbolic.Swarm.CREF.PureCRel.book (h : PureCRel interp r S who ok records sent accepted acc)
    (hc : Clean interp r S who ok g ms acc) :
    CBook interp r S g ms sent accepted acc :=
  (h.clean g ms hc).1.2.1

theorem _root_.Symbolic.Swarm.CREF.PureCRel.hist (h : PureCRel interp r S who ok records sent accepted acc)
    (hc : Clean interp r S who ok g ms acc) :
    CHist interp r S g ms :=
  (h.clean g ms hc).1.2.2.1

theorem _root_.Symbolic.Swarm.CREF.PureCRel.bks (h : PureCRel interp r S who ok records sent accepted acc)
    (hc : Clean interp r S who ok g ms acc) :
    BobRecordBaseKeyInSession interp r S g ms records :=
  (h.clean g ms hc).2

end PureCRelProjections

theorem pureBobKyberNone_empty (r : ProtocolSetup) : PureBobKyberNone r (fun _ => none) :=
  fun _ h => nomatch h

theorem pureBobKyberNone_erase {r : ProtocolSetup} {records : Participant → Option HwBytes}
    (p : Participant) (h : PureBobKyberNone r records) :
    PureBobKyberNone r (fun q => if q = p then none else records q) := by
  intro rr hrec
  by_cases hbp : r.bob = p
  · simp [hbp] at hrec
  · simp only [hbp, ↓reduceIte] at hrec
    exact h rr hrec

theorem bobRecordBaseKeyInAccepted_erase {r : ProtocolSetup} {records : Participant → Option HwBytes}
    {accepted : List HwBytes} (p : Participant)
    (h : BobRecordBaseKeyInAccepted r records accepted) :
    BobRecordBaseKeyInAccepted r (fun q => if q = p then none else records q) accepted := by
  intro rr hrec
  by_cases hbp : r.bob = p
  · simp [hbp] at hrec
  · simp only [hbp, ↓reduceIte] at hrec
    exact h rr hrec

theorem bobRecordBaseKeyInSession_erase {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {records : Participant → Option HwBytes} (p : Participant)
    (h : BobRecordBaseKeyInSession interp r S g ms records) :
    BobRecordBaseKeyInSession interp r S g ms (fun q => if q = p then none else records q) := by
  intro rr hrec
  by_cases hbp : r.bob = p
  · simp [hbp] at hrec
  · simp only [hbp, ↓reduceIte] at hrec
    exact h rr hrec

theorem pureCRelAt_eraseRecord {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes}
    {acc : List MachineEvent} (p : Participant)
    (h : PureCRelAt interp r S g ms records sent accepted acc) :
    PureCRelAt interp r S g ms (fun q => if q = p then none else records q) sent accepted acc := by
  refine ⟨fun q b hqb => ?_, h.2⟩
  by_cases hqp : q = p
  · simp [hqp] at hqb
  · simp only [hqp, ↓reduceIte] at hqb
    exact h.1 q b hqb

theorem pureCRel_eraseRecord {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes}
    {acc : List MachineEvent} (p : Participant)
    (h : PureCRel interp r S who ok records sent accepted acc) :
    PureCRel interp r S who ok (fun q => if q = p then none else records q) sent accepted acc where
  oooAll := fun q b hqb => by
    by_cases hqp : q = p
    · simp [hqp] at hqb
    · simp only [hqp, ↓reduceIte] at hqb; exact h.oooAll q b hqb
  sendsFit := h.sendsFit
  bka := bobRecordBaseKeyInAccepted_erase p h.bka
  bkn := pureBobKyberNone_erase p h.bkn
  clean := fun g ms hc =>
    ⟨pureCRelAt_eraseRecord p (h.clean g ms hc).1,
     bobRecordBaseKeyInSession_erase p (h.clean g ms hc).2⟩

end Symbolic.Swarm.CREF.CliPure
