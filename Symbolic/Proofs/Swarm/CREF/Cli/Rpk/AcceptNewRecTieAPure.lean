/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RoleSnapshots
public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR
import Symbolic.Proofs.Swarm.CREF.TROpen
import VCVio.Prelude.Core

/-!
# Snapshot, Block-Visibility, and Receive-Chain Pinning Lemmas

Proves uniqueness of current snapshots for a participant (`a2b_currentSnapshot_unique`,
`a2b_currentSnapshot_unique_of_role`), visibility alignment across `InvisibleNoEffect` framing
(`a2b_block_vis`), and receive-chain uniqueness under `StateRel` (`a2b_recvChain_eq_of_gamma`).
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR hiding runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain)
open DY.Libsignal.TripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR

private theorem a2b_not_lt_of_current {tr : ExecTrace} {p : Participant} {a b : Nat}
    {sa sb : TRState}
    (ha : (tr.at? a : Option (PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState TRState))) = some ⟨⟨p, sa⟩⟩)
    (hb : (tr.at? b : Option (PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState TRState))) = some ⟨⟨p, sb⟩⟩)
    (hca : isCurrentSnapshot tr a = true) (hinit : sa.initiator = sb.initiator) : ¬ a < b := by
  intro hlt
  have hblt : b < tr.length := by
    by_contra hge
    have hnone : (tr.at? b : Option (PersistentGlobalState.State.ExecEntryT
        (PersistentLocalState.LocalState TRState))) = none := by
      simp only [Trace.at?, hge, ↓reduceDIte]
    rw [hnone] at hb; cases hb
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hca
  rw [ha] at hca
  have hmem : b ∈ List.range' (a + 1) (tr.length - (a + 1)) :=
    List.mem_range'_1.mpr ⟨by omega, by omega⟩
  have hall := List.all_eq_true.mp hca b hmem
  rw [hb] at hall
  simp [hinit] at hall

/-- Two current snapshots of `p` with the same `initiator` flag occur at the same trace index. -/
theorem a2b_currentSnapshot_unique {tr : ExecTrace} {p : Participant} {i j : Nat}
    {st₁ st₂ : TRState}
    (h₁ : ((PersistentLocalState.getLocalState p i : Traceful TRState).run tr).1 = some st₁)
    (h₂ : ((PersistentLocalState.getLocalState p j : Traceful TRState).run tr).1 = some st₂)
    (hc₁ : isCurrentSnapshot tr i = true) (hc₂ : isCurrentSnapshot tr j = true)
    (hinit : st₁.initiator = st₂.initiator) : i = j := by
  have ha₁ := FreshSigma.at?_eq_some_of_getLocalState_some h₁
  have ha₂ := FreshSigma.at?_eq_some_of_getLocalState_some h₂
  rcases lt_trichotomy i j with h | h | h
  · exact absurd h (a2b_not_lt_of_current ha₁ ha₂ hc₁ hinit)
  · exact h
  · exact absurd h (a2b_not_lt_of_current ha₂ ha₁ hc₂ hinit.symm)

/-- Under `RoleSnapshots`, two current snapshots of `p` occur at the same trace index. -/
theorem a2b_currentSnapshot_unique_of_role {r : ProtocolSetup} {tr : ExecTrace} {p : Participant}
    {i j : Nat} {st₁ st₂ : TRState} (hrole : RoleSnapshots r tr)
    (h₁ : ((PersistentLocalState.getLocalState p i : Traceful TRState).run tr).1 = some st₁)
    (h₂ : ((PersistentLocalState.getLocalState p j : Traceful TRState).run tr).1 = some st₂)
    (hc₁ : isCurrentSnapshot tr i = true) (hc₂ : isCurrentSnapshot tr j = true) : i = j :=
  a2b_currentSnapshot_unique h₁ h₂ hc₁ hc₂
    ((hrole p st₁ i (FreshSigma.at?_eq_some_of_getLocalState_some h₁)).trans
      (hrole p st₂ j (FreshSigma.at?_eq_some_of_getLocalState_some h₂)).symm)

theorem a2b_invisible_vis_nil :
    ∀ (δ : List Move) (tr : ExecTrace), MovesFrom InvisibleNoEffect tr δ → (runMoves δ tr).2 = []
  | [], _, _ => rfl
  | m :: δ, tr, ⟨⟨hv, _⟩, hδ⟩ => by
    rw [runMoves_cons_snd, hv, a2b_invisible_vis_nil δ (m.next tr) hδ,
      List.nil_append]

/-- A move `m` framed by `InvisibleNoEffect` prefixes and suffixes accounts for the entire
visible event list of an `XplBlock`. -/
theorem a2b_block_vis {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost}
    {ms₀ pre post : List Move} {m : Move} {acc blk : List MachineEvent}
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post) :
    List.Forall₂ (EventMatchesEntry interpretation r S g) blk (m.vis (runTraceMoves r (ms₀ ++ pre))) := by
  have hm := hB.matched
  rw [b5_runMoves_append_snd, a2b_invisible_vis_nil pre _ hpre, List.nil_append,
    runMoves_cons_snd, a2b_invisible_vis_nil post _ hpost, List.append_nil]
    at hm
  rwa [TR.runTrace_append]

/-- Under `StateRel` with duplicate-free receiver ratchet keys in `rec`, two chains in `st.recv`
whose ratchet keys concretize to the same bytes are equal. -/
theorem a2b_recvChain_eq_of_gamma {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {rec : RecordRec}
    (hrel : StateRel interpretation S g st rec)
    (hnd : (rec.current.receiverChains.map
      ChainRec.senderRatchetKey).Nodup)
    {c₁ c₂ : RecvChain} (h₁ : c₁ ∈ st.recv) (h₂ : c₂ ∈ st.recv)
    (hγ : gamma interpretation S g c₁.ratchetKey = gamma interpretation S g c₂.ratchetKey) :
    c₁ = c₂ :=
  List.inj_on_of_nodup_map (RecvHistStep.recvRk_nodup_of_stateRel hrel hnd) h₁ h₂ hγ

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
