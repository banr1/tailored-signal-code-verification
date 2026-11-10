/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtNoCollision
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NoFullExplains
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvNoCollision
public import Symbolic.BugInjection.Proofs.Common.CoinsFresh
public import Symbolic.Proofs.SpecLemmas.SecurityBinaryFixed

/-!
# Spec-Half Disproof for `EvictedChainSkippedKeyCli`

Assembles `not_explains_full`, `not_nextEventCollides_send`, and `not_nextEventCollides_recv`
under `evictedCompFitsPinned` to prove `spec_half_pinned` and
`not_signalSessionSecure_of_implHalf` for `EvictedChainSkippedKeyCli`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.Top

open DY.Libsignal.Composed.Refinement (ProtocolSetup)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides)
open Symbolic.BugInjection (cliCompShape not_signalSessionSecure_of_witness)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
  (evictedI0_externContractsHoldCli evictedI0_hooksAgree)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtNoCollision
  (not_nextEventCollides_send)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NoFullExplains
  (not_explains_full)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvNoCollision
  (not_nextEventCollides_recv)
abbrev evictedCompFitsPinned : cliCompShape.Interp → ProtocolSetup → Prop :=
  Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0.evictedCompFitsPinned

theorem evictedCompFitsPinned_sub_fits :
    ∀ iw r, evictedCompFitsPinned iw r →
      Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli.fits iw r :=
  Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws.evictedCompFitsPinned_sub_fits

theorem evictedCompFitsPinned_satisfiable :
    ∃ iw r, evictedCompFitsPinned iw r :=
  Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws.evictedCompFitsPinned_satisfiable

theorem spec_half_pinned :
    cliCompShape.SpecHalf evictedCompFitsPinned
      Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli.trace := by
  intro ⟨interp, W⟩ r hfit
  have hbase := hfit.1
  obtain ⟨⟨hc, hi_eq, _, _, _, _⟩, _, _⟩ := hfit
  subst hi_eq
  refine ⟨hc.1, ?_⟩
  intro S _ hor
  have hfit0 : evictedCompFitsPinned (evictedI0, evictedHooks0) r :=
    ⟨hbase, evictedI0_externContractsHoldCli, evictedI0_hooksAgree⟩
  rcases hor with ⟨g, ss, vis, hex⟩ | ⟨evs₁, ev, evs₂, g, ss, vis, hsplit, hex, hcol⟩
  · exact not_explains_full r S g ss vis hfit0 hex
  · cases hcmd : ev.cmd with
    | init a b =>
      unfold NextEventCollides at hcol
      rw [hcmd] at hcol
      exact hcol
    | send peer =>
      exact not_nextEventCollides_send r S g ss vis evs₁ ev evs₂ hfit0 hsplit hex ⟨peer, hcmd⟩ hcol
    | recv peer =>
      exact not_nextEventCollides_recv r S g ss vis evs₁ ev evs₂ hfit0
        (fun g' ss' vis' => not_explains_full r S g' ss' vis' hfit0) hsplit hex ⟨peer, hcmd⟩ hcol

theorem not_signalSessionSecure_of_implHalf {bytes : List (BitVec 8)}
    (hi : ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      cliCompShape.ImplHalf evictedCompFitsPinned elf
        Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli.trace) :
    ¬ DY.Libsignal.Composed.Security.SignalSessionSecure bytes :=
  not_signalSessionSecure_of_witness spec_half_pinned hi
    (fun iw r hf => Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_unpinned_evictedChainSkippedKeyCli iw r ⟨hf.1.1, hf.2.1, hf.2.2⟩)

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.Top
