/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBad
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
public import Symbolic.Proofs.Swarm.CREF.Cli.World.XplTransferPure
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep

/-!
# Current-Read Premise, Quiet Prefix/Suffix Helpers, and Snapshot/Chain Uniqueness

Defines `RcvCurrentRead` for `session_recv_wire` decrypt moves and proves quiet-extension helpers
for invisible no-effect prefixes and suffixes, block-visibility inversion, current-snapshot
uniqueness, and receiver-chain uniqueness under `StateRel`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv

open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)

/-- Current-snapshot and `recvRepresentations` premise for a decrypt move `m` at `ms`. -/
def RcvCurrentRead (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (body : HwBytes) : Move → Prop
  | m@(.decrypt _ stateIdx ..) => TripleRatchet.isCurrentSnapshot (runTraceMoves r ms) stateIdx = true ∧
      ∀ t, rcvMoveTerm (runTraceMoves r ms) m = some t → t ∈ recvRepresentations interpretation r S g ms body
  | m@(.decryptSkipped _ stateIdx ..) =>
      TripleRatchet.isCurrentSnapshot (runTraceMoves r ms) stateIdx = true ∧
      ∀ t, rcvMoveTerm (runTraceMoves r ms) m = some t → t ∈ recvRepresentations interpretation r S g ms body
  | _ => True

theorem a2b_quietPre {r : ProtocolSetup} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre) :
    PureXplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
  rw [TR.runTrace_append]
  exact PureXplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)

theorem a2b_quietPost {r : ProtocolSetup} {ms₀ pre post : List Move} {m : Move}
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post) :
    PureXplQuiet.QuietExt (runTraceMoves r (ms₀ ++ pre ++ [m]))
      (runTraceMoves r (ms₀ ++ (pre ++ m :: post))) := by
  rw [show ms₀ ++ (pre ++ m :: post) = ms₀ ++ pre ++ [m] ++ post by simp,
    TR.runTrace_append (ms₁ := ms₀ ++ pre ++ [m]), TR.runTrace_snoc, TR.runTrace_append]
  exact PureXplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost)

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
abbrev StEntry := Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.StEntry
abbrev TREntry := Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.TREntry

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR

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

/-- Two current snapshots of `p` with the same role have the same trace index. -/
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

/-- The active move `m` between invisible no-effect `pre` and `post` matches the whole block `blk`. -/
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

/-- Under `StateRel` with duplicate-free receiver ratchet keys, two receiver chains with the same
concretized ratchet key are equal. -/
theorem a2b_recvChain_eq_of_gamma {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {rec : RecordRec}
    (hrel : StateRel interpretation S g st rec)
    (hnd : (rec.current.receiverChains.map
      ChainRec.senderRatchetKey).Nodup)
    {c₁ c₂ : RecvChain} (h₁ : c₁ ∈ st.recv) (h₂ : c₂ ∈ st.recv)
    (hγ : gamma interpretation S g c₁.ratchetKey = gamma interpretation S g c₂.ratchetKey) :
    c₁ = c₂ :=
  List.inj_on_of_nodup_map (RecvHistStep.recvRk_nodup_of_stateRel hrel hnd) h₁ h₂ hγ

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
