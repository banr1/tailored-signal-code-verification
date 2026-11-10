/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.BI.RAB.Defs
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import Symbolic.Proofs.Swarm.CREF.CBadG2.Stamps
import Symbolic.Proofs.Swarm.CREF.CBadReadableBridge
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyPromReject
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperCodec
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperEval
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecPendingAPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.RcvByPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SkippedProvBPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotG2BranchesPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotG2ProvBPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotG2Pure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SpinePeelPure
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedProvTRHelpers
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L02GoodExit0Cut
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L04BridgeBQuietFail
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L05BridgeCCaseA
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L06BridgeCCaseB
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L09SlotRecvWCli
import Symbolic.Proofs.Swarm.Leaves.IC12_Stage1MatchedPrefixPure
import Symbolic.Proofs.Swarm.TRREF.HooksOKXTRPure
import Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey
import Symbolic.Proofs.Swarm.UA.BI.G.RecvStep
import Symbolic.Proofs.Swarm.UA.BI.RAB.Base
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Whisper Receive Slot Refinement under Break and Invert Events

Proves `uab_slot_recvw_of : XlateInvSpecB -> XlateExcWSpecB -> UASlotRecvWSpecB`, advancing
`PqTurnSim1A` and `UAInvB` across whisper-tagged `recv` CLI calls by combining `MatchesEvents` cut
uniqueness across environment steps with raw decrypt witness lifting.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.G.SlotRecvW

open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
cref_hide_foreign_instances

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent StateAndMessage)
open _root_.DY.Libsignal.Composed (reachability)
open _root_.DY.Libsignal.Composed.Refinement (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost Step Move VisEntry
  EnvMatches invertEntry
  Explains MatchesEvents MatchesEventsAt BundlePreKeyIds activeBundleIds
  RunRejected Clean callStarts callCount runSteps runTrace runTraceMoves runVis
  setupTrace stepView runWrapped recvRepresentations recvRepresentationsOn RecvCollision
  RecvCollisionOn ReselectCollision ReselectCollisionOn honestSaltsOf honestKeysOf prefixTerms
  principalTerms plaintextTerms MemoCollisionOn whisperTrials PqFromHonest preKeyWire parsePreKeyWire)
open _root_.DY.Libsignal.Composed.Refinement.Cli (CliTurn CliCall DirectorySnapshot InputsFor FilesBounded
  BobCallAllowed StdinBounded PreKeyNoMatch ValidCall coinsLen scrub PqModelRel ModelAgree
  ExternContractsHoldCli runEventOf runInput peerOf cliEntryEvents cliExitEvents ReadCollisionCli
  ModelAcceptsTermAfterAttackerSends SignalMsgAcceptedOnlyViaCollision CollisionAfterExplainedPrefix
  NextEventCollides)
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3 (PqTurnSim1A pqTurnSim1A_caller_after
  toCliCallNone inputsFor_toCliCallNone clean_dirs_caller_eq)
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification.E2E (PEParams wireWhisper encodeRecordUnderExtras)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession (Inputs pqRecvInputs pqRecvWhisperModel pqxdhExpectedOutcome partyAddress
  filesOf encodeDir)
open Symbolic.Swarm.COMPOSED.CompTrace (NetEntry NetE at?_append_cases proj_inj_eq)
open Symbolic.Swarm.CREF (compSemOf compSemOf_ready SemReady CleanBy pureTrSlots)
open Symbolic.Swarm.Leaves.IC12Stage1MP (matchedPrefix_callCount_eq)
open Symbolic.Swarm.CREF.Cli (interpOfParams externContractsHoldCli_interpOfParams
  modelHookBridge_interpOfParams ModelHookBridge caller_pqPartyInv_of_allowed wfPq_of_pqPartyInv
  records_of_pqPartyInv keyToBytes32_bytesToKey32 peerOf_eq_addrE_other
  inputsEquiv_pqRecvInputs exited_eq_pqObserve_iff scrub_filesOf_pqInputs_reject
  scrub_filesOf_pqInputs_accept pqDirInv_after_reject pqDirInv_after_accept_same
  pqPartyInv_of_pqRecvWhisperModel PqPartyInv)
open Symbolic.Swarm.CREF.CliPure (leakRecords_party_eq_of_cliNextCall
  leakRecords_eq_records_of_bobOff_false pureCRecRelH_single coinSplit_callStarts_length_eq)
open Symbolic.Swarm.CREF.TR (PureTRRecordStateInv sentBodies)
open Symbolic.Swarm.CREF.TR.G1 (G1cAttackerBuiltSeedExcl' InstallWitnessTR)
open Symbolic.Swarm.CREF.TR.RecvDecStep (installWitnessTR_of_reachable)
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt (RecvAtFacts NoRatchetPkDispatchAtSt)
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure (pureTrSlotsPend
  trRecordStateInv_pend_of_aliceInitPending)
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure (PureRcvAcceptCall
  rcv_pending_callEnd_of_pureAccept RecvWireRawWitness SkippedPkDispatchAtKPure
  recvWireStepWitness_of_skipped_branchK recvWireStepWitness_of_noRatchet_branch
  recvWireStepWitness_of_ratchetDH_branch)
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure (evalRecvWireWithCoinsW_branch_cases)
open Symbolic.Swarm.Coinsplit.Lift (CliLiveAtCli explainsCli_toClean)
open Symbolic.Proofs.Swarm.UA.Defs (SchedFits callsOf flatEvents)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Defs (UAInvB UASlotPostB UASlotRecvWSpecB XlateInvSpecB
  XlateExcWSpecB)
open Symbolic.Proofs.Swarm.UA.Base (callsOf_append schedFits_of_append
  runSteps_append runTrace_append ghostWF_of_append modelRunWF_of_append)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Base (collisionAtCli_append readCollisionCli_append)

section Sec1

attribute [local instance 2000]
  _root_.DY.Libsignal.Composed.instBytesFunctor_symbolic _root_.DY.Libsignal.Composed.instBytesLength_symbolic
  _root_.DY.Libsignal.Composed.instAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instExecTraceTypes_symbolic
  _root_.DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instHasExecBytes
  _root_.DY.Libsignal.Composed.instHasExecEntryT _root_.DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  _root_.DY.Libsignal.Composed.instHasExecTrace _root_.DY.Libsignal.Composed.instHasSubF
  _root_.DY.Libsignal.Composed.instHasSubFAttackerKnowledge _root_.DY.Libsignal.Composed.instHasSubFLength

/-! ## `MatchesEvents` Cut Uniqueness and Accepting Receive Collisions -/

private theorem matchesEvents_restrict_tail {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (more : List CliEvent) (evs : List CliEvent)
    {tr : ExecTrace} {ss : List Step} {vis : List VisEntry}
    (h : MatchesEvents interp r S g tr ss (evs ++ more) vis) :
    ∃ ss₁ ss₂ vis₁ vis₂, ss = ss₁ ++ ss₂ ∧ vis = vis₁ ++ vis₂ ∧
      MatchesEvents interp r S g tr ss₁ evs vis₁ ∧
      MatchesEventsAt interp r S g (activeBundleIds evs) (runSteps ss₁ tr) ss₂ more vis₂ :=
  Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey.matchesEvents_split more evs h

private def envVis (s : Step) (tr : ExecTrace) : EnvEvent → List VisEntry
  | .leak _ _ => stepView s tr false
  | .breakDH | .breakKEM => []
  | .invertDH _ _ => invertEntry s tr .leakRecord
  | .invertKEM _ _ => invertEntry s tr (.leakPq true)
  | .registerCorrupt _ _ => []

private theorem envMatches_vis {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {s : Step} {ev : EnvEvent} {v : List VisEntry}
    (hem : EnvMatches interp r S g tr s ev v) : v = envVis s tr ev := by
  cases ev with
  | leak _ _ => exact hem.2.2.2.1
  | breakDH => exact hem.2
  | breakKEM => exact hem.2
  | invertDH _ _ => obtain ⟨_, _, _, _, hv, _⟩ := hem; exact hv
  | invertKEM _ _ => obtain ⟨_, _, _, _, hv, _⟩ := hem; exact hv
  | registerCorrupt _ _ => exact hem.elim

private theorem envMatches_cls {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {s : Step} {ev : EnvEvent} {v : List VisEntry}
    (hem : EnvMatches interp r S g tr s ev v) : s.cls = .env := by
  cases ev with
  | leak _ _ => exact hem.1
  | breakDH => rw [hem.1]; rfl
  | breakKEM => rw [hem.1]; rfl
  | invertDH _ _ => obtain ⟨_, rfl, _⟩ := hem; rfl
  | invertKEM _ _ => obtain ⟨_, rfl, _⟩ := hem; rfl
  | registerCorrupt _ _ => exact hem.elim

private def isActiveEvent : CliEvent → Bool
  | .env _ => true
  | .run ev => match ev.exit with | some (0, _) => true | _ => false

private def isNonInvisible (s : Step) : Bool := s.cls != .invisible

private theorem filter_nonInvisible_eq_nil {ss : List Step}
    (hinv : ∀ x ∈ ss, x.cls = .invisible) : ss.filter isNonInvisible = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx; unfold isNonInvisible; rw [hinv x hx]; decide

private theorem matchesEvents_filter_nonInvisible_length {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsAt interp r S g initIds tr ss evs vis) :
    (ss.filter isNonInvisible).length = (evs.filter isActiveEvent).length := by
  induction hme with
  | nil hinv => rw [filter_nonInvisible_eq_nil hinv]; rfl
  | @run0 _ _ pre _ ev _ _ hpre hrej _ ih =>
    have hact : isActiveEvent (.run ev) = false := by
      unfold isActiveEvent
      cases hex : ev.exit with
      | none => simp [hex]
      | some p =>
        rcases p with ⟨code, out⟩
        cases code with
        | zero => exact absurd hex (hrej out)
        | succ _ => simp [hex]
    rw [List.filter_append, filter_nonInvisible_eq_nil hpre, List.nil_append,
      List.filter_cons_of_neg (by simp [hact]), ih]
  | @run1 _ _ pre s _ ev _ _ _ hpre hrm _ ih =>
    obtain ⟨out, hex⟩ := hrm.2.2.2.2.2.1
    have hact : isActiveEvent (.run ev) = true := by simp [isActiveEvent, hex]
    have hs : isNonInvisible s = true := by unfold isNonInvisible; rw [hrm.1]; decide
    rw [List.filter_append, filter_nonInvisible_eq_nil hpre, List.nil_append,
      List.filter_cons_of_pos hs, List.filter_cons_of_pos hact, List.length_cons,
      List.length_cons, ih]
  | @env _ _ pre s _ ev _ _ _ hpre hem _ ih =>
    have hs : isNonInvisible s = true := by
      unfold isNonInvisible; rw [envMatches_cls hem]; decide
    rw [List.filter_append, filter_nonInvisible_eq_nil hpre, List.nil_append,
      List.filter_cons_of_pos hs, List.filter_cons_of_pos rfl, List.length_cons,
      List.length_cons, ih]

private theorem matchesEvents_append_invisible {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss extra : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsAt interp r S g initIds tr ss evs vis)
    (hextra : ∀ x ∈ extra, x.cls = .invisible) :
    MatchesEventsAt interp r S g initIds tr (ss ++ extra) evs vis := by
  induction hme with
  | @nil _ _ _ hinv =>
    exact .nil (fun x hx => (List.mem_append.mp hx).elim (hinv x) (hextra x))
  | @run0 _ _ _ _ _ _ _ hpre hrej _ ih => rw [List.append_assoc]; exact .run0 hpre hrej ih
  | @run1 _ _ _ _ _ _ _ _ _ hpre hrm _ ih =>
    rw [List.append_assoc, List.cons_append]; exact .run1 hpre hrm ih
  | @env _ _ _ _ _ _ _ _ _ hpre hem _ ih =>
    rw [List.append_assoc, List.cons_append]; exact .env hpre hem ih

private theorem matchesEvents_cons_invisible {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {x : Step} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hx : x.cls = .invisible) (hme : MatchesEventsAt interp r S g initIds tr (x :: ss) evs vis) :
    MatchesEventsAt interp r S g initIds (x.next tr) ss evs vis := by
  generalize hxs : x :: ss = xs at hme
  induction hme generalizing x ss with
  | nil hinv => subst hxs; exact .nil (fun y hy => hinv y (List.mem_cons_of_mem x hy))
  | @run0 _ _ pre _ _ _ _ hpre hrej hrest ih =>
    cases pre with
    | nil =>
      simp only [List.nil_append] at hxs
      dsimp only [runSteps] at ih
      exact .run0 (pre := []) (fun _ h => nomatch h) hrej (ih hx hxs)
    | cons p₀ _ =>
      simp only [List.cons_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, rfl⟩
      exact .run0 (fun y hy => hpre y (List.mem_cons_of_mem _ hy)) hrej hrest
  | @run1 _ _ pre _ _ _ _ _ _ hpre hrm hrest _ =>
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, _⟩
      rw [hrm.1] at hx; cases hx
    | cons p₀ _ =>
      simp only [List.cons_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, rfl⟩
      exact .run1 (fun y hy => hpre y (List.mem_cons_of_mem _ hy)) hrm hrest
  | @env _ _ pre _ _ ev _ _ _ hpre hem hrest _ =>
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, _⟩
      rw [envMatches_cls hem] at hx; cases hx
    | cons p₀ _ =>
      simp only [List.cons_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, rfl⟩
      exact .env (fun y hy => hpre y (List.mem_cons_of_mem _ hy)) hem hrest

private theorem matchesEvents_vis_nonInvisible {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {x : Step} {ss : List Step}
    {ev₀ : CliEvent} {evs' : List CliEvent} {vis : List VisEntry}
    (hx : x.cls ≠ .invisible) (hme : MatchesEventsAt interp r S g initIds tr (x :: ss) (ev₀ :: evs') vis) :
    (∃ ev, ev₀ = .run ev ∧ RunRejected ev ∧ MatchesEventsAt interp r S g initIds tr (x :: ss) evs' vis) ∨
    (∃ ev vs initIds', ev₀ = .run ev ∧ (∃ out, ev.exit = some (0, out)) ∧
      vis = stepView x tr (runWrapped ev) ++ vs ∧ MatchesEventsAt interp r S g initIds' (x.next tr) ss evs' vs) ∨
    (∃ ev vs, ev₀ = .env ev ∧ vis = envVis x tr ev ++ vs ∧
      MatchesEventsAt interp r S g initIds (x.next tr) ss evs' vs) := by
  generalize hxs : x :: ss = xs at hme
  generalize hevs : ev₀ :: evs' = evs at hme
  cases hme with
  | nil _ => cases hevs
  | @run0 _ _ pre _ ev _ _ hpre hrej hrest =>
    injection hevs with hev₀ hevs₁; subst hev₀ hevs₁
    cases pre with
    | cons p₀ _ =>
      simp only [List.cons_append, List.cons.injEq] at hxs
      exact absurd (hpre p₀ List.mem_cons_self) (hxs.1 ▸ hx)
    | nil => simp only [List.nil_append] at hxs; subst hxs; exact Or.inl ⟨ev, rfl, hrej, hrest⟩
  | @run1 _ _ pre _ _ ev _ _ vs hpre hrm hrest =>
    injection hevs with hev₀ hevs₁; subst hev₀ hevs₁
    cases pre with
    | cons p₀ _ =>
      simp only [List.cons_append, List.cons.injEq] at hxs
      exact absurd (hpre p₀ List.mem_cons_self) (hxs.1 ▸ hx)
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, rfl⟩
      exact Or.inr (Or.inl ⟨ev, vs, _, rfl, hrm.2.2.2.2.2.1,
        congrArg (· ++ vs) hrm.2.2.2.2.2.2.1, hrest⟩)
  | @env _ _ pre s _ ev _ v vs hpre hem hrest =>
    injection hevs with hev₀ hevs₁; subst hev₀ hevs₁
    cases pre with
    | cons p₀ _ =>
      simp only [List.cons_append, List.cons.injEq] at hxs
      exact absurd (hpre p₀ List.mem_cons_self) (hxs.1 ▸ hx)
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hxs; rcases hxs with ⟨rfl, rfl⟩
      exact Or.inr (Or.inr ⟨ev, vs, rfl, congrArg (· ++ vs) (envMatches_vis hem), hrest⟩)

private theorem matchesEvents_nil_steps_inv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ev₀ : CliEvent} {evs' : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsAt interp r S g initIds tr [] (ev₀ :: evs') vis) :
    MatchesEventsAt interp r S g initIds tr [] evs' vis := by
  generalize hxs : ([] : List Step) = xs at hme
  generalize hevs : ev₀ :: evs' = evs at hme
  cases hme with
  | nil _ => cases hevs
  | @run1 _ _ pre _ _ _ _ _ _ _ _ _ => cases pre <;> simp at hxs
  | @env _ _ pre _ _ _ _ _ _ _ _ _ => cases pre <;> simp at hxs
  | @run0 _ _ pre _ _ _ _ _ _ hrest =>
    injection hevs with _ hevs₁; subst hevs₁
    rcases List.append_eq_nil_iff.mp hxs.symm with ⟨rfl, rfl⟩; exact hrest

private theorem matchesEvents_vis_unique {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost} :
    ∀ {evs : List CliEvent} {ss : List Step} {initIds₁ initIds₂ : Option BundlePreKeyIds}
      {tr : ExecTrace} {vis₁ vis₂ : List VisEntry},
      MatchesEventsAt interp r S g₁ initIds₁ tr ss evs vis₁ →
      MatchesEventsAt interp r S g₂ initIds₂ tr ss evs vis₂ →
      vis₁ = vis₂
  | [], _, _, _, _, _, _, h₁, h₂ => by cases h₁; cases h₂; rfl
  | ev₀ :: evs', ss, initIds₁, initIds₂, tr, vis₁, vis₂, h₁, h₂ => by
    induction ss generalizing initIds₁ initIds₂ tr vis₁ vis₂ with
    | nil =>
      exact matchesEvents_vis_unique (matchesEvents_nil_steps_inv h₁) (matchesEvents_nil_steps_inv h₂)
    | cons x ss' ih_ss =>
      by_cases hx : x.cls = .invisible
      · exact @ih_ss initIds₁ initIds₂ (x.next tr) vis₁ vis₂
          (matchesEvents_cons_invisible hx h₁) (matchesEvents_cons_invisible hx h₂)
      · rcases matchesEvents_vis_nonInvisible hx h₁ with
            ⟨ev₁, rfl, hrej₁, hrest₁⟩ | ⟨ev₁, vs₁, _, rfl, ⟨out₁, hex₁⟩, rfl, hrest₁⟩ |
            ⟨ev₁, vs₁, rfl, rfl, hrest₁⟩
        · rcases matchesEvents_vis_nonInvisible hx h₂ with
              ⟨_, heq, _, hrest₂⟩ | ⟨_, _, _, heq, ⟨out₂, hex₂⟩, _, _⟩ | ⟨_, _, heq, _⟩
          · injection heq; exact matchesEvents_vis_unique hrest₁ hrest₂
          · injection heq with hev; subst hev; exact absurd hex₂ (hrej₁ out₂)
          · cases heq
        · rcases matchesEvents_vis_nonInvisible hx h₂ with
              ⟨_, heq, hrej₂, _⟩ | ⟨_, vs₂, _, heq, _, rfl, hrest₂⟩ | ⟨_, _, heq, _⟩
          · injection heq with hev; subst hev; exact absurd hex₁ (hrej₂ out₁)
          · injection heq with hev; subst hev; rw [matchesEvents_vis_unique hrest₁ hrest₂]
          · cases heq
        · rcases matchesEvents_vis_nonInvisible hx h₂ with
              ⟨_, heq, _⟩ | ⟨_, _, _, heq, _⟩ | ⟨_, vs₂, heq, rfl, hrest₂⟩
          · cases heq
          · cases heq
          · injection heq with hev; subst hev; rw [matchesEvents_vis_unique hrest₁ hrest₂]

private theorem honestKeysOf_append :
    ∀ (ss₁ ss₂ : List Step) (tr : ExecTrace),
      honestKeysOf tr (ss₁ ++ ss₂) = honestKeysOf tr ss₁ ++ honestKeysOf (runSteps ss₁ tr) ss₂
  | [], _, _ => rfl
  | s :: ss₁, ss₂, tr => by
    simp only [List.cons_append, honestKeysOf, runSteps, honestKeysOf_append ss₁ ss₂ (s.next tr),
      List.append_assoc]

private theorem honestKeysOf_map_network :
    ∀ (ext : List _root_.DY.Bytes) (tr : ExecTrace), honestKeysOf tr (ext.map Step.network) = []
  | [], _ => rfl
  | x :: ext, tr => by
    simp [honestKeysOf, Step.publishedSpqrKey?, honestKeysOf_map_network ext ((Step.network x).next tr)]

private theorem honestSaltsOf_append_network (r : ProtocolSetup) (ss : List Step)
    (ext : List _root_.DY.Bytes) :
    honestSaltsOf r (ss ++ ext.map Step.network) = honestSaltsOf r ss := by
  simp [honestSaltsOf, honestKeysOf_append, honestKeysOf_map_network]

private theorem network_next_eq_append (tr : ExecTrace) (x : _root_.DY.Bytes) :
    (Step.network x).next tr = tr.append (NetE x) := by
  change ((_root_.DY.Network.sendMessage x).run tr).2.val = tr.append (NetE x)
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    _root_.DY.Traceful.run_mk]

private theorem step_le_next (s : Step) (tr : ExecTrace) : tr ≤ s.next tr :=
  ((reachability.step s.toInput).2.run tr).2.property

private theorem runSteps_le : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => _root_.DY.Trace.le_refl tr
  | s :: ss, tr => _root_.DY.Trace.le_trans _ _ _ (step_le_next s tr) (runSteps_le ss (s.next tr))

private theorem prefixTerms_runSteps_network {r : ProtocolSetup} {vis : List VisEntry} :
    ∀ (ext : List _root_.DY.Bytes) (tr : ExecTrace),
      prefixTerms r (runSteps (ext.map Step.network) tr) vis = prefixTerms r tr vis
  | [], _ => rfl
  | x :: ext, tr => by
    dsimp only [List.map, runSteps]
    rw [prefixTerms_runSteps_network ext, network_next_eq_append]
    simp [prefixTerms, principalTerms, Symbolic.Swarm.CREF.storedStates_append_network,
      Symbolic.Swarm.CREF.storedSecrets_append_network, NetE]

private theorem whisperTrials_runSteps_network {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {msg : _root_.DY.Libsignal.TripleRatchet.TRSignalMsg} :
    ∀ (ext : List _root_.DY.Bytes) (tr : ExecTrace),
      whisperTrials interp r S g (runSteps (ext.map Step.network) tr) msg =
        whisperTrials interp r S g tr msg
  | [], _ => rfl
  | x :: ext, tr => by
    dsimp only [List.map, runSteps]
    rw [whisperTrials_runSteps_network ext, network_next_eq_append,
      Symbolic.Swarm.CREF.whisperTrials_append_network interp r S g tr x msg]

private theorem recvCollisionOn_of_append_network {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {ext : List _root_.DY.Bytes} {vis : List VisEntry}
    {t : _root_.DY.Bytes}
    (hcol : RecvCollisionOn interp r S g (runTrace r (ss ++ ext.map Step.network)) vis
      (honestSaltsOf r (ss ++ ext.map Step.network)) t) :
    RecvCollisionOn interp r S g (runTrace r ss) vis (honestSaltsOf r ss) t := by
  rw [runTrace_append, honestSaltsOf_append_network] at hcol
  have hle_ext := runSteps_le (ext.map Step.network) (runTrace r ss)
  have hkn : ∀ u : _root_.DY.Bytes, u.AttackerKnows (runTrace r ss) →
      u.AttackerKnows (runSteps (ext.map Step.network) (runTrace r ss)) :=
    fun _ hu => _root_.DY.Bytes.AttackerKnows_le _ _ _ hle_ext hu
  have hpfx_sub : prefixTerms r (runSteps (ext.map Step.network) (runTrace r ss)) vis ⊆
      prefixTerms r (runTrace r ss) vis :=
    fun _ hu => by rwa [prefixTerms_runSteps_network ext (runTrace r ss)] at hu
  unfold RecvCollisionOn at hcol ⊢
  cases hp : _root_.DY.Libsignal.TripleRatchet.parseTrSignalMsg t with
  | none =>
    simp only [hp] at hcol ⊢
    exact Symbolic.Swarm.CREF.Stage1Trials.MemoCollisionOn.mono_quiet
      (List.Subset.refl _) hpfx_sub rfl hkn hcol
  | some msg =>
    simp only [hp] at hcol ⊢
    rw [whisperTrials_runSteps_network ext (runTrace r ss)] at hcol
    exact hcol.imp
      (Symbolic.Swarm.CREF.Stage1Trials.MemoCollisionOn.mono_quiet
        (List.Subset.refl _) hpfx_sub rfl hkn)
      (Symbolic.Swarm.CREF.Stage1Trials.MacTagForgeryOrCollision.mono_ctxs (List.Subset.refl _) hkn)

private theorem getMessageSentAt_append_net {tr : ExecTrace} {x u : _root_.DY.Bytes} {idx : Nat}
    (h : (tr.append (NetE x)).getMessageSentAt idx = some u) :
    (∃ k, tr.getMessageSentAt k = some u) ∨ u = x := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at h
  rcases hat : ((tr.append (NetE x)).at? idx : Option NetEntry) with _ | ⟨y⟩
  · simp [hat] at h
  · simp [hat] at h; subst h
    rcases at?_append_cases hat with ⟨_, heq⟩ | ⟨_, hproj⟩
    · refine Or.inl ⟨idx, ?_⟩; simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]; simp [heq]
    · rw [proj_inj_eq] at hproj; injection hproj with h1; subst h1; exact Or.inr rfl

private theorem getMessageSentAt_runSteps_network :
    ∀ (ext : List _root_.DY.Bytes) {tr : ExecTrace} {idx : Nat} {u : _root_.DY.Bytes},
      (runSteps (ext.map Step.network) tr).getMessageSentAt idx = some u →
      (∃ k, tr.getMessageSentAt k = some u) ∨ u ∈ ext
  | [], _, idx, _, h => Or.inl ⟨idx, h⟩
  | x :: ext, _, _, u, h => by
    simp only [List.map_cons, runSteps, network_next_eq_append] at h
    rcases getMessageSentAt_runSteps_network ext h with ⟨k, hk⟩ | hmem
    · exact (getMessageSentAt_append_net hk).imp id (fun (hux : u = x) => hux ▸ List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem x hmem)

private theorem recvCollisionOn_transfer_via_xlate {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {evs : List CliEvent} {g g₁ : Ghost} {ss : List Step} {vis : List VisEntry}
    {n : Nat} {t : _root_.DY.Bytes}
    (hInv : XlateInvSpecB) (hr : ProtocolSetupWF r) (hS : SemReady interp r S)
    (hfit : SchedFits (callsOf evs) who ok)
    (hex : Explains interp r S g ss vis evs) (hnrc : ¬ ReadCollisionCli interp r S g ss evs)
    (haddr : g₁.addr = g.addr) (hσ : ∀ i, i < n → g₁.σ i = g.σ i)
    (hlen : (runTrace r ss).length ≤ n)
    (ht_src : (∃ k, (runTrace r ss).getMessageSentAt k = some t) ∨ t.AttackerKnows (runTrace r ss))
    (hcol₁ : RecvCollisionOn interp r S g₁ (runTrace r ss) vis (honestSaltsOf r ss) t) :
    RecvCollisionOn interp r S g (runTrace r ss) vis (honestSaltsOf r ss) t := by
  obtain ⟨τ, ms, hex_cli, hnrc_cli, gtr, gsalts, gpfx, gpt⟩ := hInv hr hS hfit hex hnrc
  have hc := explainsCli_toClean hex_cli hnrc_cli
  have hfr : Symbolic.Swarm.CREF.CBadSigmaFrame g g₁ n :=
    ⟨fun ts hts len => congrFun (hσ ts hts) len, haddr⟩
  have hga := Symbolic.Swarm.CREF.cbadG2_gammaAgree_of_sigmaFrame interp S hfr
  have hst := Symbolic.Swarm.CREF.cbadG2_stamps_of_matched hc.matched (gtr ▸ hlen)
  have ht_st := ht_src.elim
    (fun ⟨k, hk⟩ => Symbolic.Swarm.CREF.cbadG2_stampsLt_getMessageSentAt hst (gtr.symm ▸ hk))
    (fun hkn => hst.knows (gtr.symm ▸ hkn))
  have hcol₁_m := (Symbolic.Proofs.Swarm.UA.BI.G.RecvStep.recvCollision_iff_of_xlate (g := g₁) gtr gsalts gpfx gpt).mpr hcol₁
  have hcol_m := Symbolic.Swarm.CREF.CliPure.cbadG2_recvCollision_transfer hga hst ht_st hcol₁_m
  exact (Symbolic.Proofs.Swarm.UA.BI.G.RecvStep.recvCollision_iff_of_xlate (g := g) gtr gsalts gpfx gpt).mp hcol_m

private theorem eq_of_append_cons_filter {α : Type} {p : α → Bool}
    {xs₁ xs₂ : List α} {a b : α} {ys₁ ys₂ : List α}
    (heq : xs₁ ++ a :: ys₁ = xs₂ ++ b :: ys₂) (ha : p a = true) (hb : p b = true)
    (hlen : (xs₁.filter p).length = (xs₂.filter p).length) :
    xs₁ = xs₂ ∧ a = b ∧ ys₁ = ys₂ := by
  induction xs₁ generalizing xs₂ with
  | nil =>
    cases xs₂ with
    | nil => simp only [List.nil_append, List.cons.injEq] at heq; exact ⟨rfl, heq.1, heq.2⟩
    | cons _ _ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
      rcases heq with ⟨rfl, _⟩; simp [ha] at hlen
  | cons x₁ xs₁ ih =>
    cases xs₂ with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
      rcases heq with ⟨rfl, _⟩; simp [hb] at hlen
    | cons x₂ xs₂ =>
      simp only [List.cons_append, List.cons.injEq] at heq; rcases heq with ⟨rfl, htail⟩
      have hlen' : (xs₁.filter p).length = (xs₂.filter p).length := by
        cases hx : p x₁ <;> simp [hx] at hlen <;> omega
      obtain ⟨rfl, rfl, rfl⟩ := ih htail hlen'
      exact ⟨rfl, rfl, rfl⟩

private theorem snoc_inj {α : Type} {xs ys : List α} {x y : α}
    (h : xs ++ [x] = ys ++ [y]) : xs = ys ∧ x = y := by
  have hl := congrArg List.length h
  simp only [List.length_append, List.length_singleton] at hl
  obtain ⟨rfl, hxy⟩ := List.append_inj h (by omega)
  exact ⟨rfl, List.singleton_injective hxy⟩

private theorem isNonInvisible_of_decryptMsgIdx {m : Step} {idx : Nat}
    (h : m.decryptMsgIdx? = some idx) : isNonInvisible m = true := by
  cases m <;> simp [Step.decryptMsgIdx?, isNonInvisible, Step.cls] at h ⊢

private theorem not_readCollisionCli_of_acceptsViaCli {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {evs_pre : List CliEvent} {ev : RunEvent} {g g₁ : Ghost}
    {ss : List Step} {vis : List VisEntry} {ext : List _root_.DY.Bytes}
    {m : Step} {msgIdx : Nat} {t_acc : _root_.DY.Bytes}
    (hInv : XlateInvSpecB) (hr : ProtocolSetupWF r) (hS : SemReady interp r S)
    (hfit : SchedFits (callsOf evs_pre) who ok)
    (hex_pre : Explains interp r S g ss vis evs_pre)
    (hnrc_pre : ¬ ReadCollisionCli interp r S g ss evs_pre)
    (hext_kn : ∀ x ∈ ext, x.AttackerKnows (runTrace r ss))
    (hm_dec : m.decryptMsgIdx? = some msgIdx)
    (haddr : g₁.addr = g.addr)
    (hσ : ∀ i, i < (runTrace r ss).length → g₁.σ i = g.σ i)
    (hget_acc : (runTrace r (ss ++ ext.map Step.network)).getMessageSentAt msgIdx = some t_acc)
    (hncol_acc : ¬ RecvCollisionOn interp r S g (runTrace r ss) vis (honestSaltsOf r ss) t_acc) :
    ¬ ReadCollisionCli interp r S g₁ (ss ++ ext.map Step.network ++ [m]) (evs_pre ++ [.run ev]) := by
  rintro ⟨evs₁, ev₀, evs₂, ss₁, ss₂, m₀, vis_a, msgIdx₀, out₀, b₀, t₀,
    hevs_eq, hss_eq, hcmd₀, hexit₀, hbody₀, hme_a, hm₀_dec, hget₀, hcol₀⟩
  have hm_ni : isNonInvisible m = true := isNonInvisible_of_decryptMsgIdx hm_dec
  have hm₀_ni : isNonInvisible m₀ = true := isNonInvisible_of_decryptMsgIdx hm₀_dec
  have hext_inv : ∀ x ∈ ext.map Step.network, x.cls = .invisible := by
    intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; rfl
  rcases List.eq_nil_or_concat evs₂ with rfl | ⟨evs₂', last, hlast⟩
  · obtain ⟨rfl, _⟩ := snoc_inj hevs_eq
    have hlen_filter : ((ss ++ ext.map Step.network).filter isNonInvisible).length =
        (ss₁.filter isNonInvisible).length := by
      rw [List.filter_append, filter_nonInvisible_eq_nil hext_inv, List.append_nil,
        matchesEvents_filter_nonInvisible_length hex_pre.2.2.2,
        matchesEvents_filter_nonInvisible_length hme_a]
    obtain ⟨hss₁_eq, rfl, _⟩ := eq_of_append_cons_filter hss_eq hm_ni hm₀_ni hlen_filter
    subst hss₁_eq
    cases Option.some.inj (hm_dec.symm.trans hm₀_dec)
    cases Option.some.inj (hget_acc.symm.trans hget₀)
    have hme_ext := matchesEvents_append_invisible hex_pre.2.2.2 hext_inv
    rw [matchesEvents_vis_unique hme_a hme_ext] at hcol₀
    have hcol_ss := recvCollisionOn_of_append_network hcol₀
    rw [runTrace_append] at hget_acc
    have ht_src := (getMessageSentAt_runSteps_network ext hget_acc).imp id (hext_kn t_acc)
    exact hncol_acc (recvCollisionOn_transfer_via_xlate hInv hr hS hfit hex_pre hnrc_pre
      haddr hσ (Nat.le_refl _) ht_src hcol_ss)
  · rw [List.concat_eq_append] at hlast; subst hlast
    have hevs_assoc : evs₁ ++ .run ev₀ :: (evs₂' ++ [last]) =
        (evs₁ ++ .run ev₀ :: evs₂') ++ [last] := by simp [List.append_assoc]
    rw [hevs_assoc] at hevs_eq
    obtain ⟨hevs_pre, _⟩ := snoc_inj hevs_eq; subst hevs_pre
    obtain ⟨ss_a, ss_b, vis₁', vis₂', rfl, rfl, hme₁', hme₂'⟩ :=
      matchesEvents_restrict_tail (.run ev₀ :: evs₂') evs₁ hex_pre.2.2.2
    generalize hE : CliEvent.run ev₀ :: evs₂' = E at hme₂'
    cases hme₂' with
    | nil _ => cases hE
    | env _ _ _ => cases hE
    | run0 _ hrej _ =>
      injection hE with hev _; injection hev with hev'; subst hev'; exact hrej out₀ hexit₀
    | @run1 _ _ pre₀ s₀ ss_c _ _ _ _ hpre₀ hrm₀ _ =>
      injection hE with hev _; injection hev with hev'; subst hev'
      have hs₀_ni : isNonInvisible s₀ = true := by simp [isNonInvisible, hrm₀.1]
      let ss_cut := ss_a ++ pre₀
      have hss_split : ss_a ++ (pre₀ ++ s₀ :: ss_c) = ss_cut ++ s₀ :: ss_c := by
        simp [ss_cut, List.append_assoc]
      have hme_cut := matchesEvents_append_invisible hme₁' hpre₀
      have hss_eq' : ss_cut ++ s₀ :: (ss_c ++ ext.map Step.network ++ [m]) = ss₁ ++ m₀ :: ss₂ := by
        simpa [ss_cut, List.append_assoc] using hss_eq
      have hlen_filter : (ss_cut.filter isNonInvisible).length = (ss₁.filter isNonInvisible).length := by
        rw [matchesEvents_filter_nonInvisible_length hme_cut,
          matchesEvents_filter_nonInvisible_length hme_a]
      obtain ⟨hcut_eq, rfl, _⟩ := eq_of_append_cons_filter hss_eq' hs₀_ni hm₀_ni hlen_filter
      subst hcut_eq
      rw [matchesEvents_vis_unique hme_a hme_cut] at hcol₀
      have hex_cut : Explains interp r S g ss_cut vis₁' evs₁ :=
        ⟨hex_pre.1, ghostWF_of_append hex_pre.2.1,
          modelRunWF_of_append (hss_split ▸ hex_pre.2.2.1), hme_cut⟩
      have hnrc_cut : ¬ ReadCollisionCli interp r S g ss_cut evs₁ := fun hrc_cut =>
        hnrc_pre (hss_split ▸ readCollisionCli_append (s₀ :: ss_c) (.run ev₀ :: evs₂') hrc_cut)
      have hfit_cut : SchedFits (callsOf evs₁) who ok := by
        rw [callsOf_append] at hfit; exact schedFits_of_append hfit
      have hlen_cut : (runTrace r ss_cut).length ≤ (runTrace r (ss_a ++ (pre₀ ++ s₀ :: ss_c))).length := by
        rw [hss_split, runTrace_append r ss_cut (s₀ :: ss_c)]
        exact _root_.DY.Trace.length_le _ _ (runSteps_le (s₀ :: ss_c) (runTrace r ss_cut))
      have hcol_g := recvCollisionOn_transfer_via_xlate hInv hr hS hfit_cut hex_cut hnrc_cut
        haddr hσ hlen_cut (Or.inl ⟨msgIdx₀, hget₀⟩) hcol₀
      exact hnrc_pre ⟨evs₁, ev₀, evs₂', ss_cut, ss_c, s₀, vis₁', msgIdx₀, out₀, b₀, t₀,
        rfl, hss_split, hcmd₀, hexit₀, hbody₀, hme_cut, hm₀_dec, hget₀, hcol_g⟩

end Sec1

/-! ## Raw Decrypt Witness and Leaked Record Helpers -/

private theorem recvWireStepWitness_noAcceptCol
    {interpretation : ExternInterpretation} (hExt : ExternContractsHoldCli interpretation)
    {r₀ : ProtocolSetup} (hwf : ProtocolSetupWF r₀) (hik : Symbolic.Swarm.CREF.TR.IkShape interpretation r₀)
    {S : OpaqueSymbolSemantics} (hS : S = compSemOf interpretation r₀)
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant} {records : Participant → Option HwBytes}
    {sent accepted : List HwBytes} {opkUsed : Bool}
    {mid acc : List MachineEvent} {rec body : HwBytes} {sm : StateAndMessage}
    (hC : PureRcvAcceptCall interpretation r₀ S who ok j p records sent accepted opkUsed acc mid rec body sm)
    (g : Ghost) (ms₁ : List Move) (t : _root_.DY.Bytes)
    (hc : CleanBy interpretation r₀ S who ok g ms₁ acc)
    (ht : t ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hnocol : ¬ RecvCollision interpretation r₀ S g ms₁ t)
    (hnors : ¬ ReselectCollision interpretation r₀ S g ms₁ t)
    (hfresh : Symbolic.Swarm.CREF.TR.TRRecvFreshAll r₀ ms₁)
    (hPkDNR : NoRatchetPkDispatchAtSt interpretation r₀ S g ms₁ acc)
    (hPkDSk : SkippedPkDispatchAtKPure interpretation r₀ S g ms₁ acc)
    (hABS' : G1cAttackerBuiltSeedExcl' interpretation r₀ S g ms₁) :
    RecvWireRawWitness interpretation r₀ S who g ms₁ acc mid p body sm.message := by
  obtain ⟨_, g_rw, coins, _, hwire, hcanon_q, hmid_cases, _, heval⟩ :=
    rcv_pending_callEnd_of_pureAccept interpretation hC
  obtain ⟨m, newPqrState, pqrKey, htry, hrecv_spqr, hbranch⟩ :=
    evalRecvWireWithCoinsW_branch_cases interpretation body mid sm g_rw coins hwire hmid_cases heval
  have ⟨slots, hrsi⟩ : ∃ slots, PureTRRecordStateInv interpretation r₀ S slots g ms₁
      (fun q => if q = p then some rec else none) := by
    rcases pureCRecRelH_single (hC.hrel.recs hc p rec hC.hrec).2.2 hC.hss with hrsi | ⟨hp, hpend⟩
    · exact ⟨pureTrSlots r₀, hrsi⟩
    · exact ⟨pureTrSlotsPend r₀, trRecordStateInv_pend_of_aliceInitPending hp hpend⟩
  have hch := hC.hrel.hist hc
  have hat : RecvAtFacts interpretation r₀ S g ms₁ := ⟨hch.1, hch.2.1, hch.2.2.1, hch.2.2.2, hfresh⟩
  have hrec_p : (fun q => if q = p then some rec else none) p = some rec := by simp
  have hsent : sent = sentBodies acc := (hC.hrel.book hc).1
  have hfit := hC.hrel.sendsFit
  have hIW : InstallWitnessTR r₀ (runTraceMoves r₀ ms₁) :=
    installWitnessTR_of_reachable r₀ ms₁ hc.matched.2.1.2.2.1.1
  have hwho_vis : who[callCount (runVis r₀ ms₁)]? = some p := by
    rw [matchedPrefix_callCount_eq hc.matched, hC.hj]; exact hC.hwho
  rcases hbranch with
    ⟨ci, rc, ck, rfl, rfl, hrc, hrc_key, hck, hskip_idx⟩ |
    ⟨ci, rc, ck, rfl, rfl, hrc, hrc_key, hck, hstep_idx⟩ |
    ⟨rngBytes, rfl, hrng_len, rfl, hrc_none⟩
  · exact recvWireStepWitness_of_skipped_branchK interpretation hExt r₀ hwf S hS
      (fun q => if q = p then some rec else none) sent p rec body acc g ms₁ sm g_rw m
      ci rc ck newPqrState pqrKey hc.matched hrsi hat hPkDSk hsent hfit hrec_p hC.hpq
      t ht hnocol hnors hwire hcanon_q htry hrc hrc_key hck hskip_idx hrecv_spqr heval hwho_vis
  · exact recvWireStepWitness_of_noRatchet_branch interpretation hExt r₀ hwf S hS
      (fun q => if q = p then some rec else none) sent p rec body acc g ms₁ sm g_rw m
      ci rc ck newPqrState pqrKey hc.matched hrsi hat hsent hfit hrec_p hC.hpq
      t ht hnocol hnors hwire hcanon_q htry hrc hrc_key hck hstep_idx hrecv_spqr heval hIW hPkDNR hwho_vis
  · exact recvWireStepWitness_of_ratchetDH_branch interpretation hExt r₀ hwf hik S hS
      (fun q => if q = p then some rec else none) sent p rec body rngBytes acc g ms₁ sm g_rw m
      newPqrState pqrKey hc.matched hc.1 hrsi hat hsent hfit hrec_p hC.hpq hC.hstate_lt
      t ht hnocol hwire hcanon_q hrng_len htry hrc_none hrecv_spqr heval hABS' hwho_vis

private theorem leakRecords_alice_eq_after {interp' : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {t t_clean t_clean' : CliTurn}
    {accepted accepted' : List HwBytes} {c : CliCall} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hsim : PqTurnSim1A interp' P r t t_clean accepted)
    (hsim' : PqTurnSim1A interp' P r (CliTurn.after t r c code out files) t_clean' accepted') :
    t_clean'.leakRecords r r.alice =
      (t_clean.after r (toCliCallNone c) code out files).leakRecords r r.alice := by
  have h1 : t_clean'.leakRecords r r.alice = t_clean'.records r r.alice := by
    rw [leakRecords_eq_records_of_bobOff_false r hsim'.clean_bobOff]
  have h2 : (t_clean.after r (toCliCallNone c) code out files).leakRecords r r.alice =
      (t_clean.after r (toCliCallNone c) code out files).records r r.alice := by
    unfold CliTurn.leakRecords; simp [hwf.1]
  rw [h1, h2]; unfold CliTurn.records
  have hd1 := hsim'.dirs_other r.alice hwf.1
  have hd0 := hsim.dirs_other r.alice hwf.1
  have hp_eq : (toCliCallNone c).party = c.party := rfl
  have hdir_eq : t_clean'.dirs r.alice =
      (t_clean.after r (toCliCallNone c) code out files).dirs r.alice := by
    rw [hd1]; unfold CliTurn.after; dsimp only; rw [hp_eq]
    by_cases ha : r.alice = c.party <;> simp [ha, hd0]
  rw [hdir_eq]

private theorem leakRecords_alice_eq_of_bob_call {interp' : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {t t_clean t_clean' : CliTurn}
    {accepted accepted' : List HwBytes} {c : CliCall} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hbob : c.party = r.bob)
    (hsim : PqTurnSim1A interp' P r t t_clean accepted)
    (hsim' : PqTurnSim1A interp' P r (CliTurn.after t r c code out files) t_clean' accepted') :
    t_clean'.leakRecords r r.alice = t_clean.leakRecords r r.alice := by
  rw [leakRecords_alice_eq_after hwf hsim hsim',
    leakRecords_eq_records_of_bobOff_false r hsim.clean_bobOff]
  unfold CliTurn.leakRecords; simp [hwf.1, CliTurn.records, CliTurn.after, toCliCallNone, hbob]

/-! ## Whisper Receive Slot Specification -/

/-- Proves `UASlotRecvWSpecB` from `XlateInvSpecB` and `XlateExcWSpecB`. -/
theorem uab_slot_recvw_of (hInv : XlateInvSpecB) (hExcW : XlateExcWSpecB) : UASlotRecvWSpecB := by
  intro interp P r hext hagree hwf t t_clean c i body code out files accepted evs_pre
    hsim hp hcmd hbun hcoins hstdin hbody_lt hfb hbca hrec_ne hpq hin hRel
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let ev := runEventOf c (some (code, out))
  let evs := evs_pre ++ [.run ev]
  have hS : SemReady interp' r S := compSemOf_ready interp' r hwf
  obtain ⟨t_clean', accepted', hsim', hstep_gen⟩ :=
    Symbolic.Swarm.Coinsplit.Lift.L09.slot_recvW_cli_gen
      Symbolic.Swarm.Coinsplit.Lift.L02.outcomeFaithfulCli_of_goodExit0Cut
      Symbolic.Swarm.Coinsplit.Lift.L04.bridgeB_quiet_fail
      Symbolic.Swarm.Coinsplit.Lift.L05.bridgeC_caseA
      Symbolic.Swarm.Coinsplit.Lift.L06.bridgeC_caseB
      interp P r hext hagree hwf (σ_pre := flatEvents evs_pre)
      hsim hp hcmd hbun hcoins hstdin hbody_lt hfb hbca hrec_ne hpq hin hRel
  refine ⟨t_clean', accepted', hsim', fun who ok hfit hinv_pre => ?_⟩
  rcases hinv_pre with hcol_pre | ⟨hlive_pre, hap_pre, ⟨g₀, ss₀, vis₀, hex₀, hnrc₀⟩⟩
  · exact Or.inl (collisionAtCli_append [.run ev] hcol_pre)
  · by_cases hcol : CollisionAfterExplainedPrefix interp' r S evs
    · exact Or.inl hcol
    · obtain ⟨hfit_pre, hwho_pre, hok_pre, hflat_eq⟩ := Symbolic.Proofs.Swarm.UA.BI.G.RecvStep.schedFits_recv_call hcmd hfit
      let c1 := toCliCallNone c
      have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
      have hb' : ModelHookBridge interp' P := modelHookBridge_interpOfParams hagree
      obtain ⟨hd_eq, hrec_eq, hbca1⟩ := clean_dirs_caller_eq hwf hsim hbca hp
      have hrec_ne1 : t_clean.records r c1.party ≠ none := by
        change t_clean.records r c.party ≠ none; rwa [hrec_eq]
      have hsb1 : StdinBounded c1 := by
        unfold StdinBounded; simp only [c1, toCliCallNone, hcmd, hstdin]
        refine ⟨fun body₀ hb₀ => (List.cons.inj hb₀).2 ▸ hbody_lt,
          fun hnw => absurd (by simp) hnw, fun q hq => ?_,
          fun _ _ _ _ _ _ _ _ _ _ _ hpw => ?_⟩
        · simp [parsePreKeyWire, wireWhisperTag,
            _root_.DY.Libsignal.PQXDH.Refinement.wirePrekeyTag] at hq
        · unfold preKeyWire at hpw; exact absurd (List.cons.inj hpw).1 (by decide)
      have hnext1 : ValidCall interp' r t_clean c1 := by
        refine ⟨by simpa [c1, toCliCallNone, hcmd, coinsLen] using hcoins,
          hsb1, hd_eq.symm ▸ hfb, hbca1, ?_⟩
        dsimp only [c1, toCliCallNone]; rw [hcmd]
        exact ⟨hp, rfl, rfl, Or.inl ⟨hrec_ne1, body, hstdin, hsim.sent_eq.symm ▸ hpq⟩⟩
      have hin1 : InputsFor c1 (t_clean.dirs c1.party) i :=
        hd_eq.symm ▸ inputsFor_toCliCallNone hbun hin
      obtain ⟨hparty_case, st, hinvP⟩ := caller_pqPartyInv_of_allowed hsim.dirInv hbca1 hp
      have hwf_st := wfPq_of_pqPartyInv hinvP (hd_eq.symm ▸ hfb)
      have hrec_st : t_clean.records r c1.party =
          (st.session.map fun (x, g) => encodeRecordUnderExtras (fun _ => x) g) := by
        simpa using records_of_pqPartyInv hinvP
      let rc := CryptoGames.HKDF.bytesToKey32 c1.coins
      have hcoins_rc : c1.coins = CryptoGames.HMAC.keyToBytes32 rc := (keyToBytes32_bytesToKey32 hcoins).symm
      have hpeer' : peerOf r c1.party = partyAddress st.party.other := by
        rw [peerOf_eq_addrE_other, ← hinvP.party_eq]
      have hcmd_st : c1.cmd = .recv (partyAddress st.party.other) := hpeer' ▸ hcmd
      have hi' : InputsFor c1 (filesOf (encodeDir P st)) i := by rwa [hinvP.dir_eq] at hin1
      have hstdin_st : c1.stdin = wireWhisper :: body := hstdin
      have heq_in := hstdin_st ▸ inputsEquiv_pqRecvInputs hi' hcmd_st rfl hcoins_rc
      have hobs_eq := (PqModelRel.exited_iff.mp hRel).recvWhisper st body rc hwf_st hbody_lt heq_in
      rcases exited_eq_pqObserve_iff.mp hobs_eq with
          ⟨_, rfl, rfl, rfl⟩ | ⟨st', _, hmod, rfl, rfl, rfl⟩
      ·
        have hscr : scrub (filesOf (pqRecvInputs P st (wireWhisper :: body) rc).files) =
            t_clean.dirs c1.party := by
          rw [hinvP.dir_eq]
          exact scrub_filesOf_pqInputs_reject P st _ [] _ _
            (fun _ h => nomatch h) (fun _ h => nomatch h)
        have hrec_alice : t_clean'.leakRecords r r.alice = t_clean.leakRecords r r.alice := by
          rw [leakRecords_alice_eq_after hwf hsim hsim',
            leakRecords_eq_records_of_bobOff_false r hsim.clean_bobOff]
          unfold CliTurn.leakRecords
          simp [hwf.1, CliTurn.records]
          by_cases hq : r.alice = c1.party <;> simp [CliTurn.after, c1, hq, hscr]
        have hlive' : CliLiveAtCli interp' r S who ok t_clean' accepted' (flatEvents evs) := by
          rw [hflat_eq]
          exact hstep_gen who ok hwho_pre hlive_pre (fun h => nomatch h) hok_pre
        exact Symbolic.Proofs.Swarm.UA.BI.G.RecvStep.uaInv_recv_rejected hwf hcmd Nat.one_ne_zero
          (fun _ => by simp [runInput, hcmd, hstdin]) hrec_alice hlive' hap_pre
          ⟨g₀, ss₀, vis₀, hex₀, hnrc₀⟩
      ·
        let files_acc := filesOf ((pqRecvInputs P st (wireWhisper :: body) rc).files ++ encodeDir P st')
        obtain ⟨hst', hsub⟩ := pqPartyInv_of_pqRecvWhisperModel hinvP hwf_st hmod
        have hscr : scrub files_acc = filesOf (encodeDir P st') :=
          scrub_filesOf_pqInputs_accept P st st' _ [] _ _
            (fun _ h => nomatch h) (fun _ h => nomatch h) hsub
        have hst'_after : PqPartyInv interp' P r accepted c1.party st'
            ((t_clean.after r c1 0 out files_acc).dirs c1.party) := by
          simpa [CliTurn.after, hscr] using hst'
        have hrec_after : (t_clean.after r c1 0 out files_acc).records r c1.party =
            (st'.session.map fun (x', g') => encodeRecordUnderExtras (fun _ => x') g') := by
          simpa using records_of_pqPartyInv hst'_after
        have hmod_copy := hmod
        unfold pqRecvWhisperModel at hmod_copy
        rcases hsess_st : st.session with _ | ⟨x_st, g_sess_st⟩
        · simp [hsess_st] at hmod_copy
        rw [hsess_st] at hmod_copy
        cases htry_body : SignalMessage.tryFrom protoSignalCodec body with
        | error _ => simp [htry_body] at hmod_copy
        | ok inner =>
          obtain ⟨τ₀, ms₀, _, _, htr₀, _, _, _⟩ := hInv hwf hS hfit_pre hex₀ hnrc₀
          obtain ⟨t₀, ht₀_mv⟩ :=
            Symbolic.Swarm.CREF.TR.RecvRep.recvRepresentations_nonempty_of_tryFrom
              interp' r S g₀ ms₀ body inner htry_body
          have ht₀_on : t₀ ∈ recvRepresentationsOn interp' S g₀ (runTrace r ss₀) body :=
            Symbolic.Proofs.Swarm.UA.BI.G.RecvStep.recvRepresentations_eq_of_trace htr₀ ▸ ht₀_mv
          have hev_cmd : ev.cmd = .recv (peerOf r c.party) := hcmd
          have hev_in : ev.input = wireWhisperTag :: body := by
            simp [ev, runEventOf, runInput, hcmd, hstdin]
          have hnc : Symbolic.Swarm.Coinsplit.Lift.L09.RecvWNC interp' r S c 0 out body
              (flatEvents evs_pre) who ok := by
            intro _ τ₁ g₁ ms₁ hex₁ hnrc₁
            have h0 := hExcW hwf hS hfit hlive_pre hex₀ hnrc₀ hev_cmd rfl hcoins
              ⟨t₀, ht₀_on⟩ (Or.inl ⟨body, hev_in, rfl⟩) hcol τ₁ g₁ ms₁ hex₁ hnrc₁
            simpa [ev, runEventOf, runInput, hcmd, hev_in, hstdin] using h0
          have hlive' : CliLiveAtCli interp' r S who ok t_clean' accepted' (flatEvents evs) := by
            rw [hflat_eq]
            exact hstep_gen who ok hwho_pre hlive_pre hnc hok_pre
          have hnexc : ¬ SignalMsgAcceptedOnlyViaCollision interp' r S g₀ ss₀ evs_pre ev body := by
            intro hexc
            apply hcol
            refine ⟨evs_pre, ev, [], g₀, ss₀, vis₀, rfl, hex₀, ?_⟩
            dsimp only [NextEventCollides]; rw [hev_cmd, hev_in]
            exact ⟨⟨out, rfl⟩, Or.inl ⟨rfl, hexc⟩⟩
          have hex_clean_w : ∃ g' ss' vis',
              Explains interp' r S g' ss' vis' evs_pre ∧
              ¬ ReadCollisionCli interp' r S g' ss' evs_pre ∧
              (∃ t' ∈ recvRepresentationsOn interp' S g' (runTrace r ss') body,
                ¬ RecvCollisionOn interp' r S g' (runTrace r ss') vis' (honestSaltsOf r ss') t' ∧
                ¬ ReselectCollisionOn interp' r S g' (runTrace r ss') vis'
                    (honestSaltsOf r ss') t') ∧
              ¬ ((∃ t ∈ recvRepresentationsOn interp' S g' (runTrace r ss') body,
                    ModelAcceptsTermAfterAttackerSends interp' r S g' ss' evs_pre ev t) ∧
                  ∀ t ∈ recvRepresentationsOn interp' S g' (runTrace r ss') body,
                    ModelAcceptsTermAfterAttackerSends interp' r S g' ss' evs_pre ev t →
                    RecvCollisionOn interp' r S g' (runTrace r ss') vis'
                      (honestSaltsOf r ss') t) := by
            by_contra hno_w
            apply hnexc
            refine ⟨⟨t₀, ht₀_on⟩, fun g' ss' vis' hex' hnrc' => ?_⟩
            by_contra hneither
            have hnot1 := fun h1 => hneither (Or.inl h1)
            have hnot2 := fun h2 => hneither (Or.inr h2)
            have hex_t' : ∃ t' ∈ recvRepresentationsOn interp' S g' (runTrace r ss') body,
                ¬ RecvCollisionOn interp' r S g' (runTrace r ss') vis' (honestSaltsOf r ss') t' ∧
                ¬ ReselectCollisionOn interp' r S g' (runTrace r ss') vis'
                    (honestSaltsOf r ss') t' := by
              by_contra hno_t'
              apply hnot1; intro t' ht'
              by_cases hrc_t' : RecvCollisionOn interp' r S g' (runTrace r ss') vis'
                  (honestSaltsOf r ss') t'
              · exact Or.inl hrc_t'
              · exact Or.inr (by by_contra hnrs_t'; exact hno_t' ⟨t', ht', hrc_t', hnrs_t'⟩)
            exact hno_w ⟨g', ss', vis', hex', hnrc', hex_t', hnot2⟩
          obtain ⟨g_star, ss_star, vis_star, hex_star, hnrc_star,
            ⟨t_star, ht_star_on, hnrc_t, hnrs_t⟩, hnot_ac_cli⟩ := hex_clean_w
          obtain ⟨τ_star, ms_star, hex_star_cli, hnrc_star_cli, htr_star, hsalts_star,
            hpref_star, hpt_star⟩ := hInv hwf hS hfit_pre hex_star hnrc_star
          have hc_star : Clean interp' r S who ok g_star ms_star τ_star :=
            explainsCli_toClean hex_star_cli hnrc_star_cli
          obtain ⟨hrel_star, hopk_star⟩ :=
            hlive_pre.cutRel τ_star ⟨g_star, ms_star, hex_star_cli, hnrc_star_cli⟩
          have hwho_star : who[(callStarts τ_star).length]? = some c.party := by
            rw [coinSplit_callStarts_length_eq hex_star_cli.1]; exact hwho_pre
          have hrec_sync : t_clean.leakRecords r c.party =
              st.session.map (fun xg => encodeRecordUnderExtras (fun _ => xg.1) xg.2) := by
            change t_clean.leakRecords r c1.party = _
            rw [leakRecords_party_eq_of_cliNextCall hnext1, hrec_st]
          have hpq_clean : PqFromHonest t_clean.sent body := hsim.sent_eq.symm ▸ hpq
          have hpre_star : Symbolic.Swarm.CREF.Cli.Slots.WhisperSlotPre interp' P r S who ok
              (callStarts τ_star).length c.party st (t_clean.leakRecords r) t_clean.sent accepted
              (t_clean.opkUsed r) τ_star body :=
            { extCli := hext', bridge := hb', wfR := hwf, semEq := rfl, partyMem := hp,
              partyTag := hinvP.party_eq, wfSt := hwf_st, recSync := hrec_sync,
              bodyLen := hbody_lt, pqHonest := fun _ => hpq_clean, callIdx := rfl,
              whoAt := hwho_star, cleanPre := ⟨g_star, ms_star, hc_star⟩,
              relPre := hrel_star, opkPre := hopk_star }
          obtain ⟨x, g_sess, s', _k, _msg, g_rw, mid₀, coins_eff,
            hsess_eval, hst'_eval, hrec_p, hrec_ne_in, hss, hcanonP, hrec4, hlen31, hlen32_out,
            _, hwrc, htrCanon, _, hmid_cases, _, hwho_grw, hwire_grw, hrcq_grw,
            hcoins_cases, hdco, heval⟩ :=
            Symbolic.Swarm.CREF.Cli.Slots.pqRecvWhisper_accept_eval rc hpre_star hmod
          cases Option.some.inj (hsess_st.symm.trans hsess_eval)
          let rec_in := encodeRecordUnderExtras (fun _ => x_st) g_sess_st
          let rec_out := encodeRecordUnderExtras (fun _ => x_st) { g_sess_st with session := s' }
          let sm : StateAndMessage := ⟨rec_out, out⟩
          have hmid_pure : mid₀ = [] ∨ ∃ rb : HwBytes, rb.length = 32 ∧ mid₀ = [.rng rb] := by
            rcases hmid_cases with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr ⟨CryptoGames.HMAC.keyToBytes32 rc,
                Symbolic.Swarm.CREF.Cli.Slots.keyToBytes32_length rc, rfl⟩
          have hC_star : PureRcvAcceptCall interp' r S who ok (callStarts τ_star).length c.party
              (t_clean.leakRecords r) t_clean.sent accepted (t_clean.opkUsed r)
              τ_star mid₀ rec_in body sm :=
            { hclean₀ := ⟨g_star, ms_star, hc_star⟩, hrel := hrel_star, hopk := hopk_star,
              hwho := hwho_star, hj := rfl, hp := hp, hrec := hrec_p, hne := hrec_ne_in,
              hss := hss, hlen := by dsimp [rec_in] at hlen31 ⊢; omega, hpq := hpq_clean,
              hcanonP := hcanonP, hrec4 := hrec4, hmid := hmid_pure,
              hstate_lt := by dsimp [sm, rec_out] at hlen32_out ⊢; omega,
              hwc := hwrc, hcanon_out := htrCanon,
              heval := ⟨g_rw, coins_eff, hwho_grw, hwire_grw, hrcq_grw,
                hcoins_cases, hdco, heval⟩ }
          have ht_star_mv : t_star ∈ recvRepresentations interp' r S g_star ms_star body :=
            Symbolic.Proofs.Swarm.UA.BI.G.RecvStep.recvRepresentations_eq_of_trace htr_star ▸ ht_star_on
          have hnrc_mv : ¬ RecvCollision interp' r S g_star ms_star t_star := fun h =>
            hnrc_t ((Symbolic.Proofs.Swarm.UA.BI.G.RecvStep.recvCollision_iff_of_xlate htr_star hsalts_star hpref_star hpt_star).mp h)
          have hnrs_mv : ¬ ReselectCollision interp' r S g_star ms_star t_star := fun h =>
            hnrs_t ((Symbolic.Proofs.Swarm.UA.BI.G.RecvStep.reselectCollision_iff_of_xlate htr_star hsalts_star hpref_star hpt_star).mp h)
          have hik := Symbolic.Proofs.Swarm.TRREF.Pure.rcv_ikShape_of_externCli hext' r
          have hRes_star := Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.slot_reselect_pure
            interp' hwf rfl g_star ms_star hc_star
          have hPkDNR_star := Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.rcv_hPkDNR_of_reselect
            hext'.1 hwf hc_star
            (Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.rcv_honestSkelUniq_of_matchedPrefix hc_star.matched)
            (Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.rcv_abs_of_matchedPrefix hc_star.matched)
            hRes_star
          have hPkDSk_star := Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.skipped_pk_dispatch_atK'
            hext' hwf hc_star
            (Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.rcv_skippedNotJunkSeedProvAt_of_notLowAll
              hc_star.matched.2.1.2.2.1.1 (hrel_star.hist hc_star).2.1)
            hRes_star (hrel_star.hist hc_star).2.2.1
            (Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.skippedFreshAliasExclB_of_reach
              interp' hc_star.matched.2.1.2.2.1.1)
          have hw_star := recvWireStepWitness_noAcceptCol hext' hwf hik rfl hC_star
            g_star ms_star t_star hc_star ht_star_mv hnrc_mv hnrs_mv
            (Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.rcv_hfresh_of_cleanBy interp' hc_star)
            hPkDNR_star hPkDSk_star
            (Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.rcv_abs_of_matchedPrefix hc_star.matched)
          have hmid_ev : mid₀ = [] ∨ mid₀ = [.rng ev.coins] := by
            rcases hmid_cases with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (congrArg (fun d => [MachineEvent.rng d]) hcoins_rc.symm)
          obtain ⟨t_m, ht_m_on, hacc_cli_tm⟩ :=
            Symbolic.Proofs.Swarm.UA.BI.G.RecvStep.acceptsViaCli_whisper_of_rawWitness hex_star hc_star.matched htr_star
              hev_cmd rfl hev_in hcoins hmid_ev hw_star
          have hex_good : ∃ t_good ∈ recvRepresentationsOn interp' S g_star (runTrace r ss_star) body,
              ModelAcceptsTermAfterAttackerSends interp' r S g_star ss_star evs_pre ev t_good ∧
              ¬ RecvCollisionOn interp' r S g_star (runTrace r ss_star) vis_star
                  (honestSaltsOf r ss_star) t_good := by
            by_contra hno_good
            exact hnot_ac_cli ⟨⟨t_m, ht_m_on, hacc_cli_tm⟩, fun t_a ht_a hacc_a => by
              by_contra hnc_a; exact hno_good ⟨t_a, ht_a, hacc_a, hnc_a⟩⟩
          obtain ⟨t_good, _, ⟨ext_g, m_g, msgIdx_g, g₁_g, vis₁_g,
              hext_g, hm_g, haddr_g, hσ_g, hget_g, hex₁_g⟩, hnc_good⟩ := hex_good
          have hnrc₁_g := not_readCollisionCli_of_acceptsViaCli (ev := ev) hInv hwf hS hfit_pre
            hex_star hnrc_star hext_g hm_g haddr_g hσ_g hget_g hnc_good
          have hap_post : ∀ g ss vis, Explains interp' r S g ss vis evs →
              ¬ ReadCollisionCli interp' r S g ss evs →
              Symbolic.Proofs.Swarm.UA.Defs.AliceRecordPendingInSession interp' r S g
                (runTrace r ss) (t_clean'.leakRecords r) (activeBundleIds evs) := by
            rcases hp with hp_alice | hp_bob
            · have hrec_alice_out : t_clean'.leakRecords r r.alice = some rec_out := by
                rw [leakRecords_alice_eq_after hwf hsim hsim']
                have hl : (t_clean.after r c1 0 out files_acc).leakRecords r r.alice =
                    (t_clean.after r c1 0 out files_acc).records r c1.party := by
                  unfold CliTurn.leakRecords; simp [hwf.1, c1, toCliCallNone, hp_alice]
                rw [hl, hrec_after, hst'_eval]
                rfl
              intro g ss vis hex_post hnrc_post
              obtain ⟨τ_post, ms_post, hex_post_cli, hnrc_post_cli, htr_post, _, _, _⟩ :=
                hInv hwf hS hfit hex_post hnrc_post
              have hc_post := explainsCli_toClean hex_post_cli hnrc_post_cli
              have hrole_post : Symbolic.Swarm.CREF.RoleSnapshots r (runTrace r ss) :=
                htr_post ▸ ((hlive'.cutRel τ_post ⟨g, ms_post, hex_post_cli, hnrc_post_cli⟩).1.clean
                  g ms_post hc_post).1.2.2.2
              exact Symbolic.Proofs.Swarm.UA.BI.G.RecvStep.aliceRecordPendingInSession_of_alice_canon
                hwf hev_cmd hp_alice rfl hev_in hex_post hrole_post hrec_alice_out hwrc
            · have hrec_alice_bob : t_clean'.leakRecords r r.alice = t_clean.leakRecords r r.alice :=
                leakRecords_alice_eq_of_bob_call hwf hp_bob hsim hsim'
              exact Symbolic.Proofs.Swarm.UA.BI.G.RecvStep.aliceRecordPendingInSession_whisper_same_record
                hwf hev_cmd (fun ha _ => absurd (ha.symm.trans hp_bob) hwf.1) hrec_alice_bob hap_pre
          exact Or.inr ⟨hlive', hap_post,
            ⟨g₁_g, ss_star ++ ext_g.map Step.network ++ [m_g], vis₁_g, hex₁_g, hnrc₁_g⟩⟩

end Symbolic.Proofs.Swarm.UA.BI.G.SlotRecvW
