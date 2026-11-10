/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.CBadG2.Frame
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.CBadG2.Stamps
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.UA.PendingPreKey
import Symbolic.Proofs.Swarm.UA.SlotInitTransfer
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Helpers for Bob's Non-Promote Pre-Key `recv` Slot

Provides `recv` schedule/flattening lemmas, bridges between move-level and step-level pre-key
predicates, `¬ ReadCollisionCliClassical` preservation across non-decrypting step extensions,
and `AliceRecordPendingInSession` preservation across Bob's `recv` calls.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.SlotRpkNOHelpers

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Traceful ExecTraceTypes)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (RunEvent CliEvent)
open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed (ComposedEvent reachability)
open _root_.DY.Libsignal.Composed.Refinement (ProtocolSetup Ghost OpaqueSymbolSemantics Step VisEntry Move
  BundlePreKeyIds activeBundleIds
  ProtocolSetupWF ExplainsClassical MatchesEventsClassical MatchesEventsClassicalAt
  RunMatches RunRejected ModelRunWF StepsWF
  pendingPreKey runSteps runTrace setupTrace PreKeyFields PreKeyRep parsePreKeyWire
  KnownBaseKey KnownBaseKeyOn preKeyRepresentations preKeyRepresentationsOn
  RecvCollisionOn BobSessionStartCollidesOrImplicitRejects BobSessionStartCollidesOrImplicitRejectsOn MemoCollisionOn
  runTraceMoves runVis honestSalts honestSaltsOf prefixTerms plaintextTerms callStarts)
open _root_.DY.Libsignal.Composed.Refinement.Cli (CliTurn CliCall DirectorySnapshot runEventOf
  cliEntryEvents cliExitEvents ReadCollisionCliClassical peerOf)
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3 (PqTurnSim1A)
open _root_.DY.Libsignal.PQXDH (PQXDHEvent BobKeyHandles PreKeyMsgHandles)
open _root_.DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg isCurrentSnapshot)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.SignalSession (Address)
open Symbolic.Swarm.COMPOSED.CompTrace (NetEntry RndEntry NetE RndE TREntry PQXDHEntry CEntry
  TRStEntry at?_le_some at?_append_cases proj_inj_eq Preserves)
open Symbolic.Swarm.CREF (CBadSigmaFrame
  bks_lt_length_of_at? bks_getEventAt_of_le bks_lt_length_of_getEventAt
  bks_getLocalState_of_stored bks_stored_of_getLocalState isCurrentSnapshot_of_le_of_lt
  TR.setupTrace_reachable TR.FreshSigma.traceEntriesLt_of_reachable)
open Symbolic.Proofs.Swarm.UA.Defs (AlicePendingKeysOn AliceRecordPendingInSession
  SchedFits callsOf flatEvents failedSend)
open Symbolic.Proofs.Swarm.UA.Base (callsOf_append callsOf_run_call schedFits_of_append
  flatEvents_append flatEvents_run_call failedSend_runEventOf callStarts_flatEvents_length
  ghostWF_of_append modelRunWF_of_append readCollisionCli_append runSteps_append runTrace_append)
open Symbolic.Proofs.Swarm.UA.SlotInitTransfer (runSteps_le runSteps_reachable stepsWF_append_iff
  matchesEvents_visStampsLt matchesEvents_transfer recvCollisionOn_transfer)

cref_hide_foreign_instances

/-! ## Schedule and Pre-Key Predicate Bridges -/

/-- Schedule and event-flattening consequences for any `recv` call `c`. -/
theorem schedFits_recv_call {c : CliCall} {peer : Address} {code : Nat} {out : HwBytes}
    {evs_pre : List CliEvent} {who : List Participant} {ok : Nat → Bool}
    (hcmd : c.cmd = .recv peer)
    (hfit : SchedFits (callsOf (evs_pre ++ [.run (runEventOf c (some (code, out)))])) who ok) :
    SchedFits (callsOf evs_pre) who ok ∧
      who[(callStarts (flatEvents evs_pre)).length]? = some c.party ∧
      ok (callStarts (flatEvents evs_pre)).length = decide (code = 0) ∧
      flatEvents (evs_pre ++ [.run (runEventOf c (some (code, out)))]) =
        flatEvents evs_pre ++ (cliEntryEvents c ++ cliExitEvents c code out) := by
  let ev := runEventOf c (some (code, out))
  have hfs : failedSend ev = false := by
    refine Bool.eq_false_iff.mpr fun h => ?_
    obtain ⟨⟨_, hsend⟩, _⟩ := (failedSend_runEventOf c code out).mp h
    rw [hcmd] at hsend
    cases hsend
  have hcalls_ev : callsOf [.run ev] = [(c.party, decide (code = 0))] :=
    callsOf_run_call c code out hfs
  have hcalls : callsOf (evs_pre ++ [.run ev]) = callsOf evs_pre ++ [(c.party, decide (code = 0))] := by
    rw [callsOf_append, hcalls_ev]
  have hfit' : SchedFits (callsOf evs_pre ++ [(c.party, decide (code = 0))]) who ok :=
    hcalls ▸ hfit
  have hfit_pre : SchedFits (callsOf evs_pre) who ok := schedFits_of_append hfit'
  have hk_eq : (callStarts (flatEvents evs_pre)).length = (callsOf evs_pre).length :=
    callStarts_flatEvents_length evs_pre
  have hwho_k : who[(callStarts (flatEvents evs_pre)).length]? = some c.party := by
    rw [hk_eq]
    obtain ⟨rest, hwho_eq⟩ := hfit'.1
    have hmap : ((callsOf evs_pre ++ [(c.party, decide (code = 0))]).map Prod.fst) =
        (callsOf evs_pre).map Prod.fst ++ [c.party] := by simp
    rw [hmap, List.append_assoc] at hwho_eq
    rw [← hwho_eq, List.getElem?_append_right (by simp), List.length_map, Nat.sub_self]
    rfl
  have hok_k : ok (callStarts (flatEvents evs_pre)).length = decide (code = 0) := by
    rw [hk_eq]
    exact hfit'.2 (callsOf evs_pre).length c.party (decide (code = 0)) (by simp)
  have hflat_ev : flatEvents [.run ev] = cliEntryEvents c ++ cliExitEvents c code out :=
    flatEvents_run_call c code out hfs
  have hflat : flatEvents (evs_pre ++ [.run ev]) =
      flatEvents evs_pre ++ (cliEntryEvents c ++ cliExitEvents c code out) := by
    rw [flatEvents_append, hflat_ev]
  exact ⟨hfit_pre, hwho_k, hok_k, hflat⟩

/-- `preKeyRepresentations` on moves equals `preKeyRepresentationsOn` on `runTrace r ss` when
`runTraceMoves r ms = runTrace r ss`. -/
theorem preKeyRepresentations_iff_on {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {ss : List Step} {b : HwBytes} {x : PreKeyRep}
    (htr : runTraceMoves r ms = runTrace r ss) :
    x ∈ preKeyRepresentations interp r S g ms b ↔
      x ∈ preKeyRepresentationsOn interp r S g (runTrace r ss) b := by
  unfold preKeyRepresentations preKeyRepresentationsOn
  rw [htr]

/-- `KnownBaseKey` on moves equals `KnownBaseKeyOn` on `runTrace r ss` when
`runTraceMoves r ms = runTrace r ss`. -/
theorem knownBaseKey_iff_on {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {ss : List Step} {p : PreKeyFields}
    (htr : runTraceMoves r ms = runTrace r ss) :
    KnownBaseKey interp r S g ms p ↔ KnownBaseKeyOn interp S g (runTrace r ss) p := by
  unfold KnownBaseKey KnownBaseKeyOn
  rw [htr]

/-- `BobSessionStartCollidesOrImplicitRejects` on moves equals
`BobSessionStartCollidesOrImplicitRejectsOn` on `(runTrace r ss, vis, honestSaltsOf r ss)` under
trace, salt, `prefixTerms`, and `plaintextTerms` agreement. -/
theorem bobStartCollision_iff_on {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {ss : List Step} {vis : List VisEntry}
    {p : PreKeyFields} {x : PreKeyRep}
    (htr : runTraceMoves r ms = runTrace r ss)
    (hsalts : honestSalts r ms = honestSaltsOf r ss)
    (hpre : prefixTerms r (runTrace r ss) (runVis r ms) = prefixTerms r (runTrace r ss) vis)
    (hpt : plaintextTerms (runVis r ms) = plaintextTerms vis) :
    BobSessionStartCollidesOrImplicitRejects interp r S g ms p x ↔
      BobSessionStartCollidesOrImplicitRejectsOn interp r S g (runTrace r ss) vis (honestSaltsOf r ss) p x := by
  have hmemo : ∀ (new pts : List _root_.DY.Bytes),
      MemoCollisionOn interp r S g (fun u => u.AttackerKnows (runTrace r ss))
        (runTrace r ss) (runVis r ms) new pts ↔
      MemoCollisionOn interp r S g (fun u => u.AttackerKnows (runTrace r ss))
        (runTrace r ss) vis new pts := by
    intro new pts
    unfold MemoCollisionOn
    rw [hpre, hpt]
  unfold BobSessionStartCollidesOrImplicitRejects BobSessionStartCollidesOrImplicitRejectsOn
  dsimp only
  rw [htr, hsalts]
  cases parseTrSignalMsg x.msg with
  | none => exact hmemo _ _
  | some msg => exact or_congr (hmemo _ _) Iff.rfl

/-! ## `MatchesEventsClassical` Non-Invisible Step Count and `¬ ReadCollisionCliClassical` Transfer -/

private def isNonInv (s : Step) : Bool :=
  match s.cls with
  | .invisible => false
  | _ => true

private def activeEvCount : List CliEvent → Nat
  | [] => 0
  | .run ev :: evs =>
    (match ev.exit with | some (0, _) => 1 | _ => 0) + activeEvCount evs
  | .env _ :: evs => 1 + activeEvCount evs

private theorem filter_isNonInv_invisible :
    ∀ {ss : List Step}, (∀ s ∈ ss, s.cls = .invisible) → ss.filter isNonInv = []
  | [], _ => rfl
  | s :: ss, h => by
    have hs : isNonInv s = false := by
      unfold isNonInv
      rw [h s List.mem_cons_self]
    rw [List.filter_cons_of_neg (by simp [hs])]
    exact filter_isNonInv_invisible fun s' hs' => h s' (List.mem_cons_of_mem s hs')

private theorem matchesEvents_nonInv_length {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
    {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsClassicalAt interp r S g initIds tr ss evs vis) :
    (ss.filter isNonInv).length = activeEvCount evs := by
  induction hme with
  | nil hinv =>
    simp [filter_isNonInv_invisible hinv, activeEvCount]
  | @run0 _ _ pre ss' ev evs' _ hpre hrej _ ih =>
    have hex_zero : (match ev.exit with | some (0, _) => 1 | _ => 0) = 0 := by
      rcases hex : ev.exit with _ | ⟨code, out⟩
      · rfl
      · rcases Nat.eq_zero_or_pos code with rfl | hpos
        · exact absurd hex (hrej out)
        · have hne : code ≠ 0 := Nat.ne_of_gt hpos
          simp [hne]
    rw [List.filter_append, filter_isNonInv_invisible hpre, List.nil_append, ih]
    simp [activeEvCount, hex_zero]
  | @run1 _ _ pre s ss' ev evs' _ _ hpre hrm _ ih =>
    have hs : isNonInv s = true := by
      unfold isNonInv
      rw [hrm.1]
    obtain ⟨out, hexit⟩ := hrm.2.2.2.2.2.1
    rw [List.filter_append, filter_isNonInv_invisible hpre, List.nil_append,
      List.filter_cons_of_pos hs, List.length_cons, ih]
    simp [activeEvCount, hexit]
    omega
  | @env _ _ pre s ss' ev evs' _ _ hpre hem _ ih =>
    have hs : isNonInv s = true := by
      cases ev with
      | leak _ _ => unfold isNonInv; rw [hem.1]
      | _ => cases hem
    rw [List.filter_append, filter_isNonInv_invisible hpre, List.nil_append,
      List.filter_cons_of_pos hs, List.length_cons, ih]
    simp [activeEvCount]
    omega

/-- Appending a `recv` event explained by non-decrypting steps `δ` preserves
`¬ ReadCollisionCliClassical` without requiring `¬ AcceptRecv`, covering both rejected runs
(`δ = []`) and accepting `Step.bobStart` runs. -/
theorem not_readCollisionCli_snoc_noDecrypt_any {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g₀ g' : Ghost} {ts : Nat} {ss₀ δ : List Step} {vis₀ : List VisEntry}
    {evs_pre : List CliEvent} {ev₀ : RunEvent}
    (hfr : CBadSigmaFrame g₀ g' ts)
    (hwf₀ : ModelRunWF r ss₀)
    (hme₀ : MatchesEventsClassical interp r S g₀ (setupTrace r) ss₀ evs_pre vis₀)
    (hlen₀ : (runTrace r ss₀).length ≤ ts)
    (hδ : ∀ x ∈ δ, x.decryptMsgIdx? = none)
    (hnrc₀ : ¬ ReadCollisionCliClassical interp r S g₀ ss₀ evs_pre) :
    ¬ ReadCollisionCliClassical interp r S g' (ss₀ ++ δ) (evs_pre ++ [.run ev₀]) := by
  rintro ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t,
    hevs, hss, ⟨peer, hcmd⟩, hexit, hbody, hme₁, hdec, hsent, hcol⟩
  have hilt : ss₁.length < ss₀.length := by
    by_contra hge
    have hle : ss₀.length ≤ ss₁.length := Nat.le_of_not_lt hge
    have hget : (ss₀ ++ δ)[ss₁.length]? = (ss₁ ++ m :: ss₂)[ss₁.length]? :=
      congrArg (·[ss₁.length]?) hss
    rw [List.getElem?_append_right hle, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self] at hget
    have hm_in : m ∈ δ := List.mem_of_getElem? hget
    rw [hδ m hm_in] at hdec
    cases hdec
  obtain ⟨k, hk⟩ : ∃ k, ss₀.length - ss₁.length = k + 1 := ⟨ss₀.length - ss₁.length - 1, by omega⟩
  have hss₀ : ss₀ = ss₁ ++ m :: ss₂.take k := by
    have htake := congrArg (List.take ss₀.length) hss
    rw [List.take_left, List.take_append,
      List.take_of_length_le (Nat.le_of_lt hilt), hk, List.take_succ_cons] at htake
    exact htake
  have hevs₂_ne : evs₂ ≠ [] := by
    intro hnil
    subst hnil
    have hevs_eq : evs_pre = evs₁ := List.append_inj_left' hevs rfl
    subst hevs_eq
    have hcnt₀ := matchesEvents_nonInv_length hme₀
    have hcnt₁ := matchesEvents_nonInv_length hme₁
    have hm_nonInv : isNonInv m = true := by
      cases m <;> simp [Step.decryptMsgIdx?, isNonInv, Step.cls] at hdec ⊢
    rw [hss₀, List.filter_append, List.filter_cons_of_pos hm_nonInv,
      List.length_append, List.length_cons] at hcnt₀
    omega
  have hevs_pre : evs_pre = evs₁ ++ .run ev :: evs₂.dropLast := by
    have hsplit : evs₁ ++ .run ev :: evs₂ =
        (evs₁ ++ .run ev :: evs₂.dropLast) ++ [evs₂.getLast hevs₂_ne] := by
      have hlast := (List.dropLast_append_getLast hevs₂_ne).symm
      calc evs₁ ++ .run ev :: evs₂
          = evs₁ ++ (.run ev :: (evs₂.dropLast ++ [evs₂.getLast hevs₂_ne])) := by rw [← hlast]
        _ = (evs₁ ++ .run ev :: evs₂.dropLast) ++ [evs₂.getLast hevs₂_ne] := by simp
    exact List.append_inj_left' (hevs.trans hsplit) rfl
  have hfr_symm : CBadSigmaFrame g' g₀ ts := ⟨fun i hi n => (hfr.1 i hi n).symm, hfr.2.symm⟩
  have hReach_setup : (setupTrace r).Reachable reachability := TR.setupTrace_reachable r
  have hwf₁ : StepsWF ss₁ (setupTrace r) := by
    have hwf_all := hwf₀.2.2.1
    rw [hss₀] at hwf_all
    exact ((stepsWF_append_iff ss₁ (m :: ss₂.take k) (setupTrace r)).mp hwf_all).1
  have hReach₁ : (runTrace r ss₁).Reachable reachability :=
    runSteps_reachable ss₁ hReach_setup hwf₁
  have hle_tr : runTrace r ss₁ ≤ runTrace r ss₀ := by
    rw [hss₀, runTrace_append]
    exact runSteps_le (m :: ss₂.take k) (runTrace r ss₁)
  have hlen₁ : (runTrace r ss₁).length ≤ ts :=
    Nat.le_trans (_root_.DY.Trace.length_le _ _ hle_tr) hlen₀
  have hme₁_0 : MatchesEventsClassical interp r S g₀ (setupTrace r) ss₁ evs₁ vis₁ :=
    matchesEvents_transfer hfr_symm hme₁ hReach_setup hwf₁ hlen₁
  have htr₁' := TR.FreshSigma.traceEntriesLt_of_reachable interp S g' ts hReach₁ hlen₁
  have hvis₁' := matchesEvents_visStampsLt hme₁ hReach_setup hwf₁ hlen₁ htr₁'
  have ht' := Symbolic.Swarm.CREF.cbadG2_stampsLt_getMessageSentAt_of_entries htr₁' hsent
  have hcol_0 : RecvCollisionOn interp r S g₀ (runTrace r ss₁) vis₁ (honestSaltsOf r ss₁) t :=
    recvCollisionOn_transfer hfr_symm hReach₁ hlen₁ hvis₁' ht' hcol
  exact hnrc₀ ⟨evs₁, ev, evs₂.dropLast, ss₁, ss₂.take k, m, vis₁, msgIdx, out, b, t,
    hevs_pre, hss₀, ⟨peer, hcmd⟩, hexit, hbody, hme₁_0, hdec, hsent, hcol_0⟩

/-! ## `AliceRecordPendingInSession` Preservation Across Bob `recv` Runs -/

/-- Any clean explanation `(g, ss, vis)` of `evs_pre ++ [.run ev]` for a Bob `recv` call `c`
preserves `AliceRecordPendingInSession` across `CliTurn.after`. -/
theorem aliceRecordPendingInSession_bob_recv {interp' : ExternInterpretation}
    {P : PEParams} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {t t_clean t_clean' : CliTurn} {c : CliCall}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot} {accepted accepted' : List HwBytes}
    {evs_pre : List CliEvent} {peer : Address}
    (hwf : ProtocolSetupWF r)
    (hbob : c.party = r.bob)
    (hcmd : c.cmd = .recv peer)
    (hsim : PqTurnSim1A interp' P r t t_clean accepted)
    (hsim' : PqTurnSim1A interp' P r (CliTurn.after t r c code out files) t_clean' accepted')
    (hpre_pend : ∀ g ss vis, ExplainsClassical interp' r S g ss vis evs_pre →
      ¬ ReadCollisionCliClassical interp' r S g ss evs_pre →
      AliceRecordPendingInSession interp' r S g (runTrace r ss) (t_clean.leakRecords r)
        (activeBundleIds evs_pre)) :
    let ev := runEventOf c (some (code, out))
    ∀ g ss vis, ExplainsClassical interp' r S g ss vis (evs_pre ++ [.run ev]) →
      ¬ ReadCollisionCliClassical interp' r S g ss (evs_pre ++ [.run ev]) →
      AliceRecordPendingInSession interp' r S g (runTrace r ss) (t_clean'.leakRecords r)
        (activeBundleIds (evs_pre ++ [.run ev])) := by
  intro ev g ss vis hex hnrc
  have hrec_eq : t_clean'.leakRecords r r.alice = t_clean.leakRecords r r.alice := by
    rw [CliTurn.leakRecords_eq_records_of_bobOff_false hsim'.clean_bobOff,
        CliTurn.leakRecords_eq_records_of_bobOff_false hsim.clean_bobOff]
    unfold CliTurn.records
    have hdirs' : t_clean'.dirs r.alice = (CliTurn.after t r c code out files).dirs r.alice :=
      hsim'.dirs_other r.alice hwf.1
    have hafter : (CliTurn.after t r c code out files).dirs r.alice = t.dirs r.alice := by
      simp [CliTurn.after, hbob, hwf.1]
    have hdirs : t_clean.dirs r.alice = t.dirs r.alice :=
      hsim.dirs_other r.alice hwf.1
    rw [hdirs', hafter, ← hdirs]
  have hevs : ∀ ev', .run ev' ∈ ([.run ev] : List CliEvent) →
      (∀ p d, ev'.cmd ≠ .init p d) ∧
      (ev'.party = r.alice → ∀ p out', ev'.cmd = .recv p → ev'.exit ≠ some (0, out')) := by
    intro ev' hev'
    rcases List.mem_singleton.mp hev' with h_eq
    injection h_eq with h_ev; subst h_ev
    have hcmd_ev : ev.cmd = .recv peer := hcmd
    have hparty_ev : ev.party = r.bob := hbob
    exact ⟨fun p d hc => (by rw [hcmd_ev] at hc; cases hc),
      fun ha => absurd (ha.symm.trans hparty_ev) hwf.1⟩
  exact Symbolic.Proofs.Swarm.UA.PendingPreKey.aliceRecordPendingInSession_of_explains_append
    hwf hex hnrc hevs hrec_eq (fun ss₁ vis₁ => hpre_pend g ss₁ vis₁)

end Symbolic.Proofs.Swarm.UA.SlotRpkNOHelpers
