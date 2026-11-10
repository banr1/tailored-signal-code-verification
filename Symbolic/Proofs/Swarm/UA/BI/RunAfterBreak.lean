/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.BI.RAB.Defs
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L01InitClearLeak
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L02GoodExit0Cut
import Symbolic.Proofs.Swarm.UA.Assembly
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.UA.ClassicalBridge
import Symbolic.Proofs.Swarm.UA.InitW

/-!
# Whole-Trace Run-After-Break Refinement Induction

Proves `uaTracesB_refines`, `refines_all_of_specs`, and `refines_run_after_break_of_specs` by
induction over `CliTraces` (including `breakInvert` steps), maintaining `UAInvB` and transporting
the final conclusion from `interpOfParams interp P` back to `interp` via `UAXportSpecB`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.RunAfterBreak

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.SignalSession (Inputs)
open Symbolic.Swarm.CREF (compSemOf compSemOf_ready SemReady)
open Symbolic.Swarm.CREF.Cli (interpOfParams initDirs_interpOfParams)
open Symbolic.Swarm.Coinsplit.Lift (InitClearLeakSpec)
open Symbolic.Proofs.Swarm.UA.Defs (flatEvents callsOf SchedFits)
open Symbolic.Proofs.Swarm.UA.Base (callsOf_append callsOf_leaks schedFits_of_append
  schedFits_exists flatEvents_nil runRejected_none)
open Symbolic.Proofs.Swarm.UA.Assembly (alicePending_init alicePending_clearSession)
open Symbolic.Proofs.Swarm.UA.ClassicalBridge (breakFree_nil explains_of_classical
  readCollisionCliClassical_of)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Defs (UAInvB UASlotPostB UALeakSpecB UAEnvSpecB
  UASlotInitSpecB UASlotSendSpecB UASlotRecvWSpecB UASlotRpkNOSpecB UASlotRpkPromSpecB
  UAInitWSpecB UAXportSpecB)

/-! ## Trace list helpers -/

private theorem collisionAtCli_append_B {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {evs : List CliEvent} (more : List CliEvent) (h : CollisionAfterExplainedPrefix interp r S evs) :
    CollisionAfterExplainedPrefix interp r S (evs ++ more) := by
  obtain ⟨evs₁, ev, evs₂, g, ss, vis, heq, hrest⟩ := h
  exact ⟨evs₁, ev, evs₂ ++ more, g, ss, vis, by simp [heq], hrest⟩

private theorem matchesEventsAt_snoc_rejected_B {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds} {ev : RunEvent}
    (hrej : RunRejected ev) {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEventsAt interp r S g initIds tr ss evs vis) :
    MatchesEventsAt interp r S g initIds tr ss (evs ++ [.run ev]) vis := by
  induction h with
  | @nil initIds tr ss hinv =>
    have h0 : MatchesEventsAt interp r S g initIds tr (ss ++ []) [.run ev] [] :=
      .run0 hinv hrej (.nil (by simp))
    simpa using h0
  | run1 hpre hrm _ ih => exact .run1 hpre hrm ih
  | run0 hpre hrej' _ ih => exact .run0 hpre hrej' ih
  | env hpre hem _ ih => exact .env hpre hem ih

private theorem matchesEvents_snoc_rejected_B {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ev : RunEvent} (hrej : RunRejected ev) {tr : ExecTrace}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEvents interp r S g tr ss evs vis) :
    MatchesEvents interp r S g tr ss (evs ++ [.run ev]) vis :=
  matchesEventsAt_snoc_rejected_B hrej h

private theorem explains_snoc_rejected_B {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs : List CliEvent} {ev : RunEvent}
    (hrej : RunRejected ev) (h : Explains interp r S g ss vis evs) :
    Explains interp r S g ss vis (evs ++ [.run ev]) :=
  ⟨h.1, h.2.1, h.2.2.1, matchesEvents_snoc_rejected_B hrej h.2.2.2⟩

private theorem invertsGuarded_prefix_B {interp : ExternInterpretation} {r : ProtocolSetup}
    {evs more : List CliEvent} (h : InvertsGuarded interp r (evs ++ more)) :
    InvertsGuarded interp r evs := by
  intro pre post e heq
  exact h pre (post ++ more) e (by rw [heq]; simp)

private theorem callsOf_pre_leaks_run_B {r : ProtocolSetup} {t : CliTurn} {leaks : List CliEvent}
    (hleaks : LeaksFrom r t leaks) (pre : List CliEvent) (ev : CliEvent) :
    callsOf (pre ++ leaks ++ [ev]) = callsOf pre ++ callsOf [ev] := by
  rw [callsOf_append, callsOf_append, callsOf_leaks hleaks, List.append_nil]

/-! ## Base case and call dispatch -/

/-- The empty event list has a clean explanation under any well-formed setup and ready semantics. -/
theorem init_w_b : UAInitWSpecB := by
  intro interp' r S hr hS
  obtain ⟨g, ss, vis, hex, hnrc⟩ := Symbolic.Proofs.Swarm.UA.InitW.init_w hr hS
  exact ⟨g, ss, vis, explains_of_classical hex,
    fun hrc => hnrc (readCollisionCliClassical_of hrc breakFree_nil)⟩

/-- Dispatches a guarded CLI call that exits with `code` to the matching call-slot specification. -/
theorem uaSlot_dispatch_B
    (hSlotInit : UASlotInitSpecB) (hSlotSend : UASlotSendSpecB) (hSlotRecvW : UASlotRecvWSpecB)
    (hSlotRpkNO : UASlotRpkNOSpecB) (hSlotRpkProm : UASlotRpkPromSpecB)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hr : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {evs_pre : List CliEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hnext : ValidCall interp r t c)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files))) :
    UASlotPostB interp P r t t_clean c code out files accepted evs_pre := by
  obtain ⟨hcoins, hsb, hfb, hbca, hguard⟩ := hnext
  cases hm : c.cmd with
  | init peer dir =>
    rw [hm] at hcoins hguard
    obtain ⟨halice, rfl, rfl, hstdin, hrec_none, hflat, hhon⟩ := hguard
    exact hSlotInit interp P r hext hagree hr hsim halice hm hstdin hcoins
      hrec_none hflat hhon hin hRel
  | send peer =>
    have hsb' : c.stdin.length < 2 ^ 32 := by simpa [StdinBounded, hm] using hsb
    rw [hm] at hcoins hguard
    obtain ⟨hp, rfl, hbun, hsent, hrec_ne⟩ := hguard
    exact hSlotSend interp P r hext hagree hr hsim hp hm hbun hcoins hsb'
      hfb hbca hsent hrec_ne hin hRel
  | recv peer =>
    have hcoins' : c.coins.length = 32 := by simpa [hm, coinsLen] using hcoins
    have hguard' := hguard
    rw [hm] at hguard'
    obtain ⟨hp, rfl, hbun, hdisj⟩ := hguard'
    rcases hdisj with ⟨hrec_ne, body, hstdin, hpqh_w⟩ | ⟨hbob, hkind, hpqh⟩
    · have hbody_lt : body.length < 2 ^ 32 := by
        unfold StdinBounded at hsb; rw [hm] at hsb
        exact hsb.1 body hstdin
      exact hSlotRecvW interp P r hext hagree hr hsim hp hm hbun hcoins'
        hstdin hbody_lt hfb hbca hrec_ne hpqh_w hin hRel
    · by_cases hprom_ex :
        ∃ rec_ q, t.records r r.bob = some rec_ ∧
          parsePreKeyWire c.stdin = some q ∧ EligibleForSessionPromotion rec_ c.stdin
      · obtain ⟨rec_, q, hrec_bob, hq, hprom⟩ := hprom_ex
        exact hSlotRpkProm interp P r hext hagree hr hsim hbob (hbob ▸ hm) hbun hcoins'
          hsb hfb hbca hrec_bob hq hprom hpqh hin hRel
      · have hno_prom : ∀ rec_ q, t.records r r.bob = some rec_ →
            parsePreKeyWire c.stdin = some q → ¬ EligibleForSessionPromotion rec_ c.stdin :=
          fun rec_ q hrec hq hp => hprom_ex ⟨rec_, q, hrec, hq, hp⟩
        exact hSlotRpkNO interp P r hext hagree hr hsim hbob (hbob ▸ hm) hbun hcoins'
          hsb hfb hbca hkind hpqh hno_prom hin hRel

/-! ## Whole-trace induction -/

/-- Whole-trace induction over `CliTraces` maintaining `UAInvB` across `clear`, `breakInvert`,
`step`, and `stop` transitions. -/
theorem uaTracesB_refines
    (hICL : InitClearLeakSpec) (hLeak : UALeakSpecB) (hEnv : UAEnvSpecB)
    (hSlotInit : UASlotInitSpecB) (hSlotSend : UASlotSendSpecB) (hSlotRecvW : UASlotRecvWSpecB)
    (hSlotRpkNO : UASlotRpkNOSpecB) (hSlotRpkProm : UASlotRpkPromSpecB)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hr : ProtocolSetupWF r)
    {t : CliTurn} {evs_suf : List CliEvent}
    (htr : CliTraces (PqModelRel interp P) interp r t evs_suf) :
    ∀ (t_clean : CliTurn) (accepted : List HwBytes) (evs_pre : List CliEvent),
      InvertsGuarded interp r (evs_pre ++ evs_suf) →
      PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted →
      (∀ who ok, SchedFits (callsOf (evs_pre ++ evs_suf)) who ok →
        UAInvB (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) who ok
          t_clean accepted evs_pre) →
      (∃ g ss vis, Explains (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
          g ss vis (evs_pre ++ evs_suf)) ∨
        CollisionAfterExplainedPrefix (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
          (evs_pre ++ evs_suf) := by
  induction htr with
  | done _ =>
    intro t_clean accepted evs_pre _ _ hInv
    rw [List.append_nil] at hInv ⊢
    obtain ⟨who, ok, hfit⟩ := schedFits_exists (callsOf evs_pre)
    rcases hInv who ok hfit with hcol | ⟨_, _, g, ss, vis, hex, _⟩
    · exact Or.inr hcol
    · exact Or.inl ⟨g, ss, vis, hex⟩
  | clear p _ ih =>
    intro t_clean accepted evs_pre hg hsim hInv
    refine ih (t_clean.clearSession r p) accepted evs_pre hg
      (pqTurnSim1A_clearSession p hr hsim) fun who ok hfit => ?_
    rcases hInv who ok hfit with hcol | ⟨hlive, hap, hw⟩
    · exact Or.inl hcol
    · exact Or.inr ⟨hICL.2.1 p hlive, fun g ss vis hex hnrc => alicePending_clearSession p
        (hap g ss vis hex hnrc), hw⟩
  | @breakInvert t e evs hbi _ ih =>
    intro t_clean accepted evs_pre hg hsim hInv
    have hassoc : evs_pre ++ (CliEvent.env e :: evs) = (evs_pre ++ [.env e]) ++ evs := by simp
    rw [hassoc] at hg hInv ⊢
    refine ih t_clean accepted (evs_pre ++ [.env e]) hg hsim fun who ok hfit => ?_
    have hfit_pre : SchedFits (callsOf evs_pre) who ok := by
      rw [callsOf_append] at hfit
      have h₁ := schedFits_of_append hfit
      rw [callsOf_append] at h₁
      exact schedFits_of_append h₁
    exact hEnv interp P r hext hagree hr hsim hbi (invertsGuarded_prefix_B hg) hfit_pre
      (hInv who ok hfit)
  | @step t leaks c i code out files evs_rest hleaks hnext hin hRel _ ih =>
    intro t_clean accepted evs_pre hg hsim hInv
    obtain ⟨t_clean', accepted', hsim', hpost⟩ :=
      uaSlot_dispatch_B hSlotInit hSlotSend hSlotRecvW hSlotRpkNO hSlotRpkProm
        interp P r hext hagree hr (evs_pre := evs_pre ++ leaks) hsim hnext hin hRel
    have hassoc : evs_pre ++ (leaks ++ .run (runEventOf c (some (code, out))) :: evs_rest) =
        (evs_pre ++ leaks ++ [.run (runEventOf c (some (code, out)))]) ++ evs_rest := by
      simp [List.append_assoc]
    rw [hassoc] at hg hInv ⊢
    refine ih t_clean' accepted' (evs_pre ++ leaks ++ [.run (runEventOf c (some (code, out)))])
      hg hsim' fun who ok hfit => ?_
    have hfit_run : SchedFits (callsOf (evs_pre ++ leaks ++
        [.run (runEventOf c (some (code, out)))])) who ok := by
      rw [callsOf_append] at hfit
      exact schedFits_of_append hfit
    have hfit_pre : SchedFits (callsOf evs_pre) who ok := by
      rw [callsOf_pre_leaks_run_B hleaks] at hfit_run
      exact schedFits_of_append hfit_run
    exact hpost who ok hfit_run
      (hLeak interp P r hext hagree hr hsim hleaks hfit_pre (hInv who ok hfit))
  | @stop t leaks c i o hleaks _ _ _ _ =>
    intro t_clean accepted evs_pre _ hsim hInv
    obtain ⟨who, ok, hfit⟩ :=
      schedFits_exists (callsOf (evs_pre ++ (leaks ++ [.run (runEventOf c none)])))
    have hfit_pre : SchedFits (callsOf evs_pre) who ok := by
      rw [callsOf_append] at hfit
      exact schedFits_of_append hfit
    have hInv' := hLeak interp P r hext hagree hr hsim hleaks hfit_pre (hInv who ok hfit)
    rw [← List.append_assoc]
    rcases hInv' with hcol | ⟨_, _, g, ss, vis, hex, _⟩
    · exact Or.inr (collisionAtCli_append_B _ hcol)
    · exact Or.inl ⟨g, ss, vis, explains_snoc_rejected_B (runRejected_none c) hex⟩

/-- Every guarded CLI trace from the provisioned directories is either explained under
`compSemOf (interpOfParams interp P) r` or suffers a collision after an explained prefix. -/
theorem refines_all_of_specs
    (hICL : InitClearLeakSpec) (hLeak : UALeakSpecB) (hEnv : UAEnvSpecB)
    (hSlotInit : UASlotInitSpecB) (hSlotSend : UASlotSendSpecB) (hSlotRecvW : UASlotRecvWSpecB)
    (hSlotRpkNO : UASlotRpkNOSpecB) (hSlotRpkProm : UASlotRpkPromSpecB)
    (hInitW : UAInitWSpecB) (hX : UAXportSpecB)
    (interp : ExternInterpretation) (hext : ExternContractsHoldCli interp) (P : PEParams)
    (hagree : ModelAgree interp P) (r : ProtocolSetup) (hr : ProtocolSetupWF r) (evs : List CliEvent)
    (htr : CliTraces (PqModelRel interp P) interp r (CliTurn.init (initDirs interp r)) evs)
    (hg : InvertsGuarded interp r evs) :
    (∃ g ss vis, Explains interp r (compSemOf (interpOfParams interp P) r) g ss vis evs) ∨
      CollisionAfterExplainedPrefix interp r (compSemOf (interpOfParams interp P) r) evs := by
  have hS : SemReady (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) :=
    compSemOf_ready _ r hr
  have hdirs_eq : initDirs interp r = initDirs (interpOfParams interp P) r :=
    congrFun (initDirs_interpOfParams interp P).symm r
  rw [hdirs_eq] at htr
  obtain ⟨g₀, ss₀, vis₀, hex₀, hnrc₀⟩ := hInitW hr hS
  have href := uaTracesB_refines hICL hLeak hEnv hSlotInit hSlotSend hSlotRecvW hSlotRpkNO
    hSlotRpkProm interp P r hext hagree hr htr _ [] [] (by rw [List.nil_append]; exact hg)
    (pqTurnSim1A_init hr hagree)
    (fun who ok _ => Or.inr ⟨by rw [flatEvents_nil]; exact hICL.1 hr hS who ok,
      fun _ _ _ _ _ => alicePending_init, g₀, ss₀, vis₀, hex₀, hnrc₀⟩)
  rw [List.nil_append] at href
  rcases href with ⟨g, ss, vis, hex⟩ | hcol
  · exact Or.inl ⟨g, ss, vis, ((hX interp P r _).1 g ss vis evs).mp hex⟩
  · exact Or.inr (((hX interp P r _).2 evs).mp hcol)

/-- Predicate stating that `evs` contains at least one run event after a break or invert event. -/
def RunAfterBreakB (evs : List CliEvent) : Prop :=
  ∃ (pre post : List CliEvent) (e : EnvEvent), evs = pre ++ .env e :: post ∧ e.IsBreakInvert ∧
    ∃ ev : RunEvent, CliEvent.run ev ∈ post

/-- Specialization of `refines_all_of_specs` to traces satisfying `RunAfterBreakB`, discharging
`InitClearLeakSpec` and `UAInitWSpecB`. -/
theorem refines_run_after_break_of_specs
    (hLeak : UALeakSpecB) (hEnv : UAEnvSpecB)
    (hSlotInit : UASlotInitSpecB) (hSlotSend : UASlotSendSpecB) (hSlotRecvW : UASlotRecvWSpecB)
    (hSlotRpkNO : UASlotRpkNOSpecB) (hSlotRpkProm : UASlotRpkPromSpecB) (hX : UAXportSpecB)
    (interp : ExternInterpretation)
    (hext : ExternContractsHoldCli interp) (P : PEParams) (hagree : ModelAgree interp P)
    (r : ProtocolSetup) (hr : ProtocolSetupWF r) (evs : List CliEvent)
    (htr : CliTraces (PqModelRel interp P) interp r (CliTurn.init (initDirs interp r)) evs)
    (hg : InvertsGuarded interp r evs) (_hrab : RunAfterBreakB evs) :
    (∃ g ss vis, Explains interp r (compSemOf (interpOfParams interp P) r) g ss vis evs) ∨
      CollisionAfterExplainedPrefix interp r (compSemOf (interpOfParams interp P) r) evs :=
  refines_all_of_specs
    (Symbolic.Swarm.Coinsplit.Lift.L01.init_clear_leak
      Symbolic.Swarm.Coinsplit.Lift.L02.outcomeFaithfulCli_of_goodExit0Cut)
    hLeak hEnv hSlotInit hSlotSend hSlotRecvW hSlotRpkNO hSlotRpkProm init_w_b hX
    interp hext P hagree r hr evs htr hg

end Symbolic.Proofs.Swarm.UA.BI.RunAfterBreak
