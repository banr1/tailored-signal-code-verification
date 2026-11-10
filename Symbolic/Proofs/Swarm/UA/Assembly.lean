/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
import Symbolic.Proofs.Swarm.CREF.Cli.World.InitPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.UA.Base

/-!
# CLI Model Refinement Trace Assembly

Whole-trace induction over `CliTracesClassical`: routes guarded CLI calls through the per-command
slot lemmas (`uaSlot_dispatch`) and preserves `PqTurnSim1A` and `UAInv` across trace prefixes
(`uaTraces_refines`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.Assembly

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
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
open Symbolic.Swarm.CREF.CliPure (clearSession_leakRecords cliInit_leakRecords_eq_none)
open Symbolic.Proofs.Swarm.UA.Defs (AliceRecordPendingInSession UAInv UASlotPost UALeakSpec UASlotInitSpec UASlotSendSpec
  UASlotRecvWSpec UASlotRpkNOSpec UASlotRpkPromSpec UAInitWSpec UAXportSpec SchedFits callsOf
  flatEvents)
open Symbolic.Proofs.Swarm.UA.Base (callsOf_append callsOf_leaks schedFits_of_append
  schedFits_exists flatEvents_nil collisionAtCli_append runRejected_none explains_snoc_rejected)

/-- Routes a guarded CLI call that exits with `code` to the corresponding `UASlot*Spec`. -/
theorem uaSlot_dispatch
    (hSlotInit : UASlotInitSpec) (hSlotSend : UASlotSendSpec) (hSlotRecvW : UASlotRecvWSpec)
    (hSlotRpkNO : UASlotRpkNOSpec) (hSlotRpkProm : UASlotRpkPromSpec)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hr : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {evs_pre : List CliEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hnext : ValidCall interp r t c)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files))) :
    UASlotPost interp P r t t_clean c code out files accepted evs_pre := by
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

private theorem callsOf_pre_leaks_run {r : ProtocolSetup} {t : CliTurn} {leaks : List CliEvent}
    (hleaks : LeaksFrom r t leaks) (pre : List CliEvent) (ev : CliEvent) :
    callsOf (pre ++ leaks ++ [ev]) = callsOf pre ++ callsOf [ev] := by
  rw [callsOf_append, callsOf_append, callsOf_leaks hleaks, List.append_nil]

theorem alicePending_init {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : _root_.DY.ExecTrace} {initIds : Option BundlePreKeyIds} :
    AliceRecordPendingInSession interp' r S g tr
      ((CliTurn.init (initDirs interp' r)).leakRecords r) initIds := by
  intro rec _ hrec
  rw [cliInit_leakRecords_eq_none] at hrec
  cases hrec

theorem alicePending_clearSession {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : _root_.DY.ExecTrace} {t : CliTurn} {initIds : Option BundlePreKeyIds} (p : Participant)
    (h : AliceRecordPendingInSession interp' r S g tr (t.leakRecords r) initIds) :
    AliceRecordPendingInSession interp' r S g tr ((t.clearSession r p).leakRecords r) initIds := by
  intro rec sess hrec
  rw [clearSession_leakRecords] at hrec
  by_cases hp : r.alice = p
  · simp [hp] at hrec
  · simp only [hp, ↓reduceIte] at hrec
    exact h rec sess hrec

/-- Whole-trace induction over `CliTracesClassical` extending `UAInv` from an explained prefix
`evs_pre` to `evs_pre ++ evs_suf`. -/
theorem uaTraces_refines
    (hICL : InitClearLeakSpec) (hLeak : UALeakSpec)
    (hSlotInit : UASlotInitSpec) (hSlotSend : UASlotSendSpec) (hSlotRecvW : UASlotRecvWSpec)
    (hSlotRpkNO : UASlotRpkNOSpec) (hSlotRpkProm : UASlotRpkPromSpec)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hr : ProtocolSetupWF r)
    {t : CliTurn} {evs_suf : List CliEvent}
    (htr : CliTracesClassical (PqModelRel interp P) interp r t evs_suf) :
    ∀ (t_clean : CliTurn) (accepted : List HwBytes) (evs_pre : List CliEvent),
      PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted →
      (∀ who ok, SchedFits (callsOf (evs_pre ++ evs_suf)) who ok →
        UAInv (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) who ok
          t_clean accepted evs_pre) →
      (∃ g ss vis, ExplainsClassical (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
          g ss vis (evs_pre ++ evs_suf)) ∨
        CollisionAfterExplainedPrefixClassical (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
          (evs_pre ++ evs_suf) := by
  induction htr with
  | done _ =>
    intro t_clean accepted evs_pre _ hInv
    rw [List.append_nil] at hInv ⊢
    obtain ⟨who, ok, hfit⟩ := schedFits_exists (callsOf evs_pre)
    rcases hInv who ok hfit with hcol | ⟨_, _, g, ss, vis, hex, _⟩
    · exact Or.inr hcol
    · exact Or.inl ⟨g, ss, vis, hex⟩
  | clear p _ ih =>
    intro t_clean accepted evs_pre hsim hInv
    refine ih (t_clean.clearSession r p) accepted evs_pre
      (pqTurnSim1A_clearSession p hr hsim) fun who ok hfit => ?_
    rcases hInv who ok hfit with hcol | ⟨hlive, hap, hw⟩
    · exact Or.inl hcol
    · exact Or.inr ⟨hICL.2.1 p hlive, fun g ss vis hex hnrc => alicePending_clearSession p
        (hap g ss vis hex hnrc), hw⟩
  | @step t leaks c i code out files evs_rest hleaks hnext hin hRel _ ih =>
    intro t_clean accepted evs_pre hsim hInv
    obtain ⟨t_clean', accepted', hsim', hpost⟩ :=
      uaSlot_dispatch hSlotInit hSlotSend hSlotRecvW hSlotRpkNO hSlotRpkProm
        interp P r hext hagree hr (evs_pre := evs_pre ++ leaks) hsim hnext hin hRel
    have hassoc : evs_pre ++ (leaks ++ .run (runEventOf c (some (code, out))) :: evs_rest) =
        (evs_pre ++ leaks ++ [.run (runEventOf c (some (code, out)))]) ++ evs_rest := by
      simp [List.append_assoc]
    rw [hassoc] at hInv ⊢
    refine ih t_clean' accepted' (evs_pre ++ leaks ++ [.run (runEventOf c (some (code, out)))])
      hsim' fun who ok hfit => ?_
    have hfit_run : SchedFits (callsOf (evs_pre ++ leaks ++
        [.run (runEventOf c (some (code, out)))])) who ok := by
      rw [callsOf_append] at hfit
      exact schedFits_of_append hfit
    have hfit_pre : SchedFits (callsOf evs_pre) who ok := by
      rw [callsOf_pre_leaks_run hleaks] at hfit_run
      exact schedFits_of_append hfit_run
    exact hpost who ok hfit_run
      (hLeak interp P r hext hagree hr hsim hleaks hfit_pre (hInv who ok hfit))
  | @stop t leaks c i o hleaks _ _ _ _ =>
    intro t_clean accepted evs_pre hsim hInv
    obtain ⟨who, ok, hfit⟩ :=
      schedFits_exists (callsOf (evs_pre ++ (leaks ++ [.run (runEventOf c none)])))
    have hfit_pre : SchedFits (callsOf evs_pre) who ok := by
      rw [callsOf_append] at hfit
      exact schedFits_of_append hfit
    have hInv' := hLeak interp P r hext hagree hr hsim hleaks hfit_pre (hInv who ok hfit)
    rw [← List.append_assoc]
    rcases hInv' with hcol | ⟨_, _, g, ss, vis, hex, _⟩
    · exact Or.inr (collisionAtCli_append _ hcol)
    · exact Or.inl ⟨g, ss, vis, explains_snoc_rejected (runRejected_none c) hex⟩

end Symbolic.Proofs.Swarm.UA.Assembly
