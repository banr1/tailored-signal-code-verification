/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.ClassicalBridge
public import Symbolic.Proofs.Swarm.CREF.Cli.HooksBridge
public import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L01InitClearLeak
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L02GoodExit0Cut
import Symbolic.Proofs.Swarm.UA.Assembly
import Symbolic.Proofs.Swarm.UA.BI.Break
import Symbolic.Proofs.Swarm.UA.BI.InvertDH
import Symbolic.Proofs.Swarm.UA.BI.InvertKEM
import Symbolic.Proofs.Swarm.UA.BI.RAB.Nodes
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.UA.InitW
import Symbolic.Proofs.Swarm.UA.Leak
import Symbolic.Proofs.Swarm.UA.SlotInit
import Symbolic.Proofs.Swarm.UA.SlotRecvW
import Symbolic.Proofs.Swarm.UA.SlotRpkNO
import Symbolic.Proofs.Swarm.UA.SlotRpkProm
import Symbolic.Proofs.Swarm.UA.SlotSend
import Symbolic.Proofs.Swarm.UA.Top
import Symbolic.Proofs.Swarm.UA.XlateInv
import Symbolic.Proofs.Swarm.UA.Xport

/-!
# CLI Refinement with Break and Invert Events

Proves `comp_refines_cli_model_ua_b : CompRefinesCliModel`, extending the classical CLI refinement
to traces containing guarded `breakDH`, `breakKEM`, `invertDH`, and `invertKEM` events by splitting
into passive traces (`¬ RunAfterBreak`) and interleaved traces (`RunAfterBreak`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BreakInvert

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
open CryptoVerification.E2E (PEParams)
open CryptoVerification.SignalSession (Inputs Outcome)
open Symbolic.Swarm.CREF (compSemOf compSemOf_ready SemReady)
open Symbolic.Swarm.CREF.Cli (interpOfParams initDirs_interpOfParams)
open Symbolic.Proofs.Swarm.UA.Defs (flatEvents)
open Symbolic.Proofs.Swarm.UA.Base (flatEvents_nil collisionAtCli_append)
open Symbolic.Proofs.Swarm.UA.Assembly (uaTraces_refines alicePending_init)
open Symbolic.Proofs.Swarm.UA.ClassicalBridge (BreakFree breakFree_nil breakFree_append
  breakFree_run_cons breakFree_of_leaksFrom cliTracesClassical_of_breakFree explains_of_classical
  collisionAtCli_of_classical)

/-- Classical CLI refinement instantiated at `S := compSemOf (interpOfParams interp P) r`. -/
theorem comp_refines_cli_model_classical_at (interp : ExternInterpretation)
    (hext : ExternContractsHoldCli interp) (P : PEParams) (hagree : ModelAgree interp P)
    (r : ProtocolSetup) (hr : ProtocolSetupWF r) (evs : List CliEvent)
    (htr : CliTracesClassical (PqModelRel interp P) interp r (CliTurn.init (initDirs interp r))
      evs) :
    (∃ g ss vis, ExplainsClassical interp r (compSemOf (interpOfParams interp P) r) g ss vis evs) ∨
      CollisionAfterExplainedPrefixClassical interp r (compSemOf (interpOfParams interp P) r) evs := by
  have hICL := Symbolic.Swarm.Coinsplit.Lift.L01.init_clear_leak
    Symbolic.Swarm.Coinsplit.Lift.L02.outcomeFaithfulCli_of_goodExit0Cut
  have hX := Symbolic.Proofs.Swarm.UA.Xport.xport
  have hS : SemReady (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) :=
    compSemOf_ready _ r hr
  have hdirs_eq : initDirs interp r = initDirs (interpOfParams interp P) r :=
    congrFun (initDirs_interpOfParams interp P).symm r
  rw [hdirs_eq] at htr
  obtain ⟨g₀, ss₀, vis₀, hex₀, hnrc₀⟩ := Symbolic.Proofs.Swarm.UA.InitW.init_w hr hS
  have href := uaTraces_refines hICL Symbolic.Proofs.Swarm.UA.Leak.leak_ua
    Symbolic.Proofs.Swarm.UA.SlotInit.slot_init_ua
    Symbolic.Proofs.Swarm.UA.SlotSend.slot_send_ua
    (Symbolic.Proofs.Swarm.UA.SlotRecvW.slot_recvw_ua_of
      Symbolic.Proofs.Swarm.UA.XlateInv.xlate_inv Symbolic.Proofs.Swarm.UA.Top.xlate_exc_w)
    Symbolic.Proofs.Swarm.UA.SlotRpkNO.slot_rpk_no_ua
    (Symbolic.Proofs.Swarm.UA.SlotRpkProm.slot_rpk_prom_ua_of_exc_w
      Symbolic.Proofs.Swarm.UA.Top.xlate_exc_w)
    interp P r hext hagree hr htr _ [] [] (pqTurnSim1A_init hr hagree)
    (fun who ok _ => Or.inr ⟨by rw [flatEvents_nil]; exact hICL.1 hr hS who ok,
      fun _ _ _ _ _ => alicePending_init, g₀, ss₀, vis₀, hex₀, hnrc₀⟩)
  rw [List.nil_append] at href
  rcases href with ⟨g, ss, vis, hex⟩ | hcol
  · exact Or.inl ⟨g, ss, vis, ((hX interp P r _).1 g ss vis evs).mp hex⟩
  · exact Or.inr (((hX interp P r _).2 evs).mp hcol)

/-! ## Trace Splitting -/

/-- Every event in `qs` is a break or invert environment event. -/
def AllBreakInvert (qs : List CliEvent) : Prop :=
  ∀ x ∈ qs, ∃ e : EnvEvent, x = .env e ∧ e.IsBreakInvert

/-- Some run event occurs after a break or invert event. -/
def RunAfterBreak (evs : List CliEvent) : Prop :=
  ∃ (pre post : List CliEvent) (e : EnvEvent), evs = pre ++ .env e :: post ∧ e.IsBreakInvert ∧
    ∃ ev : RunEvent, CliEvent.run ev ∈ post

theorem allBreakInvert_of_noRun {Rel : Inputs → Option Outcome → Prop}
    {interp : ExternInterpretation} {r : ProtocolSetup} {t : CliTurn} {evs : List CliEvent}
    (htr : CliTraces Rel interp r t evs) (hno : ∀ ev : RunEvent, CliEvent.run ev ∉ evs) :
    AllBreakInvert evs := by
  induction htr with
  | done _ => intro x hx; cases hx
  | clear _ _ ih => exact ih hno
  | @breakInvert t e evs hbi _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨e, rfl, hbi⟩
    · exact ih (fun ev hev => hno ev (List.mem_cons_of_mem _ hev)) x hx
  | @step _ leaks c _ code out _ _ _ _ _ _ _ _ =>
    exact absurd (by simp) (hno (runEventOf c (some (code, out))))
  | @stop _ leaks c _ _ _ _ _ _ _ =>
    exact absurd (by simp) (hno (runEventOf c none))

/-- A trace satisfying `¬ RunAfterBreak` decomposes into a `BreakFree` CLI prefix followed by
break and invert events. -/
theorem passive_split {Rel : Inputs → Option Outcome → Prop} {interp : ExternInterpretation}
    {r : ProtocolSetup} {t : CliTurn} {evs : List CliEvent} (htr : CliTraces Rel interp r t evs)
    (hnr : ¬ RunAfterBreak evs) :
    ∃ pre qs, evs = pre ++ qs ∧ BreakFree pre ∧ CliTraces Rel interp r t pre ∧ AllBreakInvert qs := by
  induction htr with
  | done t => exact ⟨[], [], rfl, breakFree_nil, .done t, fun _ hx => by cases hx⟩
  | clear p _ ih =>
    obtain ⟨pre, qs, heq, hbf, htr', hq⟩ := ih hnr
    exact ⟨pre, qs, heq, hbf, .clear p htr', hq⟩
  | @breakInvert t e evs hbi htr' _ =>
    have hno : ∀ ev : RunEvent, CliEvent.run ev ∉ evs := fun ev hev =>
      hnr ⟨[], evs, e, rfl, hbi, ev, hev⟩
    exact ⟨[], .env e :: evs, rfl, breakFree_nil, .done t,
      allBreakInvert_of_noRun (.breakInvert hbi htr') (fun ev hev => by
        rcases List.mem_cons.mp hev with h | h
        · cases h
        · exact hno ev h)⟩
  | @step t leaks c i code out files evs_rest hleak hnext hin hRel _ ih =>
    have hnr' : ¬ RunAfterBreak evs_rest := by
      rintro ⟨pre, post, e, heq, hbi, ev, hev⟩
      exact hnr ⟨leaks ++ .run (runEventOf c (some (code, out))) :: pre, post, e,
        by rw [heq]; simp, hbi, ev, hev⟩
    obtain ⟨pre, qs, heq, hbf, htr', hq⟩ := ih hnr'
    refine ⟨leaks ++ .run (runEventOf c (some (code, out))) :: pre, qs, by rw [heq]; simp,
      breakFree_append.mpr ⟨breakFree_of_leaksFrom hleak, breakFree_run_cons.mpr hbf⟩,
      .step hleak hnext hin hRel htr', hq⟩
  | @stop t leaks c i o hleak hnext hin hRel habort =>
    exact ⟨leaks ++ [.run (runEventOf c none)], [], by simp,
      breakFree_append.mpr ⟨breakFree_of_leaksFrom hleak, breakFree_run_cons.mpr breakFree_nil⟩,
      .stop hleak hnext hin hRel habort, fun _ hx => by cases hx⟩

theorem invertsGuarded_prefix {interp : ExternInterpretation} {r : ProtocolSetup}
    {evs more : List CliEvent} (h : InvertsGuarded interp r (evs ++ more)) :
    InvertsGuarded interp r evs := by
  intro pre post e heq
  exact h pre (post ++ more) e (by rw [heq]; simp)

/-! ## Passive and Interleaved Refinement -/

theorem explains_snoc_breakDH {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs : List CliEvent}
    (h : Explains interp r S g ss vis evs) :
    ∃ g' ss' vis', Explains interp r S g' ss' vis' (evs ++ [.env .breakDH]) := by
  exact Symbolic.Proofs.Swarm.UA.BI.Break.explains_snoc_breakDH h

theorem explains_snoc_breakKEM {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs : List CliEvent}
    (h : Explains interp r S g ss vis evs) :
    ∃ g' ss' vis', Explains interp r S g' ss' vis' (evs ++ [.env .breakKEM]) := by
  exact Symbolic.Proofs.Swarm.UA.BI.Break.explains_snoc_breakKEM h

theorem explains_snoc_invertDH {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs : List CliEvent} {pk sk : HwBytes}
    (hext : ExternContractsHoldCli interp) (hr : ProtocolSetupWF r)
    (h : Explains interp r S g ss vis evs)
    (hg : InvertsGuarded interp r (evs ++ [.env (.invertDH pk sk)])) :
    ∃ g' ss' vis', Explains interp r S g' ss' vis' (evs ++ [.env (.invertDH pk sk)]) := by
  exact Symbolic.Proofs.Swarm.UA.BI.InvertDH.explains_snoc_invertDH hext hr h hg

theorem explains_snoc_invertKEM {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs : List CliEvent} {pk sk : HwBytes}
    (hext : ExternContractsHoldCli interp) (hr : ProtocolSetupWF r)
    (h : Explains interp r S g ss vis evs)
    (hg : InvertsGuarded interp r (evs ++ [.env (.invertKEM pk sk)])) :
    ∃ g' ss' vis', Explains interp r S g' ss' vis' (evs ++ [.env (.invertKEM pk sk)]) := by
  exact Symbolic.Proofs.Swarm.UA.BI.InvertKEM.explains_snoc_invertKEM hext hr h hg

/-- Guarded break and invert events extend `Explains`. -/
theorem explains_append_breakInvert {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (hext : ExternContractsHoldCli interp) (hr : ProtocolSetupWF r) :
    ∀ (qs : List CliEvent) {evs : List CliEvent} {g : Ghost} {ss : List Step} {vis : List VisEntry},
      Explains interp r S g ss vis evs → AllBreakInvert qs → InvertsGuarded interp r (evs ++ qs) →
      ∃ g' ss' vis', Explains interp r S g' ss' vis' (evs ++ qs)
  | [], evs, g, ss, vis, h, _, _ => ⟨g, ss, vis, by rw [List.append_nil]; exact h⟩
  | x :: qs, evs, g, ss, vis, h, hq, hg => by
    obtain ⟨e, rfl, hbi⟩ := hq x (List.mem_cons_self ..)
    have hq' : AllBreakInvert qs := fun y hy => hq y (List.mem_cons_of_mem _ hy)
    have hassoc : evs ++ CliEvent.env e :: qs = (evs ++ [.env e]) ++ qs := by simp
    rw [hassoc] at hg ⊢
    have hg₁ : InvertsGuarded interp r (evs ++ [.env e]) := invertsGuarded_prefix hg
    have h₁ : ∃ g₁ ss₁ vis₁, Explains interp r S g₁ ss₁ vis₁ (evs ++ [.env e]) := by
      cases e with
      | breakDH => exact explains_snoc_breakDH h
      | breakKEM => exact explains_snoc_breakKEM h
      | invertDH pk sk => exact explains_snoc_invertDH hext hr h hg₁
      | invertKEM pk sk => exact explains_snoc_invertKEM hext hr h hg₁
      | leak _ _ => exact hbi.elim
      | registerCorrupt _ _ => exact hbi.elim
    obtain ⟨g₁, ss₁, vis₁, h₁⟩ := h₁
    exact explains_append_breakInvert hext hr qs h₁ hq' hg

/-- Refinement for guarded CLI traces in which a run event occurs after a break or invert event. -/
theorem refines_run_after_break (interp : ExternInterpretation)
    (hext : ExternContractsHoldCli interp) (P : PEParams) (hagree : ModelAgree interp P)
    (r : ProtocolSetup) (hr : ProtocolSetupWF r) (evs : List CliEvent)
    (htr : CliTraces (PqModelRel interp P) interp r (CliTurn.init (initDirs interp r)) evs)
    (hg : InvertsGuarded interp r evs) (hrab : RunAfterBreak evs) :
    (∃ g ss vis, Explains interp r (compSemOf (interpOfParams interp P) r) g ss vis evs) ∨
      CollisionAfterExplainedPrefix interp r (compSemOf (interpOfParams interp P) r) evs := by
  exact Symbolic.Proofs.Swarm.UA.BI.RAB.Nodes.refines_run_after_break_B interp hext P hagree r hr
    evs htr hg hrab

theorem collisionAtCli_append' {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {evs : List CliEvent} (more : List CliEvent) (h : CollisionAfterExplainedPrefix interp r S evs) :
    CollisionAfterExplainedPrefix interp r S (evs ++ more) := by
  obtain ⟨evs₁, ev, evs₂, g, ss, vis, heq, hrest⟩ := h
  exact ⟨evs₁, ev, evs₂ ++ more, g, ss, vis, by simp [heq], hrest⟩

/-- Composed protocol refinement over guarded CLI traces with break and invert events. -/
theorem comp_refines_cli_model_ua_b : CompRefinesCliModel := by
  intro interp hext P hagree r hr
  refine ⟨compSemOf (interpOfParams interp P) r, fun evs htr hg => ?_⟩
  by_cases hrab : RunAfterBreak evs
  · exact refines_run_after_break interp hext P hagree r hr evs htr hg hrab
  obtain ⟨pre, qs, rfl, hbf, htr_pre, hq⟩ := passive_split htr hrab
  rcases comp_refines_cli_model_classical_at interp hext P hagree r hr pre
      (cliTracesClassical_of_breakFree htr_pre hbf) with ⟨g, ss, vis, hex⟩ | hcol
  · exact Or.inl (explains_append_breakInvert hext hr qs (explains_of_classical hex) hq hg)
  · exact Or.inr (collisionAtCli_append' qs (collisionAtCli_of_classical hbf hcol))

end Symbolic.Proofs.Swarm.UA.BreakInvert
