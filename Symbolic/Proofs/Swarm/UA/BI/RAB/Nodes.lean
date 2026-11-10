/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.BI.RunAfterBreak
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.UA.BI.G.XlateSteps
import Symbolic.Proofs.Swarm.UA.BI.G.SlotInit
import Symbolic.Proofs.Swarm.UA.BI.G.SlotRecvW
import Symbolic.Proofs.Swarm.UA.BI.G.SlotRpkNO
import Symbolic.Proofs.Swarm.UA.BI.G.SlotRpkProm
import Symbolic.Proofs.Swarm.UA.BI.G.SlotSend
import Symbolic.Proofs.Swarm.UA.BI.G.XlateExcP
import Symbolic.Proofs.Swarm.UA.BI.G.XlateExcW
import Symbolic.Proofs.Swarm.UA.BI.G.XlateInv
import Symbolic.Proofs.Swarm.UA.BI.RAB.Env
import Symbolic.Proofs.Swarm.UA.BI.RAB.Leak
import Symbolic.Proofs.Swarm.UA.BI.RAB.Xport
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Run-After-Break Refinement Node Wiring

Instantiates the environment, call-slot, parameter-transport, and explanation-translation
specifications from their leaf modules, constructs the retired break moves `brkMovesExist`, and
combines them with `refines_run_after_break_of_specs` to prove `refines_run_after_break_B`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.RAB.Nodes

open Symbolic.Proofs.Swarm.UA.BI.RAB.Defs (UALeakSpecB UAEnvSpecB UASlotInitSpecB UASlotSendSpecB
  UASlotRecvWSpecB UASlotRpkNOSpecB UASlotRpkPromSpecB UAXportSpecB XlateInvSpecB XlateExcWSpecB
  XlateExcPSpecB)

/-! ## Environment events -/

theorem uab_env : UAEnvSpecB := Symbolic.Proofs.Swarm.UA.BI.RAB.Env.uab_env

theorem uab_leak_of (hXI : XlateInvSpecB) : UALeakSpecB :=
  Symbolic.Proofs.Swarm.UA.BI.RAB.Leak.leak_ua_of_xlate hXI

/-! ## Call slots -/

theorem uab_slot_init : UASlotInitSpecB := Symbolic.Proofs.Swarm.UA.BI.G.SlotInit.uab_slot_init

theorem uab_slot_send_of (hXI : XlateInvSpecB) : UASlotSendSpecB :=
  Symbolic.Proofs.Swarm.UA.BI.G.SlotSend.uab_slot_send_of hXI

theorem uab_slot_recvw_of (hXI : XlateInvSpecB) (hXW : XlateExcWSpecB) : UASlotRecvWSpecB :=
  Symbolic.Proofs.Swarm.UA.BI.G.SlotRecvW.uab_slot_recvw_of hXI hXW

theorem uab_slot_rpk_no_of (hXI : XlateInvSpecB) (hXP : XlateExcPSpecB) : UASlotRpkNOSpecB :=
  Symbolic.Proofs.Swarm.UA.BI.G.SlotRpkNO.uab_slot_rpk_no_of hXI hXP

theorem uab_slot_rpk_prom_of (hXI : XlateInvSpecB) (hXW : XlateExcWSpecB) : UASlotRpkPromSpecB :=
  Symbolic.Proofs.Swarm.UA.BI.G.SlotRpkProm.uab_slot_rpk_prom_of hXI hXW

/-! ## Transport and translation -/

theorem uab_xport : UAXportSpecB := Symbolic.Proofs.Swarm.UA.BI.RAB.Xport.xport

/-- Witness that `Move.brkDH` and `Move.brkKEM` satisfy `BrkMovesExist`. -/
theorem brkMovesExist : Symbolic.Proofs.Swarm.UA.BI.G.XlateSteps.BrkMovesExist := by
  exact ⟨⟨.brkDH, {
          next_eq := fun tr => by
            unfold _root_.DY.Libsignal.Composed.Refinement.Move.next
              _root_.DY.Libsignal.Composed.Refinement.Move.act
              _root_.DY.Libsignal.PQXDH.breakDH
            simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
              Symbolic.DYBridge.DY.appendEntry_eq_1,
              DY.Traceful.run_bind, DY.Traceful.run_pure, DY.Traceful.run_mk]
            exact (Symbolic.Proofs.Swarm.UA.BI.Step.next_breakDH tr).symm
          vis_nil := fun _ => Symbolic.Swarm.CREF.exposures_nil_of_not_leakKind rfl nofun
          move_ok := fun _ _ => ⟨rfl, trivial, trivial, trivial, trivial⟩
          party_none := rfl
          ppath_none := rfl
          sload_none := rfl
          not_reject := nofun
          no_readcol := nofun
          keys_nil := fun _ => rfl }⟩,
       ⟨.brkKEM, {
          next_eq := fun tr => by
            unfold _root_.DY.Libsignal.Composed.Refinement.Move.next
              _root_.DY.Libsignal.Composed.Refinement.Move.act
              _root_.DY.Libsignal.PQXDH.breakKEM
            simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
              Symbolic.DYBridge.DY.appendEntry_eq_1,
              DY.Traceful.run_bind, DY.Traceful.run_pure, DY.Traceful.run_mk]
            exact (Symbolic.Proofs.Swarm.UA.BI.Step.next_breakKEM tr).symm
          vis_nil := fun _ => Symbolic.Swarm.CREF.exposures_nil_of_not_leakKind rfl nofun
          move_ok := fun _ _ => ⟨rfl, trivial, trivial, trivial, trivial⟩
          party_none := rfl
          ppath_none := rfl
          sload_none := rfl
          not_reject := nofun
          no_readcol := nofun
          keys_nil := fun _ => rfl }⟩⟩

theorem xlate_inv_b : XlateInvSpecB :=
  Symbolic.Proofs.Swarm.UA.BI.G.XlateInv.xlate_inv_b_of brkMovesExist

theorem xlate_exc_w_b_of (hXI : XlateInvSpecB) : XlateExcWSpecB :=
  Symbolic.Proofs.Swarm.UA.BI.G.XlateExcW.xlate_exc_w_b_of hXI

theorem xlate_exc_p_b_of (hXI : XlateInvSpecB) : XlateExcPSpecB :=
  Symbolic.Proofs.Swarm.UA.BI.G.XlateExcP.xlate_exc_p_b_of hXI

/-! ## Top-level refinement -/

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY.Libsignal.HwEvents (CliEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.E2E (PEParams)
open Symbolic.Swarm.CREF (compSemOf)
open Symbolic.Swarm.CREF.Cli (interpOfParams)
open Symbolic.Proofs.Swarm.UA.BI.RunAfterBreak (RunAfterBreakB refines_run_after_break_of_specs)

/-- Every guarded CLI trace containing a run event after a break or invert event is either
explained under `compSemOf (interpOfParams interp P) r` or suffers a collision after an explained
prefix. -/
theorem refines_run_after_break_B (interp : ExternInterpretation)
    (hext : ExternContractsHoldCli interp) (P : PEParams) (hagree : ModelAgree interp P)
    (r : ProtocolSetup) (hr : ProtocolSetupWF r) (evs : List CliEvent)
    (htr : CliTraces (PqModelRel interp P) interp r (CliTurn.init (initDirs interp r)) evs)
    (hg : InvertsGuarded interp r evs) (hrab : RunAfterBreakB evs) :
    (∃ g ss vis, Explains interp r (compSemOf (interpOfParams interp P) r) g ss vis evs) ∨
      CollisionAfterExplainedPrefix interp r (compSemOf (interpOfParams interp P) r) evs :=
  refines_run_after_break_of_specs (uab_leak_of xlate_inv_b) uab_env uab_slot_init
    (uab_slot_send_of xlate_inv_b) (uab_slot_recvw_of xlate_inv_b (xlate_exc_w_b_of xlate_inv_b))
    (uab_slot_rpk_no_of xlate_inv_b (xlate_exc_p_b_of xlate_inv_b))
    (uab_slot_rpk_prom_of xlate_inv_b (xlate_exc_w_b_of xlate_inv_b)) uab_xport
    interp hext P hagree r hr evs htr hg hrab

end Symbolic.Proofs.Swarm.UA.BI.RAB.Nodes
