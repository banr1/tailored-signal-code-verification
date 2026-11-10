/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompLineage
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Composed Triple Ratchet Invariants and Bridges

Aggregates session-origin, key-schedule, DH-ratchet share randomness, and depth-0 handshake
compromise bridges for Triple Ratchet transitions within `DY.Libsignal.Composed`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompRatchet

open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal.TripleRatchet (KeyComponent findRecvChain)
open DY.Libsignal.TripleRatchet (exposeKey exposeSpqr exposeSkipped guardTrace)
open DY.Libsignal.TripleRatchet.Cheval
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open Symbolic.Swarm.COMPOSED.CompTrace

theorem CompSessionOriginInv.preserves_exposeKey
    (me : Participant) (stH : Nat) (k : KeyComponent) :
    Preserves CompSessionOriginInv (exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine Preserves.bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  obtain ⟨hrIdx, hrk, _, _⟩ := hInv₀.storedOK me st stH hst₀
  rcases k with _ | _ | _ | pk
  · simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact (hInv₀.append_exposedRK ⟨hrIdx, hrk⟩).append_other rfl rfl rfl
  · simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact (hInv₀.append_tr_inert (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h)
      (by intro _ _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ _ _ h; cases h)).append_other rfl rfl rfl
  · simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact (hInv₀.append_tr_inert (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h)
      (by intro _ _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ _ _ h; cases h)).append_other rfl rfl rfl
  · dsimp only
    rcases findRecvChain st.recv pk with _ | c
    · simp only [DY.Traceful.run_failure]
      exact hInv₀
    · simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1,
        DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
      exact (hInv₀.append_tr_inert (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h)
        (by intro _ _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ _ _ h; cases h)).append_other rfl rfl rfl

theorem CompSessionOriginInv.preserves_exposeSpqr (me : Participant) (stH : Nat) :
    Preserves CompSessionOriginInv (exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  refine Preserves.bind (Preserves.getLocalState_tr _ _) fun _ => ?_
  refine Preserves.bind (fun _ h => by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact h.append_tr_inert (by intro _ _ _ h; cases h)
      (by intro _ _ _ h; cases h) (by intro _ _ _ _ _ _ h; cases h)
      (by intro _ _ _ _ _ _ _ h; cases h)) fun _ => ?_
  exact fun _ h => by
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact h.append_other rfl rfl rfl

theorem CompSessionOriginInv.preserves_exposeSkipped (evH : Nat) :
    Preserves CompSessionOriginInv (exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine Preserves.bind (Preserves.getEntry _) fun e => ?_
  rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    refine Preserves.bind (Preserves.guardTrace _) fun _ => ?_
    refine Preserves.bind (fun _ h => by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1,
        DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
      exact h.append_tr_inert (by intro _ _ _ h; cases h)
        (by intro _ _ _ h; cases h) (by intro _ _ _ _ _ _ h; cases h)
        (by intro _ _ _ _ _ _ _ h; cases h)) fun _ => ?_
    exact fun _ h => by
      simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
      exact h.append_other rfl rfl rfl
  | _ => exact Preserves.failure

/-- Every trace reachable under `Composed.reachability` satisfies `CompSessionOriginInv`. -/
theorem compSessionOriginInv_reachable {tr : ExecTrace}
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability) :
    CompSessionOriginInv tr :=
  CompSessionOriginInv.inertOnPQXDH.reachable_induction
    CompSessionOriginInv.nil
    CompSessionOriginInv.preserves_aliceStart
    CompSessionOriginInv.preserves_bobStart
    CompSessionOriginInv.preserves_messageEncrypt
    CompSessionOriginInv.preserves_messageDecrypt
    CompSessionOriginInv.preserves_messageDecryptSkipped
    CompSessionOriginInv.preserves_exposeKey
    CompSessionOriginInv.preserves_exposeSpqr
    CompSessionOriginInv.preserves_exposeSkipped
    hreach

end Symbolic.Swarm.COMPOSED.CompRatchet
