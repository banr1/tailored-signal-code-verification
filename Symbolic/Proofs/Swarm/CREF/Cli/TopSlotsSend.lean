/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.TopDispatch
public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendWhisperSlot
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendSlot
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Session-Encoding and `opkUsed` Helpers for `pqSendModel`

Extracts post-state `oneTime` preservation and session encoding from an accepted `pqSendModel`
step, and shows that `CliTurn.opkUsed` depends on `PqBobInv` only through `oneTime`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.CREF.CliPure

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure

theorem pqSendModel_some_session_oneTime {P : PEParams} {st st' : PqParty}
    {m coins out : HwBytes} {x : RecordExtras} {g : GhostState HwBytes}
    (hsess : st.session = some (x, g))
    (hmod : pqSendModel P st m coins = some (some (st', out))) :
    st'.oneTime = st.oneTime ∧
    st'.session.map (fun (x', g') => encodeRecordUnderExtras (fun _ => x') g') =
      some (encodeRecordUnderExtras (fun _ => x) ((pqxdhSessionParams P).send g m coins).1) := by
  unfold pqSendModel at hmod
  rw [hsess] at hmod; dsimp only at hmod
  rcases henc : SessionState.messageEncrypt P.C protoSignalCodec (pqxdhSpqrSession P)
      ((pqxdhSessionParams P).sendAddrs g.party) m coins g.session with ⟨err | msg, s⟩
  · rw [henc] at hmod; cases err <;> cases hmod
  · rw [henc] at hmod; dsimp only at hmod
    cases hk : g.session.remoteIdentity with
    | none => rw [hk] at hmod; cases hmod
    | some k =>
      rw [hk] at hmod; dsimp only at hmod
      cases ht : st.trusts k <;> [simp [ht] at hmod; skip]
      simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmod
      rcases Option.some.inj (Option.some.inj hmod) with ⟨rfl, rfl⟩
      refine ⟨rfl, ?_⟩
      simp only [Option.map_some, Option.some.injEq]
      unfold Params.send encodeRecordUnderExtras
      rw [show (pqxdhSessionParams P).C = P.C from rfl,
          show (pqxdhSessionParams P).codec = protoSignalCodec from rfl,
          show (pqxdhSessionParams P).spqr = pqxdhSpqrSession P from rfl, henc]

theorem opkUsed_eq_of_pqBobInv_oneTime_eq {interp₁ interp₂ : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {acc₁ acc₂ : List HwBytes} {t₁ t₂ : CliTurn} {stB₁ stB₂ : PqParty}
    (hne : r.alice ≠ r.bob)
    (hB₁ : PqBobInv interp₁ P r acc₁ t₁.bobOff stB₁ (t₁.dirs r.bob))
    (hB₂ : PqBobInv interp₂ P r acc₂ t₂.bobOff stB₂ (t₂.dirs r.bob))
    (hone : stB₁.oneTime = stB₂.oneTime) :
    t₁.opkUsed r = t₂.opkUsed r := by
  have hu₁ := opkUsed_of_pqBobInv hne hB₁
  have hu₂ := opkUsed_of_pqBobInv hne hB₂
  cases hwo : r.withOpk
  · exact (hu₁.1 hwo).trans (hu₂.1 hwo).symm
  · cases h1 : t₁.opkUsed r
    · exact ((hu₂.2 hwo).1.mpr (hone ▸ (hu₁.2 hwo).1.mp h1)).symm
    · exact ((hu₂.2 hwo).2.mpr (hone ▸ (hu₁.2 hwo).2.mp h1)).symm

end Symbolic.Swarm.CREF.Cli
