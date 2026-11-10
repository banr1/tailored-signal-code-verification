/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# `RunHsOk` Discharge Lemmas Across CLI Domain Inputs

Proves `RunCompose.RunHsOk` for PQXDH (`pqInitInputs`, `pqSendInputs`, `pqRecvInputs`) and
session-management (`smSendInputs`, `smRecvInputs`) CLI input configurations.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose

/-- Discharges `RunHsOk` on `pqInitInputs` via `InitS0.initOk₀_pqInit_proof`. -/
theorem pqInit (S : RunSem) (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = none)
    (hinit : ∀ F peer me, InitOk₀ W F peer me → S.initOk F peer me) :
    RunHsOk S (pqInitInputs W st b t) := by
  have ha : (pqInitInputs W st b t).argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := rfl
  refine ⟨?_, ?_⟩
  · intro peer dir ownB meV hp hown had
    rw [ha, RunRefine.parseArgs_init] at hp
    cases hp
    rw [RunRefine.ownAddr_pqInit] at hown
    cases hown
    rw [RunRefine.addrParse_textBytes] at had
    cases had
    exact hinit _ _ _ (InitS0.initOk₀_pqInit_proof W st b t hwf hs)
  · intro peer _ _ _ _ hp
    rw [ha, RunRefine.parseArgs_init] at hp
    cases hp

theorem pqSend (S : RunSem) (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) : RunHsOk S (pqSendInputs W st m r) := by
  have ha : (pqSendInputs W st m r).argv = (Cmd.send (partyAddress st.party.other)).argv := rfl
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ hp
    rw [ha, RunRefine.parseArgs_send] at hp
    cases hp
  · intro _ _ _ _ _ hp
    rw [ha, RunRefine.parseArgs_send] at hp
    cases hp

/-- Reduces `RunHsOk` on `wirePrekey :: m.bytes` to `S.decPkOk` on any parsed `PreKeySignalMessage`. -/
theorem pqRecvPrekey (S : RunSem) (W : PEParams) (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
    (hprekey : ∀ pm, S.pksmParse m.bytes = some pm →
      S.decPkOk (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
        (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) pm) :
    RunHsOk S (pqRecvInputs W st (wirePrekey :: m.bytes) rc) := by
  have ha : (pqRecvInputs W st (wirePrekey :: m.bytes) rc).argv =
      (Cmd.recv (partyAddress st.party.other)).argv := rfl
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ hp
    rw [ha, RunRefine.parseArgs_recv] at hp
    cases hp
  · intro peer ownB meV rest pm hp hown had hin hparse
    rw [ha, RunRefine.parseArgs_recv] at hp
    cases hp
    rw [RunRefine.ownAddr_pqRecv] at hown
    cases hown
    rw [RunRefine.addrParse_textBytes] at had
    cases had
    have hstdin : (pqRecvInputs W st (wirePrekey :: m.bytes) rc).stdin = 3#8 :: m.bytes := rfl
    rw [hstdin] at hin
    injection hin with _ hrest
    subst hrest
    exact hprekey pm hparse

theorem pqRecvOther (S : RunSem) (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (h3 : c.head? ≠ some wirePrekey) : RunHsOk S (pqRecvInputs W st c rc) := by
  have ha : (pqRecvInputs W st c rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ hp
    rw [ha, RunRefine.parseArgs_recv] at hp
    cases hp
  · intro _ _ _ rest _ _ _ _ hin _
    have hstdin : (pqRecvInputs W st c rc).stdin = c := rfl
    rw [hstdin] at hin
    subst hin
    exact absurd rfl h3

theorem smSend (S : RunSem) (g : GhostState (List (BitVec 8))) (m : List (BitVec 8)) :
    RunHsOk S (smSendInputs g m) := by
  have ha : (smSendInputs g m).argv = (Cmd.send (partyAddress g.party.other)).argv := rfl
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ hp
    rw [ha, RunRefine.parseArgs_send] at hp
    cases hp
  · intro _ _ _ _ _ hp
    rw [ha, RunRefine.parseArgs_send] at hp
    cases hp

theorem smRecv (S : RunSem) (g : GhostState (List (BitVec 8))) (c : List (BitVec 8))
    (rc : BitVec 256) : RunHsOk S (smRecvInputs g c rc) := by
  have ha : (smRecvInputs g c rc).argv = (Cmd.recv (partyAddress g.party.other)).argv := rfl
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ hp
    rw [ha, RunRefine.parseArgs_recv] at hp
    cases hp
  · intro _ _ _ rest _ _ _ _ hin _
    have hstdin : (smRecvInputs g c rc).stdin = 2#8 :: c := rfl
    rw [hstdin] at hin
    injection hin with ht _
    exact absurd ht (by decide)

end CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0
