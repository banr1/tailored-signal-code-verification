/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.Repr
public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDir
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDirAux
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Alice Party-Directory Interface for `init`

Defines `AliceInitPartyInv` and proves that when `t.records r r.alice = none`,
it implies `st.session = none` and `AliceDirState`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
cref_open
open Symbolic.Swarm.CREF.CliPure

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession

theorem bytesToVec_32_eq_vec32 {bs : HwBytes} (hbs : bs.length = 32) :
    Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 bs = vec32 bs := by
  apply List.Vector.eq
  change (bs ++ List.replicate 32 0#8).take 32 = (vec32 bs).toList
  rw [List.take_append_of_le_length (Nat.le_of_eq hbs.symm),
      List.take_of_length_le (Nat.le_of_eq hbs),
      Proofs.libsignal.Hooks2.vec32_toList_of_length_32' bs hbs]

/-- Alice party-directory invariant matching `PqPartyInv` on `r.alice` without
assuming `FilesBounded` upfront. -/
structure AliceInitPartyInv (interp : ExternInterpretation) (P : PEParams)
    (r : ProtocolSetup) (d : DirectorySnapshot) (st : PqParty) : Prop where
  alice : AlicePqParty interp r st
  session_reach : ∀ x g, st.session = some (x, g) →
    (∃ g₀ : GhostState HwBytes, ReachablePqxdhSession P st.me x g₀ ∧
      g₀.party = g.party ∧ g₀.session = g.session) ∧
    g.party = st.party
  dir_eq : d = filesOf (encodeDir P st)

theorem AliceInitPartyInv.records_eq {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (hEq : ExternCryptoLawsHold interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {t : CliTurn} {st : PqParty}
    (hinv : AliceInitPartyInv interp P r (t.dirs r.alice) st) :
    t.records r r.alice = st.session.map fun (x, g) => encodeRecordUnderExtras (fun _ => x) g := by
  unfold CliTurn.records
  rw [hinv.dir_eq, encodeDir_of_alicePqParty hagree hEq hwf hinv.alice]
  cases hs : st.session with
  | none =>
    have hfold : filesOf (commonFiles interp r r.alice) (sessionPathOf r r.alice) = none := by
      rw [filesOf_eq_optFold (alicePathList_commonFiles interp r), sessionPathOf_alice_eq]
      refine foldl_false_eq_none _ _ fun f hf => ?_
      unfold commonFiles at hf
      simp only [peerNameOf, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl <;> (dsimp only; decide)
    simp [hfold]
  | some xg =>
    rcases xg with ⟨x, g⟩
    have hsess_al : AlicePathList [(sessionPathOf r r.alice, encodeRecordUnderExtras (fun _ => x) g)] := by
      intro f hf; rw [List.mem_singleton] at hf; subst hf
      simp [sessionPathOf_alice_eq, aliceAllPaths, aliceKeepPaths]
    rw [filesOf_append_of_alicePaths (alicePathList_commonFiles interp r) hsess_al,
        filesOf_eq_optFold hsess_al]
    simp [encodeRecordX_ne_nil x g]

theorem AliceInitPartyInv.toAliceDirState_of_records_none
    {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (hEq : ExternCryptoLawsHold interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {t : CliTurn} {st : PqParty}
    (hinv : AliceInitPartyInv interp P r (t.dirs r.alice) st)
    (hrec : t.records r r.alice = none) :
    st.session = none ∧ AliceDirState interp P r (t.dirs r.alice) st := by
  have hsess : st.session = none := by
    rw [hinv.records_eq hagree hEq hwf, Option.map_eq_none_iff] at hrec
    exact hrec
  have hst_eq : st = aliceInitPqParty interp r := by
    cases st
    cases hinv.alice with
    | mk h1 h2 h3 h4 h5 h6 h7 =>
      simp_all [aliceInitPqParty]
  have hwf_st : PqxdhPartyInSpecDomain P st := by
    rw [hst_eq]
    exact wfPq_aliceInitPqParty hagree hEq hwf
  exact ⟨hsess, ⟨hinv.alice, hwf_st, hinv.dir_eq⟩⟩

end Symbolic.Swarm.CREF.Cli.Slots
