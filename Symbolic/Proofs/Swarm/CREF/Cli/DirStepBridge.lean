/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
import Symbolic.Proofs.Refinement.Composed.Cli.Transfer

/-!
# CLI Input Equivalence and Turn-Step Invariants

Relates `InputsFor` on encoded party directories to `pqInputs`, `pqSendInputs`, and `pqRecvInputs`,
and proves `PqDirInv` preservation across `CliTurn.after` on reject and same-key-set accept steps.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli

open DY DY.Comparse
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession

/-! ## `InputsEquiv` builders -/

theorem inputsEquiv_pqInputs {c : CliCall} {P : PEParams} {st : PqParty}
    {extra : List (String × HwBytes)} {i : Inputs}
    (hi : InputsFor c (filesOf (encodeDir P st)) i)
    (hreg_extra : RegularFileList extra)
    (hextra : c.extra = extra ++ [(coinsFile, c.coins)]) :
    InputsEquiv i (pqInputs P st c.cmd extra c.coins c.stdin) := by
  obtain ⟨hargv, hdirs, hstdin, hfiles, _⟩ := hi
  refine ⟨hargv, hdirs, hstdin, fun p => ?_⟩
  by_cases hp : p ∈ stdioPaths
  · rw [filesOf_eq_none_of_mem_stdioPaths _ hp, filesOf_eq_none_of_mem_stdioPaths _ hp]
  · rw [hfiles p hp]
    have hreg_c : RegularFileList c.extra :=
      hextra ▸ hreg_extra.append (regularFile_root (by decide) (by decide) (by decide) (by decide))
    have hcomb : encodeDir P st ++ extra ++ [(coinsFile, c.coins)] =
        encodeDir P st ++ c.extra := by rw [hextra, List.append_assoc]
    change _ = filesOf (encodeDir P st ++ extra ++ [(coinsFile, c.coins)]) p
    rw [hcomb, filesOf_append_of_regular (regularFileList_encodeDir P st) hreg_c p]

theorem inputsEquiv_pqSendInputs {c : CliCall} {P : PEParams} {st : PqParty}
    {coins : List.Vector (BitVec 8) 64} {i : Inputs}
    (hi : InputsFor c (filesOf (encodeDir P st)) i) (hcmd : c.cmd = .send (partyAddress st.party.other))
    (hbun : c.bundle = []) (hcoins : c.coins = coins.toList) :
    InputsEquiv i (pqSendInputs P st c.stdin coins) := by
  unfold pqSendInputs; rw [← hcmd, ← hcoins]
  exact inputsEquiv_pqInputs hi (fun _ h => nomatch h) (by simp [CliCall.extra, hbun])

theorem inputsEquiv_pqRecvInputs {c : CliCall} {P : PEParams} {st : PqParty}
    {rc : BitVec 256} {i : Inputs}
    (hi : InputsFor c (filesOf (encodeDir P st)) i) (hcmd : c.cmd = .recv (partyAddress st.party.other))
    (hbun : c.bundle = []) (hcoins : c.coins = CryptoGames.HMAC.keyToBytes32 rc) :
    InputsEquiv i (pqRecvInputs P st c.stdin rc) := by
  unfold pqRecvInputs; rw [← hcmd, ← hcoins]
  exact inputsEquiv_pqInputs hi (fun _ h => nomatch h) (by simp [CliCall.extra, hbun])

/-! ## `PqDirInv` across `CliTurn.after` -/

theorem caller_pqPartyInv_of_allowed {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {accepted : List HwBytes} {t : CliTurn} {c : CliCall}
    (hinv : PqDirInv interp P r t accepted) (hbca : BobCallAllowed r t c)
    (hp : c.party = r.alice ∨ c.party = r.bob) :
    (c.party = r.alice ∨ (c.party = r.bob ∧ t.bobOff = false)) ∧
      ∃ st, PqPartyInv interp P r accepted c.party st (t.dirs c.party) := by
  rcases hp with ha | hb
  · obtain ⟨stA, hA⟩ := hinv.1; exact ⟨Or.inl ha, stA, ha ▸ hA⟩
  · have hbo : t.bobOff = false := by cases h : t.bobOff <;> [rfl; exact absurd hb (hbca h)]
    obtain ⟨stB, hB⟩ := hinv.2.1; unfold PqBobInv at hB; rw [hbo] at hB
    exact ⟨Or.inr ⟨hb, hbo⟩, stB, hb ▸ hB⟩

private theorem pqDirInv_of_dirs_bobOff_eq {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t t' : CliTurn} {accepted : List HwBytes}
    (h : PqDirInv interp P r t accepted)
    (hdirs : ∀ q, t'.dirs q = t.dirs q) (hbo : t'.bobOff = t.bobOff) :
    PqDirInv interp P r t' accepted := by
  obtain ⟨⟨stA, hA⟩, ⟨stB, hB⟩, hoth⟩ := h
  exact ⟨⟨stA, hdirs r.alice ▸ hA⟩, ⟨stB, hbo ▸ hdirs r.bob ▸ hB⟩,
    fun p ha hb => (hdirs p).trans (hoth p ha hb)⟩

theorem pqDirInv_after_reject {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t : CliTurn} {c : CliCall} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} (hinv : PqDirInv interp P r t accepted)
    (hscr : scrub files = t.dirs c.party) :
    PqDirInv interp P r (t.after r c 1 out files) accepted :=
  pqDirInv_of_dirs_bobOff_eq hinv
    (fun q => by unfold CliTurn.after; dsimp only; split_ifs with hq <;> [rw [hq, hscr]; rfl])
    (by simp [CliTurn.after])

theorem pqDirInv_after_accept_same {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t : CliTurn} {c : CliCall} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {st' : PqParty}
    (hne : r.alice ≠ r.bob) (hinv : PqDirInv interp P r t accepted)
    (hparty : c.party = r.alice ∨ (c.party = r.bob ∧ t.bobOff = false))
    (hnot_nm : ¬ PreKeyNoMatch r t c) (hscr : scrub files = filesOf (encodeDir P st'))
    (hst' : PqPartyInv interp P r accepted c.party st' (filesOf (encodeDir P st'))) :
    PqDirInv interp P r (t.after r c 0 out files) accepted := by
  have hbo : (t.after r c 0 out files).bobOff = t.bobOff := by simp [CliTurn.after, hnot_nm]
  refine ⟨?_, ?_, fun p ha hb => ?_⟩
  · rcases hparty with ha | ⟨hb, _⟩
    · refine ⟨st', ?_⟩; simp only [CliTurn.after, ha, ↓reduceIte, hscr]; exact ha ▸ hst'
    · obtain ⟨stA, hA⟩ := hinv.1; refine ⟨stA, ?_⟩
      simpa only [CliTurn.after, hb, hne, ↓reduceIte] using hA
  · rcases hparty with ha | ⟨hb, hbo_f⟩
    · obtain ⟨stB, hB⟩ := hinv.2.1; refine ⟨stB, ?_⟩
      rw [hbo]; simpa only [CliTurn.after, ha, hne.symm, ↓reduceIte] using hB
    · refine ⟨st', ?_⟩; rw [hbo, hbo_f]; unfold PqBobInv
      simp only [Bool.false_eq_true, ↓reduceIte, CliTurn.after, hb, hscr]; exact hb ▸ hst'
  · have hpc : p ≠ c.party := by
      rcases hparty with h1 | ⟨h1, _⟩ <;> [exact h1 ▸ ha; exact h1 ▸ hb]
    simpa only [CliTurn.after, hpc, ↓reduceIte] using hinv.2.2 p ha hb

end Symbolic.Swarm.CREF.Cli
