/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CHistStepPure
public import Symbolic.Proofs.Swarm.CREF.Cli.World.XplTransferPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TR.RecvHistDecAvail

/-!
# `CHist` Step Reduction Across Whisper Decrypt Moves

Provides quiet-extension helpers for `InvisibleNoEffect` frames and reduces `CHist`
preservation across a `DecryptBy` move (`rcvHist_snoc_of_parts`, `rcvHist_store_of_inv`) to
`SkippedInstallByteFresh`, `PureTRRecordStateInv`, and `RecRecvRkOk`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv

cref_open
open DY DY.Libsignal
open DY.Libsignal.TripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR (StateRel)

abbrev HStE := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)

theorem rcvHist_quietPre {r : ProtocolSetup} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre) :
    PureXplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
  rw [TR.runTrace_append]
  exact PureXplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)

theorem rcvHist_quietPost {r : ProtocolSetup} {ms₀ pre post : List Move} {m : Move}
    (hpost : MovesFrom InvisibleNoEffect (m.next (runTraceMoves r (ms₀ ++ pre))) post) :
    PureXplQuiet.QuietExt (runTraceMoves r (ms₀ ++ pre ++ [m])) (runTraceMoves r (ms₀ ++ (pre ++ m :: post))) := by
  rw [show ms₀ ++ (pre ++ m :: post) = ms₀ ++ pre ++ [m] ++ post by simp,
    TR.runTrace_append (ms₁ := ms₀ ++ pre ++ [m]), TR.runTrace_snoc]
  exact PureXplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost)

theorem rcvHist_avail_cases {r : ProtocolSetup} {ms : List Move} {p : Participant} {m : Move}
    (hm : DecryptBy p m) :
    ∀ st ∈ DY.Libsignal.Composed.Refinement.availableStates r (runTraceMoves r (ms ++ [m])),
      st ∈ DY.Libsignal.Composed.Refinement.availableStates r (runTraceMoves r ms) ∨
        ((runTraceMoves r (ms ++ [m])).at? ((runTraceMoves r (ms ++ [m])).length - 1) : Option HStE) =
          some ⟨⟨p, st⟩⟩ := by
  match m, hm with
  | .decrypt _ stateIdx msgIdx pqIdx spqrMsgIdx wrapped, rfl =>
    exact TR.availableStates_move_decrypt_cases r ms p stateIdx msgIdx pqIdx spqrMsgIdx wrapped
  | .decryptSkipped _ stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped, rfl =>
    exact TR.availableStates_move_decryptSkipped_cases r ms p stateIdx msgIdx skIdx pqIdx
      spqrMsgIdx wrapped

/-- Preserves `CHist` across a `DecryptBy p` move given `SkippedInstallByteFresh` preservation and
a `StateRel` / `Nodup` / `RecRecvRkOk` witness whenever the move appends a new state for `p`. -/
theorem rcvHist_snoc_of_parts {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {p : Participant} {m : Move}
    (hm : DecryptBy p m) (hch : CHist interpretation r S g ms)
    (hbf : TR.SkippedInstallByteFresh interpretation S g r ms →
      TR.SkippedInstallByteFresh interpretation S g r (ms ++ [m]))
    (hstore : ∀ newSt : TRState,
      ((runTraceMoves r (ms ++ [m])).at? ((runTraceMoves r (ms ++ [m])).length - 1) : Option HStE) =
        some ⟨⟨p, newSt⟩⟩ →
      ∃ rec' : RecordRec, StateRel interpretation S g newSt rec' ∧
        (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup ∧
        TR.CHistStep.RecRecvRkOk rec') :
    CHist interpretation r S g (ms ++ [m]) := by
  by_cases hs : ∃ newSt : TRState,
      ((runTraceMoves r (ms ++ [m])).at? ((runTraceMoves r (ms ++ [m])).length - 1) : Option HStE) =
        some ⟨⟨p, newSt⟩⟩
  · obtain ⟨newSt, hlast⟩ := hs
    obtain ⟨rec', hrel', hnd', hok'⟩ := hstore newSt hlast
    refine TR.CHistStep.cHist_step hch (fun st hst => ?_) hrel' hnd' hok' hbf
    rcases rcvHist_avail_cases hm st hst with h | h
    · exact Or.inl h
    · rw [hlast] at h; cases h; exact Or.inr rfl
  · refine TR.CHistStep.cHist_of_noStore hch (fun st hst => ?_) hbf
    rcases rcvHist_avail_cases hm st hst with h | h
    · exact h
    · exact absurd ⟨st, h⟩ hs

theorem rcvHist_idx_of_current {tr : ExecTrace} {p : Participant} {i : Nat} {st newSt : TRState}
    (hat : (tr.at? i : Option HStE) = some ⟨⟨p, st⟩⟩)
    (hlast : (tr.at? (tr.length - 1) : Option HStE) = some ⟨⟨p, newSt⟩⟩)
    (hcur : isCurrentSnapshot tr i = true) (hinit : newSt.initiator = st.initiator) :
    i = tr.length - 1 := by
  have hlt : i < tr.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := HStE) tr i
    rw [hat] at this; exact this
  by_contra hne
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur
  rw [hat] at hcur
  simp only [List.all_eq_true] at hcur
  have hj := hcur (tr.length - 1) (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  rw [hlast] at hj
  simp [hinit] at hj

theorem rcvHist_storeRel_of_inv {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {p : Participant} {b : HwBytes} {newSt : TRState}
    (hinv : TR.PureTRRecordStateInv interpretation r S (pureTrSlots r) g ms
      (fun q => if q = p then some b else none))
    (hlast : ((runTraceMoves r ms).at? ((runTraceMoves r ms).length - 1) : Option HStE) = some ⟨⟨p, newSt⟩⟩)
    (hrole : ∀ (st₁ st₂ : TRState) (i j : Nat),
      ((runTraceMoves r ms).at? i : Option HStE) = some ⟨⟨p, st₁⟩⟩ →
      ((runTraceMoves r ms).at? j : Option HStE) = some ⟨⟨p, st₂⟩⟩ → st₁.initiator = st₂.initiator) :
    ∃ rec' : RecordRec, b = recordBytes rec' ∧ StateRel interpretation S g newSt rec' ∧
      (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup := by
  obtain ⟨_, rec, st, stateIdx, hb, hget, hcur, hrel, _, _, _, hnd⟩ := hinv p b (by simp)
  have hat : ((runTraceMoves r ms).at? stateIdx : Option HStE) = some ⟨⟨p, st⟩⟩ :=
    TR.FreshSigma.at?_eq_some_of_getLocalState_some hget
  have hidx := rcvHist_idx_of_current hat hlast hcur (hrole _ _ _ _ hlast hat)
  rw [hidx, hlast] at hat
  cases hat
  exact ⟨rec, hb, hrel, hnd.1⟩

/-- Discharges the stored-state hypothesis of `rcvHist_snoc_of_parts` from `PureTRRecordStateInv`,
single-role snapshots for `p`, and `RecRecvRkOk` on `b`. -/
theorem rcvHist_store_of_inv {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {p : Participant} {b : HwBytes}
    (hinv : TR.PureTRRecordStateInv interpretation r S (pureTrSlots r) g ms
      (fun q => if q = p then some b else none))
    (hrole : ∀ (st₁ st₂ : TRState) (i j : Nat),
      ((runTraceMoves r ms).at? i : Option HStE) = some ⟨⟨p, st₁⟩⟩ →
      ((runTraceMoves r ms).at? j : Option HStE) = some ⟨⟨p, st₂⟩⟩ → st₁.initiator = st₂.initiator)
    (hok : ∀ rec' : RecordRec, b = recordBytes rec' → TR.CHistStep.RecRecvRkOk rec') :
    ∀ newSt : TRState,
      ((runTraceMoves r ms).at? ((runTraceMoves r ms).length - 1) : Option HStE) = some ⟨⟨p, newSt⟩⟩ →
      ∃ rec' : RecordRec, StateRel interpretation S g newSt rec' ∧
        (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup ∧
        TR.CHistStep.RecRecvRkOk rec' := by
  intro newSt hlast
  obtain ⟨rec', hb, hrel, hnd⟩ := rcvHist_storeRel_of_inv hinv hlast hrole
  exact ⟨rec', hrel, hnd, hok rec' hb⟩

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
