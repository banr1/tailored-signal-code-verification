/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import VCVio.Prelude.Core

/-!
# Current Snapshot and `RpkRecRel` for `bobStart`

Proves `rpkR_final_current`, showing that `rpkR_finalSt w` is stored and current after `Move.bobStart`,
and defines `RpkRecRel` packaging `TR.StateRel`, skipped-key freshness, and receiver-chain `Nodup`
invariants for an encoded `RecordRec`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (TRState isCurrentSnapshot skippedKeyUsedB receiverKeyUsedB)

/-- After `Move.bobStart`, `rpkR_finalSt w` is stored as Bob's current local state snapshot. -/
theorem rpkR_final_current {r : ProtocolSetup} {ms : List Move} {b a : Participant}
    {kh : PQXDH.BobKeyHandles} {regA : Nat} {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat}
    {spqrMsgIdx : UInt32} {shown : Nat}
    (w : BobStartOk (runTraceMoves r ms) b a kh regA mh pqIdx spqrMsgIdx) :
    ∃ stateIdx,
      ((PersistentLocalState.getLocalState b stateIdx : Traceful TRState).run
        (runTraceMoves r (ms ++ [.bobStart b a kh regA mh pqIdx spqrMsgIdx shown]))).1 =
        some (rpkR_finalSt w) ∧
      isCurrentSnapshot (runTraceMoves r (ms ++ [.bobStart b a kh regA mh pqIdx spqrMsgIdx shown]))
        stateIdx = true := by
  obtain ⟨tr₀, htr⟩ := rpkR_bobStartTr_last w
  refine ⟨tr₀.length, ?_, ?_⟩
  · rw [TR.runTrace_snoc, w.next_eq, htr]
    exact TR.RecvDec.getLocalState_append_stEntry_at_length tr₀ b (rpkR_finalSt w)
  · rw [TR.runTrace_snoc, w.next_eq, htr]
    exact TR.RecvDec.isCurrentSnapshot_append_stEntry_at_length tr₀ b (rpkR_finalSt w)

/-- Per-record relation between an encoded `RecordRec` `bytes` and `TRState` `st` on `tr`:
`TR.StateRel`, logged and unused skipped message keys, and `Nodup` receiver chains. -/
def RpkRecRel (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (p : Participant) (st : TRState) (bytes : HwBytes) : Prop :=
  ∃ rec : RecordRec,
    bytes = recordBytes rec ∧
    TR.StateRel interpretation S g st rec ∧
    (∀ c ∈ rec.current.receiverChains, ∀ k ∈ c.messageKeys,
      ∃ pk rIdx srcIdx skIdx seed,
        tr.EventLoggedAt
          (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored (st.sessionInfo p) pk
            (UInt32.ofBitVec k.1) seed rIdx srcIdx) skIdx ∧
        !skippedKeyUsedB tr skIdx ∧
        !receiverKeyUsedB tr (st.sessionInfo p) seed (UInt32.ofBitVec k.1) rIdx ∧
        gamma interpretation S g seed = k.2 ∧
        c.senderRatchetKey = TR.serializedKey (gamma interpretation S g pk) ∧
        (DY.Libsignal.TripleRatchet.findRecvChain st.toDRState.recv pk).isSome = true) ∧
    ((rec.current.receiverChains.map ChainRec.senderRatchetKey).Nodup ∧
      (∀ c ∈ rec.current.receiverChains, (c.messageKeys.map Prod.fst).Nodup) ∧
      ∀ c ∈ rec.current.receiverChains, ∀ k ∈ c.messageKeys,
        ∃ ck, c.chainKey = some ck ∧ k.1 < ck.1)

end Symbolic.Swarm.CREF
