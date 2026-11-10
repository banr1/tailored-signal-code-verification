/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.IfacePure
public import Symbolic.Proofs.Swarm.CREF.CBadG2.Frame
public import Symbolic.Proofs.Swarm.CREF.CBadReadableBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen

/-!
# Raw-Witness Branch Obligation and Three-Branch Combiner

Defines the per-branch obligation `PromRawKnBranchOK` for promote decryption and combines the
`Skipped`, `NoRatchet`, and `RatchetDH` branches in `prom_hRawKn_of_rawKnBranches`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)

/-- Per-branch obligation producing a `RawDecryptMatched` witness together with attacker-known
`pqSalt` at every clean explanation of an accepting, non-colliding promote call. -/
def PromRawKnBranchOK (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (sel : PromDecSel) : Prop :=
  ∀ (j : Nat) (e' : PromTurn) (mid acc : List MachineEvent)
    (rec : HwBytes) (tag : BitVec 8) (body : HwBytes) (sm : StateAndMessage) (pf : PreKeyFields)
    (sess sess' : Session (List (BitVec 8)))
    (coins : BitVec 256) (expected : Option (List (BitVec 8))) (pt : List (BitVec 8)),
    PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec (tag :: body) sm pf
      sess sess' coins expected pt →
    ¬ CollisionAt interpretation r S who ok (acc ++ promAccBlk (tag :: body) mid pt) →
    sel sess pf.inner mid coins →
    ∀ g ms t',
      CleanBy interpretation r S who ok g ms acc →
      PromRawCtx interpretation r S g ms acc →
      t' ∈ recvRepresentations interpretation r S g ms pf.message →
      ¬ RecvCollision interpretation r S g ms t' →
      RecvExcuseFree interpretation r S who ok g ms acc (.recv (tag :: body)) (mid ++ [.accept pt]) pf.message t' →
      ∃ (g₁ : Ghost) (stateIdx : Nat) (spqrMsgIdx : UInt32) (pqSalt t_m : DY.Bytes) (m : Move),
        CBadSigmaFrame g g₁ (runTraceMoves r ms).length ∧
        t_m ∈ recvRepresentations interpretation r S g ms pf.message ∧
        pqSalt.AttackerKnows (runTraceMoves r ms) ∧
        DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms) stateIdx = true ∧
        (m = Move.decrypt r.bob stateIdx ((runTraceMoves r ms).length + 1) (runTraceMoves r ms).length
              spqrMsgIdx (decide (tag ≠ wireWhisperTag)) ∨
          ∃ skIdx, m = Move.decryptSkipped r.bob stateIdx ((runTraceMoves r ms).length + 1) skIdx
            (runTraceMoves r ms).length spqrMsgIdx (decide (tag ≠ wireWhisperTag))) ∧
        RawDecryptMatched interpretation r S g₁
          (ms ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [m]))
          (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt]))

/-- Combines `PromDecSelCases`, `PromRawCtxSupply`, and the three `PromRawKnBranchOK` obligations
(`Skipped`, `NoRatchet`, and `RatchetDH`). -/
theorem prom_hRawKn_of_rawKnBranches
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hCases : PromDecSelCases interpretation r S who ok)
    (hCtx : PromRawCtxSupply interpretation r S who ok)
    (hSk : PromRawKnBranchOK interpretation r S who ok PromDecSelSkipped)
    (hNR : PromRawKnBranchOK interpretation r S who ok PromDecSelNoRatchet)
    (hDH : PromRawKnBranchOK interpretation r S who ok PromDecSelRatchetDH) :
    ∀ j e' mid acc rec tag body sm pf sess sess' coins expected pt,
      PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec (tag :: body) sm pf
        sess sess' coins expected pt →
      ¬ CollisionAt interpretation r S who ok (acc ++ promAccBlk (tag :: body) mid pt) →
      ∀ g ms t',
        CleanBy interpretation r S who ok g ms acc →
        t' ∈ recvRepresentations interpretation r S g ms pf.message →
        ¬ RecvCollision interpretation r S g ms t' →
        RecvExcuseFree interpretation r S who ok g ms acc (.recv (tag :: body)) (mid ++ [.accept pt]) pf.message t' →
        ∃ (g₁ : Ghost) (stateIdx : Nat) (spqrMsgIdx : UInt32) (pqSalt t_m : DY.Bytes) (m : Move),
          CBadSigmaFrame g g₁ (runTraceMoves r ms).length ∧
          t_m ∈ recvRepresentations interpretation r S g ms pf.message ∧
          pqSalt.AttackerKnows (runTraceMoves r ms) ∧
          DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms) stateIdx = true ∧
          (m = Move.decrypt r.bob stateIdx ((runTraceMoves r ms).length + 1) (runTraceMoves r ms).length
                spqrMsgIdx (decide (tag ≠ wireWhisperTag)) ∨
            ∃ skIdx, m = Move.decryptSkipped r.bob stateIdx ((runTraceMoves r ms).length + 1) skIdx
              (runTraceMoves r ms).length spqrMsgIdx (decide (tag ≠ wireWhisperTag))) ∧
          RawDecryptMatched interpretation r S g₁
            (ms ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [m]))
            (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt])) := by
  intro j e' mid acc rec tag body sm pf sess sess' coins expected pt hC hcol
    g ms t' hc ht hncol hnors
  have hx := hCtx j e' mid acc rec (tag :: body) sm pf sess sess' coins expected pt
    hC hcol g ms hc
  rcases hCases j e' mid acc rec (tag :: body) sm pf sess sess' coins expected pt hC with
    hsel | hsel | hsel
  · exact hSk j e' mid acc rec tag body sm pf sess sess' coins expected pt hC hcol
      hsel g ms t' hc hx ht hncol hnors
  · exact hNR j e' mid acc rec tag body sm pf sess sess' coins expected pt hC hcol
      hsel g ms t' hc hx ht hncol hnors
  · exact hDH j e' mid acc rec tag body sm pf sess sess' coins expected pt hC hcol
      hsel g ms t' hc hx ht hncol hnors

end Symbolic.Swarm.CREF.CliPure
