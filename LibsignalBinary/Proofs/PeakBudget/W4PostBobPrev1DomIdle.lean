/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacSuccWhisper
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget
import LibsignalBinary.Proofs.E2E.RecordX.Scope
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PqValid
import LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap

/-!
# Closed Idle Inhabitant for `PostBobPrev1Dom 286196 2097152 2469364`

Closed inhabitant of `PostBobPrev1Dom 286196 2097152 2469364` (`= PostBobPrev1Dom w4PostBobPqCap
2097152 postBobTotalPrev1Cap286K`) at `(w0G0, w0Ses0, [])`, used to instantiate the idle `hOut1`
placeholder on arms 1–3 (`untrusted`, `p1Ok`, `p2Over`) where no runtime `SessionGhostValid`
witness is present.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1DomIdle

open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
  (encodeRecordPrev1 encodeRecordPrev1Mem encodeRecordPrev1Mem_eq_of_canon)
open CryptoVerification.E2E.Record (encodeRecord lenField)
open CryptoVerification.E2E.RecordX
  (encodeRecordX_eq_toRecord sessionOfX toRecord_extrasOf_eq)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.SignalSession (fileCapBytes)
open CryptoVerification.SignalSession.Cli.Slots
  (pqSessBytes pqSessBytes_le_fileCapBytes)
open CryptoVerification.SignalSession.Cli.Slots.PqValid (reachPq_inv)
open CryptoVerification.SignalSession.NonVacuityPq (W0)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacSuccWhisper
  (w0G0 w0G0_sessionGhostValid w0RcInit w0Rec0 w0SA0 w0Ses0 w0St1 w0St1_domain w0XA)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (SessionCloneDom canonSession_of_sessionGhostValid)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom (PostBobPrev1Dom)
open LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap (reachPq_pqLength_le_286196)

private theorem g1fr_w0Rec0_eq :
    w0Rec0 = { currentSession := some (sessionOfX (fun _ => w0XA) ⟨.A, w0SA0, 0, [0]⟩) } :=
  toRecord_extrasOf_eq (fun _ => w0XA) ⟨.A, w0SA0, 0, [0]⟩

private theorem g1fr_w0Ses0_eq :
    w0Ses0 = sessionOfX (fun _ => w0XA) ⟨.A, w0SA0, 0, [0]⟩ := by
  unfold w0Ses0
  rw [g1fr_w0Rec0_eq]

private theorem g1fr_w0Rec0_some :
    ({ currentSession := some w0Ses0 } : SessionRecord (List (BitVec 8))) = w0Rec0 := by
  rw [g1fr_w0Rec0_eq, g1fr_w0Ses0_eq]

private theorem g1fr_w0Ses0_state :
    w0Ses0.state = w0SA0 := by
  rw [g1fr_w0Ses0_eq]
  rfl

private theorem g1fr_w0SA0_rc :
    w0SA0.receiverChains = [w0RcInit] :=
  rfl

private theorem g1fr_w0Ses0_rc_len1 :
    w0Ses0.state.receiverChains.length ≤ 1 := by
  rw [g1fr_w0Ses0_state, g1fr_w0SA0_rc]
  decide

private theorem g1fr_w0Ses0_dom :
    SessionCloneDom 286196 w0Ses0 := by
  obtain ⟨⟨g₀, hR₀, _, hsess₀⟩, _⟩ := w0St1_domain.1 w0XA ⟨.A, w0SA0, 0, [0]⟩ rfl
  have hsess₀' : g₀.session = w0SA0 := hsess₀
  obtain ⟨hseeds₀, _, _, _, _, _, _, _, habk, hky⟩ := reachPq_inv hR₀
  refine
    { rc_len := Nat.le_trans g1fr_w0Ses0_rc_len1 (by decide)
      seeds32 := by
        rw [g1fr_w0Ses0_state, ← hsess₀']
        exact hseeds₀
      alice_len := by
        rw [g1fr_w0Ses0_eq]
        dsimp only [sessionOfX]
        exact Nat.le_of_eq habk
      kyber_cap := by
        intro k hk
        rw [g1fr_w0Ses0_eq] at hk
        unfold sessionOfX at hk
        dsimp only at hk
        split at hk
        · exact Nat.le_of_eq (hky k hk)
        · cases hk
      pq_len := by
        rw [g1fr_w0Ses0_state, ← hsess₀']
        exact reachPq_pqLength_le_286196 hR₀ }

private theorem g1fr_w0Rec0_encode_len_le :
    (encodeRecord w0Rec0).length ≤ 2097152 := by
  have heq : encodeRecord w0Rec0 = pqSessBytes w0St1 := by
    unfold w0Rec0 pqSessBytes w0St1
    exact (encodeRecordX_eq_toRecord (fun _ => w0XA) ⟨.A, w0SA0, 0, [0]⟩).symm
  have hcap : (pqSessBytes w0St1).length ≤ fileCapBytes :=
    pqSessBytes_le_fileCapBytes w0St1_domain
  have hfc : fileCapBytes = 2097152 := rfl
  rw [heq]
  omega

private theorem g1fr_w0_total_len :
    (encodeRecordPrev1Mem w0G0 w0Ses0 []).length ≤ 2469364 := by
  have hcanon := canonSession_of_sessionGhostValid w0G0_sessionGhostValid
  rw [encodeRecordPrev1Mem_eq_of_canon [] hcanon]
  unfold encodeRecordPrev1
  rw [g1fr_w0Rec0_some, List.length_append]
  have hrec := g1fr_w0Rec0_encode_len_le
  have hlf : (lenField 2 ([] : List (BitVec 8))).length = 2 := rfl
  omega

/-- Closed `PostBobPrev1Dom 286196 2097152 2469364` inhabitant at `(w0G0, w0Ses0, [])`. -/
theorem postBobPrev1Dom_idle_w0 :
    PostBobPrev1Dom 286196 2097152 2469364 w0G0 w0Ses0 [] where
  rc_len1 := g1fr_w0Ses0_rc_len1
  gv := w0G0_sessionGhostValid
  dom := g1fr_w0Ses0_dom
  prev_len := Nat.zero_le 2097152
  total_len := g1fr_w0_total_len

/-- Closed existential `PostBobPrev1Dom 286196 2097152 2469364` inhabitant at `enc = []`. -/
theorem postBobPrev1Dom_idle_exists :
    ∃ G ses, PostBobPrev1Dom 286196 2097152 2469364 G ses [] :=
  ⟨w0G0, w0Ses0, postBobPrev1Dom_idle_w0⟩

end LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1DomIdle
