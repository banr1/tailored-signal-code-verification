/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Init.Data.String.Defs
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import Symbolic.Tests.ModelNonVacuity
import Symbolic.Proofs.Tests.Shared.Composed.HonestSession
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Non-Vacuity of the Composed Protocol Security Definitions

Proves the non-vacuity and premise-satisfiability theorems (`sanityHonestSession`,
`sanityHonestWithOPK`, `sanityHonestWithoutOPK`, `fsPremiseSatisfiable`, and
`handshakeSecrecyPremiseSatisfiable`) for `Symbolic.Specifications.Security.Model` using the
concrete witness traces `wTr` and `wTrOpk`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Model.ComposedNonVacuity

open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (coins1 dhsA dhsA2 dhsB1 ikA ikB key0
  key3 keys1 m0 m1 m2 o1 pqm1 pqskB recv9 seedB0 seedB1 seedB3 seedB3_eq spkB stA0 stA1 stA4 stB0'
  stB1 stB2 stB4' t5 t5_length t6 t6_length t7 t7_length t8 t8_length t9 t9_length t10 t10_length
  t11 t11_length t12 t12_length t13 t13_length t14 t14_length t15 wTr wTrOpk wTrOpk_honestRun
  wTrOpk_noCompromise wTrOpk_reachable wTr_aliceDone wTr_bobDone wTr_ck_sent_at wTr_cks_sent_at
  wTr_honestRun wTr_noCompromise wTr_reachable wTr_stB1_at)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (encTr exposeCkrTr exposeCksTr knows_seed recvKey)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.DiffieHellman DY.PQKem
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open TripleRatchet (kdfCk)
open TripleRatchet.Cheval (Delivered DeliveredWithSalt DeliveredWithSpqrKey)

/-- `wTr` completes a PQXDH handshake (`AliceDone` 27, `BobDone` 47), two Alice-to-Bob messages,
and Bob's DH-ratcheted reply with no compromise events. -/
theorem sanityHonestSession : SanityHonestSession := by
  have hat_snoc : ∀ {E : Type} [ExecTraceTypes.Has E]
      (tr : ExecTrace) (e : ExecTrace.Entry) (i : Nat),
      ((tr.snoc e).at? i : Option E) =
        (if i = tr.length then TraceEntryHas.proj e
         else if i < tr.length then tr.at? i else none) := by
    intro E _ tr e i
    simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_2]
    by_cases h1 : i = tr.length
    · subst h1
      have hlt : tr.length < tr.length + 1 := Nat.lt_succ_self _
      simp only [hlt, ↓reduceDIte, ↓reduceIte, Symbolic.DYBridge.DY.Trace.at_eq_2]
    · by_cases h2 : i < tr.length
      · have hlt : i < tr.length + 1 := by omega
        simp only [h1, h2, hlt, ↓reduceDIte, ↓reduceIte, Symbolic.DYBridge.DY.Trace.at_eq_2]
      · have hlt : ¬ i < tr.length + 1 := by omega
        simp only [h1, h2, hlt, ↓reduceDIte, ↓reduceIte]
  have hev : ∀ (ev : TripleRatchet.TREvent) (i : Nat),
      ((wTr.at? i : Option (DY.ProtocolEvent.ExecEntryT TripleRatchet.TREvent)) =
        some { ev := ev }) → wTr.EventLoggedAt ev i := by
    intro ev i h
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
    exact h
  have hd0 : DeliveredWithSalt "alice" "bob" (dhPk dhsA) 0 m0 key0 wTr :=
    ⟨⟨⟨34, hev _ 34 (by
        simp only [wTr, t15, t14, t13, t12, t11, t10, t9, t8, t7, t6, encTr, exposeCksTr,
          exposeCkrTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
          Symbolic.DYBridge.DY.Trace.length_eq_2, t5_length, ↓reduceIte]
        rfl)⟩,
      ⟨51, hev _ 51 (by
        simp only [wTr, t15, t14, t13, t12, t11, t10, t9, t8, encTr, exposeCksTr,
          exposeCkrTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
          Symbolic.DYBridge.DY.Trace.length_eq_2, t7_length, ↓reduceIte]
        rfl)⟩⟩,
     ⟨stA0.sessionInfo "alice", (kdfCk stA0.cks).2, 1, 30, rfl,
      ⟨35, hev _ 35 (by
        simp only [wTr, t15, t14, t13, t12, t11, t10, t9, t8, t7, t6, encTr, exposeCksTr,
          exposeCkrTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
          Symbolic.DYBridge.DY.Trace.length_eq_2, t5_length, ↓reduceIte]
        rfl)⟩⟩,
     ⟨stB0'.sessionInfo "bob", seedB0, 2, 53, rfl,
      ⟨52, hev _ 52 (by
        simp only [wTr, t15, t14, t13, t12, t11, t10, t9, t8, encTr, exposeCksTr,
          exposeCkrTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
          Symbolic.DYBridge.DY.Trace.length_eq_2, t7_length, ↓reduceIte]
        rfl)⟩⟩⟩
  have hd1 : DeliveredWithSpqrKey "alice" "bob" (dhPk dhsA) 1 m1 wTr :=
    ⟨stA1, stB1, stB2, 36, 53, 57, coins1, 2, recvKey stB1.spqr pqm1,
      by unfold TripleRatchet.Cheval.StateStoredAt
         simp only [wTr, t15, t14, t13, t12, t11, t10, t9, t8, t7, t6, encTr, exposeCksTr,
           exposeCkrTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
           Symbolic.DYBridge.DY.Trace.length_eq_2, t5_length, ↓reduceIte]
         rfl,
      wTr_stB1_at,
      by unfold TripleRatchet.Cheval.StateStoredAt
         simp only [wTr, t15, t14, t13, t12, t11, t10, t9, encTr, exposeCksTr,
           exposeCkrTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
           Symbolic.DYBridge.DY.Trace.length_eq_2, t8_length, ↓reduceIte]
         rfl,
      recv9,
      ⟨⟨⟨41, hev _ 41 (by
          simp only [wTr, t15, t14, t13, t12, t11, t10, t9, t8, t7, encTr, exposeCksTr,
            exposeCkrTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
            Symbolic.DYBridge.DY.Trace.length_eq_2, t6_length, ↓reduceIte]
          rfl)⟩,
        ⟨55, hev _ 55 (by
          simp only [wTr, t15, t14, t13, t12, t11, t10, t9, encTr, exposeCksTr,
            exposeCkrTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
            Symbolic.DYBridge.DY.Trace.length_eq_2, t8_length, ↓reduceIte]
          rfl)⟩⟩,
       ⟨stA1.sessionInfo "alice", (kdfCk stA1.cks).2, 1, 36, rfl,
        ⟨42, hev _ 42 (by
          simp only [wTr, t15, t14, t13, t12, t11, t10, t9, t8, t7, encTr, exposeCksTr,
            exposeCkrTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
            Symbolic.DYBridge.DY.Trace.length_eq_2, t6_length, ↓reduceIte]
          rfl)⟩⟩,
       ⟨stB1.sessionInfo "bob", seedB1, 2, 53, rfl,
        ⟨56, hev _ 56 (by
          simp only [wTr, t15, t14, t13, t12, t11, t10, t9, encTr, exposeCksTr,
            exposeCkrTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
            Symbolic.DYBridge.DY.Trace.length_eq_2, t8_length, ↓reduceIte]
          rfl)⟩⟩⟩⟩
  exact ⟨wTr, wTr_reachable, wTr_noCompromise,
    "alice", "bob", dhPk ikA, dhPk ikB, dhPk spkB, kemPk pqskB, o1.ek, o1.ct, keys1,
    dhPk dhsA, dhPk dhsB1, dhPk dhsA2, m0, m1, m2, key0, by decide, wTr_aliceDone, wTr_bobDone,
    hd0, hd1,
    ⟨⟨61, hev _ 61 (by
        simp only [wTr, t15, t14, t13, t12, t11, t10, encTr, exposeCksTr,
          exposeCkrTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
          Symbolic.DYBridge.DY.Trace.length_eq_2, t9_length, ↓reduceIte]
        rfl)⟩,
     ⟨69, hev _ 69 (by
        simp only [wTr, t15, t14, t13, t12, t11, encTr, exposeCksTr,
          exposeCkrTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
          Symbolic.DYBridge.DY.Trace.length_eq_2, t10_length, ↓reduceIte]
        rfl)⟩⟩,
    ⟨67, hev _ 67 (by
        simp only [wTr, t15, t14, t13, t12, t11, encTr, exposeCksTr,
          exposeCkrTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
          Symbolic.DYBridge.DY.Trace.length_eq_2, t10_length, ↓reduceIte]
        rfl)⟩⟩

/-- `wTrOpk` completes an honest handshake with a one-time prekey (`opk = some (dhPk opkB)`) and no
compromise. -/
theorem sanityHonestWithOPK : SanityHonestWithOPK :=
  ⟨wTrOpk, wTrOpk_reachable, wTrOpk_honestRun, wTrOpk_noCompromise⟩

/-- `wTr` completes an honest handshake without a one-time prekey (`opk = none`) and no
compromise. -/
theorem sanityHonestWithoutOPK : SanityHonestWithoutOPK :=
  ⟨wTr, wTr_reachable, wTr_honestRun, wTr_noCompromise⟩

/-- Both `.sender` (`MessageKey` 80) and `.receiver` (`MessageKey` 88) satisfy the forward-secrecy
premise on `wTr` via Alice's exposed sending chain key at index 75. -/
theorem fsPremiseSatisfiable : FSPremiseSatisfiable := by
  have hat_snoc : ∀ {E : Type} [ExecTraceTypes.Has E]
      (tr : ExecTrace) (e : ExecTrace.Entry) (i : Nat),
      ((tr.snoc e).at? i : Option E) =
        (if i = tr.length then TraceEntryHas.proj e
         else if i < tr.length then tr.at? i else none) := by
    intro E _ tr e i
    simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_2]
    by_cases h1 : i = tr.length
    · subst h1
      have hlt : tr.length < tr.length + 1 := Nat.lt_succ_self _
      simp only [hlt, ↓reduceDIte, ↓reduceIte, Symbolic.DYBridge.DY.Trace.at_eq_2]
    · by_cases h2 : i < tr.length
      · have hlt : i < tr.length + 1 := by omega
        simp only [h1, h2, hlt, ↓reduceDIte, ↓reduceIte, Symbolic.DYBridge.DY.Trace.at_eq_2]
      · have hlt : ¬ i < tr.length + 1 := by omega
        simp only [h1, h2, hlt, ↓reduceDIte, ↓reduceIte]
  have h80 : wTr.EventLoggedAt
      (TripleRatchet.TREvent.MessageKey (stA4.sessionInfo "alice") .sender
        (kdfCk stA4.cks).2 key3 0 3 71) 80 := by
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
    simp only [wTr, t15, t14, encTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      hat_snoc, Symbolic.DYBridge.DY.Trace.length_eq_2, t13_length, ↓reduceIte]
    rfl
  have h88 : wTr.EventLoggedAt
      (TripleRatchet.TREvent.MessageKey (stB4'.sessionInfo "bob") .receiver
        seedB3 key3 0 4 63) 88 := by
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
    simp only [wTr, t15, Symbolic.DYBridge.DY.Trace.append_eq_1,
      hat_snoc, Symbolic.DYBridge.DY.Trace.length_eq_2, t14_length, ↓reduceIte]
    rfl
  intro dir
  refine ⟨wTr, wTr_reachable, ?_⟩
  cases dir with
  | sender =>
    exact ⟨stA4.sessionInfo "alice", (kdfCk stA4.cks).2, key3, 0, 3, 71,
      ⟨80, h80⟩, Or.inl (knows_seed (i := 75) wTr_cks_sent_at)⟩
  | receiver =>
    refine ⟨stB4'.sessionInfo "bob", seedB3, key3, 0, 4, 63, ⟨88, h88⟩, Or.inl ?_⟩
    rw [← seedB3_eq]
    exact knows_seed (i := 75) wTr_cks_sent_at

/-- Session 1 (`AliceDone` 27, `BobDone` 47) on `wTr` has no PQXDH compromise and an attacker-known
initial chain key `HandshakeKeys.ck` via `ExposedCKr` at index 72 (`SessionStateExposed`). -/
theorem handshakeSecrecyPremiseSatisfiable : HandshakeSecrecyPremiseSatisfiable :=
  ⟨wTr, wTr_reachable, wTr_noCompromise, "alice", "bob", dhPk ikA, dhPk ikB, dhPk spkB,
    kemPk pqskB, o1.ek, o1.ct, keys1, by decide, wTr_aliceDone, wTr_bobDone,
    Or.inr (Or.inl (Trace.MessageSentAt_implies_AttackerKnows _ _ _ wTr_ck_sent_at))⟩

end Symbolic.Proofs.Tests.Model.ComposedNonVacuity
