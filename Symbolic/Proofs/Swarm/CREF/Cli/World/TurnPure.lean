/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.LeakRecordsCompat
public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.OpkRelC
import Symbolic.Proofs.Refinement.Composed.Cli.Transfer
import Symbolic.Proofs.Swarm.CREF.Cli.World.InitPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Sticky

/-!
# CLI Turn Path Scrubbing and `clearSession` Transitions

Proves that `scrub` preserves session and one-time-prekey paths, `CliTurn.clearSession` erases the
target participant's record in `PureCRel` without altering `COpkRelC`, and `leakRecords` agrees with
`records` on the active caller under `ValidCall`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.SignalSession (coinsFile bundleDir oneTimePreKeyFile)
open DY.Libsignal.Composed.Refinement.Cli (CliCall CliTurn SamePath scrub sessionPathOf
  PreKeyNoMatch ValidCall samePath_oneTimePreKeyFile_sessionPathOf)

@[simp] theorem samePath_refl (p : String) : SamePath p p = true := by
  unfold SamePath
  exact beq_self_eq_true _

@[simp] theorem scrub_sessionPathOf (d : String → Option HwBytes) (r : ProtocolSetup) (p : Participant) :
    scrub d (sessionPathOf r p) = d (sessionPathOf r p) := by
  unfold scrub
  have h1 : SamePath (sessionPathOf r p) coinsFile = false := by
    unfold SamePath
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have hs := normalizePath_sessionPathOf_head r p
    have hc : (Arm64.normalizePath coinsFile).head? = some "coins" := by decide
    rw [heq, hc] at hs; exact absurd hs (by decide)
  have h2 : ((Arm64.normalizePath (sessionPathOf r p)).head? == some bundleDir) = false := by
    rw [normalizePath_sessionPathOf_head]
    decide
  simp [h1, h2]

@[simp] theorem scrub_oneTimePreKeyFile (d : String → Option HwBytes) (id : BitVec 32) :
    scrub d (oneTimePreKeyFile id) = d (oneTimePreKeyFile id) := by
  unfold scrub
  have h1 : SamePath (oneTimePreKeyFile id) coinsFile = false := by
    unfold SamePath
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have hs := normalizePath_oneTimePreKeyFile_head id
    have hc : (Arm64.normalizePath coinsFile).head? = some "coins" := by decide
    rw [heq, hc] at hs; exact absurd hs (by decide)
  have h2 : ((Arm64.normalizePath (oneTimePreKeyFile id)).head? == some bundleDir) = false := by
    rw [normalizePath_oneTimePreKeyFile_head]
    decide
  simp [h1, h2]

theorem clearSession_records (t : CliTurn) (r : ProtocolSetup) (p : Participant) :
    (t.clearSession r p).records r = fun q => if q = p then none else t.records r q := by
  funext q
  by_cases hqp : q = p
  · subst hqp
    simp [CliTurn.records, CliTurn.clearSession, samePath_refl]
  · simp [CliTurn.records, CliTurn.clearSession, hqp]

theorem clearSession_leakRecords (t : CliTurn) (r : ProtocolSetup) (p : Participant) :
    (t.clearSession r p).leakRecords r = fun q => if q = p then none else t.leakRecords r q := by
  funext q
  by_cases hqp : q = p
  · subst hqp
    unfold CliTurn.leakRecords
    rw [clearSession_records]
    simp
  · unfold CliTurn.leakRecords
    rw [clearSession_records]
    simp only [hqp, ↓reduceIte, CliTurn.clearSession]
    by_cases hqb : q = r.bob
    · subst hqb
      have hne : p ≠ r.bob := Ne.symm hqp
      simp [hne]
    · simp [hqb]

@[simp] theorem clearSession_opkUsed (t : CliTurn) (r : ProtocolSetup) (p : Participant) :
    (t.clearSession r p).opkUsed r = t.opkUsed r := by
  unfold CliTurn.opkUsed CliTurn.clearSession
  dsimp only
  by_cases hbp : r.bob = p
  · subst hbp
    simp [samePath_oneTimePreKeyFile_sessionPathOf]
  · simp [hbp]

@[simp] theorem clearSession_sent (t : CliTurn) (r : ProtocolSetup) (p : Participant) :
    (t.clearSession r p).sent = t.sent := rfl

theorem pureCRel_clearSession {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {t : CliTurn} {accepted : List HwBytes} {acc : List MachineEvent} (p : Participant)
    (hrel : PureCRel interp r S who ok (t.leakRecords r) t.sent accepted acc) :
    PureCRel interp r S who ok ((t.clearSession r p).leakRecords r)
      (t.clearSession r p).sent accepted acc := by
  rw [clearSession_leakRecords, clearSession_sent]
  exact pureCRel_eraseRecord p hrel

theorem cOpkRelC_clearSession {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {t : CliTurn} {acc : List MachineEvent} (p : Participant)
    (hopk : COpkRelC interp r S who ok (t.opkUsed r) acc) :
    COpkRelC interp r S who ok ((t.clearSession r p).opkUsed r) acc := by
  rw [clearSession_opkUsed]
  exact hopk

theorem leakRecords_eq_records_of_bobOff_false {t : CliTurn} (r : ProtocolSetup)
    (hoff : t.bobOff = false) :
    t.leakRecords r = t.records r := by
  funext p
  simp [CliTurn.leakRecords, hoff]

/-- On any guarded `ValidCall`, `t.leakRecords r c.party = t.records r c.party` because
`BobCallAllowed` prevents Bob from being called when `t.bobOff = true`. -/
theorem leakRecords_party_eq_of_cliNextCall {interp : ExternInterpretation} {r : ProtocolSetup}
    {t : CliTurn} {c : CliCall} (hnext : ValidCall interp r t c) :
    t.leakRecords r c.party = t.records r c.party := by
  unfold CliTurn.leakRecords
  split
  · rename_i h
    exact absurd h.2 (hnext.2.2.2.1 h.1)
  · rfl

end Symbolic.Swarm.CREF.CliPure
