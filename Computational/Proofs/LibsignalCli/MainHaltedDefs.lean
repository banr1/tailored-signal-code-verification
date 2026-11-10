/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.ModelIface
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge

/-!
# Shared Halted-Game Tracker and Target-Adversary Query Bounds

Defines the `KemFailSessionTrack` per-session halt tracker `kemFailCoreTracker`, proves its
online soundness `validSessionHaltTracker_kemFailCoreTracker`, and defines the target-adversary
query-bound bundle `TargetAdvPerInstanceBounded`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.MainHaltedDefs

open scoped BigOperators
open OracleComp OracleSpec
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)
open CryptoVerification.E2E (SampledSessionKey bhTargetGameSpec)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack
  KemTrackLoggedInv cand_eq_none_of_kemTrackLoggedInv initKemFailSessionTrack
  kemTrackLoggedInv_init kemTrackLoggedInv_mono kemTrackLoggedInv_stepKemFailDeliver
  kemTrackLoggedInv_stepKemFailSend kemTrackLoggedInv_stepKemFailSend_candOnly
  stepKemFailDeliver stepKemFailSend)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (SessionHaltTracker
  ValidSessionHaltTracker bhClassifyTarget)

/-- `KemFailSessionTrack F C` packaged as a `SessionHaltTracker`, halting on `transmit`/`chall`
when `stepKemFailSend` detects a candidate decapsulation failure. -/
def kemFailCoreTracker {St Msg C : Type} [DecidableEq C] (F : ShaCompress) (K : MlKem) :
    SessionHaltTracker St Msg (BitVec 512) C SampledSessionKey (KemFailSessionTrack F C) where
  init k := initKemFailSessionTrack F C k.2.2
  onSend _ P coins st :=
    let tr' := stepKemFailSend F K st.1 P coins
    (tr'.cand.isSome, ({ st.1 with cand := tr'.cand }, st.2), fun ct => (tr', (ct, P) :: st.2))
  onDeliver _ Q w res st :=
    match res, st.2.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) with
    | some (.accepted _ _ _), some j => (stepKemFailDeliver F K st.1 Q j, st.2)
    | _, _ => st

/-- Under `KemTrackLoggedInv`, `kemFailCoreTracker` never halts on `KemFailBad`-free coin logs and
preserves `KemTrackLoggedInv` across `init`, `deliver`, and `send`. -/
theorem validSessionHaltTracker_kemFailCoreTracker {St Msg C : Type} [DecidableEq C]
    (F : ShaCompress) (K : MlKem) :
    ValidSessionHaltTracker
      (fun gLog : List (BitVec 512) => K.KemFailBad (gLog.map coinBytes))
      (kemFailCoreTracker (St := St) (Msg := Msg) (C := C) F K)
      (fun st gLog => KemTrackLoggedInv K st.1 gLog) where
  inv_init k _ :=
    kemTrackLoggedInv_mono (kemTrackLoggedInv_init F K k.2.2) (fun _ hr => nomatch hr)
  inv_mono c hinv :=
    kemTrackLoggedInv_mono hinv (fun _ hr => List.mem_append_left [c] hr)
  inv_deliver _ Q w res {st} {_} hinv := by
    dsimp [kemFailCoreTracker]
    cases res with
    | none => exact hinv
    | some r =>
      cases r with
      | rejected => exact hinv
      | accepted _ _ _ =>
        cases st.2.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) with
        | none => exact hinv
        | some j => exact kemTrackLoggedInv_stepKemFailDeliver hinv Q j
  send_good _ P coins {st} {gLog} hinv := by
    dsimp [kemFailCoreTracker]
    have hinv_ok := kemTrackLoggedInv_stepKemFailSend hinv P coins
    have hinv_halt := kemTrackLoggedInv_stepKemFailSend_candOnly hinv P coins
    refine ⟨fun hgood => ?_, hinv_halt, fun _ => hinv_ok⟩
    have hnone := cand_eq_none_of_kemTrackLoggedInv K hinv_ok hgood
    simp [hnone]

/-- Per-category and per-instance `IsQueryBoundP` contract on a model-target adversary `B`. -/
def TargetAdvPerInstanceBounded {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) : Prop :=
  B.IsQueryBoundP
    (fun q => bhClassifyTarget
      (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) q = true)
    b.q_ro ∧
  B.IsQueryBoundP
    (fun q => bhClassifyTarget
      (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
      (fun _ => false) (fun _ => false) q = true)
    S.N_send_tot ∧
  B.IsQueryBoundP
    (fun q => bhClassifyTarget
      (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
      (fun _ => false) (fun _ => false) q = true)
    S.N_recv_tot ∧
  B.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
    b.q_total ∧
  B.IsQueryBoundP
    (fun q => bhClassifyTarget
      (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true)
    b.q_on ∧
  B.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
    S.N_send_tot ∧
  B.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
    qStart ∧
  B.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
    (∑ k ∈ Finset.range qStart, qs k) ∧
  (∀ k < qStart, B.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
    (qs k))

end Computational.Proofs.LibsignalCli.MainHaltedDefs
