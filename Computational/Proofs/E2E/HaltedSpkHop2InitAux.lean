/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.HaltedSpkDefs
public import Computational.Proofs.E2E.SpkHop1InitBridge

/-!
# Tracker-Halted Hop-1 SPK Evaluators

Defines the `KemFailSessionTrack`-carrying SPK evaluators (`runSpkTabTrack`, `runSpkRefTrack`,
`runSpkBadTrack`, `runSpkCombTrack`), proves `prfOracleImpl` simulation and `patchGameSpk`
commutation for halted sends, and bounds `runSpkTabTrack` against `runSpkRefTrack`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.HaltedSpkHop2InitAux

open scoped BigOperators ENNReal
open Classical
open OracleComp OracleSpec
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack
  challRTrackHalted stepKemFailSend transmitRTrackHalted)
open Computational.Proofs.E2E.HaltedSpkDefs (challRTrackHalted_support deliverSpkTrackHalted_run
  liftSpkGameTrackHaltedM liftSpkNoTrackM spkOracleImplTrackHalted
  transmitRTrackHalted_support updateKemFailOnDeliver)
open CryptoGames (MACScheme Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSM.Proofs.Refinement (GameSt TransShort ct_length_lt_of_inTransit
  eps0IdealUnit isAliceSpkQuery ratchetKeyAdmissible_length_lt_of_tryFrom testSpk testSpk_le_unit)
open CryptoGames.LibsignalSM.Proofs.RoundTrip (RtHyp)
open CryptoGames.LibsignalSession (GhostState KeyPair Params PublicKey ShaCompress SignalMessage)
open CryptoGames.MACScheme (PRFState prfSpec)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.SM (ConfigR GameState MakesAtMostQueries corrR noBobSendInEpoch0 spec)
open CryptoVerification.E2E (Bytes configRefuseEarlyBobCorr sessionSchemeU spkOracleImpl)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.E2E.SpkHop1 (SpkRefInv SpkRefSt SpkTabSt badSpkCorrA
  bind_apply_le_add_of_evalDist_le_on_good bind_eq_of_support bind_evalDist_true_le_of_support
  bind_or_evalDist_true_le challR_support_spkRefInv challR_support_transShort
  corrR_patchGameSpk_of_badSpkCorrA_false corrR_support_spkRefInv corrR_support_transShort
  corrSpkRef deliverSpkBad deliverSpkRef deliverSpkRef_support_spkRefInv
  deliverSpkRef_support_transShort deliverSpkStep deliverSpkStep_patchGameSpk_of_not_spk
  evalDist_true_le_one gameInv_of_spkRefInv_win_false injectSpkBad injectSpkRef
  injectSpkRef_support_spkRefInv injectSpkRef_support_transShort injectSpkStep
  injectSpkStep_patchGameSpk_of_not_spk liftSpkTab liftSpkTab_run patchGameSpk patchGameSpk_epMgmt
  patchGameSpk_party_eq prfOracleImpl receive_patchGameSpk_of_spk_test_false send_record_patchGameSpk
  simulateQ_prfOracleImpl_liftM_bind spkBadImpl_run_bind_fst spkBadImpl_support_bad_true
  spkOracleImpl_true_tableFor_step_bind spkRefImpl_support_abort_true spkRefInv_party_eq spkStepImpl
  stateT_lift_run_any stepReceiveRef stepReceiveSpk tableFor transmitR_support_spkRefInv
  transmitR_support_transShort)
open CryptoVerification.LibsignalSpqrV1 (MlKem)

section Evaluators

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-! ## Tracker-carrying SPK evaluators -/

abbrev SpkTabTrackSt (F : ShaCompress) (Pt : Type) (ℓ : ℕ) :=
  SpkTabSt Pt ℓ × KemFailSessionTrack F Bytes

abbrev SpkRefTrackSt (F : ShaCompress) (Pt : Type) (ℓ : ℕ) :=
  SpkRefSt Pt ℓ × KemFailSessionTrack F Bytes

def spkStepImplTrack {ℓ : ℕ} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) :
    QueryImpl (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (SpkTabTrackSt P.C.F Pt ℓ) ProbComp)
  | .inl u => StateT.lift (query (spec := unifSpec) u)
  | .inr (.inl (.inl (.inl (.inl x)))) =>
    StateT.mk fun ⟨⟨st, L⟩, tr⟩ => do
      let ((a, st'), tr') ←
        ((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) x).run st).run tr
      return (a, ((st', L), tr'))
  | .inr (.inl (.inl (.inl (.inr x)))) =>
    StateT.mk fun ⟨⟨st, L⟩, tr⟩ => do
      let ((a, st'), tr') ←
        ((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) x).run st).run tr
      return (a, ((st', L), tr'))
  | .inr (.inl (.inl (.inr x))) =>
    StateT.mk fun ⟨stL, tr⟩ => do
      let (res, stL') ← (deliverSpkStep P ℓ Dh encT decT s x).run stL
      return (res, (stL', updateKemFailOnDeliver P.C.F K tr x res))
  | .inr (.inl (.inr x)) =>
    StateT.mk fun ⟨stL, tr⟩ => do
      let (res, stL') ← (injectSpkStep P ℓ Dh encT decT qep s x).run stL
      return (res, (stL', tr))
  | .inr (.inr x) =>
    StateT.mk fun ⟨stL, tr⟩ => do
      let (res, stL') ← (liftSpkTab (corrR (configRefuseEarlyBobCorr decT encT) x)).run stL
      return (res, (stL', tr))

def spkRefImplTrack {ℓ : ℕ} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) :
    QueryImpl (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (SpkRefTrackSt P.C.F Pt ℓ) ProbComp)
  | .inl u => StateT.lift (query (spec := unifSpec) u)
  | .inr (.inl (.inl (.inl (.inl x)))) =>
    StateT.mk fun ⟨⟨st, L, b⟩, tr⟩ => do
      let ((a, st'), tr') ←
        ((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) x).run st).run tr
      return (a, ((st', L, b), tr'))
  | .inr (.inl (.inl (.inl (.inr x)))) =>
    StateT.mk fun ⟨⟨st, L, b⟩, tr⟩ => do
      let ((a, st'), tr') ←
        ((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) x).run st).run tr
      return (a, ((st', L, b), tr'))
  | .inr (.inl (.inl (.inr x))) =>
    StateT.mk fun ⟨stR, tr⟩ => do
      let (res, stR') ← (deliverSpkRef P ℓ Dh encT decT s x).run stR
      return (res, (stR', updateKemFailOnDeliver P.C.F K tr x res))
  | .inr (.inl (.inr x)) =>
    StateT.mk fun ⟨stR, tr⟩ => do
      let (res, stR') ← (injectSpkRef P ℓ Dh encT decT qep s x).run stR
      return (res, (stR', tr))
  | .inr (.inr x) =>
    StateT.mk fun ⟨stR, tr⟩ => do
      let (res, stR') ← (corrSpkRef ℓ decT encT x).run stR
      return (res, (stR', tr))

def spkBadImplTrack {ℓ : ℕ} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) :
    QueryImpl (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (SpkRefTrackSt P.C.F Pt ℓ) ProbComp)
  | .inl u => StateT.lift (query (spec := unifSpec) u)
  | .inr (.inl (.inl (.inl (.inl x)))) =>
    StateT.mk fun ⟨⟨st, L, b⟩, tr⟩ => do
      let ((a, st'), tr') ←
        ((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) x).run st).run tr
      return (a, ((st', L, b), tr'))
  | .inr (.inl (.inl (.inl (.inr x)))) =>
    StateT.mk fun ⟨⟨st, L, b⟩, tr⟩ => do
      let ((a, st'), tr') ←
        ((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) x).run st).run tr
      return (a, ((st', L, b), tr'))
  | .inr (.inl (.inl (.inr x))) =>
    StateT.mk fun ⟨stB, tr⟩ => do
      let (res, stB') ← (deliverSpkBad P ℓ Dh encT decT s x).run stB
      return (res, (stB', updateKemFailOnDeliver P.C.F K tr x res))
  | .inr (.inl (.inr x)) =>
    StateT.mk fun ⟨stB, tr⟩ => do
      let (res, stB') ← (injectSpkBad P ℓ Dh encT decT qep s x).run stB
      return (res, (stB', tr))
  | .inr (.inr x) =>
    StateT.mk fun ⟨stB, tr⟩ => do
      let (res, stB') ← (corrSpkRef ℓ decT encT x).run stB
      return (res, (stB', tr))

def runSpkTabTrack {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (tr : KemFailSessionTrack P.C.F Bytes)
    (post : β → GameSt Bytes ℓ → Bool) : ProbComp Bool := do
  let (b', ((fin, _), _)) ← (simulateQ (spkStepImplTrack P K Dh encT decT qep s) oa).run ((st, L), tr)
  return post b' fin

def runSpkRefTrack {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (abort : Bool)
    (tr : KemFailSessionTrack P.C.F Bytes) (post : β → GameSt Bytes ℓ → Bool) : ProbComp Bool := do
  let (b', ((fin, _, abort'), _)) ←
    (simulateQ (spkRefImplTrack P K Dh encT decT qep s) oa).run ((sRef, L, abort), tr)
  return (abort' || post b' fin)

def runSpkBadTrack {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool)
    (tr : KemFailSessionTrack P.C.F Bytes) : ProbComp Bool := do
  let (_, ((_, _, bad'), _)) ←
    (simulateQ (spkBadImplTrack P K Dh encT decT qep s) oa).run ((st, L, bad), tr)
  return bad'

def runSpkCombTrack {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool)
    (tr : KemFailSessionTrack P.C.F Bytes) (post : β → GameSt Bytes ℓ → Bool) : ProbComp Bool := do
  let (b', ((fin, _, bad'), _)) ←
    (simulateQ (spkBadImplTrack P K Dh encT decT qep s) oa).run ((st, L, bad), tr)
  return (bad' || post b' fin)

omit [SampleableType Pt] in
@[simp] theorem runSpkTabTrack_pure {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (a : β) (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256))
    (tr : KemFailSessionTrack P.C.F Bytes) (post : β → GameSt Bytes ℓ → Bool) :
    runSpkTabTrack P K Dh encT decT qep s (pure a) st L tr post = pure (post a st) := by
  simp [runSpkTabTrack, StateT.run_pure]

omit [SampleableType Pt] in
theorem runSpkTabTrack_bind_query {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512))
    (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (k : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range t →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (tr : KemFailSessionTrack P.C.F Bytes)
    (post : β → GameSt Bytes ℓ → Bool) :
    runSpkTabTrack P K Dh encT decT qep s
      (liftM (OracleSpec.query (spec := unifSpec +
          spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) t) >>= k) st L tr post =
      ((spkStepImplTrack P K Dh encT decT qep s t).run ((st, L), tr) >>= fun r =>
        runSpkTabTrack P K Dh encT decT qep s (k r.1) r.2.1.1 r.2.1.2 r.2.2 post) := by
  simp [runSpkTabTrack, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind]

omit [SampleableType Pt] in
@[simp] theorem runSpkRefTrack_pure {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (a : β) (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256))
    (abort : Bool) (tr : KemFailSessionTrack P.C.F Bytes) (post : β → GameSt Bytes ℓ → Bool) :
    runSpkRefTrack P K Dh encT decT qep s (pure a) sRef L abort tr post =
      pure (abort || post a sRef) := by
  simp [runSpkRefTrack, StateT.run_pure]

omit [SampleableType Pt] in
theorem runSpkRefTrack_bind_query {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512))
    (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (k : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range t →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (abort : Bool)
    (tr : KemFailSessionTrack P.C.F Bytes) (post : β → GameSt Bytes ℓ → Bool) :
    runSpkRefTrack P K Dh encT decT qep s
      (liftM (OracleSpec.query (spec := unifSpec +
          spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) t) >>= k) sRef L abort tr post =
      ((spkRefImplTrack P K Dh encT decT qep s t).run ((sRef, L, abort), tr) >>= fun r =>
        runSpkRefTrack P K Dh encT decT qep s (k r.1) r.2.1.1 r.2.1.2.1 r.2.1.2.2 r.2.2 post) := by
  simp [runSpkRefTrack, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind]

omit [SampleableType Pt] in
@[simp] theorem runSpkBadTrack_pure {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (a : β) (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256))
    (bad : Bool) (tr : KemFailSessionTrack P.C.F Bytes) :
    runSpkBadTrack P K Dh encT decT qep s (pure a) st L bad tr = pure bad := by
  simp [runSpkBadTrack, StateT.run_pure]

omit [SampleableType Pt] in
theorem runSpkBadTrack_bind_query {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512))
    (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (k : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range t →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool)
    (tr : KemFailSessionTrack P.C.F Bytes) :
    runSpkBadTrack P K Dh encT decT qep s
      (liftM (OracleSpec.query (spec := unifSpec +
          spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) t) >>= k) st L bad tr =
      ((spkBadImplTrack P K Dh encT decT qep s t).run ((st, L, bad), tr) >>= fun r =>
        runSpkBadTrack P K Dh encT decT qep s (k r.1) r.2.1.1 r.2.1.2.1 r.2.1.2.2 r.2.2) := by
  simp [runSpkBadTrack, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind]

omit [SampleableType Pt] in
@[simp] theorem runSpkCombTrack_pure {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (a : β) (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256))
    (bad : Bool) (tr : KemFailSessionTrack P.C.F Bytes) (post : β → GameSt Bytes ℓ → Bool) :
    runSpkCombTrack P K Dh encT decT qep s (pure a) st L bad tr post = pure (bad || post a st) := by
  simp [runSpkCombTrack, StateT.run_pure]

omit [SampleableType Pt] in
theorem runSpkCombTrack_bind_query {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512))
    (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (k : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range t →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool)
    (tr : KemFailSessionTrack P.C.F Bytes) (post : β → GameSt Bytes ℓ → Bool) :
    runSpkCombTrack P K Dh encT decT qep s
      (liftM (OracleSpec.query (spec := unifSpec +
          spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) t) >>= k) st L bad tr post =
      ((spkBadImplTrack P K Dh encT decT qep s t).run ((st, L, bad), tr) >>= fun r =>
        runSpkCombTrack P K Dh encT decT qep s (k r.1) r.2.1.1 r.2.1.2.1 r.2.1.2.2 r.2.2 post) := by
  simp [runSpkCombTrack, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind]

/-! ## `prfOracleImpl` simulation and absorbing states -/

omit [SampleableType Pt] in
theorem spkOracleImplTrackHalted_true_tableFor_step_bind {Key α : Type} {ℓ : ℕ}
    (mac : MACScheme Key Pt (BitVec 256)) (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P_pt P' : Pt), Dh.dh x P_pt = Dh.dh x P' ↔ Dh.dh s P_pt =
        Dh.dh s P')
    (key : Key) (z : BitVec 256)
    (q : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (L : List (Pt × BitVec 256)) (tr : KemFailSessionTrack P.C.F Bytes)
    (F : (((unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range q ×
          GameState (GhostState Bytes) (Plain ℓ) Bytes) × KemFailSessionTrack P.C.F Bytes) ×
          PRFState Key Pt (BitVec 256) → ProbComp α) :
    ((simulateQ (prfOracleImpl mac)
        (((spkOracleImplTrackHalted P K ℓ Dh encT decT qep z q).run st).run tr)).run
        ⟨key, true, tableFor Dh z L⟩ >>= F) =
      ((spkStepImplTrack P K Dh encT decT qep s q).run ((st, L), tr) >>= fun r =>
        F (((r.1, r.2.1.1), r.2.2), ⟨key, true, tableFor Dh z r.2.1.2⟩)) := by
  rcases q with u | ((((q_tr | q_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | q_corr)
  · dsimp only [spkOracleImplTrackHalted, spkStepImplTrack]
    simp only [stateT_lift_run_any, StateT.run_bind, StateT.run_pure, simulateQ_bind,
      simulateQ_pure, bind_assoc, pure_bind]
    have h := spkOracleImpl_true_tableFor_step_bind mac P Dh encT decT qep s hker key z
      (.inl u) st L (fun x => F ((x.1, tr), x.2))
    dsimp only [spkOracleImpl, spkStepImpl] at h
    simp only [stateT_lift_run_any, StateT.run_bind, StateT.run_pure, simulateQ_bind,
      simulateQ_pure, bind_assoc, pure_bind] at h
    exact h
  · dsimp only [spkOracleImplTrackHalted, spkStepImplTrack, liftSpkGameTrackHaltedM]
    rw [StateT.run_mk, StateT.run_mk, StateT.run_mk, simulateQ_prfOracleImpl_liftM_bind]
    simp
  · dsimp only [spkOracleImplTrackHalted, spkStepImplTrack, liftSpkGameTrackHaltedM]
    rw [StateT.run_mk, StateT.run_mk, StateT.run_mk, simulateQ_prfOracleImpl_liftM_bind]
    simp
  · dsimp only [spkOracleImplTrackHalted, spkStepImplTrack]
    rw [deliverSpkTrackHalted_run, StateT.run_mk]
    simp only [map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
    have h := spkOracleImpl_true_tableFor_step_bind mac P Dh encT decT qep s hker key z
      (.inr (.inl (.inl (.inr (Q, c))))) st L
      (fun x => F (((x.1.1, x.1.2), updateKemFailOnDeliver P.C.F K tr (Q, c) x.1.1), x.2))
    dsimp only [spkOracleImpl, spkStepImpl] at h
    exact h
  · dsimp only [spkOracleImplTrackHalted, spkStepImplTrack, liftSpkNoTrackM]
    rw [StateT.run_mk, StateT.run_lift, StateT.run_mk]
    simp only [simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
    have h := spkOracleImpl_true_tableFor_step_bind mac P Dh encT decT qep s hker key z
      (.inr (.inl (.inr (Q, c)))) st L (fun x => F (((x.1.1, x.1.2), tr), x.2))
    dsimp only [spkOracleImpl, spkStepImpl] at h
    exact h
  · dsimp only [spkOracleImplTrackHalted, spkStepImplTrack, liftSpkNoTrackM]
    rw [StateT.run_mk, StateT.run_lift, StateT.run_mk]
    simp only [simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
    have h := spkOracleImpl_true_tableFor_step_bind mac P Dh encT decT qep s hker key z
      (.inr (.inr q_corr)) st L (fun x => F (((x.1.1, x.1.2), tr), x.2))
    dsimp only [spkOracleImpl, spkStepImpl] at h
    exact h

omit [SampleableType Pt] in
theorem simulateQ_prfOracleImpl_spkOracleImplTrackHalted_bind {Key α β : Type} {ℓ : ℕ}
    (mac : MACScheme Key Pt (BitVec 256)) (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P_pt P' : Pt), Dh.dh x P_pt = Dh.dh x P' ↔ Dh.dh s P_pt =
        Dh.dh s P')
    (key : Key) (z : BitVec 256)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (L : List (Pt × BitVec 256)) (tr : KemFailSessionTrack P.C.F Bytes)
    (F : ((β × GameState (GhostState Bytes) (Plain ℓ) Bytes) × KemFailSessionTrack P.C.F Bytes) ×
          PRFState Key Pt (BitVec 256) → ProbComp α) :
    ((simulateQ (prfOracleImpl mac)
        (((simulateQ (spkOracleImplTrackHalted P K ℓ Dh encT decT qep z) oa).run st).run tr)).run
        ⟨key, true, tableFor Dh z L⟩ >>= F) =
      ((simulateQ (spkStepImplTrack P K Dh encT decT qep s) oa).run ((st, L), tr) >>= fun r =>
        F (((r.1, r.2.1.1), r.2.2), ⟨key, true, tableFor Dh z r.2.1.2⟩)) := by
  induction oa using OracleComp.inductionOn generalizing st L tr with
  | pure a => simp [StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    rw [spkOracleImplTrackHalted_true_tableFor_step_bind mac P K Dh encT decT qep s hker key z t
      st L tr]
    refine bind_congr fun r => ih r.1 r.2.1.1 r.2.1.2 r.2.2

omit [SampleableType Pt] in
theorem spkRefImplTrack_support_abort_true {ℓ : ℕ} (P : Params Bytes (BitVec 512))
    (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (tr : KemFailSessionTrack P.C.F Bytes) :
    ∀ r ∈ support ((spkRefImplTrack P K Dh encT decT qep s t).run ((st, L, true), tr)),
      r.2.1.2.2 = true := by
  intro r hr
  rcases t with u | ((((q_tr | q_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | q_corr)
  · dsimp only [spkRefImplTrack] at hr
    rw [stateT_lift_run_any] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl
  · dsimp only [spkRefImplTrack] at hr
    rw [StateT.run_mk] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl
  · dsimp only [spkRefImplTrack] at hr
    rw [StateT.run_mk] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl
  · dsimp only [spkRefImplTrack] at hr
    rw [StateT.run_mk] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨x, hx, rfl⟩
    exact spkRefImpl_support_abort_true P Dh encT decT qep s (.inr (.inl (.inl (.inr (Q, c)))))
      st L x hx
  · dsimp only [spkRefImplTrack] at hr
    rw [StateT.run_mk] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨x, hx, rfl⟩
    exact spkRefImpl_support_abort_true P Dh encT decT qep s (.inr (.inl (.inr (Q, c))))
      st L x hx
  · dsimp only [spkRefImplTrack] at hr
    rw [StateT.run_mk] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨x, hx, rfl⟩
    exact spkRefImpl_support_abort_true P Dh encT decT qep s (.inr (.inr q_corr)) st L x hx

omit [SampleableType Pt] in
theorem evalDist_runSpkRefTrack_true {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512))
    (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (tr : KemFailSessionTrack P.C.F Bytes)
    (post : β → GameSt Bytes ℓ → Bool) :
    𝒟[runSpkRefTrack P K Dh encT decT qep s oa sRef L true tr post] {true} = 1 := by
  induction oa using OracleComp.inductionOn generalizing sRef L tr with
  | pure a => simp [runSpkRefTrack_pure]
  | query_bind t k ih =>
    rw [runSpkRefTrack_bind_query]
    exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r hr => by
      rw [spkRefImplTrack_support_abort_true P K Dh encT decT qep s t sRef L tr r hr]
      exact ih r.1 r.2.1.1 r.2.1.2.1 r.2.2

omit [SampleableType Pt] in
theorem spkBadImplTrack_support_bad_true {ℓ : ℕ} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (tr : KemFailSessionTrack P.C.F Bytes) :
    ∀ r ∈ support ((spkBadImplTrack P K Dh encT decT qep s t).run ((st, L, true), tr)),
      r.2.1.2.2 = true := by
  intro r hr
  rcases t with u | ((((q_tr | q_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | q_corr)
  · dsimp only [spkBadImplTrack] at hr
    rw [stateT_lift_run_any] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl
  · dsimp only [spkBadImplTrack] at hr
    rw [StateT.run_mk] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl
  · dsimp only [spkBadImplTrack] at hr
    rw [StateT.run_mk] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl
  · dsimp only [spkBadImplTrack] at hr
    rw [StateT.run_mk] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨x, hx, rfl⟩
    exact spkBadImpl_support_bad_true P Dh encT decT qep s (.inr (.inl (.inl (.inr (Q, c)))))
      st L x hx
  · dsimp only [spkBadImplTrack] at hr
    rw [StateT.run_mk] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨x, hx, rfl⟩
    exact spkBadImpl_support_bad_true P Dh encT decT qep s (.inr (.inl (.inr (Q, c))))
      st L x hx
  · dsimp only [spkBadImplTrack] at hr
    rw [StateT.run_mk] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨x, hx, rfl⟩
    exact spkBadImpl_support_bad_true P Dh encT decT qep s (.inr (.inr q_corr)) st L x hx

omit [SampleableType Pt] in
theorem evalDist_runSpkCombTrack_true {ℓ : ℕ} {β : Type} (P : Params Bytes (BitVec 512))
    (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (tr : KemFailSessionTrack P.C.F Bytes)
    (post : β → GameSt Bytes ℓ → Bool) :
    𝒟[runSpkCombTrack P K Dh encT decT qep s oa st L true tr post] {true} = 1 := by
  induction oa using OracleComp.inductionOn generalizing st L tr with
  | pure a => simp [runSpkCombTrack_pure]
  | query_bind t k ih =>
    rw [runSpkCombTrack_bind_query]
    exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r hr => by
      rw [spkBadImplTrack_support_bad_true P K Dh encT decT qep s t st L tr r hr]
      exact ih r.1 r.2.1.1 r.2.1.2.1 r.2.2

omit [SampleableType Pt] in
theorem spkBadImplTrack_run_bind_fst {ℓ : ℕ} {α : Type} (P : Params Bytes (BitVec 512))
    (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool)
    (tr : KemFailSessionTrack P.C.F Bytes)
    (F : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range t ×
      SpkTabTrackSt P.C.F Pt ℓ → ProbComp α) :
    ((spkBadImplTrack P K Dh encT decT qep s t).run ((st, L, bad), tr) >>= fun r =>
      F (r.1, ((r.2.1.1, r.2.1.2.1), r.2.2))) =
    ((spkStepImplTrack P K Dh encT decT qep s t).run ((st, L), tr) >>= F) := by
  rcases t with u | ((((q_tr | q_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | q_corr)
  · dsimp only [spkBadImplTrack, spkStepImplTrack]
    simp [map_eq_bind_pure_comp, bind_assoc]
  · dsimp only [spkBadImplTrack, spkStepImplTrack]
    simp [StateT.run_mk, map_eq_bind_pure_comp, bind_assoc]
  · dsimp only [spkBadImplTrack, spkStepImplTrack]
    simp [StateT.run_mk, map_eq_bind_pure_comp, bind_assoc]
  · dsimp only [spkBadImplTrack, spkStepImplTrack]
    rw [StateT.run_mk, StateT.run_mk]
    simp only [bind_assoc, pure_bind]
    exact spkBadImpl_run_bind_fst P Dh encT decT qep s (.inr (.inl (.inl (.inr (Q, c))))) st L bad
      (fun r => F (r.1, (r.2, updateKemFailOnDeliver P.C.F K tr (Q, c) r.1)))
  · dsimp only [spkBadImplTrack, spkStepImplTrack]
    rw [StateT.run_mk, StateT.run_mk]
    simp only [bind_assoc, pure_bind]
    exact spkBadImpl_run_bind_fst P Dh encT decT qep s (.inr (.inl (.inr (Q, c)))) st L bad
      (fun r => F (r.1, (r.2, tr)))
  · dsimp only [spkBadImplTrack, spkStepImplTrack]
    rw [StateT.run_mk, StateT.run_mk]
    simp only [bind_assoc, pure_bind]
    exact spkBadImpl_run_bind_fst P Dh encT decT qep s (.inr (.inr q_corr)) st L bad
      (fun r => F (r.1, (r.2, tr)))

omit [SampleableType Pt] in
theorem simulateQ_spkBadImplTrack_run_bind_post {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool)
    (tr : KemFailSessionTrack P.C.F Bytes) (post : β → GameSt Bytes ℓ → Bool) :
    ((simulateQ (spkBadImplTrack P K Dh encT decT qep s) oa).run ((st, L, bad), tr) >>= fun r =>
      pure (post r.1 r.2.1.1)) =
    runSpkTabTrack P K Dh encT decT qep s oa st L tr post := by
  induction oa using OracleComp.inductionOn generalizing st L bad tr with
  | pure a => simp [runSpkTabTrack_pure, StateT.run_pure]
  | query_bind t k ih =>
    rw [runSpkTabTrack_bind_query]
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, bind_assoc]
    rw [← spkBadImplTrack_run_bind_fst P K Dh encT decT qep s t st L bad tr
      (fun r => runSpkTabTrack P K Dh encT decT qep s (k r.1) r.2.1.1 r.2.1.2 r.2.2 post)]
    refine bind_congr fun r => ih r.1 r.2.1.1 r.2.1.2.1 r.2.1.2.2 r.2.2

omit [SampleableType Pt] in
theorem evalDist_runSpkCombTrack_le_add {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (fSt : BitVec 256 → GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool)
    (tr : KemFailSessionTrack P.C.F Bytes) (post : β → GameSt Bytes ℓ → Bool) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runSpkCombTrack P K Dh encT decT qep s oa (fSt x) L bad tr post] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runSpkTabTrack P K Dh encT decT qep s oa (fSt x) L tr post] {true} +
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runSpkBadTrack P K Dh encT decT qep s oa (fSt x) L bad tr] {true} := by
  set mx := ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
    (simulateQ (spkBadImplTrack P K Dh encT decT qep s) oa).run ((fSt x, L, bad), tr)
  have hcomb : (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runSpkCombTrack P K Dh encT decT qep s oa (fSt x) L bad tr post) =
    (mx >>= fun r => pure (post r.1 r.2.1.1 || r.2.1.2.2)) := by
    dsimp only [mx, runSpkCombTrack]
    rw [bind_assoc]
    refine bind_congr fun x => bind_congr fun r => by simp [Bool.or_comm]
  have htab : (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runSpkTabTrack P K Dh encT decT qep s oa (fSt x) L tr post) =
    (mx >>= fun r => pure (post r.1 r.2.1.1)) := by
    dsimp only [mx]
    rw [bind_assoc]
    refine bind_congr fun x => (simulateQ_spkBadImplTrack_run_bind_post P K Dh encT decT qep s oa
      (fSt x) L bad tr post).symm
  have hbad : (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runSpkBadTrack P K Dh encT decT qep s oa (fSt x) L bad tr) =
    (mx >>= fun r => pure r.2.1.2.2) := by
    dsimp only [mx, runSpkBadTrack]
    rw [bind_assoc]
  rw [hcomb, htab, hbad]
  exact bind_or_evalDist_true_le mx (fun r => post r.1 r.2.1.1) (fun r => r.2.1.2.2)

/-! ## `patchGameSpk` commutation and support preservation -/

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem stateT_lift_liftM_run2 {m : Type → Type} [Monad m] [LawfulMonad m]
    {S₁ S₂ α : Type} (c : m α) (s₁ : S₁) (s₂ : S₂) :
    (((StateT.lift (liftM c : StateT S₂ m α) : StateT S₁ (StateT S₂ m) α).run s₁).run s₂) =
      (fun a => ((a, s₁), s₂)) <$> c := by
  simp [StateT.run_lift, StateT.run_monadLift, map_eq_bind_pure_comp]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem transmitRTrackHalted_patchGameSpk {ℓ : ℕ} (P : Params Bytes (BitVec 512))
    (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qep : ℕ) (z ck0 : BitVec 256) (spk₀ : PublicKey) (sRef : GameSt Bytes ℓ)
    (tr : KemFailSessionTrack P.C.F Bytes) (x : Party × Plain ℓ × Option (BitVec 512))
    (hinv : SpkRefInv P spk₀ sRef) :
    (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr (Pt := Pt) decT encT) x).run
        (patchGameSpk P.C z ck0 sRef)).run tr) =
      Prod.map (Prod.map id (patchGameSpk P.C z ck0)) id <$>
        (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr (Pt := Pt) decT encT) x).run sRef).run tr) := by
  rcases x with ⟨Q, m, r⟩
  rcases tr with ⟨tk, hw⟩
  unfold transmitRTrackHalted
  have hsendOK : (configRefuseEarlyBobCorr (Pt := Pt) decT encT).sendOK
      (patchGameSpk P.C z ck0 sRef) Q = noBobSendInEpoch0 sRef Q := rfl
  have hsendOK0 : (configRefuseEarlyBobCorr (Pt := Pt) decT encT).sendOK sRef Q =
      noBobSendInEpoch0 sRef Q := rfl
  have hwin : (patchGameSpk P.C z ck0 sRef).win = sRef.win := rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK, hsendOK0, hwin]
  cases hok : noBobSendInEpoch0 sRef Q
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hw_flag : sRef.win
    · have hginv := gameInv_of_spkRefInv_win_false hinv hw_flag
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_liftM_run2,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine bind_congr fun ⟨coins, bad⟩ => ?_
      rw [patchGameSpk_epMgmt P.C z ck0 sRef 3 qep Q bad]
      cases hs₁ : sRef.epMgmt 3 qep Q bad with
      | none => simp
      | some s₁ =>
        simp only [Option.map_some]
        cases hcand : (stepKemFailSend P.C.F K tk Q coins).cand.isSome
        · obtain ⟨hc1, hc2, _⟩ :=
            send_record_patchGameSpk P ℓ z ck0 spk₀ sRef s₁ qep Q m coins bad false hginv hok hs₁
          simp only [hcand, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
            StateT.run_get, StateT.run_set, StateT.run_pure,
            Function.comp_apply, pure_bind, Prod.map_apply, id_eq]
          congr 1
          exact Prod.ext (Prod.ext (congrArg some hc1) hc2)
            (congrArg (fun c => (_, (c, Q) :: hw)) hc1)
        · simp [hcand]
    · simp

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem challRTrackHalted_patchGameSpk {ℓ : ℕ} (P : Params Bytes (BitVec 512))
    (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qep : ℕ) (z ck0 : BitVec 256) (spk₀ : PublicKey) (sRef : GameSt Bytes ℓ)
    (tr : KemFailSessionTrack P.C.F Bytes) (x : Party × Plain ℓ × Plain ℓ × Option (BitVec 512))
    (hinv : SpkRefInv P spk₀ sRef) :
    (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr (Pt := Pt) decT encT) x).run
        (patchGameSpk P.C z ck0 sRef)).run tr) =
      Prod.map (Prod.map id (patchGameSpk P.C z ck0)) id <$>
        (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr (Pt := Pt) decT encT) x).run sRef).run tr) := by
  rcases x with ⟨Q, m₀, m₁, r⟩
  rcases tr with ⟨tk, hw⟩
  unfold challRTrackHalted
  have hsendOK : (configRefuseEarlyBobCorr (Pt := Pt) decT encT).sendOK
      (patchGameSpk P.C z ck0 sRef) Q = noBobSendInEpoch0 sRef Q := rfl
  have hsendOK0 : (configRefuseEarlyBobCorr (Pt := Pt) decT encT).sendOK sRef Q =
      noBobSendInEpoch0 sRef Q := rfl
  have hwin : (patchGameSpk P.C z ck0 sRef).win = sRef.win := rfl
  have hb : (patchGameSpk P.C z ck0 sRef).b = sRef.b := rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK, hsendOK0, hwin, hb]
  cases hok : noBobSendInEpoch0 sRef Q
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hw_flag : sRef.win
    · have hginv := gameInv_of_spkRefInv_win_false hinv hw_flag
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_liftM_run2,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine bind_congr fun ⟨coins, bad⟩ => ?_
      rw [patchGameSpk_epMgmt P.C z ck0 sRef 3 qep Q bad]
      cases hs₁ : sRef.epMgmt 3 qep Q bad with
      | none => simp
      | some s₁ =>
        have hsafe : (patchGameSpk P.C z ck0 s₁).safeCh 3 Q = s₁.safeCh 3 Q := rfl
        have hep1 : (patchGameSpk P.C z ck0 s₁).epoch Q = s₁.epoch Q := rfl
        simp only [Option.map_some, hsafe, hep1]
        cases hch : (!s₁.safeCh 3 Q ||
          !(configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ)
            decT encT).base.challAllowedIn (s₁.epoch Q))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases hcand : (stepKemFailSend P.C.F K tk Q coins).cand.isSome
          · let m := ((configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ)
                decT encT).base.challMsg (s₁.epoch Q)).getD (if sRef.b then m₁ else m₀)
            obtain ⟨hc1, hc2, _⟩ :=
              send_record_patchGameSpk P ℓ z ck0 spk₀ sRef s₁ qep Q m coins bad true hginv hok hs₁
            rw [hep1] at hc2
            simp only [hcand, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
              StateT.run_get, StateT.run_set, StateT.run_pure,
              Function.comp_apply, pure_bind, Prod.map_apply, id_eq]
            congr 1
            exact Prod.ext (Prod.ext (congrArg some hc1) hc2)
              (congrArg (fun c => (_, (c, Q) :: hw)) hc1)
          · simp [hcand]
        · simp
    · simp

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem transmitRTrackHalted_support_spkRefInv {ℓ : ℕ} (P : Params Bytes (BitVec 512))
    (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (spk₀ : PublicKey) (sRef : GameSt Bytes ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (x : Party × Plain ℓ × Option (BitVec 512)) (hinv : SpkRefInv P spk₀ sRef) :
    ∀ us ∈ support (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr (Pt := Pt) decT encT) x).run sRef).run tr),
      SpkRefInv P spk₀ us.1.2 := by
  intro us hus
  rcases transmitRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
    (configRefuseEarlyBobCorr (Pt := Pt) decT encT) x sRef tr hus with hnone | hmem
  · rw [hnone]; exact hinv
  · exact transmitR_support_spkRefInv P decT encT qep spk₀ sRef x hinv us.1 hmem

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem challRTrackHalted_support_spkRefInv {ℓ : ℕ} (P : Params Bytes (BitVec 512))
    (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (spk₀ : PublicKey) (sRef : GameSt Bytes ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (x : Party × Plain ℓ × Plain ℓ × Option (BitVec 512)) (hinv : SpkRefInv P spk₀ sRef) :
    ∀ us ∈ support (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr (Pt := Pt) decT encT) x).run sRef).run tr),
      SpkRefInv P spk₀ us.1.2 := by
  intro us hus
  rcases challRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
    (configRefuseEarlyBobCorr (Pt := Pt) decT encT) x sRef tr hus with hnone | hmem
  · rw [hnone]; exact hinv
  · exact challR_support_spkRefInv P decT encT qep spk₀ sRef x hinv us.1 hmem

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem transmitRTrackHalted_support_transShort {ℓ : ℕ} (P : Params Bytes (BitVec 512))
    (K : MlKem) (hrt : RtHyp P ℓ) (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (qep : ℕ) (sRef : GameSt Bytes ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (x : Party × Plain ℓ × Option (BitVec 512)) (hts : TransShort sRef) :
    ∀ us ∈ support (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep cfg x).run sRef).run tr),
      TransShort us.1.2 := by
  intro us hus
  rcases transmitRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep cfg x sRef tr hus with
    hnone | hmem
  · rw [hnone]; exact hts
  · exact transmitR_support_transShort P hrt cfg qep sRef x hts us.1 hmem

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem challRTrackHalted_support_transShort {ℓ : ℕ} (P : Params Bytes (BitVec 512))
    (K : MlKem) (hrt : RtHyp P ℓ) (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (qep : ℕ) (sRef : GameSt Bytes ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (x : Party × Plain ℓ × Plain ℓ × Option (BitVec 512)) (hts : TransShort sRef) :
    ∀ us ∈ support (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep cfg x).run sRef).run tr),
      TransShort us.1.2 := by
  intro us hus
  rcases challRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep cfg x sRef tr hus with
    hnone | hmem
  · rw [hnone]; exact hts
  · exact challR_support_transShort P hrt cfg qep sRef x hts us.1 hmem

/-! ## `runSpkTabTrack` to `runSpkRefTrack` bound -/

omit [SampleableType Pt] in
theorem evalDist_runSpkTabTrack_s_le_runSpkRefTrack {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem : ℕ) (hq : MakesAtMostQueries oa rem)
    (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (abort : Bool)
    (tr : KemFailSessionTrack P.C.F Bytes)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef)
    (hcodec : P.codec = protoSignalCodec) (hrt : RtHyp P ℓ) (hts : TransShort sRef)
    (post : Bool → GameSt Bytes ℓ → Bool)
    (hpost : ∀ ck0 b' s', post b' (patchGameSpk P.C s ck0 s') = post b' s') :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
      runSpkTabTrack P K Dh encT decT qep s oa (patchGameSpk P.C s ck0 sRef) L tr post] {true} ≤
    𝒟[runSpkRefTrack P K Dh encT decT qep s oa sRef L abort tr post] {true} +
      (rem : ℝ≥0∞) * eps0IdealUnit P.C.F := by
  induction oa using OracleComp.inductionOn generalizing rem sRef L abort tr with
  | pure a =>
    simp only [runSpkTabTrack_pure, runSpkRefTrack_pure, hpost,
      OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
    cases abort with
    | false => simp only [Bool.false_or]; exact le_self_add
    | true => cases post a sRef <;> simp
  | query_bind t k ih =>
    cases abort with
    | true =>
      rw [evalDist_runSpkRefTrack_true]
      exact (evalDist_true_le_one _).trans le_self_add
    | false =>
      rw [MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq
      simp only [runSpkTabTrack_bind_query, runSpkRefTrack_bind_query]
      rcases t with u | ((((q_tr | q_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | q_corr)
      · have hq' : ∀ a, MakesAtMostQueries (k a) rem :=
          fun a => by simpa [MakesAtMostQueries] using hq.2 a
        dsimp only [spkStepImplTrack, spkRefImplTrack]
        simp only [stateT_lift_run_any, bind_assoc, pure_bind]
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
        exact bind_evalDist_true_le_of_support _ _ _ _ fun a _ =>
          ih a rem (hq' a) sRef L false tr hinv hts
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F ≤
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        dsimp only [spkStepImplTrack, spkRefImplTrack]
        simp only [StateT.run_mk, transmitRTrackHalted_patchGameSpk P K decT encT qep s _
          (KeyPair.generate P.C s).publicKey sRef tr q_tr hinv,
          map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map]
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
          (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) q_tr).run sRef).run tr)]
        refine (bind_evalDist_true_le_of_support _ _ _ _ fun us hus => ?_).trans
          (add_le_add le_rfl hrem_le)
        exact ih us.1.1 (rem - 1) (hq' us.1.1) us.1.2 L false us.2
          (transmitRTrackHalted_support_spkRefInv P K decT encT qep _ sRef tr q_tr hinv us hus)
          (transmitRTrackHalted_support_transShort P K hrt _ qep sRef tr q_tr hts us hus)
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F ≤
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        dsimp only [spkStepImplTrack, spkRefImplTrack]
        simp only [StateT.run_mk, challRTrackHalted_patchGameSpk P K decT encT qep s _
          (KeyPair.generate P.C s).publicKey sRef tr q_ch hinv,
          map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map]
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
          (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) q_ch).run sRef).run tr)]
        refine (bind_evalDist_true_le_of_support _ _ _ _ fun us hus => ?_).trans
          (add_le_add le_rfl hrem_le)
        exact ih us.1.1 (rem - 1) (hq' us.1.1) us.1.2 L false us.2
          (challRTrackHalted_support_spkRefInv P K decT encT qep _ sRef tr q_ch hinv us hus)
          (challRTrackHalted_support_transShort P K hrt _ qep sRef tr q_ch hts us hus)
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F ≤
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        have hrem_eq : eps0IdealUnit P.C.F + ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F =
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F := by
          have h1 : (rem : ℝ≥0∞) = (1 : ℕ) + (rem - 1 : ℕ) := by norm_cast; omega
          rw [h1, add_mul, Nat.cast_one, one_mul]
        dsimp only [spkStepImplTrack, spkRefImplTrack]
        simp only [StateT.run_mk, bind_assoc, pure_bind]
        by_cases hspk : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c = true
        · unfold deliverSpkStep deliverSpkRef
          simp only [StateT.run_mk]
          have hwin : ∀ ck0, (patchGameSpk P.C s ck0 sRef).win = sRef.win := fun _ => rfl
          have htr : ∀ ck0, (patchGameSpk P.C s ck0 sRef).inTransit Q.other c =
              sRef.inTransit Q.other c := fun _ => rfl
          simp only [hwin, htr]
          by_cases hw : sRef.win = true
          · simp only [hw, ↓reduceIte, pure_bind]
            exact (ih none (rem - 1) (hq' none) sRef L false
              (updateKemFailOnDeliver P.C.F K tr (Q, c) none) hinv hts).trans
              (add_le_add le_rfl hrem_le)
          · have hwF : sRef.win = false := Bool.eq_false_iff.mpr hw
            have hginv := gameInv_of_spkRefInv_win_false hinv hwF
            simp only [hw, Bool.false_eq_true, ↓reduceIte]
            cases h_in : sRef.inTransit Q.other c with
            | none =>
              simp only [pure_bind]
              exact (ih none (rem - 1) (hq' none) sRef L false
                (updateKemFailOnDeliver P.C.F K tr (Q, c) none) hinv hts).trans
                (add_le_add le_rfl hrem_le)
            | some r =>
              have hc32 : c.length < 2 ^ 32 := ct_length_lt_of_inTransit hts Q.other c r h_in
              have hQ : Q = .A := by
                unfold isAliceSpkQuery at hspk
                simp only [Bool.and_eq_true, beq_iff_eq] at hspk
                exact hspk.1.1
              subst hQ
              have hpA : (sRef.st .A).party = .A := spkRefInv_party_eq hinv .A
              have hpA_ck0 : ∀ ck0, ((patchGameSpk P.C s ck0 sRef).st .A).party = .A :=
                fun ck0 => (patchGameSpk_party_eq P.C s ck0 sRef .A).trans hpA
              have href_step : ∀ rc, stepReceiveRef P ℓ Dh encT decT s sRef .A c rc L =
                  pure (none, L) := by
                intro rc; unfold stepReceiveRef; rw [hpA]; simp [hspk]
              simp only [href_step, bind_assoc, pure_bind,
                OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
              refine (bind_apply_le_add_of_evalDist_le_on_good ($ᵗ BitVec 256) _
                (fun ck0 => runSpkTabTrack P K Dh encT decT qep s (k (some .rejected))
                  (patchGameSpk P.C s ck0 sRef) L
                  (updateKemFailOnDeliver (Msg := Plain ℓ) P.C.F K tr (.A, c) (some .rejected)) post)
                (testSpk P (sRef.st .A).session.pqRatchetState c) ?_).trans ?_
              · intro ck0 htest
                have hnone : ∀ rc,
                    stepReceiveSpk P ℓ Dh encT decT s ((patchGameSpk P.C s ck0 sRef).st .A) c rc L =
                      pure (none, L) := by
                  intro rc; unfold stepReceiveSpk
                  have hpAB : (((patchGameSpk P.C s ck0 sRef).st .A).party == .B) = false := by
                    rw [hpA_ck0 ck0]; rfl
                  simp only [hpAB, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                  exact congrArg (fun o => pure (o, L))
                    (receive_patchGameSpk_of_spk_test_false P ℓ s ck0
                      (KeyPair.generate P.C s).publicKey sRef .A c rc hginv hspk htest).2
                simp only [hnone, pure_bind, OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
                exact le_rfl
              · exact (add_le_add
                  (ih (some .rejected) (rem - 1) (hq' (some .rejected)) sRef L false
                    (updateKemFailOnDeliver (Msg := Plain ℓ) P.C.F K tr (.A, c) (some .rejected)) hinv hts)
                  (testSpk_le_unit P (sRef.st .A).session.pqRatchetState c hc32)).trans
                  (le_of_eq (by rw [add_assoc, add_comm (((rem - 1 : ℕ) : ℝ≥0∞) * _), hrem_eq]))
        · have hnspk : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c =
            false := Bool.eq_false_iff.mpr hspk
          simp only [deliverSpkStep_patchGameSpk_of_not_spk P Dh encT decT s s _ sRef Q c L false
            hinv hnspk hnspk, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
          rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
            ((deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false))]
          refine (bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_).trans
            (add_le_add le_rfl hrem_le)
          have hsupp := deliverSpkRef_support_spkRefInv P Dh encT decT s sRef Q c L false hinv r hr
          rw [hsupp.2]
          exact ih r.1 (rem - 1) (hq' r.1) r.2.1 r.2.2.1 false
            (updateKemFailOnDeliver P.C.F K tr (Q, c) r.1) hsupp.1
            (deliverSpkRef_support_transShort P Dh encT decT s sRef Q c L false hts r hr)
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F ≤
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        have hrem_eq : eps0IdealUnit P.C.F + ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F =
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F := by
          have h1 : (rem : ℝ≥0∞) = (1 : ℕ) + (rem - 1 : ℕ) := by norm_cast; omega
          rw [h1, add_mul, Nat.cast_one, one_mul]
        dsimp only [spkStepImplTrack, spkRefImplTrack]
        simp only [StateT.run_mk, bind_assoc, pure_bind]
        by_cases hspk : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c = true
        · unfold injectSpkStep injectSpkRef
          simp only [StateT.run_mk]
          have hguard : ∀ ck0, ((patchGameSpk P.C s ck0 sRef).win ||
              ((patchGameSpk P.C s ck0 sRef).inTransit Q.other c).isSome ||
              !((patchGameSpk P.C s ck0 sRef).safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) =
            (sRef.win || (sRef.inTransit Q.other c).isSome || !(sRef.safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := fun _ => rfl
          simp only [hguard]
          by_cases hg : (sRef.win || (sRef.inTransit Q.other c).isSome || !(sRef.safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
          · simp only [hg, ↓reduceIte, pure_bind]
            exact (ih none (rem - 1) (hq' none) sRef L false tr hinv hts).trans
              (add_le_add le_rfl hrem_le)
          · have hwF : sRef.win = false := by
              simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hg; exact hg.1.1.1
            have hginv := gameInv_of_spkRefInv_win_false hinv hwF
            have hc32 : c.length < 2 ^ 32 := by
              cases htry : SignalMessage.tryFrom P.codec c with
              | error _ => unfold isAliceSpkQuery at hspk; rw [htry] at hspk; simp at hspk
              | ok msg =>
                refine ratchetKeyAdmissible_length_lt_of_tryFrom P.codec decT encT c msg ?_ htry
                rw [hcodec]
                simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hg
                exact hg.2
            simp only [hg, Bool.false_eq_true, ↓reduceIte]
            have hQ : Q = .A := by
              unfold isAliceSpkQuery at hspk
              simp only [Bool.and_eq_true, beq_iff_eq] at hspk; exact hspk.1.1
            subst hQ
            have hpA : (sRef.st .A).party = .A := spkRefInv_party_eq hinv .A
            have hpA_ck0 : ∀ ck0, ((patchGameSpk P.C s ck0 sRef).st .A).party = .A :=
              fun ck0 => (patchGameSpk_party_eq P.C s ck0 sRef .A).trans hpA
            have href_step : ∀ rc, stepReceiveRef P ℓ Dh encT decT s sRef .A c rc L =
                pure (none, L) := by
              intro rc; unfold stepReceiveRef; rw [hpA]; simp [hspk]
            simp only [href_step, bind_assoc, pure_bind,
              OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
            refine (bind_apply_le_add_of_evalDist_le_on_good ($ᵗ BitVec 256) _
              (fun ck0 => runSpkTabTrack P K Dh encT decT qep s (k (some .rejected))
                (patchGameSpk P.C s ck0 sRef) L tr post)
              (testSpk P (sRef.st .A).session.pqRatchetState c) ?_).trans ?_
            · intro ck0 htest
              have hnone : ∀ rc,
                  stepReceiveSpk P ℓ Dh encT decT s ((patchGameSpk P.C s ck0 sRef).st .A) c rc L =
                    pure (none, L) := by
                intro rc; unfold stepReceiveSpk
                have hpAB : (((patchGameSpk P.C s ck0 sRef).st .A).party == .B) = false := by
                  rw [hpA_ck0 ck0]; rfl
                simp only [hpAB, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                exact congrArg (fun o => pure (o, L))
                  (receive_patchGameSpk_of_spk_test_false P ℓ s ck0
                    (KeyPair.generate P.C s).publicKey sRef .A c rc hginv hspk htest).2
              simp only [hnone, pure_bind, OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
              exact le_rfl
            · exact (add_le_add
                (ih (some .rejected) (rem - 1) (hq' (some .rejected)) sRef L false tr hinv hts)
                (testSpk_le_unit P (sRef.st .A).session.pqRatchetState c hc32)).trans
                (le_of_eq (by rw [add_assoc, add_comm (((rem - 1 : ℕ) : ℝ≥0∞) * _), hrem_eq]))
        · have hnspk : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c =
            false := Bool.eq_false_iff.mpr hspk
          simp only [injectSpkStep_patchGameSpk_of_not_spk P Dh encT decT qep s s _ sRef Q c L false
            hinv hnspk hnspk, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
          rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
            ((injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false))]
          refine (bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_).trans
            (add_le_add le_rfl hrem_le)
          have hsupp :=
            injectSpkRef_support_spkRefInv P Dh encT decT qep s sRef Q c L false hinv r hr
          rw [hsupp.2]
          exact ih r.1 (rem - 1) (hq' r.1) r.2.1 r.2.2.1 false tr hsupp.1
            (injectSpkRef_support_transShort P Dh encT decT qep s sRef Q c L false hts r hr)
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F ≤
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        dsimp only [spkStepImplTrack, spkRefImplTrack]
        simp only [StateT.run_mk, bind_assoc, pure_bind]
        by_cases hbad : badSpkCorrA decT encT sRef q_corr = true
        · unfold corrSpkRef
          rw [StateT.run_mk]
          dsimp only []
          rw [hbad, Bool.false_or]
          simp only [bind_assoc, pure_bind]
          have h1 : 𝒟[do
              let a ← (corrR (configRefuseEarlyBobCorr decT encT) q_corr).run sRef
              runSpkRefTrack P K Dh encT decT qep s (k a.1) a.2 L true tr post] {true} = 1 :=
            bind_eq_of_support _ _ (measurableSet_singleton _) fun us _ =>
              evalDist_runSpkRefTrack_true P K Dh encT decT qep s (k us.1) us.2 L tr post
          rw [h1]
          exact (evalDist_true_le_one _).trans le_self_add
        · have hbadF : badSpkCorrA decT encT sRef q_corr = false := Bool.eq_false_iff.mpr hbad
          unfold corrSpkRef
          rw [StateT.run_mk]
          dsimp only []
          rw [hbadF, Bool.false_or]
          simp only [liftSpkTab_run, corrR_patchGameSpk_of_badSpkCorrA_false P decT encT s _
            (KeyPair.generate P.C s).publicKey sRef q_corr hinv hbadF,
            map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map]
          rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
            ((corrR (configRefuseEarlyBobCorr decT encT) q_corr).run sRef)]
          refine (bind_evalDist_true_le_of_support _ _ _ _ fun us hus => ?_).trans
            (add_le_add le_rfl hrem_le)
          exact ih us.1 (rem - 1) (hq' us.1) us.2 L false tr
            (corrR_support_spkRefInv P decT encT _ sRef q_corr hinv us hus)
            (corrR_support_transShort _ sRef q_corr hts us hus)

end Evaluators

end Computational.Proofs.E2E.HaltedSpkHop2InitAux
