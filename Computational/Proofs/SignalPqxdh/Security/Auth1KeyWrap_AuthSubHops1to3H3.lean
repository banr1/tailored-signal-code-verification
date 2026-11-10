/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H1
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3D
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3E
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H2
public import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3D
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3E
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3F
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `PrfMsgKeys` Reduction Simulation

Relates the single-identity-key `PrfMsgKeys` reduction over `PrimBaseSpec` to probabilistic state
simulators and proves `ValidAuthHybrid` preservation.
-/

@[expose] public section
set_option autoImplicit false
open OracleSpec OracleComp MeasureTheory ENNReal BigOperators
namespace SignalPqxdh.Security
open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
namespace AuthSubHops1to3

def authMkStepRedProb1Key (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) :
    ProbComp ((authSpec S).Range q × ((AuthHybridStateFixed S × Bool) × Cache)) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, ((hst, sentChal), cache))
    else authMkSendRedProb S P idx evalPrf (.sendOPK u i) u bundle m0 m1 hst sentChal cache
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, ((hst, sentChal), cache))
    else authMkSendRedProb S P idx evalPrf (.sendNoOPK u i) u bundle m0 m1 hst sentChal cache
  | .recvOPK k j o msg => do
    let prep? := prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState
    let ((resp, hst'), cache') ← authMkRecvRedProb S P idx evalPrf msg prep? hst sentChal cache
    pure (resp, ((hst', sentChal), cache'))
  | .recvNoOPK k j l msg => do
    let prep? := prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState
    let ((resp, hst'), cache') ← authMkRecvRedProb S P idx evalPrf msg prep? hst sentChal cache
    pure (resp, ((hst', sentChal), cache'))
  | qOther => do
    let (resp, hst') ← authCkOtherStep1Key S P qOther hst
    pure (resp, ((hst', sentChal), cache))
def authMkRedProbImpl1Key (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache)) :
    QueryImpl (authSpec S) (StateT ((AuthHybridStateFixed S × Bool) × Cache) ProbComp) :=
  fun q => StateT.mk (fun ((hst, sentChal), cache) =>
    authMkStepRedProb1Key S P idx evalPrf q hst sentChal cache)

def authMkSlotsStepRedProb1Key (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) :
    ProbComp ((authSpec S).Range q × ((AuthHybridStateFixed S × Bool) × Cache)) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, ((hst, sentChal), cache))
    else authMkSlotsSendRedProb S P idx evalPrf (.sendOPK u i) u bundle m0 m1 hst sentChal cache
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, ((hst, sentChal), cache))
    else authMkSlotsSendRedProb S P idx evalPrf (.sendNoOPK u i) u bundle m0 m1 hst sentChal cache
  | .recvOPK k j o msg => do
    let prep? := prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState
    let ((resp, hst'), cache') ← authMkSlotsRecvRedProb S P idx evalPrf msg prep? hst sentChal cache
    pure (resp, ((hst', sentChal), cache'))
  | .recvNoOPK k j l msg => do
    let prep? := prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState
    let ((resp, hst'), cache') ← authMkSlotsRecvRedProb S P idx evalPrf msg prep? hst sentChal cache
    pure (resp, ((hst', sentChal), cache'))
  | qOther => do
    let (resp, hst') ← authCkOtherStep1Key S P qOther hst
    pure (resp, ((hst', sentChal), cache))

def authMkSlotsRedProbImpl1Key (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache)) :
    QueryImpl (authSpec S) (StateT ((AuthHybridStateFixed S × Bool) × Cache) ProbComp) :=
  fun q => StateT.mk (fun ((hst, sentChal), cache) =>
    authMkSlotsStepRedProb1Key S P idx evalPrf q hst sentChal cache)

theorem simulateQ_authMkStepReduction1Key {Cache : Type} (S : Setup) (P : Primitives) (idx : Nat)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache)
    (hV : ValidAuthHybrid S P hst) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    let evalPrf := fun s c => (impl (.derive (effectiveHkdfSaltBytes s))).run c
    (simulateQ fullImpl (authMkStepReduction1Key S idx q (cacheAuthAdvKeysFixed P hst) sentChal)).run
      cache =
      (fun (resp, ((hst', sentChal'), cache')) =>
        (((resp, cacheAuthAdvKeysFixed P hst'), sentChal'), cache')) <$>
      authMkSlotsStepRedProb1Key S P idx evalPrf q hst sentChal cache := by
  intro fullImpl evalPrf
  have hVC : ValidAuthHybrid S P (cacheAuthAdvKeysFixed P hst) :=
    (validAuthHybrid_cacheAuthAdvKeysFixed P hst).mpr hV
  have hAdv : ValidAdvKeysPow8 P (cacheAuthAdvKeysFixed P hst).toAuthHybridState.base.advKeys :=
    validAdvKeysPow8_cacheAuthAdvKeys P hst.toAuthHybridState
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkStepReduction1Key authMkSlotsStepRedProb1Key
    dsimp only
    split
    · simp [StateT.run_pure]
    · rw [simulateQ_authMkSendReduction S P idx impl (.sendOPK u i) u bundle m0 m1
            (cacheAuthAdvKeysFixed P hst) sentChal cache
            hVC.principals_le hVC.spkBundles_le hVC.opkEntries_le hAdv,
          authMkSlotsSendRedProb_cacheAuthAdvKeysFixed]
      simp [Functor.map_map]; rfl
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkStepReduction1Key authMkSlotsStepRedProb1Key
    dsimp only
    split
    · simp [StateT.run_pure]
    · rw [simulateQ_authMkSendReduction S P idx impl (.sendNoOPK u i) u bundle m0 m1
            (cacheAuthAdvKeysFixed P hst) sentChal cache
            hVC.principals_le hVC.spkBundles_le hVC.opkEntries_le hAdv,
          authMkSlotsSendRedProb_cacheAuthAdvKeysFixed]
      simp [Functor.map_map]; rfl
  | recvOPK k j o msg =>
    unfold authMkStepReduction1Key authMkSlotsStepRedProb1Key
    dsimp only
    rw [simulateQ_prfMkFullImpl_embedPrimMk_bind,
        simulateQ_prepareAuthHybridRecvOPKPrim S P k j o msg
          (cacheAuthAdvKeysFixed P hst).toAuthHybridState
          hVC.principals_le hVC.idealSessions_le hAdv,
        pure_bind]
    have hPrep : ∀ prep,
        prepareAuthHybridRecvOPKPure P k j o msg (cacheAuthAdvKeysFixed P hst).toAuthHybridState =
          some prep →
        prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.principals.length ≤ S.N_dh := by
      intro prep hp
      obtain ⟨hTag, hBase⟩ := prepareAuthHybridRecvOPKPure_finishTag_base P k j o msg _ prep hp
      rw [hTag, hBase]
      exact ⟨hVC.sentOPKEvents_le, hVC.sentNoOPKEvents_le, hVC.principals_le⟩
    rw [simulateQ_bind, StateT.run_bind,
        simulateQ_authMkRecvReduction S P idx impl msg _ (cacheAuthAdvKeysFixed P hst) sentChal
          cache hPrep]
    change (authMkSlotsRecvRedProb S P idx evalPrf msg
        ((prepareAuthHybridRecvOPKPure P k j o msg (cacheAuthAdvKeys P hst.toAuthHybridState)).map
          (PreparedAuthRecvPrim.toPure true P))
        (cacheAuthAdvKeysFixed P hst) sentChal cache >>= _) = _
    rw [prepareAuthHybridRecvOPKPure_cacheAuthAdvKeys,
        authMkSlotsRecvRedProb_cacheAuthAdvKeysFixed,
        prepareAuthHybridRecvOPKPure_map_toPure,
        bind_map_left, map_bind]
    congr 1
  | recvNoOPK k j l msg =>
    unfold authMkStepReduction1Key authMkSlotsStepRedProb1Key
    dsimp only
    rw [simulateQ_prfMkFullImpl_embedPrimMk_bind,
        simulateQ_prepareAuthHybridRecvNoOPKPrim S P k j l msg
          (cacheAuthAdvKeysFixed P hst).toAuthHybridState
          hVC.principals_le hVC.idealSessions_le hAdv,
        pure_bind]
    have hPrep : ∀ prep,
        prepareAuthHybridRecvNoOPKPure P k j l msg (cacheAuthAdvKeysFixed P hst).toAuthHybridState =
          some prep →
        prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.principals.length ≤ S.N_dh := by
      intro prep hp
      obtain ⟨hTag, hBase⟩ := prepareAuthHybridRecvNoOPKPure_finishTag_base P k j l msg _ prep hp
      rw [hTag, hBase]
      exact ⟨hVC.sentOPKEvents_le, hVC.sentNoOPKEvents_le, hVC.principals_le⟩
    rw [simulateQ_bind, StateT.run_bind,
        simulateQ_authMkRecvReduction S P idx impl msg _ (cacheAuthAdvKeysFixed P hst) sentChal
          cache hPrep]
    change (authMkSlotsRecvRedProb S P idx evalPrf msg
        ((prepareAuthHybridRecvNoOPKPure P k j l msg (cacheAuthAdvKeys P hst.toAuthHybridState)).map
          (PreparedAuthRecvPrim.toPure true P))
        (cacheAuthAdvKeysFixed P hst) sentChal cache >>= _) = _
    rw [prepareAuthHybridRecvNoOPKPure_cacheAuthAdvKeys,
        authMkSlotsRecvRedProb_cacheAuthAdvKeysFixed,
        prepareAuthHybridRecvNoOPKPure_map_toPure,
        bind_map_left, map_bind]
    congr 1
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    unfold authMkStepReduction1Key authMkSlotsStepRedProb1Key
    dsimp only
    rw [simulateQ_prfMkFullImpl_embedPrimMk_bind,
        simulateQ_stepAuthOtherPrim1Key S P _ hst (by intro h; cases h) (by intro h; cases h),
        bind_map_left, map_bind]
    rfl

theorem authMkStepRedProb_validAuthHybrid1Key {Cache : Type} (S : Setup) (P : Primitives) (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache)
    (hV : ValidAuthHybrid S P hst) :
    ∀ x ∈ support (authMkStepRedProb1Key S P idx evalPrf q hst sentChal cache),
      ValidAuthHybrid S P x.2.1.1 := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkStepRedProb1Key; dsimp only
    split
    · intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hV
    · exact authMkSendRedProb_validAuthHybrid S P idx evalPrf (.sendOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hV
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkStepRedProb1Key; dsimp only
    split
    · intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hV
    · exact authMkSendRedProb_validAuthHybrid S P idx evalPrf (.sendNoOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hV
  | recvOPK k j o msg =>
    unfold authMkStepRedProb1Key; dsimp only
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hmem, rfl⟩
    exact authMkRecvRedProb_validAuthHybrid S P idx evalPrf msg _ hst sentChal cache hV
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvOPK_validAuthHybrid P k j o msg hst hV prep hPrep res? recvCount')
      ((resp, hst'), cache') hmem
  | recvNoOPK k j l msg =>
    unfold authMkStepRedProb1Key; dsimp only
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hmem, rfl⟩
    exact authMkRecvRedProb_validAuthHybrid S P idx evalPrf msg _ hst sentChal cache hV
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvNoOPK_validAuthHybrid P k j l msg hst hV prep hPrep res? recvCount')
      ((resp, hst'), cache') hmem
  | initPrin u =>
    unfold authMkStepRedProb1Key; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid1Key S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.initPrin u) hst hV (resp, hst') hmem
  | corruptIK u =>
    unfold authMkStepRedProb1Key; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid1Key S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.corruptIK u) hst hV (resp, hst') hmem
  | genSPK u j =>
    unfold authMkStepRedProb1Key; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid1Key S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.genSPK u j) hst hV (resp, hst') hmem
  | genOPK u j o =>
    unfold authMkStepRedProb1Key; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid1Key S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.genOPK u j o) hst hV (resp, hst') hmem
  | registerKey sk =>
    unfold authMkStepRedProb1Key; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid1Key S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.registerKey sk) hst hV (resp, hst') hmem
  | roQuery secrets =>
    unfold authMkStepRedProb1Key; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid1Key S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.roQuery secrets) hst hV (resp, hst') hmem
  | roRootQuery rk dh =>
    unfold authMkStepRedProb1Key; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid1Key S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.roRootQuery rk dh) hst hV (resp, hst') hmem
  | revealDhSecrets =>
    unfold authMkStepRedProb1Key; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid1Key S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      .revealDhSecrets hst hV (resp, hst') hmem

theorem authMkSlotsStepRedProb_validAuthHybrid1Key {Cache : Type} (S : Setup) (P : Primitives)
    (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache)
    (hV : ValidAuthHybrid S P hst) :
    ∀ x ∈ support (authMkSlotsStepRedProb1Key S P idx evalPrf q hst sentChal cache),
      ValidAuthHybrid S P x.2.1.1 := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepRedProb1Key; dsimp only
    split
    · intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hV
    · exact authMkSlotsSendRedProb_validAuthHybrid S P idx evalPrf (.sendOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hV
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepRedProb1Key; dsimp only
    split
    · intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hV
    · exact authMkSlotsSendRedProb_validAuthHybrid S P idx evalPrf (.sendNoOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hV
  | recvOPK k j o msg =>
    unfold authMkSlotsStepRedProb1Key; dsimp only
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hmem, rfl⟩
    exact authMkSlotsRecvRedProb_validAuthHybrid S P idx evalPrf msg _ hst sentChal cache hV
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvOPK_validAuthHybrid P k j o msg hst hV prep hPrep res? recvCount')
      ((resp, hst'), cache') hmem
  | recvNoOPK k j l msg =>
    unfold authMkSlotsStepRedProb1Key; dsimp only
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hmem, rfl⟩
    exact authMkSlotsRecvRedProb_validAuthHybrid S P idx evalPrf msg _ hst sentChal cache hV
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvNoOPK_validAuthHybrid P k j l msg hst hV prep hPrep res? recvCount')
      ((resp, hst'), cache') hmem
  | initPrin u =>
    exact authMkStepRedProb_validAuthHybrid1Key S P idx evalPrf (.initPrin u) hst sentChal cache hV
  | corruptIK u =>
    exact authMkStepRedProb_validAuthHybrid1Key S P idx evalPrf (.corruptIK u) hst sentChal cache hV
  | genSPK u j =>
    exact authMkStepRedProb_validAuthHybrid1Key S P idx evalPrf (.genSPK u j) hst sentChal cache hV
  | genOPK u j o =>
    exact authMkStepRedProb_validAuthHybrid1Key S P idx evalPrf (.genOPK u j o) hst sentChal cache hV
  | registerKey sk =>
    exact authMkStepRedProb_validAuthHybrid1Key S P idx evalPrf (.registerKey sk) hst sentChal cache hV
  | roQuery secrets =>
    exact authMkStepRedProb_validAuthHybrid1Key S P idx evalPrf (.roQuery secrets) hst sentChal cache hV
  | roRootQuery rk dh =>
    exact authMkStepRedProb_validAuthHybrid1Key S P idx evalPrf (.roRootQuery rk dh) hst sentChal cache
      hV
  | revealDhSecrets =>
    exact authMkStepRedProb_validAuthHybrid1Key S P idx evalPrf .revealDhSecrets hst sentChal cache hV

theorem simulateQ_runWithPrfMkStep_eq_redProb1Key {Cache α : Type} (S : Setup) (P : Primitives)
  (idx : Nat)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (oa : OracleComp (unifSpec + authSpec S) α)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) (hV : ValidAuthHybrid S P hst)
    (obs1 : ((α × AuthHybridStateFixed S) × Bool) × Cache → ProbComp Bool)
    (obs2 : α × ((AuthHybridStateFixed S × Bool) × Cache) → ProbComp Bool)
    (hObs : ∀ a hst' sentChal' cache', ValidAuthHybrid S P hst' →
      obs1 (((a, cacheAuthAdvKeysFixed P hst'), sentChal'), cache') =
      obs2 (a, ((hst', sentChal'), cache'))) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    let evalPrf := fun s c => (impl (.derive (effectiveHkdfSaltBytes s))).run c
    let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((AuthHybridStateFixed S × Bool) × Cache) ProbComp) +
      authMkSlotsRedProbImpl1Key S P idx evalPrf
    ((simulateQ fullImpl (runWithPrfMkStep (authMkStepReduction1Key S idx) oa
        (cacheAuthAdvKeysFixed P hst) sentChal)).run cache >>= obs1) =
      ((simulateQ fullRed oa).run ((hst, sentChal), cache) >>= obs2) := by
  intro fullImpl evalPrf fullRed
  induction oa using OracleComp.inductionOn generalizing hst sentChal cache with
  | pure a =>
    rw [runWithPrfMkStep_pure]
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hObs a hst sentChal cache hV
  | query_bind q k ih =>
    rcases q with uq | gq
    · rw [runWithPrfMkStep_query_bind_inl, simulateQ_prfMkFullImpl_embedUnifMk_bind,
          simulateQ_run_query_inl_local, bind_assoc, bind_assoc]
      congr 1; funext u
      exact ih u hst sentChal cache hV
    · rw [runWithPrfMkStep_query_bind_inr, simulateQ_bind, StateT.run_bind,
          simulateQ_authMkStepReduction1Key S P idx impl gq hst sentChal cache hV,
          bind_map_left, bind_assoc,
          simulateQ_run_query_inr_local, bind_assoc]
      refine bind_congr_of_support
        (authMkSlotsStepRedProb1Key S P idx evalPrf gq hst sentChal cache) _ _ (fun x hx => ?_)
      rcases x with ⟨resp, ⟨⟨hst', sentChal'⟩, cache'⟩⟩
      exact ih resp hst' sentChal' cache'
        (authMkSlotsStepRedProb_validAuthHybrid1Key S P idx evalPrf gq hst sentChal cache hV _ hx)
theorem simulateQ_authMkReductionRun_eq_redProb1Key {Cache : Type} (S : Setup) (P : Primitives)
  (idx : Nat)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (initCache : Cache) (A : AuthAdversary S) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    let evalPrf := fun s c => (impl (.derive (effectiveHkdfSaltBytes s))).run c
    let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((AuthHybridStateFixed S × Bool) × Cache) ProbComp) +
      authMkSlotsRedProbImpl1Key S P idx evalPrf
    ((simulateQ fullImpl (authMkReductionRun1Key S idx A)).run initCache >>= fun (b', _) => pure b') =
      (do
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.run).run ((initSt, false), initCache)
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState) := by
  intro fullImpl evalPrf fullRed
  unfold authMkReductionRun1Key
  rw [simulateQ_prfMkFullImpl_embedUnifMk_bind, bind_assoc]
  congr 1; funext secb
  rw [simulateQ_bind, StateT.run_bind, bind_assoc]
  have hInit : AuthHybridStateFixed.empty S secb =
      cacheAuthAdvKeysFixed P (AuthHybridStateFixed.empty S secb) := rfl
  rw [hInit]
  exact simulateQ_runWithPrfMkStep_eq_redProb1Key S P idx impl A.run
    (AuthHybridStateFixed.empty S secb) false initCache (validAuthHybrid_empty S P secb)
    (fun (((b', finalSt), _), cache') =>
      (simulateQ fullImpl (embedPrimMk (finalizeAuthFixedPrim S secb b'
                                         finalSt.toAuthHybridState))).run cache' >>=
        fun (z, _) => pure z)
    (fun (b', ((finalSt, _), _)) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun b' hst' _ cache' hV' => by
      dsimp only [fullImpl]
      have hVC : ValidAuthHybrid S P (cacheAuthAdvKeysFixed P hst') :=
        (validAuthHybrid_cacheAuthAdvKeysFixed P hst').mpr hV'
      rw [simulateQ_prfMkFullImpl_embedPrimMk,
          simulateQ_finalizeAuthFixedPrim S P secb b' (cacheAuthAdvKeysFixed P
                                                        hst').toAuthHybridState
            hVC.principals_le hVC.spkBundles_le hVC.opkEntries_le hVC.sessions_le hVC.validKem]
      simp [cacheAuthAdvKeysFixed, finalizeAuthFixed_cacheAuthAdvKeys])

theorem authCkOtherStep_restoreAuthFixedMkAtIdx1Key {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    authCkOtherStep1Key S P q (restoreAuthFixedMkAtIdx idx mkSeedStar hst) =
      Prod.map id (restoreAuthFixedMkAtIdx idx mkSeedStar) <$> authCkOtherStep1Key S P q hst := by
  unfold authCkOtherStep1Key restoreAuthFixedMkAtIdx restoreAuthMkAtIdx
  dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;> simp [map_eq_bind_pure_comp, Prod.map]

end AuthSubHops1to3
end SignalPqxdh.Security
