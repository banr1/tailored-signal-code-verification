/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5B2
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhA
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5B3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `G5` Authentication-Flag Erasure and Zero-Bias Endpoint

Proves that disabling `checkAuth` does not change `authSplitFixedExp1Key` at receive stage `.g5`
and that stage `(.g5, .g5)` has zero `boolBias` over `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh (initSessionSlotIdx initSessionSlotIdx_sendOPK_lt
  initSessionSlotIdx_sendNoOPK_lt initSessionSlotIdx_inj_of_lt RelProbUpToBad
    simulateQ_relProbUpToBad evalDist_simulateQ_eq_of_step_or_bad)

theorem badSigOrKemAuth_pqxdhAuthHybridSplitKoskImpl1Key {S : Setup}
    (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool) (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridState S) (hBad : badSigOrKemAuth hst = true)
    (resp : AuthResponse) (hst' : AuthHybridState S)
    (hmem : (resp, hst') ∈
      support ((pqxdhAuthHybridSplitKoskImpl1Key sendStage recvStage useRo checkAuth S P q).run hst)) :
    badSigOrKemAuth hst' = true := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp only [h0, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h : bundle.opkB?.isNone = true
    · simp only [h, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad
    · simp only [h, Bool.false_eq_true, ↓reduceIte, runAuthHybridSendKosk_eq] at hmem
      exact badSigOrKemAuth_evalAuthHybridSendKosk sendStage useRo P (.sendOPK u i) u bundle m0 m1
        hst hBad resp hst' hmem
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp only [h0, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h : bundle.opkB?.isSome = true
    · simp only [h, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad
    · simp only [h, Bool.false_eq_true, ↓reduceIte, runAuthHybridSendKosk_eq] at hmem
      exact badSigOrKemAuth_evalAuthHybridSendKosk sendStage useRo P (.sendNoOPK u i) u bundle m0 m1
        hst hBad resp hst' hmem
  | recvOPK k j o msg =>
    rw [pqxdhAuthHybridSplitKoskImpl_recvOPK_eq1Key] at hmem
    unfold prepareAuthHybridRecvOPK at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp only [h0, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                     msg.hdr.pqspkId == UInt32.ofNat j.val &&
                     msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
                     msg.hdr.ikAPk.length == 32 &&
                     msg.hdr.ekAPk.length == 32 &&
                     msg.ephAPk.length == 32)) = true
    { simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h2 : (hst.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    { simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
    { simp only [h3, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h3, Bool.false_eq_true, ↓reduceIte] at hmem
    cases hp : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none =>
      simp only [hp, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad
    | some kp =>
      rcases kp with ⟨_, kEntry⟩
      cases hb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none =>
        simp only [hp, hb, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hBad
      | some bp =>
        rcases bp with ⟨_, bEntry⟩
        cases ho : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none =>
          simp only [hp, hb, ho, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hBad
        | some op =>
          rcases op with ⟨_, oEntry⟩
          simp only [hp, hb, ho] at hmem
          by_cases h4 : oEntry.consumed = true
          { simp only [h4, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hBad }
          simp only [h4, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
            msg.hdr.spkId msg.hdr.ekAPk).1 ||
            !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
          { simp only [h5, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hBad }
          simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
          cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none =>
            simp only [hdec, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hBad
          | some ss =>
            simp only [hdec, mem_support_fmap_iff] at hmem
            rcases hmem with ⟨res?, _, hfin⟩
            have hst_eq := (congrArg Prod.snd hfin).symm
            dsimp only at hst_eq
            rw [hst_eq]
            exact badSigOrKemAuth_finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry _
              msg _ res? hBad
  | recvNoOPK k j l msg =>
    rw [pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq1Key] at hmem
    unfold prepareAuthHybridRecvNoOPK at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp only [h0, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                     msg.hdr.pqspkId == UInt32.ofNat j.val &&
                     msg.hdr.opkId? == none &&
                     msg.hdr.ikAPk.length == 32 &&
                     msg.hdr.ekAPk.length == 32 &&
                     msg.ephAPk.length == 32)) = true
    { simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h2 : (hst.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    { simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
    { simp only [h3, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h3, Bool.false_eq_true, ↓reduceIte] at hmem
    cases hp : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none =>
      simp only [hp, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad
    | some kp =>
      rcases kp with ⟨_, kEntry⟩
      cases hb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none =>
        simp only [hp, hb, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hBad
      | some bp =>
        rcases bp with ⟨_, bEntry⟩
        simp only [hp, hb] at hmem
        by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
          msg.hdr.spkId msg.hdr.ekAPk).1 ||
          !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
        { simp only [h5, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hBad }
        simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
        cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none =>
          simp only [hdec, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hBad
        | some ss =>
          simp only [hdec, mem_support_fmap_iff] at hmem
          rcases hmem with ⟨res?, _, hfin⟩
          have hst_eq := (congrArg Prod.snd hfin).symm
          dsimp only at hst_eq
          rw [hst_eq]
          exact badSigOrKemAuth_finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry _ msg _
            res? hBad
  | initPrin u =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (hst.base.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hBad
    · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hbase
      rcases hbase with ⟨_, _, _, _, _, rfl⟩; exact hBad
  | corruptIK u =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    cases h : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hBad
    | some p =>
      rcases p with ⟨_, _⟩; simp [h, StateT.run_set] at hbase
      rcases hbase with ⟨_, rfl⟩; exact hBad
  | genSPK u j =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hBad
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at hbase
      cases hp : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [hp] at hbase; rcases hbase with ⟨_, rfl⟩; exact hBad
      | some p =>
        rcases p with ⟨_, _⟩
        simp only [hp, StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
          bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hbase
        rcases hbase with ⟨_, _, _, _, ⟨_, _⟩, _, _, _, _, rfl⟩
        exact badSigOrKemAuth_of_sub (hst := hst) (List.Subset.refl _) (Or.inr ⟨_, rfl⟩) hBad
  | genOPK u j o =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hBad
    · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hbase
      rcases hbase with ⟨_, _, _, rfl⟩; exact hBad
  | registerKey sk =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    cases h : registerAdvKey P hst.base.advKeys sk with
    | none => simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hBad
    | some kp =>
      rcases kp with ⟨_, _⟩; simp [h, StateT.run_set] at hbase
      rcases hbase with ⟨_, rfl⟩; exact hBad
  | roQuery secrets =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (!useRo) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hBad
    · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hbase
      rcases hbase with ⟨⟨_, _⟩, _, _, rfl⟩; exact hBad
  | roRootQuery rk dh =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (!useRo) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hBad
    · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hbase
      rcases hbase with ⟨⟨_, _⟩, _, _, rfl⟩; exact hBad
  | revealDhSecrets =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : useRo = true <;> (simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hBad)

theorem badSigOrKemAuth_fullSplitFixedImpl_g5_1Key {S : Setup}
    (sendStage : AuthHybridStage) (useRo checkAuth : Bool) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridStateFixed S)
    (hBad : badSigOrKemAuth hst.toAuthHybridState = true)
    (x : (unifSpec + authSpec S).Range q × AuthHybridStateFixed S)
    (hmem : x ∈
      support ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S)
        ProbComp) +
        pqxdhAuthHybridSplitFixedImpl1Key sendStage .g5 useRo checkAuth S P) q).run hst)) :
    badSigOrKemAuth x.2.toAuthHybridState = true := by
  rcases x with ⟨resp, hst'⟩
  cases q with
  | inl uq =>
    change (resp, hst') ∈
      support ((monadLift (QueryImpl.ofLift unifSpec ProbComp uq) :
        StateT (AuthHybridStateFixed S) ProbComp _).run hst) at hmem
    rw [StateT.run_monadLift, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨_, _, h2⟩
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
    rcases h2 with ⟨_, rfl⟩; exact hBad
  | inr kq =>
    change (resp, hst') ∈
      support ((pqxdhAuthHybridSplitFixedImpl1Key sendStage .g5 useRo checkAuth S P kq).run hst) at hmem
    have hIdeal : (AuthHybridStage.g5).idealMsgKeys = true := rfl
    have hApply := badSigOrKemAuth_pqxdhAuthHybridSplitKoskImpl1Key sendStage .g5 useRo checkAuth P kq
      hst.toAuthHybridState hBad
    cases kq with
    | recvOPK k j o msg =>
      clear hApply
      unfold pqxdhAuthHybridSplitFixedImpl1Key at hmem
      simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind, pqxdhAuthHybridFixedImpl_recvOPK_eq1Key .g5 hIdeal] at hmem
      unfold prepareAuthHybridRecvOPK at hmem
      by_cases h0 : (checkAuth && hst.toAuthHybridState.base.hasWonAuth) = true
      { simp only [h0, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hBad }
      simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                       msg.hdr.pqspkId == UInt32.ofNat j.val &&
                       msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
                       msg.hdr.ikAPk.length == 32 &&
                       msg.hdr.ekAPk.length == 32 &&
                       msg.ephAPk.length == 32)) = true
      { simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hBad }
      simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h2 : (hst.toAuthHybridState.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
      { simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hBad }
      simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h3 : (!koskSenderOk P hst.toAuthHybridState.base.principals
        hst.toAuthHybridState.base.advKeys msg.hdr.ikAPk) = true
      { simp only [h3, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hBad }
      simp only [h3, Bool.false_eq_true, ↓reduceIte] at hmem
      cases hp : hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none =>
        simp only [hp, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hBad
      | some kp =>
        rcases kp with ⟨_, kEntry⟩
        cases hb : hst.toAuthHybridState.base.spkBundles.find? (fun (idx, _) => idx == (k.val,
          j.val)) with
        | none =>
          simp only [hp, hb, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hBad
        | some bp =>
          rcases bp with ⟨_, bEntry⟩
          cases ho : hst.toAuthHybridState.base.opkEntries.find? (fun (idx, _) => idx == (k.val,
            j.val, o.val)) with
          | none =>
            simp only [hp, hb, ho, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hBad
          | some op =>
            rcases op with ⟨_, oEntry⟩
            simp only [hp, hb, ho] at hmem
            by_cases h4 : oEntry.consumed = true
            { simp only [h4, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hBad }
            simp only [h4, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys
              k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
              !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
            { simp only [h5, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hBad }
            simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
            cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
            | none =>
              simp only [hdec, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hBad
            | some ss =>
              simp only [hdec, mem_support_fmap_iff] at hmem
              rcases hmem with ⟨⟨res?, _⟩, _, hfin⟩
              have hst_eq : hst'.toAuthHybridState =
                (finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry _ msg
                  { hst.toAuthHybridState with recvKemRecs :=
                    _ :: hst.toAuthHybridState.recvKemRecs }
                  res?).2 :=
                congrArg AuthHybridStateFixed.toAuthHybridState (congrArg Prod.snd hfin).symm
              rw [hst_eq]
              exact badSigOrKemAuth_finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry _
                msg _ res? hBad
    | recvNoOPK k j l msg =>
      clear hApply
      unfold pqxdhAuthHybridSplitFixedImpl1Key at hmem
      simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind, pqxdhAuthHybridFixedImpl_recvNoOPK_eq1Key .g5 hIdeal] at hmem
      unfold prepareAuthHybridRecvNoOPK at hmem
      by_cases h0 : (checkAuth && hst.toAuthHybridState.base.hasWonAuth) = true
      { simp only [h0, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hBad }
      simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                       msg.hdr.pqspkId == UInt32.ofNat j.val &&
                       msg.hdr.opkId? == none &&
                       msg.hdr.ikAPk.length == 32 &&
                       msg.hdr.ekAPk.length == 32 &&
                       msg.ephAPk.length == 32)) = true
      { simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hBad }
      simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h2 : (hst.toAuthHybridState.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
      { simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hBad }
      simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h3 : (!koskSenderOk P hst.toAuthHybridState.base.principals
        hst.toAuthHybridState.base.advKeys msg.hdr.ikAPk) = true
      { simp only [h3, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hBad }
      simp only [h3, Bool.false_eq_true, ↓reduceIte] at hmem
      cases hp : hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none =>
        simp only [hp, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hBad
      | some kp =>
        rcases kp with ⟨_, kEntry⟩
        cases hb : hst.toAuthHybridState.base.spkBundles.find? (fun (idx, _) => idx == (k.val,
          j.val)) with
        | none =>
          simp only [hp, hb, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hBad
        | some bp =>
          rcases bp with ⟨_, bEntry⟩
          simp only [hp, hb] at hmem
          by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys
            k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
            !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
          { simp only [h5, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hBad }
          simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
          cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none =>
            simp only [hdec, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hBad
          | some ss =>
            simp only [hdec, mem_support_fmap_iff] at hmem
            rcases hmem with ⟨⟨res?, _⟩, _, hfin⟩
            have hst_eq : hst'.toAuthHybridState =
              (finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry _ msg
                { hst.toAuthHybridState with recvKemRecs := _ :: hst.toAuthHybridState.recvKemRecs }
                res?).2 :=
              congrArg AuthHybridStateFixed.toAuthHybridState (congrArg Prod.snd hfin).symm
            rw [hst_eq]
            exact badSigOrKemAuth_finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry _ msg _
              res? hBad
    | sendOPK u i bundle m0 m1 | sendNoOPK u i bundle m0 m1 | initPrin u | corruptIK u
    | genSPK u j | genOPK u j o | registerKey sk | roQuery secrets | roRootQuery rk dh
    | revealDhSecrets =>
      unfold pqxdhAuthHybridSplitFixedImpl1Key at hmem
      simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, StateT.run_monadLift, StateT.run_set, StateT.run_pure, bind_assoc,
        pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨r0, hst0⟩, hmem0, _, rfl⟩
      exact hApply r0 hst0 hmem0

theorem evalDist_simulateQ_resetWonAuthFixed_g5_1Key {S : Setup} {α : Type}
    (sendStage : AuthHybridStage) (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (finT finF : α × AuthHybridStateFixed S → ProbComp Bool)
    (hFinEq : ∀ a (st : AuthHybridStateFixed S),
      badSigOrKemAuth st.toAuthHybridState = false →
      AuthCleanSessionInv P S st.toAuthHybridState →
      finT (a, st) = finF (a, resetWonAuthFixed st))
    (hFinBadT : ∀ a (st : AuthHybridStateFixed S),
      badSigOrKemAuth st.toAuthHybridState = true → 𝒟[finT (a, st)] = 𝒟[$ᵗ Bool])
    (hFinBadF : ∀ a (st : AuthHybridStateFixed S),
      badSigOrKemAuth st.toAuthHybridState = true → 𝒟[finF (a, st)] = 𝒟[$ᵗ Bool])
    (oa : OracleComp (unifSpec + authSpec S) α)
    (st : AuthHybridStateFixed S)
    (hInv : AuthCleanSessionInv P S st.toAuthHybridState) :
    let fullT := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthHybridStateFixed S) ProbComp) +
      pqxdhAuthHybridSplitFixedImpl1Key sendStage .g5 true true S P
    let fullF := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthHybridStateFixed S) ProbComp) +
      pqxdhAuthHybridSplitFixedImpl1Key sendStage .g5 true false S P
    𝒟[(simulateQ fullT oa).run st >>= finT] =
      𝒟[(simulateQ fullF oa).run (resetWonAuthFixed st) >>= finF] := by
  intro fullT fullF
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    by_cases hBad : badSigOrKemAuth st.toAuthHybridState = true
    · rw [hFinBadT a st hBad, hFinBadF a (resetWonAuthFixed st) hBad]
    · have hBadF : badSigOrKemAuth st.toAuthHybridState = false := Bool.eq_false_iff.mpr hBad
      rw [hFinEq a st hBadF hInv]
  | query_bind q t ih =>
    by_cases hBad : badSigOrKemAuth st.toAuthHybridState = true
    · have hL := evalDist_simulateQ_bad_eq_uniformBool
        (fun s => badSigOrKemAuth s.toAuthHybridState) fullT
        (badSigOrKemAuth_fullSplitFixedImpl_g5_1Key sendStage true true P)
        finT hFinBadT (query q >>= t) st hBad
      have hR := evalDist_simulateQ_bad_eq_uniformBool
        (fun s => badSigOrKemAuth s.toAuthHybridState) fullF
        (badSigOrKemAuth_fullSplitFixedImpl_g5_1Key sendStage true false P)
        finF hFinBadF (query q >>= t) (resetWonAuthFixed st) hBad
      exact hL.trans hR.symm
    · have hBadF : badSigOrKemAuth st.toAuthHybridState = false := Bool.eq_false_iff.mpr hBad
      have hBadParts := Bool.or_eq_false_iff.mp hBadF
      have hNoWin : st.toAuthHybridState.base.hasWonAuth = false :=
        hInv.no_false_win hBadParts.1 hBadParts.2
      rw [simulateQ_bind, StateT.run_bind, bind_assoc,
          simulateQ_bind, StateT.run_bind, bind_assoc]
      simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      rw [← map_resetWonAuthFixed_fullSplitFixedImpl1Key sendStage .g5 true true S P q st hNoWin,
          bind_map_left]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun ⟨u, stMid⟩ hmem => ?_
      have hInvMid : AuthCleanSessionInv P S stMid.toAuthHybridState :=
        authCleanSessionInv_fullSplitFixedImpl_g5_1Key sendStage true true P hWF q st hInv u stMid hmem
      exact ih u stMid hInvMid

theorem authSplitFixedExp_g5_checkAuth_eq1Key (sendStage : AuthHybridStage)
    (S : Setup) (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (A : AuthAdversary S) :
    𝒟[authSplitFixedExp1Key sendStage .g5 true S P A] =
      𝒟[authSplitFixedExp1Key sendStage .g5 false S P A] := by
  unfold authSplitFixedExp1Key
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun secb _ => ?_
  dsimp only
  have hsim := evalDist_simulateQ_resetWonAuthFixed_g5_1Key sendStage P hWF
    (fun (b', finalSt) =>
      let allChallengedClean := finalSt.toAuthHybridState.base.sessions.all (fun s =>
        !s.challenged || authInitCorruptionClause P true finalSt.toAuthHybridState.base.principals s)
      if hasEcPkCollisionAuth P finalSt.toAuthHybridState ||
         hasBadSigAuth finalSt.toAuthHybridState ||
         hasKemPkCollisionAuth finalSt.toAuthHybridState ||
         hasBadKemShCrAuth P finalSt.toAuthHybridState then
        $ᵗ Bool
      else if true && finalSt.toAuthHybridState.base.hasWonAuth then
        return true
      else if !allChallengedClean then
        $ᵗ Bool
      else
        return (b' == secb))
    (fun (b', finalSt) =>
      let allChallengedClean := finalSt.toAuthHybridState.base.sessions.all (fun s =>
        !s.challenged || authInitCorruptionClause P true finalSt.toAuthHybridState.base.principals s)
      if hasEcPkCollisionAuth P finalSt.toAuthHybridState ||
         hasBadSigAuth finalSt.toAuthHybridState ||
         hasKemPkCollisionAuth finalSt.toAuthHybridState ||
         hasBadKemShCrAuth P finalSt.toAuthHybridState then
        $ᵗ Bool
      else if false && finalSt.toAuthHybridState.base.hasWonAuth then
        return true
      else if !allChallengedClean then
        $ᵗ Bool
      else
        return (b' == secb))
    (fun b' st hBadF hInv => by
      have hBadParts := Bool.or_eq_false_iff.mp hBadF
      have hWon : st.toAuthHybridState.base.hasWonAuth = false :=
        hInv.no_false_win hBadParts.1 hBadParts.2
      dsimp only
      have hEc : hasEcPkCollisionAuth P (resetWonAuthFixed st).toAuthHybridState =
          hasEcPkCollisionAuth P st.toAuthHybridState := rfl
      have hSig : hasBadSigAuth (resetWonAuthFixed st).toAuthHybridState =
          hasBadSigAuth st.toAuthHybridState := rfl
      have hKem : hasKemPkCollisionAuth (resetWonAuthFixed st).toAuthHybridState =
          hasKemPkCollisionAuth st.toAuthHybridState := rfl
      have hShCr : hasBadKemShCrAuth P (resetWonAuthFixed st).toAuthHybridState =
          hasBadKemShCrAuth P st.toAuthHybridState := rfl
      have hSess : (resetWonAuthFixed st).toAuthHybridState.base.sessions =
          st.toAuthHybridState.base.sessions := rfl
      have hPrin : (resetWonAuthFixed st).toAuthHybridState.base.principals =
          st.toAuthHybridState.base.principals := rfl
      simp [hEc, hSig, hKem, hShCr, hSess, hPrin, hWon])
    (fun b' st hBad => by
      dsimp only
      rcases Bool.or_eq_true_iff.mp hBad with hSig | hKem
      · simp [hSig]
      · simp [hKem])
    (fun b' st hBad => by
      dsimp only
      rcases Bool.or_eq_true_iff.mp hBad with hSig | hKem
      · simp [hSig]
      · simp [hKem])
    A.run (AuthHybridStateFixed.empty S secb) (authCleanSessionInv_empty P S secb)
  rw [resetWonAuthFixed_empty] at hsim
  exact hsim

theorem map_setSecb_pqxdhAuthHybridSplitKoskImpl_g5_1Key
    (b : Bool) (recvStage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) (q : AuthQuery S) (hst : AuthHybridState S) :
    Prod.map id (setSecb b) <$>
        ((pqxdhAuthHybridSplitKoskImpl1Key .g5 recvStage useRo checkAuth S P q).run hst) =
      (pqxdhAuthHybridSplitKoskImpl1Key .g5 recvStage useRo checkAuth S P q).run (setSecb b hst) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key
    have hb_won : (setSecb b hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb_won]
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0, Prod.map] }
    simp only [h0, Bool.false_eq_true, ↓reduceIte]
    by_cases h : bundle.opkB?.isNone = true
    · simp [h, Prod.map]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, runAuthHybridSendKosk_eq]
      exact evalAuthHybridSendKosk_g5_setSecb b useRo S P (.sendOPK u i) u bundle m0 m1 hst
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key
    have hb_won : (setSecb b hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb_won]
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0, Prod.map] }
    simp only [h0, Bool.false_eq_true, ↓reduceIte]
    by_cases h : bundle.opkB?.isSome = true
    · simp [h, Prod.map]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, runAuthHybridSendKosk_eq]
      exact evalAuthHybridSendKosk_g5_setSecb b useRo S P (.sendNoOPK u i) u bundle m0 m1 hst
  | recvOPK k j o msg =>
    rw [pqxdhAuthHybridSplitKoskImpl_recvOPK_eq1Key, pqxdhAuthHybridSplitKoskImpl_recvOPK_eq1Key,
      prepareAuthHybridRecvOPK_setSecb b checkAuth]
    cases prepareAuthHybridRecvOPK checkAuth P k j o msg hst with
    | none => simp [Prod.map]
    | some prep =>
      simp only [Option.map, evalAuthHybridRecvSchedule_setSecb, Functor.map_map]
  | recvNoOPK k j l msg =>
    rw [pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq1Key, pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq1Key,
      prepareAuthHybridRecvNoOPK_setSecb b checkAuth]
    cases prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst with
    | none => simp [Prod.map]
    | some prep =>
      simp only [Option.map, evalAuthHybridRecvSchedule_setSecb, Functor.map_map]
  | initPrin u =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
    have hb_won : (setSecb b hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb_won]
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0, Prod.map] }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase]
    have hb : (setSecb b hst).base.principals = hst.base.principals := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb]
    by_cases h : (hst.base.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp [h, Prod.map]
    · simp [h, StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map, setSecb]
  | corruptIK u =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
    have hb_won : (setSecb b hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb_won]
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0, Prod.map] }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase]
    have hb : (setSecb b hst).base.principals = hst.base.principals := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb]
    cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp [Prod.map]
    | some up =>
      rcases up with ⟨_, pEntry⟩
      simp [StateT.run_bind, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp,
        pure_bind, Function.comp_apply, Prod.map, setSecb]
  | genSPK u j =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
    have hb_won : (setSecb b hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb_won]
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0, Prod.map] }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase]
    have hb1 : (setSecb b hst).base.principals = hst.base.principals := rfl
    have hb2 : (setSecb b hst).base.spkBundles = hst.base.spkBundles := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb1, hb2]
    by_cases h : (hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp [h, Prod.map]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [Prod.map]
      | some up =>
        rcases up with ⟨_, pEntry⟩
        simp [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
          map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map, setSecb]
  | genOPK u j o =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
    have hb_won : (setSecb b hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb_won]
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0, Prod.map] }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase]
    have hb : (setSecb b hst).base.opkEntries = hst.base.opkEntries := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb]
    by_cases h : (hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp [h, Prod.map]
    · simp [h, StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map, setSecb]
  | registerKey sk =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
    have hb_won : (setSecb b hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb_won]
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0, Prod.map] }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase]
    have hb : (setSecb b hst).base.advKeys = hst.base.advKeys := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb]
    cases registerAdvKey P hst.base.advKeys sk with
    | none => simp [Prod.map]
    | some kp =>
      rcases kp with ⟨pk, advKeys'⟩
      simp [StateT.run_bind, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp,
        pure_bind, Function.comp_apply, Prod.map, setSecb]
  | roQuery secrets =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
    have hb_won : (setSecb b hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb_won]
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0, Prod.map] }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase]
    have hb : (setSecb b hst).base.roCache = hst.base.roCache := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb]
    by_cases h : (!useRo) = true
    · simp [h, Prod.map]
    · simp [h, StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map, setSecb]
  | roRootQuery rk dh =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
    have hb_won : (setSecb b hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb_won]
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0, Prod.map] }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase]
    have hb : (setSecb b hst).base.rootRoCache = hst.base.rootRoCache := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb]
    by_cases h : (!useRo) = true
    · simp [h, Prod.map]
    · simp [h, StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map, setSecb]
  | revealDhSecrets =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
    have hb_won : (setSecb b hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb_won]
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0, Prod.map] }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase]
    have hb1 : (setSecb b hst).base.principals = hst.base.principals := rfl
    have hb2 : (setSecb b hst).base.spkBundles = hst.base.spkBundles := rfl
    have hb3 : (setSecb b hst).base.opkEntries = hst.base.opkEntries := rfl
    have hb4 : (setSecb b hst).base.sessions = hst.base.sessions := rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hb1, hb2, hb3, hb4]
    by_cases h : useRo = true <;> simp [h, Prod.map, setSecb]

theorem map_setSecbFixed_fullSplitFixedImpl_g5_1Key
    (b : Bool) (recvStage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridStateFixed S) :
    Prod.map id (setSecbFixed b) <$>
        ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S)
          ProbComp) +
          pqxdhAuthHybridSplitFixedImpl1Key .g5 recvStage useRo checkAuth S P) q).run hst) =
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
        pqxdhAuthHybridSplitFixedImpl1Key .g5 recvStage useRo checkAuth S P) q).run
        (setSecbFixed b hst) := by
  cases q with
  | inl uq =>
    change Prod.map id (setSecbFixed b) <$>
        (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp)
          uq).run hst) =
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp)
        uq).run
        (setSecbFixed b hst)
    simp [QueryImpl.liftTarget, StateT.run_monadLift, map_eq_bind_pure_comp, Prod.map]
  | inr kq =>
    change Prod.map id (setSecbFixed b) <$>
        ((pqxdhAuthHybridSplitFixedImpl1Key .g5 recvStage useRo checkAuth S P kq).run hst) =
      (pqxdhAuthHybridSplitFixedImpl1Key .g5 recvStage useRo checkAuth S P kq).run
        (setSecbFixed b hst)
    have hto : (setSecbFixed b hst).toAuthHybridState = setSecb b hst.toAuthHybridState := rfl
    have hrc : (setSecbFixed b hst).recvCount = hst.recvCount := rfl
    have hmc : (setSecbFixed b hst).mkSaltCache = hst.mkSaltCache := rfl
    by_cases hIdeal : recvStage.idealMsgKeys = true
    · have hSend :=
        map_setSecb_pqxdhAuthHybridSplitKoskImpl_g5_1Key b .g5 useRo checkAuth S P kq
          hst.toAuthHybridState
      rw [pqxdhAuthHybridSplitKoskImpl_same1Key] at hSend
      cases kq with
      | recvOPK k j o msg =>
        clear hSend
        unfold pqxdhAuthHybridSplitFixedImpl1Key
        simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          StateT.run_get, pure_bind,
          pqxdhAuthHybridFixedImpl_recvOPK_eq1Key recvStage hIdeal, hto, hrc, hmc,
          prepareAuthHybridRecvOPK_setSecb b checkAuth]
        cases prepareAuthHybridRecvOPK checkAuth P k j o msg hst.toAuthHybridState with
        | none => simp [Prod.map, setSecbFixed]
        | some prep =>
          simp [ Option.map, evalAuthFixedRecvScheduleCached_setSecb, Functor.map_map, Prod.map,
              setSecbFixed]
      | recvNoOPK k j l msg =>
        clear hSend
        unfold pqxdhAuthHybridSplitFixedImpl1Key
        simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          StateT.run_get, pure_bind,
          pqxdhAuthHybridFixedImpl_recvNoOPK_eq1Key recvStage hIdeal, hto, hrc, hmc,
          prepareAuthHybridRecvNoOPK_setSecb b checkAuth]
        cases prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst.toAuthHybridState with
        | none => simp [Prod.map, setSecbFixed]
        | some prep =>
          simp [ Option.map, evalAuthFixedRecvScheduleCached_setSecb, Functor.map_map, Prod.map,
              setSecbFixed]
      | sendOPK u i bundle m0 m1 | sendNoOPK u i bundle m0 m1 | initPrin u | corruptIK u
      | genSPK u j | genOPK u j o | registerKey sk | roQuery secrets | roRootQuery rk dh |
        revealDhSecrets =>
        unfold pqxdhAuthHybridSplitFixedImpl1Key
        simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          StateT.run_get,
          StateT.run_monadLift, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
        rw [hto, hrc, hmc, ← hSend]
        simp [ map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map,
            setSecbFixed]
    · have hIdealF : recvStage.idealMsgKeys = false := Bool.eq_false_iff.mpr hIdeal
      unfold pqxdhAuthHybridSplitFixedImpl1Key
      simp only [hIdealF, Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get,
        StateT.run_monadLift, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      have h :=
        map_setSecb_pqxdhAuthHybridSplitKoskImpl_g5_1Key b recvStage useRo checkAuth S P kq
          hst.toAuthHybridState
      rw [hto, hrc, hmc, ← h]
      simp [ map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map,
          setSecbFixed]

theorem evalDist_authSplitFixedExp_g5_g5_false_eq_authFixedExpG5_1Key
    (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    𝒟[authSplitFixedExp1Key .g5 .g5 false S P A] = 𝒟[authFixedExpG5_1Key S P A] := by
  unfold authSplitFixedExp1Key authFixedExpG5_1Key authFixedIdealBranch1Key
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun secb _ => ?_
  simp only [ite_self, bind_assoc, pqxdhAuthHybridSplitFixedImpl_same1Key]
  have hsim := _root_.Proofs.SignalPqxdh.Security.map_proj_simulateQ
    (setSecbFixed secb)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
      pqxdhAuthHybridFixedImpl1Key .g5 true false S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
      pqxdhAuthHybridFixedImpl1Key .g5 true false S P)
    (fun q hst => by simpa only [pqxdhAuthHybridSplitFixedImpl_same1Key] using
      map_setSecbFixed_fullSplitFixedImpl_g5_1Key secb .g5 true false S P q hst)
    A.run (AuthHybridStateFixed.empty S false)
  rw [setSecbFixed_empty] at hsim
  rw [← hsim, bind_map_left]
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun ⟨b', finalSt⟩ _ => ?_
  have hEc : hasEcPkCollisionAuth P (setSecbFixed secb finalSt).toAuthHybridState =
      hasEcPkCollisionAuth P finalSt.toAuthHybridState := rfl
  have hSig : hasBadSigAuth (setSecbFixed secb finalSt).toAuthHybridState =
      hasBadSigAuth finalSt.toAuthHybridState := rfl
  have hKem : hasKemPkCollisionAuth (setSecbFixed secb finalSt).toAuthHybridState =
      hasKemPkCollisionAuth finalSt.toAuthHybridState := rfl
  have hShCr : hasBadKemShCrAuth P (setSecbFixed secb finalSt).toAuthHybridState =
      hasBadKemShCrAuth P finalSt.toAuthHybridState := rfl
  have hSess : (setSecbFixed secb finalSt).toAuthHybridState.base.sessions =
      finalSt.toAuthHybridState.base.sessions := rfl
  have hPrin : (setSecbFixed secb finalSt).toAuthHybridState.base.principals =
      finalSt.toAuthHybridState.base.principals := rfl
  simp only [ Prod.map, hEc, hSig, hKem, hShCr, hSess, hPrin, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, id_eq]
  generalize (!finalSt.toAuthHybridState.base.sessions.all (fun s =>
    !s.challenged || authInitCorruptionClause P true finalSt.toAuthHybridState.base.principals s)) =
      c
  generalize hasEcPkCollisionAuth P finalSt.toAuthHybridState = e1
  generalize hasBadSigAuth finalSt.toAuthHybridState = e2
  generalize hasKemPkCollisionAuth finalSt.toAuthHybridState = e3
  generalize hasBadKemShCrAuth P finalSt.toAuthHybridState = e4
  cases c <;> cases e1 <;> cases e2 <;> cases e3 <;> cases e4
  all_goals simp only [Bool.or_true, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, pure_bind]
  all_goals first
    | exact (evalDist_uniformBool_beq_local secb).symm
    | rw [Bool.beq_comm]

theorem authSplitFixedExp_g5_g5_false_boolBias_eq_zero1Key
    (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    (𝒟[authSplitFixedExp1Key .g5 .g5 false S P A].boolBias).toReal = 0 := by
  rw [evalDist_authSplitFixedExp_g5_g5_false_eq_authFixedExpG5_1Key]
  exact authFixedAdvG5_eq_zero1Key S P A

theorem evalDist_authSplitFixedExp_g5_g5_true_eq_authFixedExpG5_1Key
    (S : Setup) (P : Primitives) (hWF : WellFormedPrimitivesδ P) (A : AuthAdversary S) :
    𝒟[authSplitFixedExp1Key .g5 .g5 true S P A] = 𝒟[authFixedExpG5_1Key S P A] := by
  rw [authSplitFixedExp_g5_checkAuth_eq1Key .g5 S P hWF A]
  exact evalDist_authSplitFixedExp_g5_g5_false_eq_authFixedExpG5_1Key S P A

theorem authSplitFixedExp_g5_g5_true_boolBias_eq_zero1Key
    (S : Setup) (P : Primitives) (hWF : WellFormedPrimitivesδ P) (A : AuthAdversary S) :
    (𝒟[authSplitFixedExp1Key .g5 .g5 true S P A].boolBias).toReal = 0 := by
  rw [authSplitFixedExp_g5_checkAuth_eq1Key .g5 S P hWF A]
  exact authSplitFixedExp_g5_g5_false_boolBias_eq_zero1Key S P A

end SignalPqxdh.Security
