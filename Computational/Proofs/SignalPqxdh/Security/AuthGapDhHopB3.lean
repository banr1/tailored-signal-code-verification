/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopB1
import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopB2
import Computational.Proofs.SignalPqxdh.Security.Collisions
import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingA -- shake: keep

/-!
# `Auth` hop `G0 → G3`: KEM split-key hash collision bridge and assembly

Couples the `G3` hybrid game to `runAuthShCrSim` and combines the EC/KEM collision, EUF-CMA, and
`KemShCr` bounds via freeze-on-win hybrids to prove `auth_hop_G0_G3_le`.
-/

@[expose] public section
set_option autoImplicit false
open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
namespace Proofs.SignalPqxdh.Security
/-! ## Freeze-on-win provenance hybrids -/
def CommutesProj {St1 St2 R : Type} (proj : St2 → St1) (st : St2)
    (m1 : StateT St1 ProbComp R) (m2 : StateT St2 ProbComp R) : Prop :=
  (m1.run (proj st)) = Prod.map id proj <$> (m2.run st)
theorem CommutesProj.get_bind {St1 St2 R : Type} (proj : St2 → St1) (st : St2)
    {f1 : St1 → StateT St1 ProbComp R} {f2 : St2 → StateT St2 ProbComp R}
    (hf : CommutesProj proj st (f1 (proj st)) (f2 st)) :
    CommutesProj proj st (get >>= f1) (get >>= f2) := hf
theorem CommutesProj.get_right {St1 St2 R : Type} (proj : St2 → St1) (st : St2)
    {m1 : StateT St1 ProbComp R} {f2 : St2 → StateT St2 ProbComp R}
    (hf : CommutesProj proj st m1 (f2 st)) : CommutesProj proj st m1 (get >>= f2) := hf
theorem CommutesProj.pure {St1 St2 R : Type} (proj : St2 → St1) (st : St2) (x : R) :
    CommutesProj proj st (Pure.pure x) (Pure.pure x) := by
  simp [CommutesProj, Prod.map]
theorem CommutesProj.liftM_bind {St1 St2 R1 R2 : Type} (proj : St2 → St1) (st : St2)
    (mx : ProbComp R1) {f1 : R1 → StateT St1 ProbComp R2} {f2 : R1 → StateT St2 ProbComp R2}
    (hf : ∀ a, CommutesProj proj st (f1 a) (f2 a)) :
    CommutesProj proj st ((liftM mx : StateT St1 ProbComp R1) >>= f1)
      ((liftM mx : StateT St2 ProbComp R1) >>= f2) := by
  unfold CommutesProj at *; simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
    bind_assoc, pure_bind, map_bind, hf]
theorem CommutesProj.set_bind {St1 St2 R : Type} (proj : St2 → St1) (st st2 : St2) (st1 : St1)
    {f1 : PUnit → StateT St1 ProbComp R} {f2 : PUnit → StateT St2 ProbComp R} (h : st1 = proj st2)
    (hf : CommutesProj proj st2 (f1 PUnit.unit) (f2 PUnit.unit)) :
    CommutesProj proj st (set st1 >>= f1) (set st2 >>= f2) := by
  unfold CommutesProj at *; simp only [StateT.run_bind, StateT.run_set, pure_bind, h, hf]
theorem CommutesProj.ite {St1 St2 R : Type} (proj : St2 → St1) (st : St2)
    (c : Prop) [Decidable c] {t1 e1 : StateT St1 ProbComp R} {t2 e2 : StateT St2 ProbComp R}
    (ht : CommutesProj proj st t1 t2) (he : CommutesProj proj st e1 e2) :
    CommutesProj proj st (if c then t1 else e1) (if c then t2 else e2) := by
  by_cases hc : c <;> simp [hc, ht, he]
theorem evalAuthHybridRecvSchedule_g3 {S : Setup} (useRo : Bool) (P : Primitives)
    (hst : AuthHybridState S) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) :
    evalAuthHybridRecvSchedule .g3 useRo P hst kEntry bEntry opkPk? secrets msg = (do
      let (drKey, roCache') ← evalHkdfOrRo useRo P hst.base.roCache secrets
      let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
      let ((rk1, ck1_0), rootRoCache') ←
        evalRootKdfOrRo useRo P hst.base.rootRoCache drKey.rootKey dhRatchet
      let (mkSeed, ck1_1) := (P.chainKdfSeed ck1_0, P.chainKdfNext ck1_0)
      match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none => return none
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
        let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        match P.aeadDec deriveMessageKeys ad msg.aeadCt with
        | none => return none
        | some pt => return some (drKey, rk1, ck1_1, pt, roCache', rootRoCache')) := by
  unfold evalAuthHybridRecvSchedule
  dsimp only [AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
    AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys, AuthHybridStage.idealFreshAead,
    AuthHybridStage.idealUnmatchedRecvAead]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind, ite_self]
  apply bind_congr; rintro ⟨drKey, roCache'⟩; apply bind_congr; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
  cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
  | none => rfl
  | some spqrPair =>
    rcases spqrPair with ⟨_pqrStB, spqrSalt?⟩; rfl
theorem runAuthHybridSendKosk_g3_commutes_base (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S) : CommutesProj AuthHybridState.base hst
      (runAuthSendWithProv S P (checkBundleProvenanceExact P) sid u bundle m0 m1)
      (runAuthHybridSendKosk .g3 true S P sid u bundle m0 m1) := by
  unfold runAuthSendWithProv runAuthHybridSendKosk
  dsimp only [AuthHybridStage.idealFreshAead, AuthHybridStage.idealDrKey,
    AuthHybridStage.idealRk, AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
  apply CommutesProj.get_bind
  refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
  refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
  cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => exact CommutesProj.pure _ hst _
  | some uPair =>
    rcases uPair with ⟨_, uEntry⟩; dsimp only
    refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
    refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
    apply CommutesProj.liftM_bind; intro ekASk; apply CommutesProj.liftM_bind; intro kemCoins
    apply CommutesProj.liftM_bind; intro ephASk; apply CommutesProj.liftM_bind; intro spqrCoins
    refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
    cases P.kemEncaps bundle.pqspkB kemCoins with
    | none => exact CommutesProj.pure _ hst _
    | some kemPair =>
      rcases kemPair with ⟨ss, kemCt⟩; dsimp only
      apply CommutesProj.liftM_bind; rintro ⟨drKey, roCache'⟩
      apply CommutesProj.liftM_bind; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩; dsimp only
      cases P.spqrInitSend drKey.pqrKey spqrCoins with
      | none => exact CommutesProj.pure _ hst _
      | some spqrTriple =>
        rcases spqrTriple with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only
        cases (findHonestPrincipal P hst.base.principals bundle.ikB).isSome <;>
          exact CommutesProj.set_bind _ _ _ _ rfl (CommutesProj.pure _ _ _)
def freezeImpl {ι : Type} {spec : OracleSpec.{0, 0} ι} {St : Type}
    (hasWon : St → Bool) (defResp : ∀ q : ι, spec.Range q)
    (impl : QueryImpl spec (StateT St ProbComp)) :
    QueryImpl spec (StateT St ProbComp) := fun q => do
  let st ← get
  if hasWon st then return defResp q else impl q
def pqxdhAuthWithProvFrozenImpl (S : Setup) (P : Primitives) (provFn : ProvFnType) :
    QueryImpl (authSpec S) (StateT (AuthState S) ProbComp) :=
  freezeImpl AuthState.hasWonAuth (fun _ => .noneResp) (pqxdhAuthWithProvImpl S P provFn)
noncomputable def runAuthWithProvFrozen (prov : ProvFnType) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthState S) := do
  let secb ← $ᵗ Bool; let initSt := AuthState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
    pqxdhAuthWithProvFrozenImpl S P prov
  let (b', finalSt) ← (simulateQ impl A.run).run initSt; return (secb, b', finalSt)
noncomputable def authExpG0Frozen (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  runAuthWithProvFrozen (checkBundleProvenance P) S P A >>= contAuth S P
noncomputable def authExpG0_1WithProvFrozen (prov : ProvFnType) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  runAuthWithProvFrozen prov S P A >>= fun a =>
    if hasEcPkCollisionAuth P a.2.2 then $ᵗ Bool else contAuth S P a
noncomputable def authExpG1WithProvFrozen (prov : ProvFnType) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  runAuthWithProvFrozen prov S P A >>= fun a =>
    if hasEcPkCollisionAuth P a.2.2 || hasBadSigAuth a.2.2 then $ᵗ Bool else contAuth S P a
noncomputable def authExpG2_1WithProvFrozen (prov : ProvFnType) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  runAuthWithProvFrozen prov S P A >>= fun a =>
    if (hasEcPkCollisionAuth P a.2.2 || hasBadSigAuth a.2.2) ||
       hasKemPkCollisionAuth a.2.2 then $ᵗ Bool else contAuth S P a
theorem pqxdhAuthHybridKoskImpl_g3_commutes_base (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (hst : AuthHybridState S) : CommutesProj AuthHybridState.base hst
      (pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceExact P) q)
      (pqxdhAuthHybridKoskImpl .g3 true true S P q) := by
  by_cases hWonT : hst.base.hasWonAuth = true
  · cases q <;>
      simp [CommutesProj, pqxdhAuthWithProvFrozenImpl, freezeImpl, pqxdhAuthHybridKoskImpl,
        StateT.run_bind, StateT.run_get, pure_bind, hWonT, Prod.map]
  · have hWon : hst.base.hasWonAuth = false := Bool.eq_false_iff.mpr hWonT
    have hL : ((pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceExact P) q).run hst.base) =
        (pqxdhAuthWithProvImpl S P (checkBundleProvenanceExact P) q).run hst.base := by
      simp [pqxdhAuthWithProvFrozenImpl, freezeImpl, StateT.run_bind, StateT.run_get,
        pure_bind, hWon]
    unfold CommutesProj; rw [hL]; change CommutesProj AuthHybridState.base hst
      (pqxdhAuthWithProvImpl S P (checkBundleProvenanceExact P) q)
      (pqxdhAuthHybridKoskImpl .g3 true true S P q)
    cases q with
    | sendOPK u i bundle m0 m1 =>
      unfold pqxdhAuthWithProvImpl pqxdhAuthHybridKoskImpl; dsimp only; apply CommutesProj.get_right
      simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _)
        (runAuthHybridSendKosk_g3_commutes_base S P (.sendOPK u i) u bundle m0 m1 hst)
    | sendNoOPK u i bundle m0 m1 =>
      unfold pqxdhAuthWithProvImpl pqxdhAuthHybridKoskImpl; dsimp only; apply CommutesProj.get_right
      simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _)
        (runAuthHybridSendKosk_g3_commutes_base S P (.sendNoOPK u i) u bundle m0 m1 hst)
    | recvOPK k j o msg =>
      unfold pqxdhAuthWithProvImpl pqxdhAuthImpl pqxdhAuthHybridKoskImpl
      apply CommutesProj.get_bind; dsimp only; simp only [hWon, Bool.and_false]
      refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
      refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
      refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
      cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none => exact CommutesProj.pure _ hst _
      | some kp =>
        rcases kp with ⟨_, kEntry⟩; dsimp only
        cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => exact CommutesProj.pure _ hst _
        | some bp =>
          rcases bp with ⟨_, bEntry⟩; dsimp only
          cases hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
          | none => exact CommutesProj.pure _ hst _
          | some op =>
            rcases op with ⟨_, oEntry⟩; dsimp only
            refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
            refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
            by_cases hct : msg.hdr.kemCt.length = kyberCtLen
            · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = false := by simp [hct]
              simp only [hctb, Bool.false_eq_true, ↓reduceIte]
              cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none => exact CommutesProj.pure _ hst _
              | some ss =>
                unfold CommutesProj; simp only [StateT.run_bind, StateT.run_set, pure_bind]
                rw [evalAuthHybridRecvSchedule_g3]; dsimp only
                simp only [StateT.run_monadLift, monadLift_self, map_bind, bind_assoc, pure_bind]
                apply bind_congr; rintro ⟨drKey, roCache'⟩
                apply bind_congr; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩; dsimp only
                cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
                | none => simp [StateT.run_pure, Prod.map]
                | some spqrPair =>
                  rcases spqrPair with ⟨_pqrStB, spqrSalt?⟩; dsimp only
                  cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
                    (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg)
                    msg.aeadCt with
                  | none => simp [StateT.run_pure, Prod.map]
                  | some pt =>
                    dsimp only; simp only [pure_bind]
                    cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                    | none => simp [StateT.run_set, Prod.map]
                    | some sp =>
                      rcases sp with ⟨_, senderEntry⟩; dsimp only
                      cases (!senderEntry.corrupted) <;> simp [StateT.run_set, Prod.map]
            · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = true := by simp [hct]
              rw [hP.kemDecaps_len_reject _ _ hct]
              simp only [hctb, ↓reduceIte]
              exact CommutesProj.pure _ hst _
    | recvNoOPK k j l msg =>
      unfold pqxdhAuthWithProvImpl pqxdhAuthImpl pqxdhAuthHybridKoskImpl
      apply CommutesProj.get_bind; dsimp only; simp only [hWon, Bool.and_false]
      refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
      refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
      refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
      cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none => exact CommutesProj.pure _ hst _
      | some kp =>
        rcases kp with ⟨_, kEntry⟩; dsimp only
        cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => exact CommutesProj.pure _ hst _
        | some bp =>
          rcases bp with ⟨_, bEntry⟩; dsimp only
          refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
          by_cases hct : msg.hdr.kemCt.length = kyberCtLen
          · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = false := by simp [hct]
            simp only [hctb, Bool.false_eq_true, ↓reduceIte]
            cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
            | none => exact CommutesProj.pure _ hst _
            | some ss =>
              dsimp only; unfold CommutesProj; simp only [StateT.run_bind, StateT.run_set, pure_bind]
              rw [evalAuthHybridRecvSchedule_g3]; dsimp only
              simp only [StateT.run_monadLift, monadLift_self, map_bind, bind_assoc, pure_bind]
              apply bind_congr; rintro ⟨drKey, roCache'⟩
              apply bind_congr; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩; dsimp only
              cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
              | none => simp [StateT.run_pure, Prod.map]
              | some spqrPair =>
                rcases spqrPair with ⟨_pqrStB, spqrSalt?⟩; dsimp only
                cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
                  (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
                | none => simp [StateT.run_pure, Prod.map]
                | some pt =>
                  dsimp only; simp only [pure_bind]
                  cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                  | none => simp [StateT.run_set, Prod.map]
                  | some sp =>
                    rcases sp with ⟨_, senderEntry⟩; dsimp only
                    cases (!senderEntry.corrupted) <;> simp [StateT.run_set, Prod.map]
          · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = true := by simp [hct]
            rw [hP.kemDecaps_len_reject _ _ hct]
            simp only [hctb, ↓reduceIte]
            exact CommutesProj.pure _ hst _
    | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
    | revealDhSecrets | registerKey _ =>
      unfold pqxdhAuthWithProvImpl pqxdhAuthHybridKoskImpl liftAuthBase CommutesProj
      simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self, hWon, Prod.map]
theorem map_base_pqxdhAuthHybridKoskImpl_g3 (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (hst : AuthHybridState S) : Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q).run hst =
    (pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceExact P) q).run hst.base :=
  (pqxdhAuthHybridKoskImpl_g3_commutes_base S P hP q hst).symm
theorem map_base_fullAuthHybridKoskImpl_g3 (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridState S) :
    Prod.map id AuthHybridState.base <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
        pqxdhAuthHybridKoskImpl .g3 true true S P) q).run hst =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
      pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceExact P)) q).run hst.base := by
  cases q with
  | inl uq => simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr kq => exact map_base_pqxdhAuthHybridKoskImpl_g3 S P hP kq hst
noncomputable def runAuthKoskG3 (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthHybridState S) := do
  let secb ← $ᵗ Bool; let initSt := AuthHybridState.empty S secb
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
    pqxdhAuthHybridKoskImpl .g3 true true S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt; return (secb, b', finalSt)
theorem runAuthKoskG3_map_base (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    (fun (secb, b', finalSt) => (secb, b', finalSt.base)) <$> runAuthKoskG3 S P A =
      runAuthWithProvFrozen (checkBundleProvenanceExact P) S P A := by
  unfold runAuthKoskG3 runAuthWithProvFrozen; simp only [map_bind, map_pure]
  refine bind_congr (fun secb => ?_)
  have hsim := map_proj_simulateQ AuthHybridState.base
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
      pqxdhAuthHybridKoskImpl .g3 true true S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
      pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceExact P))
    (map_base_fullAuthHybridKoskImpl_g3 S P hP) A.run (AuthHybridState.empty S secb)
  dsimp only [AuthHybridState.empty] at hsim; rw [← hsim, bind_map_left]; rfl
theorem authExpG2_1WithProv_exact_eq_kosk (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    authExpG2_1WithProvFrozen (checkBundleProvenanceExact P) S P A =
      (runAuthKoskG3 S P A >>= fun (secb, b', finalSt) =>
        if (hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt) ||
           hasKemPkCollisionAuth finalSt then $ᵗ Bool
        else contAuth S P (secb, b', finalSt.base)) := by
  unfold authExpG2_1WithProvFrozen; rw [← runAuthKoskG3_map_base S P hP A, bind_map_left]; rfl
theorem authKoskExpAtStage_g3_eq (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    authKoskExpAtStage .g3 S P A = (runAuthKoskG3 S P A >>= fun (secb, b', finalSt) =>
        if ((hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt) ||
            hasKemPkCollisionAuth finalSt) || hasBadKemShCrAuth P finalSt then
          $ᵗ Bool
        else contAuth S P (secb, b', finalSt.base)) := by
  unfold authKoskExpAtStage runAuthKoskG3 contAuth; simp only [bind_assoc, pure_bind]
theorem auth_hop_G2_1_exact_G3_le_prob (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    |(𝒟[authExpG2_1WithProvFrozen (checkBundleProvenanceExact P) S P A].boolBias).toReal -
     authFixedAdvG3 S P A| ≤ (𝒟[runAuthKoskG3 S P A >>= fun (_, _, finalSt) =>
        pure (hasBadKemShCrAuth P finalSt)] {true}).toReal := by
  change |(𝒟[authExpG2_1WithProvFrozen (checkBundleProvenanceExact P) S P A].boolBias).toReal -
     (𝒟[authFixedExpAtStage .g3 S P A].boolBias).toReal| ≤ _
  rw [authFixedExpAtStage_eq_authKoskExpAtStage .g3 S P A, authExpG2_1WithProv_exact_eq_kosk S P hP A,
      authKoskExpAtStage_g3_eq S P A]
  exact abs_sub_boolBias_abort_or_le (runAuthKoskG3 S P A) (fun (_, _, finalSt) =>
      (hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt) || hasKemPkCollisionAuth finalSt)
    (fun (_, _, finalSt) => hasBadKemShCrAuth P finalSt)
    (fun (secb, b', finalSt) => contAuth S P (secb, b', finalSt.base))
/-! ## Bridge to `runAuthShCrSim` -/
abbrev AuthHybridShCrState (S : Setup) := ShCrState S (AuthHybridState S)
def mapShCrBase {S : Setup} {B1 B2 : Type} (f : B1 → B2) (hst : ShCrState S B1) : ShCrState S B2 :=
  { base := f hst.base, targetBIdx? := hst.targetBIdx?, targetPk := hst.targetPk,
    targetSk := hst.targetSk, sendCount := hst.sendCount, initKemRecs := hst.initKemRecs,
    recvKemRecs := hst.recvKemRecs }
theorem mapShCrBase_liftShCrBase {S : Setup} {B1 B2 R : Type} (f : B1 → B2)
    (m1 : StateT B1 ProbComp R) (m2 : StateT B2 ProbComp R) (hst : ShCrState S B1)
    (hm : Prod.map id f <$> m1.run hst.base = m2.run (f hst.base)) :
    Prod.map id (mapShCrBase f) <$> (liftShCrBase m1).run hst =
      (liftShCrBase m2).run (mapShCrBase f hst) := by
  unfold liftShCrBase mapShCrBase StateT.run; dsimp only; rw [← hm]; simp [Prod.map]
theorem mapShCrBase_recordAcceptKemGeneric {S : Setup} {B1 B2 R : Type} (P : Primitives)
    (f : B1 → B2) (getBundles1 : B1 → List ((Nat × Nat) × SpkBundleEntry))
    (getBundles2 : B2 → List ((Nat × Nat) × SpkBundleEntry)) (isNoneResp : R → Bool)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr) (out : R) (hst : ShCrState S B1)
    (hb : getBundles2 (f hst.base) = getBundles1 hst.base) : Prod.map id (mapShCrBase f) <$>
      (recordAcceptKemGeneric P getBundles1 isNoneResp k j hdr out).run hst =
      (recordAcceptKemGeneric P getBundles2 isNoneResp k j hdr out).run (mapShCrBase f hst) := by
  unfold recordAcceptKemGeneric mapShCrBase StateT.run; dsimp only; rw [hb]
  cases isNoneResp out
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases (getBundles1 hst.base).find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => simp [Prod.map]
    | some bp =>
      rcases bp with ⟨_, bEntry⟩; dsimp only
      cases P.kemDecaps bEntry.pqspkSk hdr.kemCt <;> simp [Prod.map]
  · simp [Prod.map]
theorem mapShCrBase_runShCrAcceptGeneric {S : Setup} {B1 B2 R : Type} (P : Primitives)
    (f : B1 → B2) (getBundles1 : B1 → List ((Nat × Nat) × SpkBundleEntry))
    (getBundles2 : B2 → List ((Nat × Nat) × SpkBundleEntry)) (isNoneResp : R → Bool)
    (m1 : StateT B1 ProbComp R) (m2 : StateT B2 ProbComp R)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr) (hst : ShCrState S B1)
    (hm : Prod.map id f <$> m1.run hst.base = m2.run (f hst.base))
    (hb : ∀ b, getBundles2 (f b) = getBundles1 b) : Prod.map id (mapShCrBase f) <$>
      (runShCrAcceptGeneric P getBundles1 isNoneResp m1 k j hdr).run hst =
      (runShCrAcceptGeneric P getBundles2 isNoneResp m2 k j hdr).run (mapShCrBase f hst) := by
  unfold runShCrAcceptGeneric; simp only [StateT.run_bind, map_bind]
  rw [← mapShCrBase_liftShCrBase f m1 m2 hst hm, bind_map_left]
  refine bind_congr (fun x => ?_)
  exact mapShCrBase_recordAcceptKemGeneric P f getBundles1 getBundles2
    isNoneResp k j hdr x.1 x.2 (hb x.2.base)
theorem mapShCrBase_applyShCrFinish {S : Setup} {B1 B2 R : Type} (f : B1 → B2)
    (sid : SessionId S) (pqspkPk ss kemCt : Bytes) (hst : ShCrState S B1) (out : R × Option B1) :
    Prod.map id (mapShCrBase f) (applyShCrFinish sid pqspkPk ss kemCt hst out) =
    applyShCrFinish sid pqspkPk ss kemCt (mapShCrBase f hst) (Prod.map id (Option.map f) out) := by
  rcases out with ⟨resp, none | b'⟩ <;> rfl
theorem mapShCrBase_runShCrInitiate4 {S : Setup} {B1 B2 R U : Type} (P : Primitives)
    (f : B1 → B2) (getPrincipals1 : B1 → List (Nat × PrincipalEntry))
    (getPrincipals2 : B2 → List (Nat × PrincipalEntry)) (noneResp : R)
    (preCheck1 : B1 → Option U) (preCheck2 : B2 → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finish1 : U → Bytes → Bytes → Bytes → Bytes → Bytes → B1 → ProbComp (R × Option B1))
    (finish2 : U → Bytes → Bytes → Bytes → Bytes → Bytes → B2 → ProbComp (R × Option B2))
    (hst : ShCrState S B1) (hPrin : getPrincipals2 (f hst.base) = getPrincipals1 hst.base)
    (hPre : preCheck2 (f hst.base) = preCheck1 hst.base)
    (hFin : ∀ uInfo, preCheck1 hst.base = some uInfo → ∀ ekASk ephASk spqrCoins ss kemCt,
        Prod.map id (Option.map f) <$> finish1 uInfo ekASk ephASk spqrCoins ss kemCt hst.base =
          finish2 uInfo ekASk ephASk spqrCoins ss kemCt (f hst.base)) :
    Prod.map id (mapShCrBase f) <$>
      (runShCrInitiate4 P getPrincipals1 noneResp preCheck1 sid bundle finish1).run hst =
      (runShCrInitiate4 P getPrincipals2 noneResp preCheck2 sid bundle finish2).run
        (mapShCrBase f hst) := by
  unfold runShCrInitiate4 StateT.run; dsimp only [mapShCrBase]; rw [hPrin, hPre]
  cases hpc : preCheck1 hst.base with
  | none => simp [Prod.map, mapShCrBase]
  | some uInfo =>
    dsimp only; simp only [map_bind]; apply bind_congr; intro ekASk
    apply bind_congr; intro kemCoins; apply bind_congr; intro ephASk
    apply bind_congr; intro spqrCoins
    cases !checkBundleSigs P (getPrincipals1 hst.base) bundle
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => simp [Prod.map, mapShCrBase]
      | some kemPair =>
        rcases kemPair with ⟨ss, kemCt⟩
        dsimp only; rw [← hFin uInfo hpc ekASk ephASk spqrCoins ss kemCt]
        simp only [Functor.map_map]; congr 1; funext out
        exact mapShCrBase_applyShCrFinish f sid bundle.pqspkB ss kemCt hst out
    · simp [Prod.map, mapShCrBase]
def finishAuthHybridG3Base (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uInfo : PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes)
    (ekASk ephASk spqrCoins ss kemCt : Bytes)
    (hst : AuthHybridState S) : ProbComp (AuthResponse × Option (AuthHybridState S)) := do
  let st := hst.base; let (uEntry, peerPrincipal?, msgPlain) := uInfo; let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  let ekAPk := P.x25519Base ekASk; let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB; let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKey, roCache') ← evalHkdfOrRo true P st.roCache secrets; let ephAPk := P.x25519Base ephASk
  let dhRatchet := P.x25519 ephASk bundle.spkB
  let ((rk1, ck1_0), rootRoCache') ← evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet
  let mkSeed := P.chainKdfSeed ck1_0; let ck1_1 := P.chainKdfNext ck1_0
  match P.spqrInitSend drKey.pqrKey spqrCoins with
  | none => return (.noneResp, none)
  | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
    let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
    let (resp, hst') := finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer
      bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
      spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache' hst
    return (resp, some hst')
def clearHybridWon {S : Setup} (h : AuthHybridState S) : AuthHybridState S :=
  { h with base := { h.base with hasWonAuth := false } }
@[simp]
theorem clearHybridWon_eq_self {S : Setup} (h : AuthHybridState S)
    (hWon : h.base.hasWonAuth = false) : clearHybridWon h = h := by
  cases h; rename_i base _ _ _; cases base; simp [clearHybridWon] at hWon ⊢; exact hWon
def pqxdhAuthHybridKoskUnfrozenImpl (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthHybridState S) ProbComp)
  | .sendOPK u i bundle m0 m1 => do
    if bundle.opkB?.isNone then return .noneResp
    runAuthHybridSendKosk .g3 true S P (.sendOPK u i) u bundle m0 m1
  | .sendNoOPK u i bundle m0 m1 => do
    if bundle.opkB?.isSome then return .noneResp
    runAuthHybridSendKosk .g3 true S P (.sendNoOPK u i) u bundle m0 m1
  | q_other =>
    StateT.mk (fun h =>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q_other).run (clearHybridWon h))
theorem pqxdhAuthHybridKoskImpl_g3_of_hasWonAuth_false (S : Setup) (P : Primitives)
    (q : AuthQuery S) (h : AuthHybridState S) (hWon : h.base.hasWonAuth = false) :
    (pqxdhAuthHybridKoskImpl .g3 true true S P q).run h =
    (pqxdhAuthHybridKoskUnfrozenImpl S P q).run h := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridKoskImpl pqxdhAuthHybridKoskUnfrozenImpl
    simp [StateT.run_bind, StateT.run_get, pure_bind, hWon]
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridKoskImpl pqxdhAuthHybridKoskUnfrozenImpl
    simp [StateT.run_bind, StateT.run_get, pure_bind, hWon]
  | _ =>
    change (pqxdhAuthHybridKoskImpl .g3 true true S P _).run h =
      (pqxdhAuthHybridKoskImpl .g3 true true S P _).run (clearHybridWon h)
    rw [clearHybridWon_eq_self h hWon]
theorem pqxdhAuthHybridKoskImpl_g3_eq_freeze (S : Setup) (P : Primitives)
    (q : AuthQuery S) (h : AuthHybridState S) :
    (pqxdhAuthHybridKoskImpl .g3 true true S P q).run h =
    (freezeImpl (fun h : AuthHybridState S => h.base.hasWonAuth)
      (fun _ => .noneResp) (pqxdhAuthHybridKoskUnfrozenImpl S P) q).run h := by
  simp only [freezeImpl, StateT.run_bind, StateT.run_get, pure_bind]
  cases hWon : h.base.hasWonAuth
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact pqxdhAuthHybridKoskImpl_g3_of_hasWonAuth_false S P q h hWon
  · unfold pqxdhAuthHybridKoskImpl; simp [StateT.run_bind, StateT.run_get, pure_bind, hWon]
noncomputable def runAuthKoskG3Unfrozen (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthHybridState S) := do
  let secb ← $ᵗ Bool; let initSt := AuthHybridState.empty S secb
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
    pqxdhAuthHybridKoskUnfrozenImpl S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt; return (secb, b', finalSt)
def pqxdhAuthHybridShCrImpl (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthHybridShCrState S) ProbComp)
  | .genSPK u j => liftShCrBase (pqxdhAuthHybridKoskUnfrozenImpl S P (.genSPK u j))
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure .noneResp
    else runShCrInitiate4 P (fun h => h.base.principals) AuthResponse.noneResp
      (fun h => preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1 h.base) (.sendOPK u i) bundle
      (finishAuthHybridG3Base S P (.sendOPK u i) bundle m0 m1)
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure .noneResp
    else runShCrInitiate4 P (fun h => h.base.principals) AuthResponse.noneResp
      (fun h => preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1 h.base) (.sendNoOPK u i) bundle
      (finishAuthHybridG3Base S P (.sendNoOPK u i) bundle m0 m1)
  | .recvOPK k j o msg =>
    runShCrAcceptGeneric P (fun h => h.base.spkBundles) isNoneAuthShCrResp
      (pqxdhAuthHybridKoskUnfrozenImpl S P (.recvOPK k j o msg)) k j msg.hdr
  | .recvNoOPK k j l msg =>
    runShCrAcceptGeneric P (fun h => h.base.spkBundles) isNoneAuthShCrResp
      (pqxdhAuthHybridKoskUnfrozenImpl S P (.recvNoOPK k j l msg)) k j msg.hdr
  | q_other => liftShCrBase (pqxdhAuthHybridKoskUnfrozenImpl S P q_other)
theorem map_base_runAuthHybridShCrSend (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridShCrState S) : Prod.map id ShCrState.base <$>
      (runShCrInitiate4 P (fun h : AuthHybridState S => h.base.principals) AuthResponse.noneResp
        (fun h => preCheckAuthSim S P sid u bundle m0 m1 h.base) sid bundle
        (finishAuthHybridG3Base S P sid bundle m0 m1)).run hst =
    (runAuthHybridSendKosk .g3 true S P sid u bundle m0 m1).run hst.base := by
  rw [show (runShCrInitiate4 P (fun h : AuthHybridState S => h.base.principals)
        AuthResponse.noneResp (fun h => preCheckAuthSim S P sid u bundle m0 m1 h.base) sid bundle
        (finishAuthHybridG3Base S P sid bundle m0 m1)).run hst =
      runShCrInitiate4 P (fun h : AuthHybridState S => h.base.principals) AuthResponse.noneResp
        (fun h => preCheckAuthSim S P sid u bundle m0 m1 h.base) sid bundle
        (finishAuthHybridG3Base S P sid bundle m0 m1) hst from rfl]
  unfold runShCrInitiate4 preCheckAuthSim checkBundleSigs finishAuthHybridG3Base
    finishAuthHybridSend applyShCrFinish runAuthHybridSendKosk
  dsimp only [AuthHybridStage.idealFreshAead, AuthHybridStage.idealDrKey,
    AuthHybridStage.idealRk, AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
    StateT.run_get, pure_bind]
  cases m0.length != m1.length; case true => simp [StateT.run_pure, Prod.map]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hst.base.base.usedSendSessions.contains sid; case true => simp [StateT.run_pure, Prod.map]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hst.base.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => simp [StateT.run_pure, Prod.map]
  | some p =>
    rcases p with ⟨_, uEntry⟩; dsimp only
    cases (!match findHonestPrincipal P hst.base.base.principals bundle.ikB with
           | some (_, pEntry) => !pEntry.corrupted | none => false) && (m0 != m1)
    case true => simp [StateT.run_pure, Prod.map]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases (!koskBundleOk P hst.base.base.principals hst.base.base.spkBundles
      hst.base.base.opkEntries hst.base.base.advKeys bundle)
    case true => simp [StateT.run_pure, Prod.map]
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, map_bind, bind_assoc, pure_bind]
    apply bind_congr; intro ekASk; apply bind_congr; intro kemCoins
    apply bind_congr; intro ephASk; apply bind_congr; intro spqrCoins
    cases !(P.sigVerify (resolveSigPk P hst.base.base.principals bundle.ikB)
              (encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (resolveSigPk P hst.base.base.principals bundle.ikB)
              (encodeKEM bundle.pqspkB) bundle.pqspkSig)
    case true => simp [StateT.run_pure, Prod.map]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases P.kemEncaps bundle.pqspkB kemCoins with
    | none => simp [StateT.run_pure, Prod.map]
    | some kemPair =>
      rcases kemPair with ⟨ss, kemCt⟩; dsimp only
      simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind,
        bind_assoc, pure_bind]
      apply bind_congr; rintro ⟨drKey, roCache'⟩
      apply bind_congr; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩; dsimp only
      cases P.spqrInitSend drKey.pqrKey spqrCoins with
      | none => simp [StateT.run_pure, Prod.map]
      | some spqrTriple =>
        rcases spqrTriple with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only
        cases (findHonestPrincipal P hst.base.base.principals bundle.ikB).isSome <;>
          (simp only [StateT.run_bind, StateT.run_set, Prod.map, map_pure, pure_bind]; rfl)
theorem map_base_pqxdhAuthHybridShCrImpl (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridShCrState S) : Prod.map id ShCrState.base <$>
      (pqxdhAuthHybridShCrImpl S P q).run hst =
    (pqxdhAuthHybridKoskUnfrozenImpl S P q).run hst.base := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridShCrImpl pqxdhAuthHybridKoskUnfrozenImpl; dsimp only
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact map_base_runAuthHybridShCrSend S P (.sendOPK u i) u bundle m0 m1 hst
    · simp [StateT.run_pure, Prod.map]
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridShCrImpl pqxdhAuthHybridKoskUnfrozenImpl; dsimp only
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact map_base_runAuthHybridShCrSend S P (.sendNoOPK u i) u bundle m0 m1 hst
    · simp [StateT.run_pure, Prod.map]
  | recvOPK k j o msg =>
    exact map_base_runShCrAcceptGeneric P (fun h : AuthHybridState S => h.base.spkBundles)
      isNoneAuthShCrResp (pqxdhAuthHybridKoskUnfrozenImpl S P (.recvOPK k j o msg)) k j msg.hdr hst
  | recvNoOPK k j l msg =>
    exact map_base_runShCrAcceptGeneric P (fun h : AuthHybridState S => h.base.spkBundles)
      isNoneAuthShCrResp
      (pqxdhAuthHybridKoskUnfrozenImpl S P (.recvNoOPK k j l msg)) k j msg.hdr hst
  | genSPK _ _ | initPrin _ | corruptIK _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
  | revealDhSecrets | registerKey _ =>
    exact map_base_liftShCrBase (pqxdhAuthHybridKoskUnfrozenImpl S P _) hst
theorem map_base_fullAuthHybridShCrImpl (S : Setup) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridShCrState S) :
    Prod.map id ShCrState.base <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridShCrState S) ProbComp) +
        pqxdhAuthHybridShCrImpl S P) q).run hst =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
      pqxdhAuthHybridKoskUnfrozenImpl S P) q).run hst.base := by
  cases q with
  | inl uq => simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr kq => exact map_base_pqxdhAuthHybridShCrImpl S P kq hst
def eraseOpkAuthSessions {S : Setup} : AuthState S → AuthState S := mapAuthSessions (fun s =>
    let (s', o', p') := eraseOpkTriples (s.spkHonest, s.opkHonest, s.pqspkHonest)
    { s with spkHonest := s', opkHonest := o', pqspkHonest := p' })
def projHybridToSim (S : Setup) (P : Primitives) (h : AuthHybridState S) : AuthState S :=
  projAuthSim S P (eraseOpkAuthSessions h.base)
theorem map_projHybridToSim_pqxdhAuthHybridKoskImpl_g3_clear (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (h : AuthHybridState S) : Prod.map id (projHybridToSim S P) <$>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q).run (clearHybridWon h) =
    (pqxdhAuthSimImpl S P q).run (projHybridToSim S P h) := by
  have h1 : Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q).run (clearHybridWon h) =
    (pqxdhAuthWithProvImpl S P (checkBundleProvenanceExact P) q).run (clearHybridWon h).base := by
    rw [map_base_pqxdhAuthHybridKoskImpl_g3 S P hP q (clearHybridWon h)]; rfl
  have h2 : Prod.map id eraseOpkAuthSessions <$>
      (pqxdhAuthWithProvImpl S P (checkBundleProvenanceExact P) q).run (clearHybridWon h).base =
    (pqxdhAuthWithProvImpl S P (checkBundleProvenanceNoOpk P) q).run
      (eraseOpkAuthSessions (clearHybridWon h).base) :=
    (pqxdhAuthWithProvImpl_commutes_mapAuthSessions S P eraseOpkTriples
      (checkBundleProvenanceNoOpk P) (checkBundleProvenanceExact P)
      (checkBundleProvenanceNoOpk_eq_eraseOpk_exact P) q (clearHybridWon h).base).symm
  have h3 : Prod.map id (projAuthSim S P) <$>
      (pqxdhAuthWithProvImpl S P (checkBundleProvenanceNoOpk P) q).run
        (eraseOpkAuthSessions (clearHybridWon h).base) =
    (pqxdhAuthSimImpl S P q).run (projHybridToSim S P h) :=
    (pqxdhAuthSimImpl_commutes_projAuthSim S P hP q
      (eraseOpkAuthSessions (clearHybridWon h).base)).symm
  calc Prod.map id (projHybridToSim S P) <$>
        (pqxdhAuthHybridKoskImpl .g3 true true S P q).run (clearHybridWon h)
      = Prod.map id (projAuthSim S P) <$> (Prod.map id eraseOpkAuthSessions <$>
            (Prod.map id AuthHybridState.base <$>
              (pqxdhAuthHybridKoskImpl .g3 true true S P q).run (clearHybridWon h))) := by
        simp only [Functor.map_map]; rfl
    _ = (pqxdhAuthSimImpl S P q).run (projHybridToSim S P h) := by
        rw [h1, h2, h3]
theorem preCheckAuthSim_peerPrincipal (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) (uInfo : PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes)
    (h : preCheckAuthSim S P sid u bundle m0 m1 st = some uInfo) :
    uInfo.2.1 = findHonestPrincipal P st.principals bundle.ikB := by
  unfold preCheckAuthSim at h; revert h
  cases m0.length != m1.length; case true => intro h; cases h
  cases st.usedSendSessions.contains sid; case true => intro h; cases h
  cases st.principals.find? (fun (idx, _) => idx == u.val) with
  | none => intro h; cases h
  | some p =>
    dsimp only
    cases (!match findHonestPrincipal P st.principals bundle.ikB with
           | some (_, pEntry) => !pEntry.corrupted | none => false) && (m0 != m1)
    case true => intro h; cases h
    cases !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle
    case true => intro h; cases h
    simp only [Bool.false_eq_true, ↓reduceIte]; intro h; injection h with h'; subst h'; rfl
theorem map_projHybridToSim_finishAuthHybridG3Base (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uInfo : PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes)
    (ekASk ephASk spqrCoins ss kemCt : Bytes) (h : AuthHybridState S)
    (hPeer : uInfo.2.1 = findHonestPrincipal P h.base.principals bundle.ikB) :
    Prod.map id (Option.map (projHybridToSim S P)) <$>
      finishAuthHybridG3Base S P sid bundle m0 m1 uInfo ekASk ephASk spqrCoins ss kemCt h =
    finishAuthSimBase S P sid bundle m0 m1 uInfo ekASk ephASk spqrCoins ss kemCt
      (projHybridToSim S P h) := by
  rcases uInfo with ⟨uEntry, peerPrincipal?, msgPlain⟩; dsimp only at hPeer; subst hPeer
  unfold finishAuthHybridG3Base finishAuthSimBase finishAuthHybridSend
    projHybridToSim projAuthSim eraseOpkAuthSessions mapAuthSessions eraseOpkTriples
    checkBundleProvenanceExact
  dsimp only; simp only [map_bind]; apply bind_congr; rintro ⟨drKey, roCache'⟩
  apply bind_congr; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩; dsimp only
  cases P.spqrInitSend drKey.pqrKey spqrCoins with
  | none => simp [Prod.map]
  | some spqrTriple =>
    rcases spqrTriple with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
    dsimp only; rw [map_pure]; congr 1; dsimp only [Prod.map, Option.map]; congr 1; congr 1
    cases findHonestPrincipal P h.base.principals bundle.ikB <;> rfl
theorem mapShCrBase_pqxdhAuthHybridShCrImpl (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (hst : AuthHybridShCrState S) :
    Prod.map id (mapShCrBase (projHybridToSim S P)) <$> (pqxdhAuthHybridShCrImpl S P q).run hst =
    (pqxdhAuthShCrSimImpl false S P q).run (mapShCrBase (projHybridToSim S P) hst) := by
  cases q with
  | genSPK u j =>
    dsimp only [pqxdhAuthHybridShCrImpl, pqxdhAuthShCrSimImpl, runAuthShCrGenSPK]
    rw [runShCrGenSPKGeneric_false_run]; exact mapShCrBase_liftShCrBase (projHybridToSim S P)
      (pqxdhAuthHybridKoskUnfrozenImpl S P (.genSPK u j)) (pqxdhAuthSimImpl S P (.genSPK u j)) hst
      (map_projHybridToSim_pqxdhAuthHybridKoskImpl_g3_clear S P hP (.genSPK u j) hst.base)
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridShCrImpl pqxdhAuthShCrSimImpl; dsimp only
    cases bundle.opkB?.isNone; case true => simp [StateT.run_pure, Prod.map]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine mapShCrBase_runShCrInitiate4 P (projHybridToSim S P)
      (fun h => h.base.principals) AuthState.principals AuthResponse.noneResp
      (fun h => preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1 h.base)
      (preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1) (.sendOPK u i) bundle
      (finishAuthHybridG3Base S P (.sendOPK u i) bundle m0 m1)
      (finishAuthSimBase S P (.sendOPK u i) bundle m0 m1) hst rfl ?_ ?_
    · unfold preCheckAuthSim projHybridToSim projAuthSim eraseOpkAuthSessions mapAuthSessions
      dsimp only; rw [koskBundleOk_map_cache]
    · exact fun uInfo hpc ek eph spqr ss ct => map_projHybridToSim_finishAuthHybridG3Base S P
        (.sendOPK u i) bundle m0 m1 uInfo ek eph spqr ss ct hst.base
        (preCheckAuthSim_peerPrincipal S P (.sendOPK u i) u bundle m0 m1 hst.base.base uInfo hpc)
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridShCrImpl pqxdhAuthShCrSimImpl; dsimp only
    cases bundle.opkB?.isSome; case true => simp [StateT.run_pure, Prod.map]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine mapShCrBase_runShCrInitiate4 P (projHybridToSim S P)
      (fun h => h.base.principals) AuthState.principals AuthResponse.noneResp
      (fun h => preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1 h.base)
      (preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1) (.sendNoOPK u i) bundle
      (finishAuthHybridG3Base S P (.sendNoOPK u i) bundle m0 m1)
      (finishAuthSimBase S P (.sendNoOPK u i) bundle m0 m1) hst rfl ?_ ?_
    · unfold preCheckAuthSim projHybridToSim projAuthSim eraseOpkAuthSessions mapAuthSessions
      dsimp only; rw [koskBundleOk_map_cache]
    · exact fun uInfo hpc ek eph spqr ss ct => map_projHybridToSim_finishAuthHybridG3Base S P
        (.sendNoOPK u i) bundle m0 m1 uInfo ek eph spqr ss ct hst.base
        (preCheckAuthSim_peerPrincipal S P (.sendNoOPK u i) u bundle m0 m1 hst.base.base uInfo hpc)
  | recvOPK k j o msg =>
    exact mapShCrBase_runShCrAcceptGeneric P (projHybridToSim S P)
      (fun h => h.base.spkBundles) AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthHybridKoskUnfrozenImpl S P (.recvOPK k j o msg))
      (pqxdhAuthSimImpl S P (.recvOPK k j o msg)) k j msg.hdr hst
      (map_projHybridToSim_pqxdhAuthHybridKoskImpl_g3_clear S P hP (.recvOPK k j o msg) hst.base)
      (fun _ => rfl)
  | recvNoOPK k j l msg =>
    exact mapShCrBase_runShCrAcceptGeneric P (projHybridToSim S P)
      (fun h => h.base.spkBundles) AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthHybridKoskUnfrozenImpl S P (.recvNoOPK k j l msg))
      (pqxdhAuthSimImpl S P (.recvNoOPK k j l msg)) k j msg.hdr hst
      (map_projHybridToSim_pqxdhAuthHybridKoskImpl_g3_clear S P hP (.recvNoOPK k j l msg) hst.base)
      (fun _ => rfl)
  | initPrin _ | corruptIK _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
  | revealDhSecrets | registerKey _ =>
    exact mapShCrBase_liftShCrBase (projHybridToSim S P) _ _ hst
      (map_projHybridToSim_pqxdhAuthHybridKoskImpl_g3_clear S P hP _ hst.base)
theorem mapShCrBase_fullAuthHybridShCrImpl (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridShCrState S) :
    Prod.map id (mapShCrBase (projHybridToSim S P)) <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridShCrState S) ProbComp) +
        pqxdhAuthHybridShCrImpl S P) q).run hst =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthShCrState S) ProbComp) +
      pqxdhAuthShCrSimImpl false S P) q).run (mapShCrBase (projHybridToSim S P) hst) := by
  cases q with
  | inl uq => simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr kq => exact mapShCrBase_pqxdhAuthHybridShCrImpl S P hP kq hst
noncomputable def runAuthHybridShCr (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthHybridShCrState S) := do
  let secb ← $ᵗ Bool; let initSt : AuthHybridShCrState S := { base := AuthHybridState.empty S secb }
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridShCrState S) ProbComp) +
    pqxdhAuthHybridShCrImpl S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt; return (secb, b', finalHst)
theorem runAuthHybridShCr_map_base (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    (fun (secb, b', finalHst) => (secb, b', finalHst.base)) <$> runAuthHybridShCr S P A =
      runAuthKoskG3Unfrozen S P A := by
  unfold runAuthHybridShCr runAuthKoskG3Unfrozen; simp only [map_bind, map_pure]
  refine bind_congr (fun secb => ?_)
  have hsim := map_proj_simulateQ ShCrState.base
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridShCrState S) ProbComp) +
      pqxdhAuthHybridShCrImpl S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
      pqxdhAuthHybridKoskUnfrozenImpl S P)
    (map_base_fullAuthHybridShCrImpl S P) A.run ({ base := AuthHybridState.empty S secb })
  rw [← hsim, bind_map_left]; rfl
theorem runAuthHybridShCr_map_shcr (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    (fun (secb, b', finalHst) => (secb, b', mapShCrBase (projHybridToSim S P) finalHst)) <$>
      runAuthHybridShCr S P A =
    runAuthShCrSim S P A := by
  unfold runAuthHybridShCr runAuthShCrSim; simp only [map_bind, map_pure]
  refine bind_congr (fun secb => ?_)
  have hsim := map_proj_simulateQ (mapShCrBase (projHybridToSim S P))
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridShCrState S) ProbComp) +
      pqxdhAuthHybridShCrImpl S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthShCrState S) ProbComp) +
      pqxdhAuthShCrSimImpl false S P)
    (mapShCrBase_fullAuthHybridShCrImpl S P hP) A.run ({ base := AuthHybridState.empty S secb })
  dsimp only [mapShCrBase, projHybridToSim, AuthHybridState.empty,
    eraseOpkAuthSessions, mapAuthSessions_empty, projAuthSim_empty] at hsim
  rw [← hsim, bind_map_left]; rfl
/-! ## KEM record synchronization invariant -/
def dropSendIdx {S : Setup} (r : _root_.Proofs.SignalPqxdh.Security.InitKemRecord S) :
    _root_.SignalPqxdh.Security.InitKemRecord S :=
  { sid := r.sid, pqspkPk := r.pqspkPk, kemCt := r.kemCt, kemSs := r.kemSs }
def dropBIdx (r : _root_.Proofs.SignalPqxdh.Security.RecvKemRecord) :
    _root_.SignalPqxdh.Security.RecvKemRecord :=
  { k := r.k, j := r.j, pqspkPk := r.pqspkPk, pqspkSk := r.pqspkSk,
    kemCt := r.kemCt, kemSs := r.kemSs }
theorem isKemShCrPair_eq_of_drop {S : Setup} (P : Primitives)
    (i' : _root_.Proofs.SignalPqxdh.Security.InitKemRecord S)
    (r' : _root_.Proofs.SignalPqxdh.Security.RecvKemRecord) :
    (P.kemDecaps (dropBIdx r').pqspkSk (dropBIdx r').kemCt == some (dropSendIdx i').kemSs &&
     ((dropBIdx r').kemCt != (dropSendIdx i').kemCt ||
      (dropSendIdx i').pqspkPk != (dropBIdx r').pqspkPk)) =
    isKemShCrPair P i' r' := by
  unfold dropSendIdx dropBIdx isKemShCrPair; dsimp only; rw [Bool.eq_iff_iff]; simp
def ValidHybridShCr (S : Setup) (hst : AuthHybridShCrState S) : Prop := (∀ i ∈ hst.base.initKemRecs,
    ∃ i' ∈ hst.initKemRecs, dropSendIdx i' = i ∧ i'.sendIdx < hst.sendCount) ∧
  (∀ r ∈ hst.base.recvKemRecs, ∃ r' ∈ hst.recvKemRecs, dropBIdx r' = r ∧ r'.bIdx < S.N_spk_tot)
theorem mem_support_finishAuthHybridG3Base (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uInfo : PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes)
    (ekASk ephASk spqrCoins ss kemCt : Bytes) (h : AuthHybridState S)
    (out : AuthResponse × Option (AuthHybridState S))
    (hout : out ∈ support
      (finishAuthHybridG3Base S P sid bundle m0 m1 uInfo ekASk ephASk spqrCoins ss kemCt h)) :
    out.2 = none ∨ ∃ base', out.2 = some base' ∧
      base'.initKemRecs =
        { sid := sid, pqspkPk := bundle.pqspkB, kemCt := kemCt, kemSs := ss } :: h.initKemRecs ∧
      base'.recvKemRecs = h.recvKemRecs := by
  rcases uInfo with ⟨uEntry, peerPrincipal?, msgPlain⟩
  unfold finishAuthHybridG3Base finishAuthHybridSend at hout; dsimp only at hout
  simp only [MonadAttach.mem_support_bind] at hout
  rcases hout with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hout⟩
  dsimp only at hout; revert hout
  cases P.spqrInitSend drKey.pqrKey spqrCoins
  · intro hout
    simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout; exact Or.inl rfl
  · rename_i spqrTriple; rcases spqrTriple with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
    intro hout; simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout
    exact Or.inr ⟨_, rfl, rfl, rfl⟩
def RecvHybridStep {S : Setup} (P : Primitives) (k : Fin S.N_id) (j : Fin S.N_recv)
    (hdr : HandshakeHdr) (h base' : AuthHybridState S) : Prop :=
  base'.initKemRecs = h.initKemRecs ∧ base'.base.spkBundles = h.base.spkBundles ∧
  (base'.recvKemRecs = h.recvKemRecs ∨ ∃ idxPair bEntry ss,
      h.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) = some (idxPair, bEntry) ∧
      P.kemDecaps bEntry.pqspkSk hdr.kemCt = some ss ∧
      base'.recvKemRecs =
        { k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
          pqspkSk := bEntry.pqspkSk, kemCt := hdr.kemCt, kemSs := ss } :: h.recvKemRecs)
theorem SatisfiesAt.set_bind {St R : Type} (Q : St → Prop) (st st' : St)
    {f : PUnit → StateT St ProbComp R} (hf : SatisfiesAt Q st' (f PUnit.unit)) :
    SatisfiesAt Q st (set st' >>= f) := by
  intro x hx; simp only [StateT.run_bind, StateT.run_set, pure_bind] at hx; exact hf x hx
theorem pqxdhAuthHybridKoskImpl_recvOPK_step (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (h : AuthHybridState S) : SatisfiesAt (RecvHybridStep P k j msg.hdr h) h
      (pqxdhAuthHybridKoskUnfrozenImpl S P (.recvOPK k j o msg)) := by
  have h0 : RecvHybridStep P k j msg.hdr h (clearHybridWon h) := ⟨rfl, rfl, Or.inl rfl⟩
  change SatisfiesAt (RecvHybridStep P k j msg.hdr h) (clearHybridWon h)
    (pqxdhAuthHybridKoskImpl .g3 true true S P (.recvOPK k j o msg))
  unfold pqxdhAuthHybridKoskImpl; apply SatisfiesAt.get_bind; dsimp only [clearHybridWon]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  cases h.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact SatisfiesAt.pure _ _ _ h0
  | some kp =>
    rcases kp with ⟨_, kEntry⟩; dsimp only
    cases hfind : h.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact SatisfiesAt.pure _ _ _ h0
    | some bp =>
      rcases bp with ⟨idxPair, bEntry⟩; dsimp only
      cases h.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
      | none => exact SatisfiesAt.pure _ _ _ h0
      | some op =>
        rcases op with ⟨_, oEntry⟩; dsimp only; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
        apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
        cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => exact SatisfiesAt.pure _ _ _ h0
        | some ss =>
          dsimp only; apply SatisfiesAt.set_bind; apply SatisfiesAt.liftM_bind; intro schedOut
          cases schedOut with
          | none =>
            exact SatisfiesAt.pure _ _ _ ⟨rfl, rfl, Or.inr ⟨idxPair, bEntry, ss, hfind, hdec, rfl⟩⟩
          | some tup =>
            rcases tup with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
            cases findHonestPrincipal P h.base.principals msg.hdr.ikAPk with
            | none =>
              apply SatisfiesAt.set_bind
              exact SatisfiesAt.pure _ _ _
                ⟨rfl, rfl, Or.inr ⟨idxPair, bEntry, ss, hfind, hdec, rfl⟩⟩
            | some sp =>
              rcases sp with ⟨_, senderEntry⟩; dsimp only
              cases !senderEntry.corrupted <;>
                (simp only [Bool.false_eq_true, ↓reduceIte]; apply SatisfiesAt.set_bind
                 exact SatisfiesAt.pure _ _ _
                   ⟨rfl, rfl, Or.inr ⟨idxPair, bEntry, ss, hfind, hdec, rfl⟩⟩)
theorem pqxdhAuthHybridKoskImpl_recvNoOPK_step (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (h : AuthHybridState S) : SatisfiesAt (RecvHybridStep P k j msg.hdr h) h
      (pqxdhAuthHybridKoskUnfrozenImpl S P (.recvNoOPK k j l msg)) := by
  have h0 : RecvHybridStep P k j msg.hdr h (clearHybridWon h) := ⟨rfl, rfl, Or.inl rfl⟩
  change SatisfiesAt (RecvHybridStep P k j msg.hdr h) (clearHybridWon h)
    (pqxdhAuthHybridKoskImpl .g3 true true S P (.recvNoOPK k j l msg))
  unfold pqxdhAuthHybridKoskImpl; apply SatisfiesAt.get_bind; dsimp only [clearHybridWon]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  cases h.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact SatisfiesAt.pure _ _ _ h0
  | some kp =>
    rcases kp with ⟨_, kEntry⟩; dsimp only
    cases hfind : h.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact SatisfiesAt.pure _ _ _ h0
    | some bp =>
      rcases bp with ⟨idxPair, bEntry⟩; dsimp only; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
      cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
      | none => exact SatisfiesAt.pure _ _ _ h0
      | some ss =>
        dsimp only; apply SatisfiesAt.set_bind; apply SatisfiesAt.liftM_bind; intro schedOut
        cases schedOut with
        | none =>
          exact SatisfiesAt.pure _ _ _ ⟨rfl, rfl, Or.inr ⟨idxPair, bEntry, ss, hfind, hdec, rfl⟩⟩
        | some tup =>
          rcases tup with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
          cases findHonestPrincipal P h.base.principals msg.hdr.ikAPk with
          | none =>
            apply SatisfiesAt.set_bind
            exact SatisfiesAt.pure _ _ _ ⟨rfl, rfl, Or.inr ⟨idxPair, bEntry, ss, hfind, hdec, rfl⟩⟩
          | some sp =>
            rcases sp with ⟨_, senderEntry⟩; dsimp only
            cases !senderEntry.corrupted <;>
              (simp only [Bool.false_eq_true, ↓reduceIte]; apply SatisfiesAt.set_bind
               exact SatisfiesAt.pure _ _ _
                 ⟨rfl, rfl, Or.inr ⟨idxPair, bEntry, ss, hfind, hdec, rfl⟩⟩)
theorem runShCrAcceptGeneric_validHybridShCr {S : Setup} (P : Primitives)
    (baseAccept : StateT (AuthHybridState S) ProbComp AuthResponse)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (hst : AuthHybridShCrState S) (hV : ValidHybridShCr S hst)
    (hBase : SatisfiesAt (RecvHybridStep P k j hdr hst.base) hst.base baseAccept)
    (x : AuthResponse × AuthHybridShCrState S)
    (hx : x ∈ support ((runShCrAcceptGeneric P (fun h : AuthHybridState S => h.base.spkBundles)
      isNoneAuthShCrResp baseAccept k j hdr).run hst)) :
    ValidHybridShCr S x.2 ∧ x.2.sendCount = hst.sendCount := by
  unfold runShCrAcceptGeneric at hx; simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨y, hy, hx⟩
  simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨z, hz, hy⟩; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
  rcases hBase z hz with ⟨hInitEq, hBundlesEq, hRecvCases⟩
  rcases hRecvCases with hRecvEq | ⟨idxPair, bEntry, ss, hfind, hdec, hRecvCons⟩
  · rcases mem_support_recordAcceptKemGeneric P (fun h : AuthHybridState S => h.base.spkBundles)
        isNoneAuthShCrResp k j hdr z.1 { hst with base := z.2 } x hx with
      rfl | ⟨_, _, _, _, _, rfl⟩
    · refine ⟨⟨?_, ?_⟩, rfl⟩
      · intro i hi; rw [hInitEq] at hi; exact hV.1 i hi
      · intro r hr; rw [hRecvEq] at hr; exact hV.2 r hr
    · refine ⟨⟨?_, ?_⟩, rfl⟩
      · intro i hi; dsimp only at hi; rw [hInitEq] at hi; exact hV.1 i hi
      · intro r hr; dsimp only at hr; rw [hRecvEq] at hr
        rcases hV.2 r hr with ⟨r', hr', hdrop, hlt⟩
        exact ⟨r', List.mem_cons_of_mem _ hr', hdrop, hlt⟩
  · unfold recordAcceptKemGeneric isNoneAuthShCrResp StateT.run at hx
    simp only [Bool.false_eq_true, ↓reduceIte] at hx; rw [hBundlesEq, hfind] at hx; dsimp only at hx
    rw [hdec] at hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · intro i hi; dsimp only at hi; rw [hInitEq] at hi; exact hV.1 i hi
    · intro r hr; dsimp only at hr; rw [hRecvCons] at hr; simp only [List.mem_cons] at hr
      rcases hr with rfl | hr_old
      · exact ⟨{ bIdx := spkBundleFlatIdx S k j, k := k.val, j := j.val,
                 pqspkPk := bEntry.pqspkPk, pqspkSk := bEntry.pqspkSk,
                 kemCt := hdr.kemCt, kemSs := ss },
               List.mem_cons_self, rfl, bundleSlotIndex_lt S k j⟩
      · rcases hV.2 r hr_old with ⟨r', hr', hdrop, hlt⟩
        exact ⟨r', List.mem_cons_of_mem _ hr', hdrop, hlt⟩
theorem runShCrInitiate4_validHybridShCr {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridShCrState S) (hV : ValidHybridShCr S hst)
    (x : AuthResponse × AuthHybridShCrState S)
    (hx : x ∈ support ((runShCrInitiate4 P (fun h : AuthHybridState S => h.base.principals)
      AuthResponse.noneResp (fun h => preCheckAuthSim S P sid u bundle m0 m1 h.base)
      sid bundle (finishAuthHybridG3Base S P sid bundle m0 m1)).run hst)) :
    ValidHybridShCr S x.2 ∧ x.2.sendCount ≤ hst.sendCount + 1 := by
  rcases mem_support_runShCrInitiate4 P (fun h : AuthHybridState S => h.base.principals)
      AuthResponse.noneResp (fun h => preCheckAuthSim S P sid u bundle m0 m1 h.base)
      sid bundle (finishAuthHybridG3Base S P sid bundle m0 m1) hst x hx with
    ⟨rfl, _⟩ | ⟨uInfo, _, _, rfl | ⟨ekASk, ephASk, spqrCoins, ss, kemCt, out, hout, rfl⟩⟩
  · exact ⟨hV, Nat.le_succ _⟩
  · refine ⟨⟨?_, hV.2⟩, le_rfl⟩
    intro i hi; rcases hV.1 i hi with ⟨i', hi', hdrop, hlt⟩
    exact ⟨i', hi', hdrop, Nat.lt_succ_of_lt hlt⟩
  · rcases mem_support_finishAuthHybridG3Base S P sid bundle m0 m1 uInfo
        ekASk ephASk spqrCoins ss kemCt hst.base out hout with
      hnone | ⟨base', hsome, hInitCons, hRecvEq⟩
    · unfold applyShCrFinish; rw [hnone]; dsimp only; refine ⟨⟨?_, hV.2⟩, le_rfl⟩
      intro i hi; rcases hV.1 i hi with ⟨i', hi', hdrop, hlt⟩
      exact ⟨i', hi', hdrop, Nat.lt_succ_of_lt hlt⟩
    · unfold applyShCrFinish; rw [hsome]; dsimp only; refine ⟨⟨?_, ?_⟩, le_rfl⟩
      · intro i hi; dsimp only at hi; rw [hInitCons] at hi; simp only [List.mem_cons] at hi
        rcases hi with rfl | hi_old
        · exact ⟨{ sendIdx := hst.sendCount, sid := sid, pqspkPk := bundle.pqspkB,
                   kemCt := kemCt, kemSs := ss },
                 List.mem_cons_self, rfl, Nat.lt_succ_self _⟩
        · rcases hV.1 i hi_old with ⟨i', hi', hdrop, hlt⟩
          exact ⟨i', List.mem_cons_of_mem _ hi', hdrop, Nat.lt_succ_of_lt hlt⟩
      · intro r hr; dsimp only at hr; rw [hRecvEq] at hr; exact hV.2 r hr
theorem liftShCrBase_liftAuthBase_validHybridShCr {S : Setup}
    (m : StateT (AuthState S) ProbComp AuthResponse) (hst : AuthHybridShCrState S)
    (hV : ValidHybridShCr S hst) (x : AuthResponse × AuthHybridShCrState S)
    (hx : x ∈ support ((liftShCrBase (StateT.mk (fun h : AuthHybridState S =>
      (do
        let hst ← get; let st := hst.base
        if true && st.hasWonAuth then return AuthResponse.noneResp
        liftAuthBase m : StateT (AuthHybridState S) ProbComp AuthResponse).run
          (clearHybridWon h)))).run hst)) :
    ValidHybridShCr S x.2 ∧ x.2.sendCount = hst.sendCount := by
  dsimp only [liftShCrBase, StateT.run, StateT.mk] at hx
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨y, hy, rfl⟩; change y ∈ support ((do
    let hst ← get; let st := hst.base
    if true && st.hasWonAuth then return AuthResponse.noneResp
    liftAuthBase m : StateT (AuthHybridState S) ProbComp AuthResponse).run
      (clearHybridWon hst.base)) at hy
  simp only [clearHybridWon, StateT.run_bind, StateT.run_get, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, pure_bind] at hy
  unfold liftAuthBase at hy
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, pure_bind, bind_assoc,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
  rcases hy with ⟨z, _, rfl⟩; exact ⟨hV, rfl⟩
theorem pqxdhAuthHybridShCrImpl_validHybridShCr_step (S : Setup) (P : Primitives)
    (gq : AuthQuery S) (hst : AuthHybridShCrState S) (hV : ValidHybridShCr S hst)
    (x : (authSpec S).Range gq × AuthHybridShCrState S)
    (hx : x ∈ support ((pqxdhAuthHybridShCrImpl S P gq).run hst)) : ValidHybridShCr S x.2 ∧
    x.2.sendCount ≤ hst.sendCount + (if isAuthSendQuery (.inr gq) then 1 else 0) := by
  cases gq with
  | sendOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthHybridShCrImpl, isAuthSendQuery] at hx ⊢
    cases hNone : bundle.opkB?.isNone
    · rw [hNone] at hx; simp only [Bool.false_eq_true, ↓reduceIte] at hx ⊢
      exact runShCrInitiate4_validHybridShCr P (.sendOPK u i) u bundle m0 m1 hst hV x hx
    · rw [hNone] at hx
      simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨hV, Nat.le_succ _⟩
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthHybridShCrImpl, isAuthSendQuery] at hx ⊢
    cases hSome : bundle.opkB?.isSome
    · rw [hSome] at hx; simp only [Bool.false_eq_true, ↓reduceIte] at hx ⊢
      exact runShCrInitiate4_validHybridShCr P (.sendNoOPK u i) u bundle m0 m1 hst hV x hx
    · rw [hSome] at hx
      simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨hV, Nat.le_succ _⟩
  | recvOPK k j o msg =>
    dsimp only [pqxdhAuthHybridShCrImpl, isAuthSendQuery] at hx ⊢
    rcases runShCrAcceptGeneric_validHybridShCr P
      (pqxdhAuthHybridKoskUnfrozenImpl S P (.recvOPK k j o msg)) k j msg.hdr hst hV
      (pqxdhAuthHybridKoskImpl_recvOPK_step S P k j o msg hst.base) x hx with ⟨hV', hSend⟩
    exact ⟨hV', by omega⟩
  | recvNoOPK k j l msg =>
    dsimp only [pqxdhAuthHybridShCrImpl, isAuthSendQuery] at hx ⊢
    rcases runShCrAcceptGeneric_validHybridShCr P
      (pqxdhAuthHybridKoskUnfrozenImpl S P (.recvNoOPK k j l msg)) k j msg.hdr hst hV
      (pqxdhAuthHybridKoskImpl_recvNoOPK_step S P k j l msg hst.base) x hx with ⟨hV', hSend⟩
    exact ⟨hV', by omega⟩
  | genSPK _ _ | initPrin _ | corruptIK _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
  | revealDhSecrets | registerKey _ =>
    rcases liftShCrBase_liftAuthBase_validHybridShCr
      (pqxdhAuthImpl true true S P _) hst hV x hx with ⟨hV', hSend⟩
    exact ⟨hV', by simp [isAuthSendQuery, hSend]⟩
theorem simulateQ_pqxdhAuthHybridShCrImpl_invariant {S : Setup} (P : Primitives)
    {α : Type} (oa : OracleComp (unifSpec + authSpec S) α) (n : Nat)
    (hBound : OracleComp.IsQueryBoundP oa isAuthSendQuery n)
    (hst : AuthHybridShCrState S) (hV : ValidHybridShCr S hst) (x : α × AuthHybridShCrState S)
    (hx : x ∈ support ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridShCrState S) ProbComp) +
        pqxdhAuthHybridShCrImpl S P) oa).run hst)) :
    ValidHybridShCr S x.2 ∧ x.2.sendCount ≤ hst.sendCount + n := by
  induction oa using OracleComp.inductionOn generalizing n hst x with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx; subst hx
    exact ⟨hV, Nat.le_add_right _ _⟩
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hBound
    cases q with
    | inl uq =>
      rw [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx; rcases hx with ⟨u, _, hx⟩
      have hCont : OracleComp.IsQueryBoundP (k u) isAuthSendQuery n := by
        simpa [isAuthSendQuery] using hBound.2 u
      exact ih u n hCont hst hV x hx
    | inr gq =>
      rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx; rcases hx with ⟨y, hy, hx⟩
      rcases pqxdhAuthHybridShCrImpl_validHybridShCr_step S P gq hst hV y hy with ⟨hVy, hSendy⟩
      by_cases hSend : isAuthSendQuery (.inr gq)
      · have hPos : 0 < n := (hBound.1).resolve_left (not_not.mpr hSend)
        have hCont : OracleComp.IsQueryBoundP (k y.1) isAuthSendQuery (n - 1) := by
          simpa [hSend] using hBound.2 y.1
        simp only [hSend, ↓reduceIte] at hSendy
        rcases ih y.1 (n - 1) hCont y.2 hVy x hx with ⟨hVx, hSendx⟩
        exact ⟨hVx, by omega⟩
      · have hCont : OracleComp.IsQueryBoundP (k y.1) isAuthSendQuery n := by
          simpa [hSend] using hBound.2 y.1
        simp only [hSend, ↓reduceIte] at hSendy
        rcases ih y.1 n hCont y.2 hVy x hx with ⟨hVx, hSendx⟩
        exact ⟨hVx, by omega⟩
theorem hasBadKemShCrAuth_imp_hasBadKemShCrRecords {S : Setup} (P : Primitives)
    (hst : AuthHybridShCrState S)
    (hV : ValidHybridShCr S hst) (hSend : hst.sendCount ≤ S.N_send_tot)
    (hBad : _root_.SignalPqxdh.Security.hasBadKemShCrAuth P hst.base = true) :
    _root_.Proofs.SignalPqxdh.Security.hasBadKemShCrRecords S P
      hst.initKemRecs hst.recvKemRecs = true := by
  unfold _root_.SignalPqxdh.Security.hasBadKemShCrAuth
    _root_.SignalPqxdh.Security.hasBadKemShCrRecords at hBad
  change hst.base.initKemRecs.any (fun i =>
    hst.base.recvKemRecs.any (fun r =>
      P.kemDecaps r.pqspkSk r.kemCt == some i.kemSs &&
      (r.kemCt != i.kemCt || i.pqspkPk != r.pqspkPk))) = true at hBad
  rw [List.any_eq_true] at hBad; rcases hBad with ⟨i, hi, hBadR⟩; rw [List.any_eq_true] at hBadR
  rcases hBadR with ⟨r, hr, hPred⟩; rcases hV.1 i hi with ⟨i', hi', rfl, hiLt⟩
  rcases hV.2 r hr with ⟨r', hr', rfl, hrLt⟩
  have hiTot : i'.sendIdx < S.N_send_tot := Nat.lt_of_lt_of_le hiLt hSend
  have hPos : 0 < S.N_send_tot := Nat.pos_of_ne_zero (by omega)
  let idx := r'.bIdx * S.N_send_tot + i'.sendIdx
  have hIdxLt : idx < S.N_spk_tot * S.N_send_tot := by
    dsimp [idx]
    calc r'.bIdx * S.N_send_tot + i'.sendIdx
        < r'.bIdx * S.N_send_tot + S.N_send_tot := Nat.add_lt_add_left hiTot _
      _ = (r'.bIdx + 1) * S.N_send_tot := by ring
      _ ≤ S.N_spk_tot * S.N_send_tot := Nat.mul_le_mul_right _ hrLt
  have hDiv : idx / S.N_send_tot = r'.bIdx := by
    dsimp [idx]; rw [Nat.mul_comm, Nat.mul_add_div hPos, Nat.div_eq_of_lt hiTot, Nat.add_zero]
  have hMod : idx % S.N_send_tot = i'.sendIdx := by
    dsimp [idx]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hiTot]
  rw [isKemShCrPair_eq_of_drop P i' r'] at hPred
  unfold _root_.Proofs.SignalPqxdh.Security.hasBadKemShCrRecords; rw [List.any_eq_true]
  refine ⟨idx, List.mem_range.mpr hIdxLt, ?_⟩
  unfold _root_.Proofs.SignalPqxdh.Security.hasBadKemShCrRecordsAt
  rw [hDiv, hMod, List.any_eq_true]; refine ⟨i', hi', ?_⟩
  simp only [beq_self_eq_true, Bool.true_and, List.any_eq_true]; exact ⟨r', hr', by simp [hPred]⟩
theorem badKemShCrProbAuth_g3_unfrozen_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (𝒟[runAuthKoskG3Unfrozen S P A.val >>= fun (_, _, finalSt) =>
      pure (_root_.SignalPqxdh.Security.hasBadKemShCrAuth P finalSt)] {true}).toReal ≤
    badKemShCrProbAuth S P A.val := by
  have hLHS : (runAuthKoskG3Unfrozen S P A.val >>= fun (_, _, finalSt) =>
        pure (_root_.SignalPqxdh.Security.hasBadKemShCrAuth P finalSt)) =
      (runAuthHybridShCr S P A.val >>= fun (_, _, finalHst) =>
        pure (_root_.SignalPqxdh.Security.hasBadKemShCrAuth P finalHst.base)) := by
    rw [← runAuthHybridShCr_map_base S P A.val, bind_map_left]
  have hRHS : badKemShCrProbAuth S P A.val =
      (𝒟[runAuthHybridShCr S P A.val >>= fun (_, _, finalHst) =>
        pure (_root_.Proofs.SignalPqxdh.Security.hasBadKemShCrRecords S P
          finalHst.initKemRecs finalHst.recvKemRecs)] {true}).toReal := by
    unfold badKemShCrProbAuth; rw [← runAuthHybridShCr_map_shcr S P hP A.val, bind_map_left]; rfl
  rw [hLHS, hRHS]; refine toReal_bind_bool_mono_of_support (runAuthHybridShCr S P A.val)
    (fun (_, _, finalHst) => _root_.SignalPqxdh.Security.hasBadKemShCrAuth P finalHst.base)
    (fun (_, _, finalHst) => _root_.Proofs.SignalPqxdh.Security.hasBadKemShCrRecords S P
      finalHst.initKemRecs finalHst.recvKemRecs)
    (fun ⟨secb, b', finalHst⟩ hmem => ?_)
  unfold runAuthHybridShCr at hmem
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hmem
  rcases hmem with ⟨secb0, _, ⟨b0, hst0⟩, hsim, hEq⟩
  injection hEq with _ hEq2; injection hEq2 with _ hEq3
  subst hEq3
  have hV0 : ValidHybridShCr S { base := AuthHybridState.empty S secb0 } :=
    ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
  rcases simulateQ_pqxdhAuthHybridShCrImpl_invariant P A.val.run S.N_send_tot A.property.2.1
    { base := AuthHybridState.empty S secb0 } hV0 (b0, finalHst) hsim with ⟨hV, hSend⟩
  exact hasBadKemShCrAuth_imp_hasBadKemShCrRecords P finalHst hV (by simpa using hSend)
/-! ## Hop `G0 → G3` assembly -/
theorem simulateQ_freezeImpl_mem_support_of_true
    {ι : Type} {spec : OracleSpec.{0, 0} ι} {St α : Type}
    (hasWon : St → Bool) (defResp : ∀ q : ι, spec.Range q)
    (impl : QueryImpl spec (StateT St ProbComp))
    (oa : OracleComp (unifSpec + spec) α) (st : St) (hWon : hasWon st = true) :
    ∀ x ∈ support ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
        freezeImpl hasWon defResp impl) oa).run st),
      x.2 = st := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    intro x hx
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; rfl
  | query_bind q k ih =>
    intro x hx
    cases q with
    | inl uq =>
      rw [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx; rcases hx with ⟨u, _, hx⟩
      exact ih u st hWon x hx
    | inr gq =>
      rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx; rcases hx with ⟨y, hy, hx⟩
      simp only [freezeImpl, StateT.run_bind, StateT.run_get, pure_bind, hWon, ↓reduceIte,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ih (defResp gq) st hWon x hx
theorem simulateQ_mem_support_of_sticky {ι : Type} {spec : OracleSpec.{0, 0} ι} {St α : Type}
    (hasWon : St → Bool) (impl : QueryImpl spec (StateT St ProbComp))
    (hSticky : ∀ (q : ι) (st : St), hasWon st = true →
      ∀ x ∈ support ((impl q).run st), hasWon x.2 = true)
    (oa : OracleComp (unifSpec + spec) α) (st : St) (hWon : hasWon st = true) :
    ∀ x ∈ support ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl) oa).run st),
      hasWon x.2 = true := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    intro x hx
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact hWon
  | query_bind q k ih =>
    intro x hx
    cases q with
    | inl uq =>
      rw [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx; rcases hx with ⟨u, _, hx⟩
      exact ih u st hWon x hx
    | inr gq =>
      rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx; rcases hx with ⟨y, hy, hx⟩
      exact ih y.1 y.2 (hSticky gq st hWon y hy) x hx
theorem evalDist_bind_eq_const_of_support {α : Type} (mx : ProbComp α)
    (f : α → ProbComp Bool) (c : ProbComp Bool) (h : ∀ x ∈ support mx, f x = c) :
    𝒟[mx >>= f] = 𝒟[c] := by
  have h_congr : 𝒟[mx >>= f] = 𝒟[mx >>= fun _ => c] :=
    OracleComp.evalDist_bind_congr_of_support mx f (fun _ => c) (fun x hx => by rw [h x hx])
  rw [h_congr, OracleComp.evalDist_bind_const]
theorem evalDist_simulateQ_freeze_hasWonAuth {ι : Type} {spec : OracleSpec.{0, 0} ι} {St α : Type}
    (hasWon : St → Bool) (defResp : ∀ q : ι, spec.Range q)
    (impl : QueryImpl spec (StateT St ProbComp)) (hSticky : ∀ (q : ι) (st : St), hasWon st = true →
      ∀ x ∈ support ((impl q).run st), hasWon x.2 = true)
    (post : α × St → ProbComp Bool) (c : ProbComp Bool)
    (hPost : ∀ x : α × St, hasWon x.2 = true → post x = c)
    (oa : OracleComp (unifSpec + spec) α) (st : St) :
    𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
      impl) oa).run st >>= post] =
    𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
      freezeImpl hasWon defResp impl) oa).run st >>= post] := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => rfl
  | query_bind q k ih =>
    cases q with
    | inl uq =>
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl, bind_assoc, bind_assoc]
      exact OracleComp.evalDist_bind_congr_of_support _ _ _ (fun u _ => ih u st)
    | inr gq =>
      cases hWon : hasWon st
      · rw [simulateQ_run_query_inr, simulateQ_run_query_inr, bind_assoc, bind_assoc]
        have hEq : ((freezeImpl hasWon defResp impl gq).run st) = (impl gq).run st := by
          simp [freezeImpl, StateT.run_bind, StateT.run_get, pure_bind, hWon]
        rw [hEq]
        exact OracleComp.evalDist_bind_congr_of_support _ _ _ (fun y _ => ih y.1 y.2)
      · refine (evalDist_bind_eq_const_of_support _ post c (fun x hx => ?_)).trans
          (evalDist_bind_eq_const_of_support _ post c (fun x hx => ?_)).symm
        · exact hPost x (simulateQ_mem_support_of_sticky hasWon impl hSticky _ st hWon x hx)
        · exact hPost x
            (simulateQ_freezeImpl_mem_support_of_true hasWon defResp impl _ st hWon x hx ▸ hWon)
theorem evalDist_simulateQ_bad_freeze_proj_le_unfrozen
    {ι : Type} {spec : OracleSpec.{0, 0} ι} {St1 St2 α : Type}
    (proj : St1 → St2) (hasWon : St1 → Bool) (defResp : ∀ q : ι, spec.Range q)
    (impl1 : QueryImpl spec (StateT St1 ProbComp)) (impl2 : QueryImpl spec (StateT St2 ProbComp))
    (hComm : ∀ (q : ι) (st : St1), hasWon st = false →
      Prod.map id proj <$> (impl1 q).run st = (impl2 q).run (proj st))
    (bad : St2 → Bool) (hMono : ∀ (q : ι) (st2 : St2) (x : spec.Range q × St2),
      x ∈ support ((impl2 q).run st2) → bad st2 = true → bad x.2 = true)
    (oa : OracleComp (unifSpec + spec) α) (st : St1) :
    𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St1 ProbComp) +
      freezeImpl hasWon defResp impl1) oa).run st >>= fun (_, s1) => pure (bad (proj s1))] {true} ≤
    𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St2 ProbComp) +
      impl2) oa).run (proj st) >>= fun (_, s2) => pure (bad s2)] {true} := by
  have hMonoSim : ∀ (oa' : OracleComp (unifSpec + spec) α) (st2 : St2) (x : α × St2),
      x ∈ support ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St2 ProbComp) +
        impl2) oa').run st2) → bad st2 = true → bad x.2 = true := by
    intro oa'
    induction oa' using OracleComp.inductionOn with
    | pure a =>
      intro st2 x hx hB
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hB
    | query_bind q k ih =>
      intro st2 x hx hB
      cases q with
      | inl uq =>
        rw [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx; rcases hx with ⟨u, _, hx⟩
        exact ih u st2 x hx hB
      | inr gq =>
        rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx; rcases hx with ⟨y, hy, hx⟩
        exact ih y.1 y.2 x hx (hMono gq st2 y hy hB)
  rw [evalDist_bind_true_eq_probExpect_ite, evalDist_bind_true_eq_probExpect_ite]
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => simp [simulateQ_pure, probExpect_pure]
  | query_bind q k ih =>
    cases q with
    | inl uq =>
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl, probExpect_bind, probExpect_bind]
      exact probExpect_mono_of_support _ _ _ (fun u _ => ih u st)
    | inr gq =>
      cases hWon : hasWon st
      · rw [simulateQ_run_query_inr, simulateQ_run_query_inr, probExpect_bind, probExpect_bind]
        have hFr : ((freezeImpl hasWon defResp impl1 gq).run st) = (impl1 gq).run st := by
          simp [freezeImpl, StateT.run_bind, StateT.run_get, pure_bind, hWon]
        rw [hFr, ← hComm gq st hWon, probExpect_map]
        exact probExpect_mono_of_support ((impl1 gq).run st) _ _ (fun ⟨out, st'⟩ _ => ih out st')
      · cases hBad : bad (proj st)
        · refine le_of_eq_of_le (probExpect_eq_zero_of_support _ _ (fun x hx => ?_)) zero_le
          have hst := simulateQ_freezeImpl_mem_support_of_true hasWon defResp impl1 _ st hWon x hx
          simp [hst, hBad]
        · refine (probExpect_const_le_of_support _ _ 1 (fun x _ => by split_ifs <;> simp)).trans
            (le_probExpect_const_of_support _ _ 1 (fun x hx => ?_))
          have hBad' := hMonoSim _ (proj st) x hx hBad; simp [hBad']
theorem evalDist_simulateQ_bad_freeze_le_unfrozen
    {ι : Type} {spec : OracleSpec.{0, 0} ι} {St α : Type}
    (hasWon : St → Bool) (defResp : ∀ q : ι, spec.Range q)
    (impl : QueryImpl spec (StateT St ProbComp)) (bad : St → Bool)
    (hMono : ∀ (q : ι) (st : St) (x : spec.Range q × St),
      x ∈ support ((impl q).run st) → bad st = true → bad x.2 = true)
    (oa : OracleComp (unifSpec + spec) α) (st : St) :
    𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
      freezeImpl hasWon defResp impl) oa).run st >>= fun (_, s1) => pure (bad s1)] {true} ≤
    𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
      impl) oa).run st >>= fun (_, s2) => pure (bad s2)] {true} :=
  evalDist_simulateQ_bad_freeze_proj_le_unfrozen id hasWon defResp impl impl
    (fun q s _ => by simp [Prod.map_id]) bad hMono oa st
theorem runAuthSendWithProv_pres_hasWonAuth (S : Setup) (P : Primitives) (provFn : ProvFnType)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) :
    PreservesAt AuthState.hasWonAuth st (runAuthSendWithProv S P provFn sid u bundle m0 m1) := by
  unfold runAuthSendWithProv; dsimp only; prove_preserves_at
theorem pqxdhAuthImpl_recvOPK_pres_hasWonAuth (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (st : AuthState S) (hWon : st.hasWonAuth = true) :
    PreservesAt AuthState.hasWonAuth st (pqxdhAuthImpl true true S P (.recvOPK k j o msg)) := by
  unfold pqxdhAuthImpl; dsimp only
  repeat (first
    | with_reducible apply PreservesAt.pure
    | (rw [pure_bind])
    | with_reducible apply PreservesAt.get_bind
    | (with_reducible apply PreservesAt.liftM_bind; intro _)
    | ((with_reducible apply PreservesAt.set_bind); simp [hWon])
    | (split; try dsimp only))
theorem pqxdhAuthImpl_recvNoOPK_pres_hasWonAuth (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (st : AuthState S) (hWon : st.hasWonAuth = true) :
    PreservesAt AuthState.hasWonAuth st (pqxdhAuthImpl true true S P (.recvNoOPK k j l msg)) := by
  unfold pqxdhAuthImpl; dsimp only
  repeat (first
    | with_reducible apply PreservesAt.pure
    | (rw [pure_bind])
    | with_reducible apply PreservesAt.get_bind
    | (with_reducible apply PreservesAt.liftM_bind; intro _)
    | ((with_reducible apply PreservesAt.set_bind); simp [hWon])
    | (split; try dsimp only))
theorem pqxdhAuthWithProvImpl_hasWonAuth_sticky (S : Setup) (P : Primitives) (provFn : ProvFnType)
    (q : AuthQuery S) (st : AuthState S) (hWon : st.hasWonAuth = true) :
    ∀ x ∈ support ((pqxdhAuthWithProvImpl S P provFn q).run st), x.2.hasWonAuth = true := by
  have hPres : PreservesAt AuthState.hasWonAuth st (pqxdhAuthWithProvImpl S P provFn q) := by
    cases q with
    | sendOPK u i bundle m0 m1 =>
      unfold pqxdhAuthWithProvImpl; dsimp only
      split
      · exact PreservesAt.pure _ _ _
      · exact runAuthSendWithProv_pres_hasWonAuth S P provFn (.sendOPK u i) u bundle m0 m1 st
    | sendNoOPK u i bundle m0 m1 =>
      unfold pqxdhAuthWithProvImpl; dsimp only
      split
      · exact PreservesAt.pure _ _ _
      · exact runAuthSendWithProv_pres_hasWonAuth S P provFn (.sendNoOPK u i) u bundle m0 m1 st
    | recvOPK k j o msg => exact pqxdhAuthImpl_recvOPK_pres_hasWonAuth S P k j o msg st hWon
    | recvNoOPK k j l msg => exact pqxdhAuthImpl_recvNoOPK_pres_hasWonAuth S P k j l msg st hWon
    | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
    | revealDhSecrets | registerKey _ =>
      unfold pqxdhAuthWithProvImpl pqxdhAuthImpl; dsimp only; prove_preserves_at
  intro x hx; rw [hPres x hx, hWon]
theorem evalDist_pqxdhAuthExp_eq_G0Frozen (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    𝒟[pqxdhAuthExp S P A] = 𝒟[authExpG0Frozen S P A] := by
  have hG0 : pqxdhAuthExp S P A =
      (runAuthWithProv (checkBundleProvenance P) S P A >>= contAuth S P) := by
    rw [runAuthWithProv_checkBundleProvenance]
    unfold pqxdhAuthExp pqxdhAuthExpCore runAuthSim contAuth; simp [bind_assoc]
  rw [hG0]; unfold authExpG0Frozen runAuthWithProv runAuthWithProvFrozen; simp only [bind_assoc]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact evalDist_simulateQ_freeze_hasWonAuth AuthState.hasWonAuth (fun _ => .noneResp)
    (pqxdhAuthWithProvImpl S P (checkBundleProvenance P))
    (pqxdhAuthWithProvImpl_hasWonAuth_sticky S P (checkBundleProvenance P))
    (fun (b', finalSt) => contAuth S P (secb, b', finalSt)) (pure true)
    (fun ⟨b', finalSt⟩ hWon => by dsimp only at hWon; simp [contAuth, hWon])
    A.run (AuthState.empty S secb)
theorem pqxdhAuthWithProvFrozenImpl_commutes_mapAuthSessions (S : Setup) (P : Primitives)
    (f : Bool × Bool × Bool → Bool × Bool × Bool) (prov1 prov2 : ProvFnType)
    (h_prov : ∀ p b o bnd, prov1 p b o bnd = f (prov2 p b o bnd))
    (q : AuthQuery S) (st : AuthState S) :
    let mapEntry : AuthInitiatorEntry S → AuthInitiatorEntry S := fun s =>
      let (s', o', p') := f (s.spkHonest, s.opkHonest, s.pqspkHonest)
      { s with spkHonest := s', opkHonest := o', pqspkHonest := p' }
    CommutesRel (mapAuthSessions mapEntry) st (pqxdhAuthWithProvFrozenImpl S P prov1 q)
      (pqxdhAuthWithProvFrozenImpl S P prov2 q) := by
  intro mapEntry; unfold pqxdhAuthWithProvFrozenImpl freezeImpl; apply CommutesRel.get_bind
  dsimp only [mapAuthSessions]; apply CommutesRel.ite
  · exact CommutesRel.pure _ st _
  · exact pqxdhAuthWithProvImpl_commutes_mapAuthSessions S P f prov1 prov2 h_prov q st
theorem runAuthWithProvFrozen_eq_map (S : Setup) (P : Primitives)
    (f : Bool × Bool × Bool → Bool × Bool × Bool) (prov1 prov2 : ProvFnType)
    (h_prov : ∀ p b o bnd, prov1 p b o bnd = f (prov2 p b o bnd)) (A : AuthAdversary S) :
    let mapEntry : AuthInitiatorEntry S → AuthInitiatorEntry S := fun s =>
      let (s', o', p') := f (s.spkHonest, s.opkHonest, s.pqspkHonest)
      { s with spkHonest := s', opkHonest := o', pqspkHonest := p' }
    runAuthWithProvFrozen prov1 S P A =
      (fun (secb, b', st) => (secb, b', mapAuthSessions mapEntry st)) <$>
        runAuthWithProvFrozen prov2 S P A := by
  intro mapEntry; unfold runAuthWithProvFrozen; simp only [map_bind, map_pure]
  refine bind_congr (fun secb => ?_)
  have hsim := CommutesRel.simulateQ_add_unif (mapAuthSessions mapEntry)
    (pqxdhAuthWithProvFrozenImpl S P prov1) (pqxdhAuthWithProvFrozenImpl S P prov2)
    (pqxdhAuthWithProvFrozenImpl_commutes_mapAuthSessions S P f prov1 prov2 h_prov)
    A.run (AuthState.empty S secb)
  unfold CommutesRel at hsim; rw [mapAuthSessions_empty] at hsim; rw [hsim, bind_map_left]; rfl
theorem ecCollProbAuth_frozen_le_bound (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    (𝒟[runAuthWithProvFrozen (checkBundleProvenance P) S P A >>= fun (_, _, finalSt) =>
      pure (hasEcPkCollisionAuth P finalSt)] {true}).toReal ≤
      ((S.N_dh * (S.N_dh - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  refine ecCollProb_le_of_step S.N_dh P (ValidAuthEc S P) (ecTaggedAuth S P)
    (hasEcPkCollisionAuth P) (pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenance P))
    (AuthState.empty S) (fun _ => ⟨validEcLists_nil S, rfl⟩) (fun _ => rfl)
    (fun st hV => validTaggedPks_ecTaggedFromLists S P st.principals st.spkBundles st.opkEntries
      (sessPksAuth S P st) hV.1)
    (fun st _ => by simp [hasEcPkCollisionAuth, map_snd_ecTaggedAuth])
    (fun q st hV x hx => ?_) (fun q st s1 s2 hV => ?_) A.run
  · simp only [pqxdhAuthWithProvFrozenImpl, freezeImpl, pqxdhAuthWithProvImpl_checkBundleProvenance,
      StateT.run_bind, StateT.run_get, pure_bind] at hx
    split_ifs at hx
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hV
    · exact (pqxdhAuthImpl_ec_step true true S P hCWF q st 0 0 hV).1 x hx
  · simp only [pqxdhAuthWithProvFrozenImpl, freezeImpl, pqxdhAuthWithProvImpl_checkBundleProvenance,
      StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp [probExpect_pure]
    · exact (pqxdhAuthImpl_ec_step true true S P hCWF q st s1 s2 hV).2
theorem kemCollProbAuth_frozen_le_bound (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    (𝒟[runAuthWithProvFrozen (checkBundleProvenance P) S P A >>= fun (_, _, finalSt) =>
      pure (hasKemPkCollisionAuth finalSt)] {true}).toReal ≤
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  refine kemCollProb_simulateQ_le S AuthState.spkBundles (AuthState.empty S)
    (fun _ => rfl) (pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenance P))
    (fun q st hV x hx => ?_) (fun b1 b2 q st hV => ?_) A.run
  · simp only [pqxdhAuthWithProvFrozenImpl, freezeImpl, pqxdhAuthWithProvImpl_checkBundleProvenance,
      StateT.run_bind, StateT.run_get, pure_bind] at hx
    split_ifs at hx
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hV
    · exact (pqxdhAuthImpl_valid_and_potential_le true true S P hCWF 0 0 q st hV).1 x hx
  · simp only [pqxdhAuthWithProvFrozenImpl, freezeImpl, pqxdhAuthWithProvImpl_checkBundleProvenance,
      StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp [probExpect_pure]
    · exact (pqxdhAuthImpl_valid_and_potential_le true true S P hCWF b1 b2 q st hV).2
theorem auth_hop_G0_G0_1_frozen_le (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    |(𝒟[authExpG0Frozen S P A].boolBias).toReal -
     (𝒟[authExpG0_1WithProvFrozen (checkBundleProvenance P) S P A].boolBias).toReal| ≤
      ((S.N_dh * (S.N_dh - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  refine (abs_sub_boolBias_abort_le (runAuthWithProvFrozen (checkBundleProvenance P) S P A)
    (fun (_, _, finalSt) => hasEcPkCollisionAuth P finalSt) (contAuth S P)).trans
    (ecCollProbAuth_frozen_le_bound S P hCWF A)
theorem authExpG0_1WithProvFrozen_eq_of_squash (S : Setup) (P : Primitives)
    (prov1 prov2 : ProvFnType)
    (h_prov : ∀ p b o bnd, prov1 p b o bnd = squashTriples (prov2 p b o bnd))
    (A : AuthAdversary S) :
    authExpG0_1WithProvFrozen prov1 S P A = authExpG0_1WithProvFrozen prov2 S P A := by
  unfold authExpG0_1WithProvFrozen
  rw [runAuthWithProvFrozen_eq_map S P squashTriples prov1 prov2 h_prov A, bind_map_left]
  congr 1; ext ⟨secb, b', st⟩; dsimp only
  rw [hasEcPkCollisionAuth_mapAuthSessions P squashTriples st,
      contAuth_mapAuthSessions_squash S P secb b' st]
theorem authExpG0_1WithProvFrozen_orig_eq_dual (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    authExpG0_1WithProvFrozen (checkBundleProvenance P) S P A =
      authExpG0_1WithProvFrozen (checkBundleProvenanceDual P) S P A := by
  rw [← authExpG0_1WithProvFrozen_eq_of_squash S P
        (checkBundleProvenanceSquashed P) (checkBundleProvenance P)
        (checkBundleProvenanceSquashed_eq_squash_orig P) A,
      authExpG0_1WithProvFrozen_eq_of_squash S P
        (checkBundleProvenanceSquashed P) (checkBundleProvenanceDual P)
        (checkBundleProvenanceSquashed_eq_squash_dual P) A]
theorem authExpG1WithProvFrozen_eq_of_eraseOpk (S : Setup) (P : Primitives)
    (prov1 prov2 : ProvFnType)
    (h_prov : ∀ p b o bnd, prov1 p b o bnd = eraseOpkTriples (prov2 p b o bnd))
    (A : AuthAdversary S) :
    authExpG1WithProvFrozen prov1 S P A = authExpG1WithProvFrozen prov2 S P A := by
  unfold authExpG1WithProvFrozen
  rw [runAuthWithProvFrozen_eq_map S P eraseOpkTriples prov1 prov2 h_prov A, bind_map_left]
  congr 1; ext ⟨secb, b', st⟩; dsimp only
  rw [hasEcPkCollisionAuth_mapAuthSessions P eraseOpkTriples st,
      hasBadSigAuth_mapAuthSessions_eraseOpk st]
  by_cases h_bad : (hasEcPkCollisionAuth P st || hasBadSigAuth st) = true
  · simp [h_bad]
  · have h_ok : hasBadSigAuth st = false := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h_bad; exact h_bad.2
    simp [h_bad, contAuth_mapAuthSessions_eraseOpk_of_not_badSig S P secb b' st h_ok]
theorem authExpG1WithProvFrozen_dual_eq_exact (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    authExpG1WithProvFrozen (checkBundleProvenanceDual P) S P A =
      authExpG1WithProvFrozen (checkBundleProvenanceExact P) S P A := by
  rw [← authExpG1WithProvFrozen_eq_of_eraseOpk S P
        (checkBundleProvenanceNoOpk P) (checkBundleProvenanceDual P)
        (checkBundleProvenanceNoOpk_eq_eraseOpk_dual P) A,
      authExpG1WithProvFrozen_eq_of_eraseOpk S P
        (checkBundleProvenanceNoOpk P) (checkBundleProvenanceExact P)
        (checkBundleProvenanceNoOpk_eq_eraseOpk_exact P) A]
theorem kemCollProbAuth_frozen_exact_eq (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    (𝒟[runAuthWithProvFrozen (checkBundleProvenanceExact P) S P A >>= fun (_, _, finalSt) =>
      pure (hasKemPkCollisionAuth finalSt)] {true}).toReal =
    (𝒟[runAuthWithProvFrozen (checkBundleProvenance P) S P A >>= fun (_, _, finalSt) =>
      pure (hasKemPkCollisionAuth finalSt)] {true}).toReal := by
  have h_map : ∀ (f : Bool × Bool × Bool → Bool × Bool × Bool) (prov1 prov2 : ProvFnType)
      (h_prov : ∀ p b o bnd, prov1 p b o bnd = f (prov2 p b o bnd)),
      (runAuthWithProvFrozen prov1 S P A >>= fun (_, _, s) => pure (hasKemPkCollisionAuth s)) =
      (runAuthWithProvFrozen prov2 S P A >>= fun (_, _, s) => pure (hasKemPkCollisionAuth s)) := by
    intro f prov1 prov2 h_prov
    rw [runAuthWithProvFrozen_eq_map S P f prov1 prov2 h_prov A, bind_map_left]; rfl
  rw [← h_map eraseOpkTriples (checkBundleProvenanceNoOpk P) (checkBundleProvenanceExact P)
        (checkBundleProvenanceNoOpk_eq_eraseOpk_exact P),
      h_map eraseOpkTriples (checkBundleProvenanceNoOpk P) (checkBundleProvenanceDual P)
        (checkBundleProvenanceNoOpk_eq_eraseOpk_dual P),
      ← h_map squashTriples (checkBundleProvenanceSquashed P) (checkBundleProvenanceDual P)
        (checkBundleProvenanceSquashed_eq_squash_dual P),
      h_map squashTriples (checkBundleProvenanceSquashed P) (checkBundleProvenance P)
        (checkBundleProvenanceSquashed_eq_squash_orig P)]
theorem auth_hop_kemColl_frozen_exact_le (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    |(𝒟[authExpG1WithProvFrozen (checkBundleProvenanceExact P) S P A].boolBias).toReal -
     (𝒟[authExpG2_1WithProvFrozen (checkBundleProvenanceExact P) S P A].boolBias).toReal| ≤
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  have h1 : |(𝒟[authExpG1WithProvFrozen (checkBundleProvenanceExact P) S P A].boolBias).toReal -
     (𝒟[authExpG2_1WithProvFrozen (checkBundleProvenanceExact P) S P A].boolBias).toReal| ≤
      (𝒟[runAuthWithProvFrozen (checkBundleProvenanceExact P) S P A >>= fun (_, _, finalSt) =>
        pure (hasKemPkCollisionAuth finalSt)] {true}).toReal :=
    abs_sub_boolBias_abort_or_le (runAuthWithProvFrozen (checkBundleProvenanceExact P) S P A)
      (fun (_, _, finalSt) => hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt)
      (fun (_, _, finalSt) => hasKemPkCollisionAuth finalSt) (contAuth S P)
  rw [kemCollProbAuth_frozen_exact_eq] at h1
  exact h1.trans (kemCollProbAuth_frozen_le_bound S P hCWF A)
theorem authSim_safe_step (S : Setup) (P : Primitives) (k : Nat)
    (q : AuthQuery S) (st : AuthState S) (hSafe : (authSigLens S).Safe P k st) :
    ∀ x ∈ support ((pqxdhAuthSimImpl S P q).run st), (authSigLens S).Safe P k x.2 := by
  cases q with
  | initPrin u => exact (authSigLens S).safe_step_initPrin P k u st hSafe
  | corruptIK u => exact (authSigLens S).safe_step_corruptIK P k u st hSafe
  | genSPK u j => exact (authSigLens S).safe_step_genSPK P k u j st hSafe
  | sendOPK u i bnd m0 m1 =>
    exact safe_step_initiate_auth S P k bnd _ st
      (pqxdhAuthSimImpl_sendOPK_pres S P u i bnd m0 m1 st) hSafe
  | sendNoOPK u i bnd m0 m1 =>
    exact safe_step_initiate_auth S P k bnd _ st
      (pqxdhAuthSimImpl_sendNoOPK_pres S P u i bnd m0 m1 st) hSafe
  | genOPK _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ | roQuery _ | roRootQuery _ _
  | revealDhSecrets | registerKey _ =>
    exact (authSigLens S).safe_step_other P k _ st (pqxdhAuthSimImpl_other_pres S P _ st
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)) hSafe
theorem authSim_after_step (S : Setup) (P : Primitives) (k : Nat)
    (sk : Bytes) (q : AuthQuery S) (st : AuthState S) (s : SigReductionState (AuthState S))
    (budget : Nat) (signedMsgs : List Bytes) (fL : (authSpec S).Range q × AuthState S → ℝ≥0∞)
    (fR : ((authSpec S).Range q × SigReductionState (AuthState S) × Nat) × List Bytes → ℝ≥0∞)
    (hAfter : (authSigLens S).ActiveAfter P k sk st s budget signedMsgs)
    (hfL1 : ∀ x, fL x ≤ 1) (hfL0 : ∀ x, (authSigLens S).Safe P k x.2 → fL x = 0)
    (hfR1 : ∀ y, SigWon P sk y.1.2.1 y.2 → 1 ≤ fR y)
    (hih : ∀ out st' s' b' msgs', (authSigLens S).ActiveAfter P k sk st' s' b' msgs' →
      fL (out, st') ≤ fR ((out, s', b'), msgs')) :
    probExpect ((pqxdhAuthSimImpl S P q).run st) fL ≤
      probExpect (runSigStepSim P sk budget (stepAuthForSig S P q s) signedMsgs) fR := by
  have hs := hAfter.1; subst hs
  cases q with
  | initPrin u =>
    exact (authSigLens S).after_step_initPrin P k sk u st _ budget signedMsgs fL fR hAfter hfL0 hih
  | corruptIK u =>
    exact (authSigLens S).after_step_corruptIK P k sk u st _ budget signedMsgs fL fR hAfter hfL0 hih
  | genSPK u j =>
    exact (authSigLens S).after_step_genSPK P k sk u j st _ budget signedMsgs fL fR hAfter hfL0 hih
  | sendOPK u i bnd m0 m1 =>
    exact after_step_initiate_auth S P k sk bnd _ st _ budget signedMsgs fL fR
      (pqxdhAuthSimImpl_other_commutes S P k (.sendOPK u i bnd m0 m1) st
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h))
      (pqxdhAuthSimImpl_sendOPK_pres S P u i bnd m0 m1 st) hAfter hfL1 hfL0 hfR1 hih
  | sendNoOPK u i bnd m0 m1 =>
    exact after_step_initiate_auth S P k sk bnd _ st _ budget signedMsgs fL fR
      (pqxdhAuthSimImpl_other_commutes S P k (.sendNoOPK u i bnd m0 m1) st
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h))
      (pqxdhAuthSimImpl_sendNoOPK_pres S P u i bnd m0 m1 st) hAfter hfL1 hfL0 hfR1 hih
  | genOPK _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ | roQuery _ | roRootQuery _ _
  | revealDhSecrets | registerKey _ =>
    exact (authSigLens S).after_step_other P k sk _ st _ budget signedMsgs fL fR
      (pqxdhAuthSimImpl_other_commutes S P k _ st
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h))
      (pqxdhAuthSimImpl_other_pres S P _ st
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)) hAfter hfL0 hih
theorem authSim_before_step (S : Setup) (P : Primitives) (k : Nat)
    (q : AuthQuery S) (st : AuthState S) (budget : Nat)
    (fL : (authSpec S).Range q × AuthState S → ℝ≥0∞)
    (fR : Bytes →
      ((authSpec S).Range q × SigReductionState (AuthState S) × Nat) × List Bytes → ℝ≥0∞)
    (hBefore : (authSigLens S).ActiveBefore P k st budget)
    (hih_before : ∀ out st' b', (authSigLens S).ActiveBefore P k st' b' →
      fL (out, st') ≤ probExpect sampleScalar32 (fun sk =>
        fR sk ((out, ⟨st', k, P.sigPkGen sk, none⟩, b'), [])))
    (hih_after : ∀ sk out st' s' b' msgs', (authSigLens S).ActiveAfter P k sk st' s' b' msgs' →
      fL (out, st') ≤ fR sk ((out, s', b'), msgs')) :
    probExpect ((pqxdhAuthSimImpl S P q).run st) fL ≤ probExpect sampleScalar32 (fun sk =>
        probExpect (runSigStepSim P sk budget
          (stepAuthForSig S P q ⟨st, k, P.sigPkGen sk, none⟩) []) (fR sk)) := by
  cases q with
  | initPrin u =>
    exact (authSigLens S).before_step_initPrin P k u st budget fL fR hBefore hih_before hih_after
  | corruptIK u =>
    exact (authSigLens S).before_step_corruptIK P k u st budget fL fR hBefore hih_before
  | genSPK u j =>
    exact (authSigLens S).before_step_genSPK P k u j st budget fL fR hBefore hih_before
  | sendOPK u i bnd m0 m1 =>
    exact before_step_initiate_auth S P k bnd _ st budget fL fR
      (pqxdhAuthSimImpl_sendOPK_pres S P u i bnd m0 m1 st) hBefore hih_before
  | sendNoOPK u i bnd m0 m1 =>
    exact before_step_initiate_auth S P k bnd _ st budget fL fR
      (pqxdhAuthSimImpl_sendNoOPK_pres S P u i bnd m0 m1 st) hBefore hih_before
  | genOPK _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ | roQuery _ | roRootQuery _ _
  | revealDhSecrets | registerKey _ =>
    exact (authSigLens S).before_step_other P k _ st budget fL fR
      (pqxdhAuthSimImpl_other_pres S P _ st
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)) hBefore hih_before
noncomputable abbrev authFrozenBadExpect (S : Setup) (P : Primitives) (k : Nat) {α : Type}
    (oa : OracleComp (unifSpec + authSpec S) α) (fst : AuthState S) : ℝ≥0∞ :=
  probExpect ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthState S) ProbComp) +
    pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceNoOpk P)) oa).run fst)
    (fun (_, finalSt) => if (authSigLens S).badAt P k (projAuthSim S P finalSt) then 1 else 0)
theorem probExpect_safe_freeze_eq_zero {S : Setup} {α : Type} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : Nat)
    (oa : OracleComp (unifSpec + authSpec S) α) (fst : AuthState S)
    (hSafe : (authSigLens S).Safe P k (projAuthSim S P fst)) : authFrozenBadExpect S P k oa fst =
      0 := by
  refine probExpect_safe_eq_zero (pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceNoOpk P))
    (fun s => (authSigLens S).badAt P k (projAuthSim S P s))
    (fun s => (authSigLens S).Safe P k (projAuthSim S P s))
    (fun s hs => (authSigLens S).safe_badAt_eq_false P k (projAuthSim S P s) hs) ?_ oa fst hSafe
  intro gq s hs x hx
  simp only [pqxdhAuthWithProvFrozenImpl, freezeImpl, StateT.run_bind, StateT.run_get,
    pure_bind] at hx
  split_ifs at hx
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hs
  · have hmem : Prod.map id (projAuthSim S P) x ∈
        support ((pqxdhAuthSimImpl S P gq).run (projAuthSim S P s)) := by
      rw [← (pqxdhAuthSimImpl_commutes_projAuthSim S P hP gq s).symm, support_map]; exact ⟨x, hx, rfl⟩
    exact authSim_safe_step S P k gq (projAuthSim S P s) hs (Prod.map id (projAuthSim S P) x) hmem
noncomputable def liftAuthSimFL (S : Setup) (P : Primitives) {q : AuthQuery S}
    (fL0 : (authSpec S).Range q × AuthState S → ℝ≥0∞) :
    (authSpec S).Range q × AuthState S → ℝ≥0∞ := fun (out, st') =>
  ⨆ (fst' : { fst' : AuthState S // projAuthSim S P fst' = st' }),
    letI : Decidable (ValidAuthSim S P st') := Classical.propDecidable _
    if ValidAuthSim S P st' then fL0 (out, fst'.val) else 0
theorem probExpect_liftAuthSimFL_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (gq : AuthQuery S)
    (fst : AuthState S) (hInv : ValidAuthSim S P (projAuthSim S P fst))
    (fL0 : (authSpec S).Range gq × AuthState S → ℝ≥0∞) :
    probExpect ((pqxdhAuthWithProvImpl S P (checkBundleProvenanceNoOpk P) gq).run fst) fL0 ≤
      probExpect ((pqxdhAuthSimImpl S P gq).run (projAuthSim S P fst))
        (liftAuthSimFL S P fL0) := by
  rw [← (pqxdhAuthSimImpl_commutes_projAuthSim S P hP gq fst).symm, probExpect_map]
  refine probExpect_mono_of_support
    ((pqxdhAuthWithProvImpl S P (checkBundleProvenanceNoOpk P) gq).run fst) fL0
    (fun x => liftAuthSimFL S P fL0 (Prod.map id (projAuthSim S P) x)) (fun ⟨out, fst'⟩ hx => ?_)
  have hmem : (out, projAuthSim S P fst') ∈
      support ((pqxdhAuthSimImpl S P gq).run (projAuthSim S P fst)) := by
    rw [← (pqxdhAuthSimImpl_commutes_projAuthSim S P hP gq fst).symm, support_map]
    exact ⟨(out, fst'), hx, rfl⟩
  have hInv' := pqxdhAuthSimImpl_validAuthSim_step S P gq (projAuthSim S P fst) hInv
    (out, projAuthSim S P fst') hmem
  dsimp only [liftAuthSimFL, Prod.map]; refine le_iSup_of_le ⟨fst', rfl⟩ ?_; simp [hInv']
theorem probExpect_activeAfter_freeze_le {S : Setup} {α : Type}
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (k : Nat) (sk : Bytes) (oa : OracleComp (unifSpec + authSpec S) α)
    (fst : AuthState S) (s : SigReductionState (AuthState S))
    (budget : Nat) (signedMsgs : List Bytes)
    (hAfter : (authSigLens S).ActiveAfter P k sk (projAuthSim S P fst) s budget signedMsgs)
    (hInv : ValidAuthSim S P (projAuthSim S P fst)) : authFrozenBadExpect S P k oa fst ≤
    probExpect ((simulateQ (sigEufCmaFullImpl P sk)
        (runWithSigBudgetPrim (stepAuthForSigPrim S) oa s budget)).run signedMsgs)
      (sigWinInd P sk) := by
  unfold authFrozenBadExpect; induction oa using OracleComp.inductionOn
    generalizing fst s budget signedMsgs with
  | pure x =>
    rw [probExpect_runWithSigBudgetPrim_pure]; simp [probExpect_pure,
      (authSigLens S).activeAfter_badAt_eq_false P k sk (projAuthSim S P fst) s budget
        signedMsgs hAfter]
  | query_bind q mx ih =>
    cases q with
    | inl n =>
      rw [probExpect_runWithSigBudgetPrim_query_inl]
      simp only [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_add_query_left,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift,
        monadLift_self, probExpect_bind, probExpect_pure]
      exact probExpect_mono_of_support _ _ _ (fun u _ => ih u fst s budget signedMsgs hAfter hInv)
    | inr gq =>
      cases hWon : fst.hasWonAuth
      · rw [probExpect_runWithSigBudgetPrim_query_inr]
        simp only [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_add_query_right,
          probExpect_bind]
        change probExpect
          ((pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceNoOpk P) gq).run fst) _ ≤
          probExpect
            (runSigStepSim P sk budget (evalStepPrim P (stepAuthForSigPrim S) gq s) signedMsgs) _
        have hFr : ((pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceNoOpk P) gq).run fst) =
            (pqxdhAuthWithProvImpl S P (checkBundleProvenanceNoOpk P) gq).run fst := by
          simp [pqxdhAuthWithProvFrozenImpl, freezeImpl, StateT.run_bind, StateT.run_get,
            pure_bind, hWon]
        have hEv : evalStepPrim P (stepAuthForSigPrim S) gq s = stepAuthForSig S P gq s := by
          have hs := hAfter.1; subst hs
          have hL := validAuthSim_lengths_le S P (projAuthSim S P fst) hInv
          exact evalStepPrim_stepAuthForSigPrim S P gq _
            (by simpa [SigGameLens.eraseSk, authSigLens] using hL.1) hL.2.1 hL.2.2 hInv.2.2.2
        rw [hFr, hEv]
        let fL0 := fun x : (authSpec S).Range gq × AuthState S =>
          authFrozenBadExpect S P k (mx x.1) x.2
        let fL' := liftAuthSimFL S P fL0
        have hStepL := probExpect_liftAuthSimFL_le S P hP gq fst hInv fL0
        refine hStepL.trans (authSim_after_step S P k sk gq (projAuthSim S P fst) s budget
          signedMsgs fL' _ hAfter ?_ ?_ ?_ ?_)
        · rintro ⟨out, st'⟩; dsimp only [fL', liftAuthSimFL, fL0, authFrozenBadExpect]
          refine iSup_le (fun ⟨fst', _⟩ => ?_)
          split_ifs
          · exact probExpect_const_le_of_support _ _ 1 (fun ⟨_, finalSt⟩ _ => by
              by_cases h : (authSigLens S).badAt P k (projAuthSim S P finalSt) <;> simp [h])
          · exact zero_le
        · rintro ⟨out, st'⟩ hSafe; dsimp only [fL', liftAuthSimFL, fL0]
          refine le_antisymm (iSup_le (fun ⟨fst', hproj⟩ => ?_)) bot_le; split_ifs
          · rw [probExpect_safe_freeze_eq_zero P hP k (mx out) fst' (hproj ▸ hSafe)]
          · exact le_rfl
        · rintro ⟨⟨out, s', b'⟩, msgs'⟩ hWonSig
          exact probExpect_sigWon_ge_one P sk (stepAuthForSigPrim S) (fun q s hSome => ⟨.noneResp,
              by simp [evalStepPrim, stepAuthForSigPrim, hSome, SigStepResultPrim.toProbComp]⟩)
            (mx out) s' b' msgs' hWonSig
        · intro out st' s' b' msgs' hAfter'; dsimp only [fL', liftAuthSimFL, fL0]
          refine iSup_le (fun ⟨fst', hproj⟩ => ?_); split_ifs with hInv'
          · subst hproj; exact ih out fst' s' b' msgs' hAfter' hInv'
          · exact zero_le
      · refine le_of_eq_of_le (probExpect_eq_zero_of_support _ _ (fun x hx => ?_)) zero_le
        dsimp only [pqxdhAuthWithProvFrozenImpl] at hx
        have hst := simulateQ_freezeImpl_mem_support_of_true AuthState.hasWonAuth
          (fun _ => .noneResp) (pqxdhAuthWithProvImpl S P (checkBundleProvenanceNoOpk P))
          _ fst hWon x hx
        simp [hst, (authSigLens S).activeAfter_badAt_eq_false P k sk (projAuthSim S P fst) s budget
            signedMsgs hAfter]
theorem probExpect_activeBefore_freeze_le {S : Setup} {α : Type}
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (k : Nat) (oa : OracleComp (unifSpec + authSpec S) α)
    (fst : AuthState S) (budget : Nat)
    (hBefore : (authSigLens S).ActiveBefore P k (projAuthSim S P fst) budget)
    (hInv : ValidAuthSim S P (projAuthSim S P fst)) : authFrozenBadExpect S P k oa fst ≤
    probExpect sampleScalar32 (fun sk =>
      probExpect ((simulateQ (sigEufCmaFullImpl P sk)
          (runWithSigBudgetPrim (stepAuthForSigPrim S) oa
            ⟨projAuthSim S P fst, k, P.sigPkGen sk, none⟩ budget)).run [])
        (sigWinInd P sk)) := by
  unfold authFrozenBadExpect; induction oa using OracleComp.inductionOn
    generalizing fst budget with
  | pure x =>
    simp [probExpect_runWithSigBudgetPrim_pure, probExpect_pure,
      (authSigLens S).activeBefore_badAt_eq_false P k (projAuthSim S P fst) budget hBefore]
  | query_bind q mx ih =>
    cases q with
    | inl n =>
      rw [simulateQ_run_query_inl, probExpect_bind]
      simp only [probExpect_runWithSigBudgetPrim_query_inl]; rw [probExpect_swap sampleScalar32]
      exact probExpect_mono_of_support _ _ _ (fun u _ => ih u fst budget hBefore hInv)
    | inr gq =>
      cases hWon : fst.hasWonAuth
      · simp only [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_add_query_right,
          probExpect_bind, probExpect_runWithSigBudgetPrim_query_inr]
        change probExpect
          ((pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceNoOpk P) gq).run fst) _ ≤
          probExpect sampleScalar32 (fun sk =>
            probExpect (runSigStepSim P sk budget (evalStepPrim P (stepAuthForSigPrim S) gq
                ⟨projAuthSim S P fst, k, P.sigPkGen sk, none⟩) []) _)
        have hFr : ((pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceNoOpk P) gq).run fst) =
            (pqxdhAuthWithProvImpl S P (checkBundleProvenanceNoOpk P) gq).run fst := by
          simp [pqxdhAuthWithProvFrozenImpl, freezeImpl, StateT.run_bind, StateT.run_get,
            pure_bind, hWon]
        have hR_eq : ∀ sk, evalStepPrim P (stepAuthForSigPrim S) gq
            ⟨projAuthSim S P fst, k, P.sigPkGen sk, none⟩ =
            stepAuthForSig S P gq ⟨projAuthSim S P fst, k, P.sigPkGen sk, none⟩ := by
          intro sk; have hL := validAuthSim_lengths_le S P (projAuthSim S P fst) hInv
          exact evalStepPrim_stepAuthForSigPrim S P gq _ hL.1 hL.2.1 hL.2.2 hInv.2.2.2
        rw [hFr]; simp only [hR_eq]
        let fL0 := fun x : (authSpec S).Range gq × AuthState S =>
          authFrozenBadExpect S P k (mx x.1) x.2
        let fL' := liftAuthSimFL S P fL0
        have hStepL := probExpect_liftAuthSimFL_le S P hP gq fst hInv fL0
        refine hStepL.trans (authSim_before_step S P k gq (projAuthSim S P fst) budget fL' _
          hBefore ?_ ?_)
        · intro out st' b' hBefore'; dsimp only [fL', liftAuthSimFL, fL0]
          refine iSup_le (fun ⟨fst', hproj⟩ => ?_); split_ifs with hInv'
          · subst hproj; exact ih out fst' b' hBefore' hInv'
          · exact zero_le
        · intro sk out st' s' b' msgs' hAfter'; dsimp only [fL', liftAuthSimFL, fL0]
          refine iSup_le (fun ⟨fst', hproj⟩ => ?_); split_ifs with hInv'
          · subst hproj
            exact probExpect_activeAfter_freeze_le P hP k sk (mx out) fst' s' b' msgs' hAfter' hInv'
          · exact zero_le
      · refine le_of_eq_of_le (probExpect_eq_zero_of_support _ _ (fun x hx => ?_)) zero_le
        dsimp only [pqxdhAuthWithProvFrozenImpl] at hx
        have hst := simulateQ_freezeImpl_mem_support_of_true AuthState.hasWonAuth
          (fun _ => .noneResp) (pqxdhAuthWithProvImpl S P (checkBundleProvenanceNoOpk P))
          _ fst hWon x hx
        simp [hst,
          (authSigLens S).activeBefore_badAt_eq_false P k (projAuthSim S P fst) budget hBefore]
theorem evalDist_badAt_authWithProvFrozen_noOpk_le_sigEufCmaExp (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (k : Nat) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[runAuthWithProvFrozen (checkBundleProvenanceNoOpk P) S P A.val >>= fun (_, _, finalSt) =>
      pure ((authSigLens S).badAt P k finalSt)] {true} ≤
    𝒟[sigEufCmaExp P (sigReductionAuthAt S b k A)] {true} := by
  have hNil := validEcLists_nil S
  unfold runAuthWithProvFrozen sigReductionAuthAt simulateAuthForSigPrim
  rw [evalDist_bind_true_eq_probExpect_ite, evalDist_sigEufCmaExp_simulateForSigPrim_eq]
  simp only [probExpect_bind, probExpect_pure]
  refine probExpect_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact probExpect_activeBefore_freeze_le P hP k A.val.run (AuthState.empty S secb) S.N_spk_tot
    ((authSigLens S).activeBefore_empty P k (projAuthSim S P (AuthState.empty S secb)) rfl rfl rfl)
    ⟨hNil.1, hNil.2.1, hNil.2.2.1, fun _ h => by cases h⟩
theorem auth_hop_sigEufCma_frozen_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    |(𝒟[authExpG0_1WithProvFrozen (checkBundleProvenance P) S P A.val].boolBias).toReal -
     (𝒟[authExpG1WithProvFrozen (checkBundleProvenanceExact P) S P A.val].boolBias).toReal| ≤
      (S.N_id : ℝ) * SigEufCma P (sigReductionAuth S b A) := by
  rw [authExpG0_1WithProvFrozen_orig_eq_dual, ← authExpG1WithProvFrozen_dual_eq_exact]
  have h2 : authExpG1WithProvFrozen (checkBundleProvenanceDual P) S P A.val =
      (runAuthWithProvFrozen (checkBundleProvenanceDual P) S P A.val >>= fun a =>
        if hasEcPkCollisionAuth P a.2.2 ||
           (hasBadSigAuth a.2.2 && noPrinPkColl P a.2.2.principals) then $ᵗ Bool
        else contAuth S P a) := by
    unfold authExpG1WithProvFrozen; congr 1; ext ⟨secb, b', finalSt⟩; dsimp only
    have h_or : (hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt) =
        (hasEcPkCollisionAuth P finalSt ||
          (hasBadSigAuth finalSt && noPrinPkColl P finalSt.principals)) := by
      cases hnp : noPrinPkColl P finalSt.principals; swap; · simp
      have hcoll : hasDuplicateBytes (allHonestEcPksAuth P finalSt) = true := by
        unfold allHonestEcPksAuth; simp only [HasAuthState.toAuthState, List.append_assoc]
        exact hasDuplicateBytes_append_of_left _ _ (by unfold noPrinPkColl at hnp; simpa using hnp)
      simp [hasEcPkCollisionAuth, hcoll]
    rw [h_or]
  have hAbort :
      |(𝒟[authExpG0_1WithProvFrozen (checkBundleProvenanceDual P) S P A.val].boolBias).toReal -
       (𝒟[authExpG1WithProvFrozen (checkBundleProvenanceDual P) S P A.val].boolBias).toReal| ≤
      (𝒟[runAuthWithProvFrozen (checkBundleProvenanceDual P) S P A.val >>= fun (_, _, finalSt) =>
        pure (hasBadSigAuth finalSt && noPrinPkColl P finalSt.principals)] {true}).toReal := by
    rw [h2]; exact abs_sub_boolBias_abort_or_le
      (runAuthWithProvFrozen (checkBundleProvenanceDual P) S P A.val)
      (fun (_, _, s) => hasEcPkCollisionAuth P s)
      (fun (_, _, s) => hasBadSigAuth s && noPrinPkColl P s.principals) (contAuth S P)
  have hMapDual :
      (runAuthWithProvFrozen (checkBundleProvenanceDual P) S P A.val >>= fun (_, _, finalSt) =>
        pure (hasBadSigAuth finalSt && noPrinPkColl P finalSt.principals)) =
      (runAuthWithProvFrozen (checkBundleProvenanceNoOpk P) S P A.val >>= fun (_, _, finalSt) =>
        pure ((List.range S.N_id).any (fun k => hasBadSigAuthAt S P k finalSt))) := by
    rw [runAuthWithProvFrozen_eq_map S P eraseOpkTriples
          (checkBundleProvenanceNoOpk P) (checkBundleProvenanceDual P)
          (checkBundleProvenanceNoOpk_eq_eraseOpk_dual P) A.val,
        bind_map_left]
    refine bind_congr (fun ⟨secb, b', st⟩ => ?_)
    dsimp only; rw [← hasBadSigAuth_eq_any_range S P, hasBadSigAuth_mapAuthSessions_eraseOpk]; rfl
  have hSum :
      (𝒟[runAuthWithProvFrozen (checkBundleProvenanceDual P) S P A.val >>= fun (_, _, finalSt) =>
        pure (hasBadSigAuth finalSt && noPrinPkColl P finalSt.principals)] {true}).toReal ≤
      ∑ k ∈ Finset.range S.N_id, SigEufCma P (sigReductionAuthAt S b k A) := by
    rw [hMapDual]
    refine (toReal_any_range_le_sum (runAuthWithProvFrozen (checkBundleProvenanceNoOpk P) S P A.val)
      S.N_id (fun k (_, _, finalSt) => hasBadSigAuthAt S P k finalSt)).trans ?_
    refine Finset.sum_le_sum (fun k _ => ?_)
    exact (ENNReal.toReal_le_toReal
      (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_ne_top _ _)).mpr
      (evalDist_badAt_authWithProvFrozen_noOpk_le_sigEufCmaExp S P hP b k A)
  exact (hAbort.trans hSum).trans (sum_sigReductionAuth_le S P b A)
theorem auth_hop_G0_G2_1_exact_frozen_le (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) (hCWF : CryptoWellFormedPrimitivesδ P) :
    |AuthAdvantageReal S P A.val -
     (𝒟[authExpG2_1WithProvFrozen (checkBundleProvenanceExact P) S P A.val].boolBias).toReal| ≤
      (S.N_id : ℝ) * SigEufCma P (sigReductionAuth S b A) +
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  have hG0 : AuthAdvantageReal S P A.val = (𝒟[authExpG0Frozen S P A.val].boolBias).toReal := by
    unfold AuthAdvantageReal AuthAdvantage; rw [evalDist_pqxdhAuthExp_eq_G0Frozen]
  rw [hG0]; have h0 := auth_hop_G0_G0_1_frozen_le S P hCWF A.val
  have h1 := auth_hop_sigEufCma_frozen_le S P hCWF b A
  have h2 := auth_hop_kemColl_frozen_exact_le S P hCWF A.val
  have hSendNonneg :
      ((S.N_dh * (S.N_dh - 1) : ℕ) : ℝ) ≤
        ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right _ _
  have ht1 := abs_sub_le ((𝒟[authExpG0Frozen S P A.val].boolBias).toReal)
    ((𝒟[authExpG0_1WithProvFrozen (checkBundleProvenance P) S P A.val].boolBias).toReal)
    ((𝒟[authExpG1WithProvFrozen (checkBundleProvenanceExact P) S P A.val].boolBias).toReal)
  have ht2 := abs_sub_le ((𝒟[authExpG0Frozen S P A.val].boolBias).toReal)
    ((𝒟[authExpG1WithProvFrozen (checkBundleProvenanceExact P) S P A.val].boolBias).toReal)
    ((𝒟[authExpG2_1WithProvFrozen (checkBundleProvenanceExact P) S P A.val].boolBias).toReal)
  set_option exponentiation.threshold 512 in
  linarith
def HybridRecsSub {S : Setup} (h h' : AuthHybridState S) : Prop :=
  (∀ i ∈ h.initKemRecs, i ∈ h'.initKemRecs) ∧ (∀ r ∈ h.recvKemRecs, r ∈ h'.recvKemRecs)
theorem runAuthHybridSendKosk_g3_sub (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (h : AuthHybridState S) : SatisfiesAt (HybridRecsSub h) h
      (runAuthHybridSendKosk .g3 true S P sid u bundle m0 m1) := by
  have h0 : HybridRecsSub h h := ⟨fun _ hi => hi, fun _ hr => hr⟩
  unfold runAuthHybridSendKosk; dsimp only [AuthHybridStage.idealFreshAead,
    AuthHybridStage.idealDrKey, AuthHybridStage.idealRk, AuthHybridStage.idealCk,
    AuthHybridStage.idealMsgKeys]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]; apply SatisfiesAt.get_bind
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  cases h.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => exact SatisfiesAt.pure _ _ _ h0
  | some p =>
    rcases p with ⟨_, uEntry⟩; dsimp only; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
    apply SatisfiesAt.ite_return _ _ _ _ h0; intro _; apply SatisfiesAt.liftM_bind; intro ekASk
    apply SatisfiesAt.liftM_bind; intro kemCoins; apply SatisfiesAt.liftM_bind; intro ephASk
    apply SatisfiesAt.liftM_bind; intro spqrCoins; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
    cases P.kemEncaps bundle.pqspkB kemCoins with
    | none => exact SatisfiesAt.pure _ _ _ h0
    | some kp =>
      rcases kp with ⟨ss, kemCt⟩; dsimp only; apply SatisfiesAt.liftM_bind; rintro ⟨drKey, roCache'⟩
      apply SatisfiesAt.liftM_bind; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩; dsimp only
      cases P.spqrInitSend drKey.pqrKey spqrCoins with
      | none => exact SatisfiesAt.pure _ _ _ h0
      | some spqrTriple =>
        rcases spqrTriple with ⟨_, _, _⟩; dsimp only
        refine SatisfiesAt.set_of_pres (HybridRecsSub h) _ _
          ⟨fun _ hi => List.mem_cons_of_mem _ hi, fun _ hr => hr⟩ ?_
        intro x hx; split at hx <;>
          (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx; rw [hx])
theorem pqxdhAuthHybridKoskUnfrozenImpl_hasBadKemShCrAuth_mono (S : Setup) (P : Primitives)
    (q : AuthQuery S) (h : AuthHybridState S) (x : (authSpec S).Range q × AuthHybridState S)
    (hx : x ∈ support ((pqxdhAuthHybridKoskUnfrozenImpl S P q).run h))
    (hBad : _root_.SignalPqxdh.Security.hasBadKemShCrAuth P h = true) :
    _root_.SignalPqxdh.Security.hasBadKemShCrAuth P x.2 = true := by
  have hSub : HybridRecsSub h x.2 := by
    cases q with
    | sendOPK u i bundle m0 m1 =>
      exact (SatisfiesAt.ite_return (HybridRecsSub h) h _ _ ⟨fun _ hi => hi, fun _ hr => hr⟩
        (fun _ => runAuthHybridSendKosk_g3_sub S P (.sendOPK u i) u bundle m0 m1 h)) x hx
    | sendNoOPK u i bundle m0 m1 =>
      exact (SatisfiesAt.ite_return (HybridRecsSub h) h _ _ ⟨fun _ hi => hi, fun _ hr => hr⟩
        (fun _ => runAuthHybridSendKosk_g3_sub S P (.sendNoOPK u i) u bundle m0 m1 h)) x hx
    | recvOPK k j o msg =>
      rcases pqxdhAuthHybridKoskImpl_recvOPK_step S P k j o msg h x hx with
        ⟨hInit, _, hRecv | ⟨_, _, _, _, _, hRecv⟩⟩
      · exact ⟨fun _ hi => hInit ▸ hi, fun _ hr => hRecv ▸ hr⟩
      · exact ⟨fun _ hi => hInit ▸ hi, fun _ hr => hRecv ▸ List.mem_cons_of_mem _ hr⟩
    | recvNoOPK k j l msg =>
      rcases pqxdhAuthHybridKoskImpl_recvNoOPK_step S P k j l msg h x hx with
        ⟨hInit, _, hRecv | ⟨_, _, _, _, _, hRecv⟩⟩
      · exact ⟨fun _ hi => hInit ▸ hi, fun _ hr => hRecv ▸ hr⟩
      · exact ⟨fun _ hi => hInit ▸ hi, fun _ hr => hRecv ▸ List.mem_cons_of_mem _ hr⟩
    | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
    | revealDhSecrets | registerKey _ =>
      change x ∈ support ((do
        let hst ← get; let st := hst.base
        if true && st.hasWonAuth then return AuthResponse.noneResp
        liftAuthBase (pqxdhAuthImpl true true S P _) :
          StateT (AuthHybridState S) ProbComp AuthResponse).run (clearHybridWon h)) at hx
      simp only [clearHybridWon, StateT.run_bind, StateT.run_get, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, pure_bind] at hx
      unfold liftAuthBase at hx
      simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, pure_bind, bind_assoc,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨_, _, rfl⟩
      exact ⟨fun _ hi => hi, fun _ hr => hr⟩
  unfold _root_.SignalPqxdh.Security.hasBadKemShCrAuth
    _root_.SignalPqxdh.Security.hasBadKemShCrRecords at hBad ⊢
  change h.initKemRecs.any _ = true at hBad; change x.2.initKemRecs.any _ = true
  rw [List.any_eq_true] at hBad ⊢; rcases hBad with ⟨i, hi, hBadR⟩
  rw [List.any_eq_true] at hBadR; rcases hBadR with ⟨r, hr, hPred⟩
  exact ⟨i, hSub.1 i hi, List.any_eq_true.mpr ⟨r, hSub.2 r hr, hPred⟩⟩
theorem badKemShCrProbAuth_g3_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (𝒟[runAuthKoskG3 S P A.val >>= fun (_, _, finalSt) =>
      pure (_root_.SignalPqxdh.Security.hasBadKemShCrAuth P finalSt)] {true}).toReal ≤
    badKemShCrProbAuth S P A.val := by
  refine le_trans ?_ (badKemShCrProbAuth_g3_unfrozen_le S P hP b A)
  refine (ENNReal.toReal_le_toReal
    (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_ne_top _ _)).mpr ?_
  unfold runAuthKoskG3 runAuthKoskG3Unfrozen
  rw [evalDist_bind_true_eq_probExpect_ite, evalDist_bind_true_eq_probExpect_ite]
  simp only [probExpect_bind, probExpect_pure]
  have hImplEq : pqxdhAuthHybridKoskImpl .g3 true true S P =
      freezeImpl (fun h : AuthHybridState S => h.base.hasWonAuth)
        (fun _ => .noneResp) (pqxdhAuthHybridKoskUnfrozenImpl S P) := by
    funext q; apply StateT.ext; intro h; exact pqxdhAuthHybridKoskImpl_g3_eq_freeze S P q h
  rw [hImplEq]
  refine probExpect_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have h := evalDist_simulateQ_bad_freeze_le_unfrozen
    (fun h : AuthHybridState S => h.base.hasWonAuth) (fun _ => .noneResp)
    (pqxdhAuthHybridKoskUnfrozenImpl S P) (_root_.SignalPqxdh.Security.hasBadKemShCrAuth P)
    (pqxdhAuthHybridKoskUnfrozenImpl_hasBadKemShCrAuth_mono S P)
    A.val.run (AuthHybridState.empty S secb)
  rwa [evalDist_bind_true_eq_probExpect_ite, evalDist_bind_true_eq_probExpect_ite] at h
/-- Bounds the `G0 → G3` advantage gap in terms of `sigReductionAuth` and `shcrReductionAuth`. -/
theorem auth_hop_G0_G3_le (S : Setup) :
    AuthHopG0G3Stmt S (sigReductionAuth S) (shcrReductionAuth S) := by
  intro P hP b A
  have h0_2_1 := auth_hop_G0_G2_1_exact_frozen_le S P b A hP
  have h2_1_3 := auth_hop_G2_1_exact_G3_le_prob S P hP A.val
  have hShCrProb := badKemShCrProbAuth_g3_le S P hP b A
  have hShCrRed := badKemShCrProbAuth_le_kemShCr S P hP b A
  have htri := abs_sub_le (AuthAdvantageReal S P A.val)
    ((𝒟[authExpG2_1WithProvFrozen (checkBundleProvenanceExact P) S P A.val].boolBias).toReal)
    (authFixedAdvG3 S P A.val)
  set_option exponentiation.threshold 512 in
  linarith
end Proofs.SignalPqxdh.Security
