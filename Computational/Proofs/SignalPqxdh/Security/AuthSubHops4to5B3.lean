/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5B2
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure
import Computational.Proofs.SignalPqxdh.Security.FgGapDhA -- shake: keep
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC -- shake: keep

/-!
# PQXDH authentication post-handshake sub-hops 4–5: `checkAuth` equivalence and `G5` zero bias

Shows that the `checkAuth` flag does not change `authSplitFixedExp` at receive stage `.g5`, that
the oracle is equivariant under `setSecbFixed`, and that `G5` has zero `boolBias`.
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


def badSigOrKemAuth {S : Setup} (hst : AuthHybridState S) : Bool :=
  hasBadSigAuth hst || hasKemPkCollisionAuth hst

theorem badSigOrKemAuth_of_sub {S : Setup} {hst hst' : AuthHybridState S}
    (hSess : hst.base.sessions ⊆ hst'.base.sessions)
    (hBundles : hst.base.spkBundles = hst'.base.spkBundles ∨
      ∃ x, hst'.base.spkBundles = x :: hst.base.spkBundles)
    (hBad : badSigOrKemAuth hst = true) :
    badSigOrKemAuth hst' = true := by
  unfold badSigOrKemAuth at hBad ⊢
  rcases Bool.or_eq_true_iff.mp hBad with hSig | hKem
  · apply Bool.or_eq_true_iff.mpr; left
    unfold hasBadSigAuth at hSig ⊢
    dsimp only [HasAuthState.toAuthState] at hSig ⊢
    rcases List.any_eq_true.mp hSig with ⟨x, hx, hpx⟩
    exact List.any_eq_true.mpr ⟨x, hSess hx, hpx⟩
  · apply Bool.or_eq_true_iff.mpr; right
    unfold hasKemPkCollisionAuth allHonestKemPksAuth at hKem ⊢
    dsimp only [HasAuthState.toAuthState] at hKem ⊢
    rcases hBundles with hEq | ⟨x, hCons⟩
    · rw [← hEq]; exact hKem
    · rw [hCons, List.map_cons]
      change (_ || hasDuplicateBytes _) = true
      rw [hKem, Bool.or_true]

theorem badSigOrKemAuth_evalAuthHybridSendKosk {S : Setup}
    (stage : AuthHybridStage) (useRo : Bool) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S) (hBad : badSigOrKemAuth hst = true)
    (resp : AuthResponse) (hst' : AuthHybridState S)
    (hmem : (resp, hst') ∈
      support (evalAuthHybridSendKosk stage useRo S P sid u bundle m0 m1 hst)) :
    badSigOrKemAuth hst' = true := by
  unfold evalAuthHybridSendKosk at hmem
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hBad
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h2 : (hst.base.usedSendSessions.contains sid) = true
    · simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hBad
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
      cases h3 : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [h3] at hmem
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hBad
      | some up =>
        rcases up with ⟨_, uEntry⟩
        rw [h3] at hmem; dsimp only at hmem
        rcases ite_mem_support hmem with hmem | hmem
        · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hBad
        · by_cases h5 : (!koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
            hst.base.advKeys bundle) = true
          · simp only [h5, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hBad
          · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
            rw [MonadAttach.mem_support_bind] at hmem; rcases hmem with ⟨ekASk, _, hmem⟩
            rw [MonadAttach.mem_support_bind] at hmem; rcases hmem with ⟨kemCoins, _, hmem⟩
            rw [MonadAttach.mem_support_bind] at hmem; rcases hmem with ⟨ephASk, _, hmem⟩
            rw [MonadAttach.mem_support_bind] at hmem; rcases hmem with ⟨spqrCoins, _, hmem⟩
            by_cases h6 : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
              (encodeEC bundle.spkB) bundle.spkSig &&
              P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
              (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
            · simp only [h6, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hBad
            · simp only [h6, Bool.false_eq_true, ↓reduceIte] at hmem
              cases h7 : P.kemEncaps bundle.pqspkB kemCoins with
              | none =>
                rw [h7] at hmem
                simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hBad
              | some kc =>
                rcases kc with ⟨ss, kemCt⟩
                rw [h7] at hmem; dsimp only at hmem
                rw [MonadAttach.mem_support_bind] at hmem
                rcases hmem with ⟨⟨drKey, roCache', ⟨rk1, ck1_0⟩, rootRoCache', ⟨mkSeed, ck1_1⟩⟩,
                  _, hmem⟩
                cases h8 : P.spqrInitSend drKey.pqrKey spqrCoins with
                | none =>
                  rw [h8] at hmem
                  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact hBad
                | some spqr =>
                  rcases spqr with ⟨_, spqrSalt?, pqRatchetMsg⟩
                  rw [h8] at hmem; dsimp only at hmem
                  rw [MonadAttach.mem_support_bind] at hmem
                  rcases hmem with ⟨deriveMessageKeys, _, hmem⟩
                  simp only [support_pure, Set.mem_singleton_iff] at hmem
                  have hst_eq := congrArg Prod.snd hmem
                  dsimp only at hst_eq
                  rw [hst_eq]
                  exact badSigOrKemAuth_of_sub (hst := hst)
                    (by unfold finishAuthHybridSend; exact List.subset_cons_self _ _)
                    (Or.inl rfl) hBad

theorem badSigOrKemAuth_finishAuthHybridRecvOPK {S : Setup}
    (checkAuth : Bool) (P : Primitives) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes))))
    (hBad : badSigOrKemAuth hstDec = true) :
    badSigOrKemAuth
      (finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg hstDec
        res?).2 =
      true := by
  unfold finishAuthHybridRecvOPK
  cases res? with
  | none => exact hBad
  | some r =>
    rcases r with ⟨_, _, _, _, _, _⟩; dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => exact hBad
    | some sp =>
      rcases sp with ⟨_, _⟩; dsimp only
      split_ifs <;> exact hBad

theorem badSigOrKemAuth_finishAuthHybridRecvNoOPK {S : Setup}
    (checkAuth : Bool) (P : Primitives) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes))))
    (hBad : badSigOrKemAuth hstDec = true) :
    badSigOrKemAuth
      (finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg hstDec res?).2 =
      true := by
  unfold finishAuthHybridRecvNoOPK
  cases res? with
  | none => exact hBad
  | some r =>
    rcases r with ⟨_, _, _, _, _, _⟩; dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => exact hBad
    | some sp =>
      rcases sp with ⟨_, _⟩; dsimp only
      split_ifs <;> exact hBad

theorem badSigOrKemAuth_pqxdhAuthHybridSplitKoskImpl {S : Setup}
    (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool) (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridState S) (hBad : badSigOrKemAuth hst = true)
    (resp : AuthResponse) (hst' : AuthHybridState S)
    (hmem : (resp, hst') ∈
      support ((pqxdhAuthHybridSplitKoskImpl sendStage recvStage useRo checkAuth S P q).run hst)) :
    badSigOrKemAuth hst' = true := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl at hmem
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
    unfold pqxdhAuthHybridSplitKoskImpl at hmem
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
    rw [pqxdhAuthHybridSplitKoskImpl_recvOPK_eq] at hmem
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
    rw [pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq] at hmem
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hBad }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : useRo = true <;> (simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hBad)

theorem badSigOrKemAuth_fullSplitFixedImpl_g5 {S : Setup}
    (sendStage : AuthHybridStage) (useRo checkAuth : Bool) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridStateFixed S)
    (hBad : badSigOrKemAuth hst.toAuthHybridState = true)
    (x : (unifSpec + authSpec S).Range q × AuthHybridStateFixed S)
    (hmem : x ∈
      support ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S)
        ProbComp) +
        pqxdhAuthHybridSplitFixedImpl sendStage .g5 useRo checkAuth S P) q).run hst)) :
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
      support ((pqxdhAuthHybridSplitFixedImpl sendStage .g5 useRo checkAuth S P kq).run hst) at hmem
    have hIdeal : (AuthHybridStage.g5).idealMsgKeys = true := rfl
    have hApply := badSigOrKemAuth_pqxdhAuthHybridSplitKoskImpl sendStage .g5 useRo checkAuth P kq
      hst.toAuthHybridState hBad
    cases kq with
    | recvOPK k j o msg =>
      clear hApply
      unfold pqxdhAuthHybridSplitFixedImpl at hmem
      simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind, pqxdhAuthHybridFixedImpl_recvOPK_eq .g5 hIdeal] at hmem
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
      unfold pqxdhAuthHybridSplitFixedImpl at hmem
      simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind, pqxdhAuthHybridFixedImpl_recvNoOPK_eq .g5 hIdeal] at hmem
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
      unfold pqxdhAuthHybridSplitFixedImpl at hmem
      simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, StateT.run_monadLift, StateT.run_set, StateT.run_pure, bind_assoc,
        pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨r0, hst0⟩, hmem0, _, rfl⟩
      exact hApply r0 hst0 hmem0

theorem evalDist_simulateQ_bad_eq_uniformBool {ι α St : Type} {QSpec : OracleSpec.{0, 0} ι}
    (bad : St → Bool) (full : QueryImpl (unifSpec + QSpec) (StateT St ProbComp))
    (hPres : ∀ q st, bad st = true → ∀ x ∈ support ((full q).run st), bad x.2 = true)
    (fin : α × St → ProbComp Bool)
    (hFin : ∀ a st, bad st = true → 𝒟[fin (a, st)] = 𝒟[$ᵗ Bool])
    (oa : OracleComp (unifSpec + QSpec) α) (st : St) (hbad : bad st = true) :
    𝒟[(simulateQ full oa).run st >>= fin] = 𝒟[$ᵗ Bool] := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hFin a st hbad
  | query_bind q t ih =>
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    calc 𝒟[(full q).run st >>= fun x => (simulateQ full (t x.1)).run x.2 >>= fin]
      _ = 𝒟[(full q).run st >>= fun _ => ($ᵗ Bool : ProbComp Bool)] := by
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun x hx => ?_
          exact ih x.1 x.2 (hPres q st hbad x hx)
      _ = 𝒟[$ᵗ Bool] := OracleComp.evalDist_bind_const _ _

theorem evalDist_simulateQ_resetWonAuthFixed_g5 {S : Setup} {α : Type}
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
      pqxdhAuthHybridSplitFixedImpl sendStage .g5 true true S P
    let fullF := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthHybridStateFixed S) ProbComp) +
      pqxdhAuthHybridSplitFixedImpl sendStage .g5 true false S P
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
        (badSigOrKemAuth_fullSplitFixedImpl_g5 sendStage true true P)
        finT hFinBadT (query q >>= t) st hBad
      have hR := evalDist_simulateQ_bad_eq_uniformBool
        (fun s => badSigOrKemAuth s.toAuthHybridState) fullF
        (badSigOrKemAuth_fullSplitFixedImpl_g5 sendStage true false P)
        finF hFinBadF (query q >>= t) (resetWonAuthFixed st) hBad
      exact hL.trans hR.symm
    · have hBadF : badSigOrKemAuth st.toAuthHybridState = false := Bool.eq_false_iff.mpr hBad
      have hBadParts := Bool.or_eq_false_iff.mp hBadF
      have hNoWin : st.toAuthHybridState.base.hasWonAuth = false :=
        hInv.no_false_win hBadParts.1 hBadParts.2
      rw [simulateQ_bind, StateT.run_bind, bind_assoc,
          simulateQ_bind, StateT.run_bind, bind_assoc]
      simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      rw [← map_resetWonAuthFixed_fullSplitFixedImpl sendStage .g5 true true S P q st hNoWin,
          bind_map_left]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun ⟨u, stMid⟩ hmem => ?_
      have hInvMid : AuthCleanSessionInv P S stMid.toAuthHybridState :=
        authCleanSessionInv_fullSplitFixedImpl_g5 sendStage true true P hWF q st hInv u stMid hmem
      exact ih u stMid hInvMid

theorem authSplitFixedExp_g5_checkAuth_eq (sendStage : AuthHybridStage)
    (S : Setup) (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (A : AuthAdversary S) :
    𝒟[authSplitFixedExp sendStage .g5 true S P A] =
      𝒟[authSplitFixedExp sendStage .g5 false S P A] := by
  unfold authSplitFixedExp
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun secb _ => ?_
  dsimp only
  have hsim := evalDist_simulateQ_resetWonAuthFixed_g5 sendStage P hWF
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

def setSecb (b : Bool) {S : Setup} (hst : AuthHybridState S) : AuthHybridState S :=
  { hst with base := { hst.base with secb := b } }

def setSecbFixed (b : Bool) {S : Setup} (hst : AuthHybridStateFixed S) : AuthHybridStateFixed S :=
  { hst with toAuthHybridState := setSecb b hst.toAuthHybridState }

@[simp]
theorem setSecb_empty (b : Bool) (S : Setup) (secb : Bool) :
    setSecb b (AuthHybridState.empty S secb) = AuthHybridState.empty S b := rfl

@[simp]
theorem setSecbFixed_empty (b : Bool) (S : Setup) (secb : Bool) :
    setSecbFixed b (AuthHybridStateFixed.empty S secb) = AuthHybridStateFixed.empty S b := rfl

theorem map_ite_eq {α β : Type} (f : α → β) (c : Bool) (t1 e1 : ProbComp α) (t2 e2 : ProbComp β)
    (ht : f <$> t1 = t2) (he : f <$> e1 = e2) :
    f <$> (if c then t1 else e1) = (if c then t2 else e2) := by
  cases c <;> [exact he; exact ht]

theorem evalAuthHybridSendKosk_g5_setSecb (b useRo : Bool)
    (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S) :
    Prod.map id (setSecb b) <$>
        evalAuthHybridSendKosk .g5 useRo S P sid u bundle m0 m1 hst =
      evalAuthHybridSendKosk .g5 useRo S P sid u bundle m0 m1 (setSecb b hst) := by
  unfold evalAuthHybridSendKosk
  have hb_used : (setSecb b hst).base.usedSendSessions = hst.base.usedSendSessions := rfl
  have hb_princ : (setSecb b hst).base.principals = hst.base.principals := rfl
  have hb_spk : (setSecb b hst).base.spkBundles = hst.base.spkBundles := rfl
  have hb_opk : (setSecb b hst).base.opkEntries = hst.base.opkEntries := rfl
  have hb_adv : (setSecb b hst).base.advKeys = hst.base.advKeys := rfl
  have hb_ro : (setSecb b hst).base.roCache = hst.base.roCache := rfl
  have hb_rro : (setSecb b hst).base.rootRoCache = hst.base.rootRoCache := rfl
  dsimp only [AuthHybridStage.idealFreshAead, ↓reduceIte, ite_self]
  rw [hb_used, hb_princ, hb_spk, hb_opk, hb_adv, hb_ro, hb_rro]
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte, map_pure]; rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.base.usedSendSessions.contains sid) = true
    · simp only [h2, ↓reduceIte, map_pure]; rfl
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp only [map_pure]; rfl
      | some up =>
        rcases up with ⟨_, uEntry⟩
        dsimp only
        apply map_ite_eq
        · simp only [map_pure]; rfl
        · by_cases h4 : (!koskBundleOk P hst.base.principals hst.base.spkBundles
                           hst.base.opkEntries hst.base.advKeys bundle) = true
          · simp only [h4, ↓reduceIte, map_pure]; rfl
          · simp only [h4, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp,
              bind_assoc]
            congr 1; funext ekASk; congr 1; funext kemCoins
            congr 1; funext ephASk; congr 1; funext spqrCoins
            by_cases h5 : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                              (encodeEC bundle.spkB) bundle.spkSig &&
                             P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                              (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
            · simp only [h5, ↓reduceIte, pure_bind]; rfl
            · simp only [h5, Bool.false_eq_true, ↓reduceIte]
              cases P.kemEncaps bundle.pqspkB kemCoins with
              | none => dsimp only; simp only [pure_bind]; rfl
              | some sc =>
                rcases sc with ⟨ss, kemCt⟩
                dsimp only
                simp only [bind_assoc]
                congr 1; funext ⟨drKey, roCache', ⟨rk1, ck1_0⟩, rootRoCache', ⟨mkSeed, ck1_1⟩⟩
                cases P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => dsimp only; simp only [pure_bind]; rfl
                | some pqr =>
                  rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                  dsimp only
                  simp only [bind_assoc]
                  congr 1

theorem finishAuthHybridRecvOPK_setSecb (b checkAuth : Bool) {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × UInt32 × UInt32 × Bytes))
    (msg : PreKeyMsg) (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
                    List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    Prod.map id (setSecb b)
      (finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg hstDec res?)
        =
    finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg (setSecb b
      hstDec) res? := by
  unfold finishAuthHybridRecvOPK setSecb
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some sp =>
      rcases sp with ⟨_, senderEntry⟩
      dsimp only
      split_ifs <;> rfl

theorem finishAuthHybridRecvNoOPK_setSecb (b checkAuth : Bool) {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × UInt32 × UInt32 × Bytes))
    (msg : PreKeyMsg) (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
                    List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    Prod.map id (setSecb b)
      (finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg hstDec res?) =
    finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg (setSecb b hstDec)
      res? := by
  unfold finishAuthHybridRecvNoOPK setSecb
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some sp =>
      rcases sp with ⟨_, senderEntry⟩
      dsimp only
      split_ifs <;> rfl

theorem prepareAuthHybridRecvOPK_setSecb (b checkAuth : Bool) {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    prepareAuthHybridRecvOPK checkAuth P k j o msg (setSecb b hst) =
      (prepareAuthHybridRecvOPK checkAuth P k j o msg hst).map (fun prep =>
        { prep with
          hstDec := setSecb b prep.hstDec
          finish := fun res? => Prod.map id (setSecb b) (prep.finish res?) }) := by
  unfold prepareAuthHybridRecvOPK
  have hb_used : (setSecb b hst).base.usedRecvOPK = hst.base.usedRecvOPK := rfl
  have hb_princ : (setSecb b hst).base.principals = hst.base.principals := rfl
  have hb_adv : (setSecb b hst).base.advKeys = hst.base.advKeys := rfl
  have hb_spk : (setSecb b hst).base.spkBundles = hst.base.spkBundles := rfl
  have hb_opk : (setSecb b hst).base.opkEntries = hst.base.opkEntries := rfl
  have hb_kyber : (setSecb b hst).base.seenKyberBaseKeys = hst.base.seenKyberBaseKeys := rfl
  have hb_rec : (setSecb b hst).recvKemRecs = hst.recvKemRecs := rfl
  have hb_won : (setSecb b hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
  have hb_ideal : (setSecb b hst).idealSessions = hst.idealSessions := rfl
  dsimp only
  rw [hb_won, hb_used, hb_princ, hb_adv, hb_spk, hb_opk, hb_kyber, hb_rec, hb_ideal]
  by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
  { simp only [h0, ↓reduceIte, Option.map] }
  simp only [h0, Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                   msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
                   msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 &&
                   msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, Option.map]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [h2, ↓reduceIte, Option.map]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, Option.map]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => rfl
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => rfl
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            cases hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
            | none => rfl
            | some op =>
              rcases op with ⟨_, oEntry⟩
              dsimp only
              by_cases h4 : oEntry.consumed = true
              · simp only [h4, ↓reduceIte, Option.map]
              · simp only [h4, Bool.false_eq_true, ↓reduceIte]
                by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                  msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                               !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                · simp only [h5, ↓reduceIte, Option.map]
                · simp only [h5, Bool.false_eq_true, ↓reduceIte]
                  cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none => rfl
                  | some ss =>
                    dsimp only [Option.map]
                    congr 1; congr 1
                    funext res?
                    exact (finishAuthHybridRecvOPK_setSecb b checkAuth P k j o kEntry bEntry oEntry
                      (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                        msg.hdr.spkId msg.hdr.ekAPk).2
                      msg { hst with recvKemRecs := _ :: hst.recvKemRecs } res?).symm

theorem prepareAuthHybridRecvNoOPK_setSecb (b checkAuth : Bool) {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    prepareAuthHybridRecvNoOPK checkAuth P k j l msg (setSecb b hst) =
      (prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst).map (fun prep =>
        { prep with
          hstDec := setSecb b prep.hstDec
          finish := fun res? => Prod.map id (setSecb b) (prep.finish res?) }) := by
  unfold prepareAuthHybridRecvNoOPK
  have hb_used : (setSecb b hst).base.usedRecvNoOPK = hst.base.usedRecvNoOPK := rfl
  have hb_princ : (setSecb b hst).base.principals = hst.base.principals := rfl
  have hb_adv : (setSecb b hst).base.advKeys = hst.base.advKeys := rfl
  have hb_spk : (setSecb b hst).base.spkBundles = hst.base.spkBundles := rfl
  have hb_kyber : (setSecb b hst).base.seenKyberBaseKeys = hst.base.seenKyberBaseKeys := rfl
  have hb_rec : (setSecb b hst).recvKemRecs = hst.recvKemRecs := rfl
  have hb_won : (setSecb b hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
  have hb_ideal : (setSecb b hst).idealSessions = hst.idealSessions := rfl
  dsimp only
  rw [hb_won, hb_used, hb_princ, hb_adv, hb_spk, hb_kyber, hb_rec, hb_ideal]
  by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
  { simp only [h0, ↓reduceIte, Option.map] }
  simp only [h0, Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                   msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == none &&
                   msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 &&
                   msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, Option.map]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    · simp only [h2, ↓reduceIte, Option.map]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, Option.map]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => rfl
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => rfl
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            dsimp only
            by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
              msg.hdr.spkId msg.hdr.ekAPk).1 ||
                           !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
            · simp only [h5, ↓reduceIte, Option.map]
            · simp only [h5, Bool.false_eq_true, ↓reduceIte]
              cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none => rfl
              | some ss =>
                dsimp only [Option.map]
                congr 1; congr 1
                funext res?
                exact (finishAuthHybridRecvNoOPK_setSecb b checkAuth P k j l kEntry bEntry
                  (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                    msg.hdr.spkId msg.hdr.ekAPk).2
                  msg { hst with recvKemRecs := _ :: hst.recvKemRecs } res?).symm

theorem evalAuthHybridRecvSchedule_setSecb (b : Bool) {S : Setup}
    (stage : AuthHybridStage) (useRo : Bool) (P : Primitives)
    (hst : AuthHybridState S) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) :
    evalAuthHybridRecvSchedule stage useRo P (setSecb b hst) kEntry bEntry opkPk? secrets msg =
      evalAuthHybridRecvSchedule stage useRo P hst kEntry bEntry opkPk? secrets msg := rfl

theorem evalAuthFixedRecvScheduleCached_setSecb (b : Bool) {S : Setup}
    (stage : AuthHybridStage) (useRo : Bool) (P : Primitives)
    (hst : AuthHybridState S) (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) :
    evalAuthFixedRecvScheduleCached stage useRo P (setSecb b hst) recvCount mkSaltCache
      kEntry bEntry opkPk? secrets msg =
      evalAuthFixedRecvScheduleCached stage useRo P hst recvCount mkSaltCache
        kEntry bEntry opkPk? secrets msg := rfl

theorem map_setSecb_pqxdhAuthHybridSplitKoskImpl_g5
    (b : Bool) (recvStage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) (q : AuthQuery S) (hst : AuthHybridState S) :
    Prod.map id (setSecb b) <$>
        ((pqxdhAuthHybridSplitKoskImpl .g5 recvStage useRo checkAuth S P q).run hst) =
      (pqxdhAuthHybridSplitKoskImpl .g5 recvStage useRo checkAuth S P q).run (setSecb b hst) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl
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
    unfold pqxdhAuthHybridSplitKoskImpl
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
    rw [pqxdhAuthHybridSplitKoskImpl_recvOPK_eq, pqxdhAuthHybridSplitKoskImpl_recvOPK_eq,
      prepareAuthHybridRecvOPK_setSecb b checkAuth]
    cases prepareAuthHybridRecvOPK checkAuth P k j o msg hst with
    | none => simp [Prod.map]
    | some prep =>
      simp only [Option.map, evalAuthHybridRecvSchedule_setSecb, Functor.map_map]
  | recvNoOPK k j l msg =>
    rw [pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq, pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq,
      prepareAuthHybridRecvNoOPK_setSecb b checkAuth]
    cases prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst with
    | none => simp [Prod.map]
    | some prep =>
      simp only [Option.map, evalAuthHybridRecvSchedule_setSecb, Functor.map_map]
  | initPrin u =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
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
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
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

theorem map_setSecbFixed_fullSplitFixedImpl_g5
    (b : Bool) (recvStage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridStateFixed S) :
    Prod.map id (setSecbFixed b) <$>
        ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S)
          ProbComp) +
          pqxdhAuthHybridSplitFixedImpl .g5 recvStage useRo checkAuth S P) q).run hst) =
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
        pqxdhAuthHybridSplitFixedImpl .g5 recvStage useRo checkAuth S P) q).run
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
        ((pqxdhAuthHybridSplitFixedImpl .g5 recvStage useRo checkAuth S P kq).run hst) =
      (pqxdhAuthHybridSplitFixedImpl .g5 recvStage useRo checkAuth S P kq).run
        (setSecbFixed b hst)
    have hto : (setSecbFixed b hst).toAuthHybridState = setSecb b hst.toAuthHybridState := rfl
    have hrc : (setSecbFixed b hst).recvCount = hst.recvCount := rfl
    have hmc : (setSecbFixed b hst).mkSaltCache = hst.mkSaltCache := rfl
    by_cases hIdeal : recvStage.idealMsgKeys = true
    · have hSend :=
        map_setSecb_pqxdhAuthHybridSplitKoskImpl_g5 b .g5 useRo checkAuth S P kq
          hst.toAuthHybridState
      rw [pqxdhAuthHybridSplitKoskImpl_same] at hSend
      cases kq with
      | recvOPK k j o msg =>
        clear hSend
        unfold pqxdhAuthHybridSplitFixedImpl
        simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          StateT.run_get, pure_bind,
          pqxdhAuthHybridFixedImpl_recvOPK_eq recvStage hIdeal, hto, hrc, hmc,
          prepareAuthHybridRecvOPK_setSecb b checkAuth]
        cases prepareAuthHybridRecvOPK checkAuth P k j o msg hst.toAuthHybridState with
        | none => simp [Prod.map, setSecbFixed]
        | some prep =>
          simp [ Option.map, evalAuthFixedRecvScheduleCached_setSecb, Functor.map_map, Prod.map,
              setSecbFixed]
      | recvNoOPK k j l msg =>
        clear hSend
        unfold pqxdhAuthHybridSplitFixedImpl
        simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          StateT.run_get, pure_bind,
          pqxdhAuthHybridFixedImpl_recvNoOPK_eq recvStage hIdeal, hto, hrc, hmc,
          prepareAuthHybridRecvNoOPK_setSecb b checkAuth]
        cases prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst.toAuthHybridState with
        | none => simp [Prod.map, setSecbFixed]
        | some prep =>
          simp [ Option.map, evalAuthFixedRecvScheduleCached_setSecb, Functor.map_map, Prod.map,
              setSecbFixed]
      | sendOPK u i bundle m0 m1 | sendNoOPK u i bundle m0 m1 | initPrin u | corruptIK u
      | genSPK u j | genOPK u j o | registerKey sk | roQuery secrets | roRootQuery rk dh |
        revealDhSecrets =>
        unfold pqxdhAuthHybridSplitFixedImpl
        simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          StateT.run_get,
          StateT.run_monadLift, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
        rw [hto, hrc, hmc, ← hSend]
        simp [ map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map,
            setSecbFixed]
    · have hIdealF : recvStage.idealMsgKeys = false := Bool.eq_false_iff.mpr hIdeal
      unfold pqxdhAuthHybridSplitFixedImpl
      simp only [hIdealF, Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get,
        StateT.run_monadLift, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      have h :=
        map_setSecb_pqxdhAuthHybridSplitKoskImpl_g5 b recvStage useRo checkAuth S P kq
          hst.toAuthHybridState
      rw [hto, hrc, hmc, ← h]
      simp [ map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map,
          setSecbFixed]

theorem evalDist_uniformBool_beq_local (b : Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun z => pure (b == z)] = 𝒟[($ᵗ Bool : ProbComp Bool)] := by
  cases b
  · simpa using ProbComp.evalDist_bind_not_uniformBool (fun z => (pure z : ProbComp Bool))
  · simp

theorem evalDist_authSplitFixedExp_g5_g5_false_eq_authFixedExpG5
    (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    𝒟[authSplitFixedExp .g5 .g5 false S P A] = 𝒟[authFixedExpG5 S P A] := by
  unfold authSplitFixedExp authFixedExpG5 authFixedIdealBranch
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun secb _ => ?_
  simp only [ite_self, bind_assoc, pqxdhAuthHybridSplitFixedImpl_same]
  have hsim := _root_.Proofs.SignalPqxdh.Security.map_proj_simulateQ
    (setSecbFixed secb)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
      pqxdhAuthHybridFixedImpl .g5 true false S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
      pqxdhAuthHybridFixedImpl .g5 true false S P)
    (fun q hst => by simpa only [pqxdhAuthHybridSplitFixedImpl_same] using
      map_setSecbFixed_fullSplitFixedImpl_g5 secb .g5 true false S P q hst)
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

theorem authSplitFixedExp_g5_g5_false_boolBias_eq_zero
    (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    (𝒟[authSplitFixedExp .g5 .g5 false S P A].boolBias).toReal = 0 := by
  rw [evalDist_authSplitFixedExp_g5_g5_false_eq_authFixedExpG5]
  exact authFixedAdvG5_eq_zero S P A

theorem evalDist_authSplitFixedExp_g5_g5_true_eq_authFixedExpG5
    (S : Setup) (P : Primitives) (hWF : WellFormedPrimitivesδ P) (A : AuthAdversary S) :
    𝒟[authSplitFixedExp .g5 .g5 true S P A] = 𝒟[authFixedExpG5 S P A] := by
  rw [authSplitFixedExp_g5_checkAuth_eq .g5 S P hWF A]
  exact evalDist_authSplitFixedExp_g5_g5_false_eq_authFixedExpG5 S P A

theorem authSplitFixedExp_g5_g5_true_boolBias_eq_zero
    (S : Setup) (P : Primitives) (hWF : WellFormedPrimitivesδ P) (A : AuthAdversary S) :
    (𝒟[authSplitFixedExp .g5 .g5 true S P A].boolBias).toReal = 0 := by
  rw [authSplitFixedExp_g5_checkAuth_eq .g5 S P hWF A]
  exact authSplitFixedExp_g5_g5_false_boolBias_eq_zero S P A

end SignalPqxdh.Security
