/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.RoKemHopB
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ProbabilityTheory ENNReal
open scoped BigOperators
open SignalPqxdh SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security

theorem pqxdhKeyIndShCrCachedImpl_pauseSome (S : Setup) (P : Primitives) (bIdx sIdx : Nat) (pk sk :
  Bytes)
    (gq : KeyIndQuery S) (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec +
      keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (paused : PausedShCrKem S (KeyIndState S))
    (hV : ValidTargetRecv KeyIndState.spkBundles bIdx pk sk hst)
    (hSome : tryPauseKeyIndQuery S P sIdx gq cont hst = some paused) :
    ∃ (noneOut : (keyIndSpec S).Range gq)
      (postKem : Bytes → Bytes → ProbComp ((keyIndSpec S).Range gq × KeyIndShCrState S)),
      (∀ ss ct, paused.resume ss ct =
        (postKem ss ct >>= fun y =>
          (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (KeyIndShCrState S) ProbComp) +
              pqxdhKeyIndShCrCachedImpl true S P) (cont y.1)).run y.2)) ∧
      (∀ obs : (keyIndSpec S).Range gq × KeyIndShCrState S → ProbComp Bool,
        𝒟[(pqxdhKeyIndShCrCachedImpl true S P gq).run hst >>= obs] =
        𝒟[sampleCoins32 >>= fun r =>
          match P.kemEncaps paused.bundle.pqspkB r with
          | none => obs (noneOut, { hst with sendCount := sIdx + 1 })
          | some (ss, ct) => postKem ss ct >>= obs]) ∧
      (∀ ss ct, ∀ y ∈ support (postKem ss ct),
        ValidTargetRecv KeyIndState.spkBundles bIdx pk sk y.2 ∧
        sIdx < y.2.sendCount ∧
        (∀ i ∈ y.2.initKemRecs, i ∈ hst.initKemRecs ∨
          (i.sendIdx = sIdx ∧
           i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss))) := by
  cases gq with
  | initiateOPK u i bundle =>
    dsimp only [tryPauseKeyIndQuery] at hSome
    rw [show pqxdhKeyIndShCrCachedImpl true S P (.initiateOPK u i bundle) =
      (if bundle.opkB?.isNone then pure .noneResp else runKeyIndShCrInitiate true S P (.sendOPK u i)
        u bundle) from rfl]
    cases hopk : bundle.opkB?.isNone
    · rw [hopk] at hSome
      simp only [Bool.false_eq_true, ↓reduceIte] at hSome ⊢
      exact runShCrInitiate2_pauseSome P KeyIndState.principals KeyIndState.spkBundles
        (pqxdhKeyIndShCrCachedImpl true S P) KeyIndResponse.noneResp (preCheckKeyInd S P (.sendOPK u
          i) u bundle)
        (.sendOPK u i) bundle (finishKeyIndBase S P (.sendOPK u i) bundle)
        bIdx sIdx pk sk cont hst paused
        (fun uInfo ekASk ss kemCt out hout =>
          finishKeyIndBase_spkBundles S P (.sendOPK u i) bundle uInfo ekASk ss kemCt hst.base out
          hout)
        hV hSome
    · rw [hopk] at hSome; simp at hSome
  | initiateNoOPK u i bundle =>
    dsimp only [tryPauseKeyIndQuery] at hSome
    rw [show pqxdhKeyIndShCrCachedImpl true S P (.initiateNoOPK u i bundle) =
      (if bundle.opkB?.isSome then pure .noneResp else runKeyIndShCrInitiate true S P (.sendNoOPK u
        i) u bundle) from rfl]
    cases hopk : bundle.opkB?.isSome
    · rw [hopk] at hSome
      simp only [Bool.false_eq_true, ↓reduceIte] at hSome ⊢
      exact runShCrInitiate2_pauseSome P KeyIndState.principals KeyIndState.spkBundles
        (pqxdhKeyIndShCrCachedImpl true S P) KeyIndResponse.noneResp (preCheckKeyInd S P (.sendNoOPK
          u i) u bundle)
        (.sendNoOPK u i) bundle (finishKeyIndBase S P (.sendNoOPK u i) bundle)
        bIdx sIdx pk sk cont hst paused
        (fun uInfo ekASk ss kemCt out hout =>
          finishKeyIndBase_spkBundles S P (.sendNoOPK u i) bundle uInfo ekASk ss kemCt hst.base out
          hout)
        hV hSome
    · rw [hopk] at hSome; simp at hSome
  | genSPK u j => cases hSome
  | acceptOPK k j o hdr => cases hSome
  | acceptNoOPK k j l hdr => cases hSome
  | initPrin u => cases hSome
  | corruptIK u => cases hSome
  | genOPK u j o => cases hSome
  | testSession sid => cases hSome
  | roQuery secrets => cases hSome
  | revealDhSecrets => cases hSome
  | revealSessionKey sid => cases hSome
  | registerKey sk => cases hSome
  | revealSpkSk u j => cases hSome

theorem badKemShCrProbKeyIndAt_le_kemShCrProb (S : Setup) (P : Primitives)
    (idx : Nat) (A : KeyIndAdversary S) :
    badKemShCrProbKeyIndAt S P idx A ≤
      (𝒟[kemShCrExpProb P (shcrChoosePkKeyIndAt S P (idx / S.N_send_tot) (idx % S.N_send_tot) A)]
        {true}).toReal := by
  unfold badKemShCrProbKeyIndAt shcrChoosePkKeyIndAt
  have hEq :
      (runKeyIndShCrSim S P A >>= fun (_, _, finalHst) =>
        pure (hasBadKemShCrRecordsAt S P idx finalHst.initKemRecs finalHst.recvKemRecs)) =
      (($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb)) >>= fun b0 =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndShCrState S) ProbComp) +
            pqxdhKeyIndShCrCachedImpl false S P) A.run).run { base := b0 } >>= fun x =>
        pure (hasBadKemShCrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)) := by
    unfold runKeyIndShCrSim
    simp only [bind_assoc, pure_bind]
    refine bind_congr (fun secb => ?_)
    have hSim := CommutesRel.simulateQ_add_unif (cacheShCrAdvKeys S P)
      (pqxdhKeyIndShCrCachedImpl false S P) (pqxdhKeyIndShCrImpl false S P)
      (pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P)
      A.run { base := KeyIndState.empty S secb }
    unfold CommutesRel at hSim
    have hInit : cacheShCrAdvKeys S P { base := KeyIndState.empty S secb } =
        { base := KeyIndState.empty S secb } := rfl
    rw [hInit] at hSim
    rw [hSim, bind_map_left]
    rfl
  rw [hEq]
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  exact badKemShCrProbGenericAt_le_kemShCr P
    ($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb))
    KeyIndState.spkBundles
    (pqxdhKeyIndShCrCachedImpl false S P)
    (pqxdhKeyIndShCrCachedImpl true S P)
    (tryPauseKeyIndQuery S P)
    idx
    (by
      intro b0 hb0
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hb0
      rcases hb0 with ⟨secb, _, rfl⟩
      rfl)
    (pqxdhKeyIndShCrCachedImpl_clearFalse S P)
    (pqxdhKeyIndShCrCachedImpl_afterGen S P (idx / S.N_send_tot))
    (pqxdhKeyIndShCrCachedImpl_beforeGen S P (idx / S.N_send_tot))
    (pqxdhKeyIndShCrCachedImpl_validStep S P (idx / S.N_send_tot))
    (pqxdhKeyIndShCrCachedImpl_sendStep S P)
    (pqxdhKeyIndShCrCachedImpl_pauseNone S P (idx % S.N_send_tot))
    (pqxdhKeyIndShCrCachedImpl_pauseSome S P (idx / S.N_send_tot) (idx % S.N_send_tot))
    A.run

theorem map_base_runKeyIndShCrInitiate_false (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (hst : KeyIndShCrState S) :
    (Prod.map id ShCrState.base <$>
      (runKeyIndShCrInitiate false S P sid u bundle).run hst) =
      (runKeyIndInitiate true S P sid u bundle).run hst.base := by
  rw [show (runKeyIndShCrInitiate false S P sid u bundle).run hst =
    runShCrInitiate2 P KeyIndState.principals KeyIndResponse.noneResp
      (preCheckKeyInd S P sid u bundle) sid bundle (finishKeyIndBase S P sid bundle) hst from rfl]
  unfold runShCrInitiate2 preCheckKeyInd checkBundleSigs finishKeyIndBase applyShCrFinish
    runKeyIndInitiate
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hsid : hst.base.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hfind : List.find? (fun x => x.1 == u.val) hst.base.principals with
    | none => simp [StateT.run_pure, Prod.map]
    | some uPair =>
      rcases uPair with ⟨fst, uEntry⟩
      dsimp only
      cases hkosk : (!koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
        hst.base.advKeys bundle)
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, map_bind, bind_assoc, pure_bind]
        apply bind_congr; intro ekASk
        apply bind_congr; intro kemCoins
        cases hsig : (P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeEC
          bundle.spkB) bundle.spkSig &&
            P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM bundle.pqspkB)
              bundle.pqspkSig)
        · simp [StateT.run_pure, Prod.map]
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases hkem : P.kemEncaps bundle.pqspkB kemCoins with
          | none => simp [StateT.run_pure, Prod.map]
          | some kemPair =>
            rcases kemPair with ⟨ss, kemCt⟩
            dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind, bind_assoc,
              pure_bind]
            apply bind_congr; intro roOut
            rcases roOut with ⟨drKeyReal, roCache'⟩
            dsimp only
            cases keyIndPartnerRandKey? P hst.base.respSessions _ with
            | some k =>
              dsimp only
              simp only [StateT.run_bind, map_pure]
              cases findHonestPrincipal P hst.base.principals bundle.ikB <;>
                simp [StateT.run_set, StateT.run_pure, Prod.map]
            | none =>
              dsimp only
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind,
                bind_assoc, pure_bind]
              apply bind_congr; intro drKeyRand
              cases findHonestPrincipal P hst.base.principals bundle.ikB <;>
                simp [StateT.run_set, StateT.run_pure, Prod.map]
      · simp [StateT.run_pure, Prod.map]
  · simp [StateT.run_pure, Prod.map]

theorem map_base_pqxdhKeyIndShCrImpl_false (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) :
    (Prod.map id ShCrState.base <$>
      (pqxdhKeyIndShCrImpl false S P q).run hst) =
      (pqxdhKeyIndImpl true S P q).run hst.base := by
  cases q with
  | genSPK u j =>
    exact map_base_liftShCrBase (pqxdhKeyIndImpl true S P (.genSPK u j)) hst
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndShCrImpl pqxdhKeyIndImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact map_base_runKeyIndShCrInitiate_false S P (.sendOPK u i) u bundle hst
    · simp [StateT.run_pure, Prod.map]
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndShCrImpl pqxdhKeyIndImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact map_base_runKeyIndShCrInitiate_false S P (.sendNoOPK u i) u bundle hst
    · simp [StateT.run_pure, Prod.map]
  | acceptOPK k j o hdr =>
    exact map_base_runShCrAcceptGeneric P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndImpl true S P (.acceptOPK k j o hdr)) k j hdr hst
  | acceptNoOPK k j l hdr =>
    exact map_base_runShCrAcceptGeneric P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndImpl true S P (.acceptNoOPK k j l hdr)) k j hdr hst
  | initPrin u => exact map_base_liftShCrBase (pqxdhKeyIndImpl true S P (.initPrin u)) hst
  | corruptIK u => exact map_base_liftShCrBase (pqxdhKeyIndImpl true S P (.corruptIK u)) hst
  | genOPK u j o => exact map_base_liftShCrBase (pqxdhKeyIndImpl true S P (.genOPK u j o)) hst
  | testSession sid => exact map_base_liftShCrBase (pqxdhKeyIndImpl true S P (.testSession sid)) hst
  | roQuery bytes => exact map_base_liftShCrBase (pqxdhKeyIndImpl true S P (.roQuery bytes)) hst
  | revealDhSecrets => exact map_base_liftShCrBase (pqxdhKeyIndImpl true S P .revealDhSecrets) hst
  | revealSessionKey sid =>
    exact map_base_liftShCrBase (pqxdhKeyIndImpl true S P (.revealSessionKey sid)) hst
  | registerKey sk => exact map_base_liftShCrBase (pqxdhKeyIndImpl true S P (.registerKey sk)) hst
  | revealSpkSk u j => exact map_base_liftShCrBase (pqxdhKeyIndImpl true S P (.revealSpkSk u j)) hst

/-! ## Hybrid games and base-state projection -/

theorem kemCollProbKeyInd_le (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : KeyIndAdversary S) :
    kemCollProbKeyInd useRo S P A ≤ ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 :=
  _root_.SignalPqxdh.Security.kemCollProbKeyInd_le_bound useRo S P hP A

theorem map_base_fullKeyIndShCrImpl_false (S : Setup) (P : Primitives)
    (q : (unifSpec + keyIndSpec S).Domain) (hst : KeyIndShCrState S) :
    (Prod.map id ShCrState.base <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyIndShCrImpl false S P) q).run hst) =
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndState S) ProbComp) + pqxdhKeyIndImpl true S P) q).run hst.base := by
  cases q with
  | inl uq =>
    simp [QueryImpl.liftTarget, StateT.run_monadLift]
  | inr kq =>
    exact map_base_pqxdhKeyIndShCrImpl_false S P kq hst

noncomputable def badKemShCrProbKeyInd (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyIndShCrSim S P A >>= fun (_, _, finalHst) =>
    pure (hasBadKemShCrRecords S P finalHst.initKemRecs finalHst.recvKemRecs)] {true}).toReal

noncomputable abbrev keyIndExpG2_5 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool :=
  _root_.SignalPqxdh.Security.keyIndExpG2_1 S P A

noncomputable abbrev keyIndAdvG2_5 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  _root_.SignalPqxdh.Security.keyIndAdvG2_1 S P A

noncomputable def keyIndExpG2_5ShCr (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool := do
  let (secb, b', finalHst) ← runKeyIndShCrSim S P A
  let finalSt := finalHst.base
  let allTestedClean :=
    finalSt.sessions.all (fun s =>
      !s.tested || isKeyIndInitStillFresh P true finalSt.principals finalSt.spkBundles
        finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested || isKeyIndRespStillFresh P true finalSt.principals finalSt.spkBundles
        finalSt.sessions r)
  if ((!allTestedClean || hasEcPkCollisionKeyInd P finalSt) || hasBadSigKeyInd finalSt) ||
     hasKemPkCollisionKeyInd finalSt then
    let coin ← $ᵗ Bool
    return coin
  else
    return (b' == secb)

noncomputable def keyIndAdvG2_5ShCr (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyIndExpG2_5ShCr S P A].boolBias).toReal

noncomputable def keyIndExpG3 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool := do
  let (secb, b', finalHst) ← runKeyIndShCrSim S P A
  let finalSt := finalHst.base
  let allTestedClean :=
    finalSt.sessions.all (fun s =>
      !s.tested || isKeyIndInitStillFresh P true finalSt.principals finalSt.spkBundles
        finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested || isKeyIndRespStillFresh P true finalSt.principals finalSt.spkBundles
        finalSt.sessions r)
  if (((!allTestedClean || hasEcPkCollisionKeyInd P finalSt) || hasBadSigKeyInd finalSt) ||
      hasKemPkCollisionKeyInd finalSt) ||
     hasBadKemShCrRecords S P finalHst.initKemRecs finalHst.recvKemRecs then
    let coin ← $ᵗ Bool
    return coin
  else
    return (b' == secb)

noncomputable def keyIndAdvG3 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyIndExpG3 S P A].boolBias).toReal

theorem keyInd_hop_kemColl_le_prob (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    |keyIndAdvG2 S P A - keyIndAdvG2_5 S P A| ≤ kemCollProbKeyInd true S P A :=
  _root_.SignalPqxdh.Security.keyInd_hop_G2_G2_1_le_prob S P A

theorem keyInd_hop_badKemShCr_le_prob (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    |keyIndAdvG2_5ShCr S P A - keyIndAdvG3 S P A| ≤ badKemShCrProbKeyInd S P A := by
  unfold keyIndAdvG2_5ShCr keyIndAdvG3 keyIndExpG2_5ShCr keyIndExpG3 badKemShCrProbKeyInd
  exact abs_sub_boolBias_abort_or_le (runKeyIndShCrSim S P A)
    (fun (_, _, finalHst) =>
      ((!(finalHst.base.sessions.all (fun s =>
            !s.tested || isKeyIndInitStillFresh P true finalHst.base.principals
              finalHst.base.spkBundles finalHst.base.respSessions s) &&
          finalHst.base.respSessions.all (fun r =>
            !r.tested || isKeyIndRespStillFresh P true finalHst.base.principals
              finalHst.base.spkBundles finalHst.base.sessions r)) ||
       hasEcPkCollisionKeyInd P finalHst.base) ||
       hasBadSigKeyInd finalHst.base) ||
       hasKemPkCollisionKeyInd finalHst.base)
    (fun (_, _, finalHst) => hasBadKemShCrRecords S P finalHst.initKemRecs finalHst.recvKemRecs)
    (fun (secb, b', _) => pure (b' == secb))

theorem badKemShCrProbKeyInd_le_sum (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    badKemShCrProbKeyInd S P A ≤
      ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot), badKemShCrProbKeyIndAt S P idx A := by
  unfold badKemShCrProbKeyInd badKemShCrProbKeyIndAt hasBadKemShCrRecords
  exact toReal_any_range_le_sum (runKeyIndShCrSim S P A) (S.N_spk_tot * S.N_send_tot)
    (fun idx (_, _, finalHst) =>
      hasBadKemShCrRecordsAt S P idx finalHst.initKemRecs finalHst.recvKemRecs)

theorem keyIndExpG2_5ShCr_eq (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    keyIndExpG2_5ShCr S P A = keyIndExpG2_5 S P A := by
  unfold keyIndExpG2_5ShCr keyIndExpG2_5 _root_.SignalPqxdh.Security.keyIndExpG2_1
    _root_.SignalPqxdh.Security.keyIndExpG2_1Core runKeyIndShCrSim
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro secb
  have hsim := map_proj_simulateQ ShCrState.base
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyIndShCrImpl false S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndState S) ProbComp) + pqxdhKeyIndImpl true S P)
    (map_base_fullKeyIndShCrImpl_false S P)
    A.run { base := KeyIndState.empty S secb }
  rw [← hsim, bind_map_left]
  rfl

theorem keyIndAdvG2_5_eq_ShCr (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    keyIndAdvG2_5 S P A = keyIndAdvG2_5ShCr S P A := by
  unfold keyIndAdvG2_5 _root_.SignalPqxdh.Security.keyIndAdvG2_1 keyIndAdvG2_5ShCr
  rw [keyIndExpG2_5ShCr_eq]

def bundleSlotIndex (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv) : Nat :=
  u.val * S.N_recv + j.val

theorem bundleSlotIndex_lt (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv) :
    bundleSlotIndex S u j < S.N_spk_tot := by
  unfold bundleSlotIndex Setup.N_spk_tot
  have hu : u.val + 1 ≤ S.N_id := u.isLt
  have hj : j.val < S.N_recv := j.isLt
  calc
    u.val * S.N_recv + j.val < u.val * S.N_recv + S.N_recv := Nat.add_lt_add_left hj _
    _ = (u.val + 1) * S.N_recv := by ring
    _ ≤ S.N_id * S.N_recv := Nat.mul_le_mul_right S.N_recv hu

theorem sessionSlotIndex_lt {S : Setup} (sid : SessionId S)
    (h : IsSendSessionId S sid := by trivial) :
    sessionSlotIndex sid < S.N_send_tot :=
  sessSlotFlatIdx_lt S sid h

/-! ## Black-box `KemShCr` reduction and `G2 → G3` bound -/

theorem finishKeyIndBase_validKeyIndEc (S : Setup) (P : Primitives)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (bundle : PreKeyBundleInput) (uEntry : PrincipalEntry)
    (ekASk ss kemCt : Bytes) (st : KeyIndState S)
    (hV : ValidKeyIndEcC S P st)
    (hFresh : st.sessions.any (fun e => e.sid == sid) = false)
    (out : KeyIndResponse × Option (KeyIndState S))
    (hout : out ∈ support (finishKeyIndBase S P sid bundle uEntry ekASk ss kemCt st)) :
    ∀ base', out.2 = some base' → ValidKeyIndEcC S P base' := by
  intro base' hbase
  rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hAdv, hR⟩
  have hFresh' : ((sessPksKeyInd S st).map Prod.fst).any (fun s => s == sid) = false := by
    simpa [sessPksKeyInd, List.any_map, Function.comp_def] using hFresh
  have hCons :=
    (validSessionIds_cons S sid ((sessPksKeyInd S st).map Prod.fst) hSend hVSess hFresh').1
  unfold finishKeyIndBase at hout
  dsimp only at hout
  simp only [MonadAttach.mem_support_bind] at hout
  rcases hout with ⟨⟨drKeyReal, roCache'⟩, _, hout⟩
  dsimp only at hout
  split at hout
  · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hout
    subst hout; injection hbase with h; subst h
    refine ⟨⟨hVP, hVS, hVO, ?_⟩, hAdv, hR⟩
    simpa [sessPksKeyInd] using hCons
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨drKeyRand, _, rfl⟩
    injection hbase with h; subst h
    refine ⟨⟨hVP, hVS, hVO, ?_⟩, hAdv, hR⟩
    simpa [sessPksKeyInd] using hCons

theorem postKem2_validKeyIndEc_and_recvKemRecs (S : Setup) (P : Primitives)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (bundle : PreKeyBundleInput) (uEntry : PrincipalEntry)
    (hst : KeyIndShCrState S) (ss kemCt : Bytes)
    (hV : ValidKeyIndEcC S P hst.base)
    (hFresh : hst.base.sessions.any (fun e => e.sid == sid) = false) :
    ∀ y ∈ support (postKem2 sid bundle uEntry (finishKeyIndBase S P sid bundle) hst ss kemCt),
      ValidKeyIndEcC S P y.2.base ∧ y.2.recvKemRecs = hst.recvKemRecs := by
  intro y hy
  unfold postKem2 at hy
  simp only [MonadAttach.mem_support_bind, support_map, Set.mem_image] at hy
  rcases hy with ⟨ekASk, _, out, hout, rfl⟩
  rcases out with ⟨resp, none | base'⟩
  · exact ⟨hV, rfl⟩
  · exact ⟨finishKeyIndBase_validKeyIndEc S P sid hSend bundle uEntry ekASk ss kemCt hst.base hV
    hFresh (resp, some base') hout base' rfl, rfl⟩

theorem pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs (embedTarget : Bool) (S : Setup) (P
  : Primitives)
    (gq : KeyIndQuery S) (hst : KeyIndShCrState S) (hV : ValidKeyIndEcC S P hst.base) :
    ∀ x ∈ support ((pqxdhKeyIndShCrCachedImpl embedTarget S P gq).run hst),
      ValidKeyIndEcC S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + 1 := by
  intro x hx
  cases gq with
  | genSPK u j =>
    dsimp only [pqxdhKeyIndShCrCachedImpl, runKeyIndShCrGenSPK, runShCrGenSPKGeneric,
      StateT.run] at hx
    have hBase : ∀ x ∈ support ((liftShCrBase (genSpkBaseGeneric P KeyIndState.principals
      KeyIndState.spkBundles
        (fun st bs => { st with spkBundles :=
          bs }) KeyIndResponse.noneResp KeyIndResponse.bundleResp u j)).run hst),
        ValidKeyIndEcC S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + 1 := by
      intro x hx
      simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hx
      rcases hx with ⟨y, hy, rfl⟩
      refine ⟨?_, by simp⟩
      rcases mem_support_genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
        (fun st bs => { st with spkBundles :=
          bs }) KeyIndResponse.noneResp KeyIndResponse.bundleResp u j hst.base y hy with
        rfl | ⟨uEntry, spkSk, rSpk, pqspkPk, pqspkSk, rPq, hFresh, rfl⟩
      · exact hV
      · exact ⟨⟨hV.1.1, (validSpkBundles_cons S u j _ hst.base.spkBundles hV.1.2.1 hFresh).1,
        hV.1.2.2.1, hV.1.2.2.2⟩, hV.2⟩
    have hTarget : ∀ x ∈ support ((genSpkTargetGeneric P KeyIndState.principals
      KeyIndState.spkBundles
        (fun st bs => { st with spkBundles :=
          bs }) KeyIndResponse.noneResp KeyIndResponse.bundleResp u j).run hst),
        ValidKeyIndEcC S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + 1 := by
      intro x hx
      rcases mem_support_genSpkTargetGeneric P KeyIndState.principals KeyIndState.spkBundles
        (fun st bs => { st with spkBundles :=
          bs }) KeyIndResponse.noneResp KeyIndResponse.bundleResp u j hst x hx with
        rfl | ⟨uEntry, spkSk, rSpk, rPq, hFresh, rfl⟩
      · exact ⟨hV, by simp⟩
      · exact ⟨⟨⟨hV.1.1, (validSpkBundles_cons S u j _ hst.base.spkBundles hV.1.2.1 hFresh).1,
        hV.1.2.2.1, hV.1.2.2.2⟩, hV.2⟩, by simp⟩
    revert hx
    cases embedTarget
    · exact hBase x
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hst.targetBIdx? with
      | none => exact hBase x
      | some bIdx =>
        dsimp only
        split_ifs
        · exact hTarget x
        · exact hBase x
  | initiateOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrCachedImpl] at hx
    split_ifs at hx with hopk
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨hV, by simp⟩
    · rcases mem_support_runShCrInitiate2 P KeyIndState.principals KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
        (finishKeyIndBase S P (.sendOPK u i) bundle) hst x hx with
        ⟨rfl, _⟩ | ⟨uEntry, hPre, _, rfl | ⟨ekASk, ss, kemCt, out, hout, rfl⟩⟩
      · exact ⟨hV, by simp⟩
      · exact ⟨hV, by simp⟩
      · have hFresh : hst.base.sessions.any (fun e => e.sid == .sendOPK u i) = false := by
          unfold preCheckKeyInd at hPre
          cases h : hst.base.sessions.any (fun e => e.sid == .sendOPK u i)
          · rfl
          · rw [h] at hPre; simp at hPre
        rcases out with ⟨resp, none | base'⟩
        · exact ⟨hV, by simp [applyShCrFinish]⟩
        · exact ⟨finishKeyIndBase_validKeyIndEc S P (.sendOPK u i) trivial bundle uEntry ekASk ss
          kemCt hst.base hV hFresh (resp, some base') hout base' rfl, by simp [applyShCrFinish]⟩
  | initiateNoOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrCachedImpl] at hx
    split_ifs at hx with hopk
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨hV, by simp⟩
    · rcases mem_support_runShCrInitiate2 P KeyIndState.principals KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
        (finishKeyIndBase S P (.sendNoOPK u i) bundle) hst x hx with
        ⟨rfl, _⟩ | ⟨uEntry, hPre, _, rfl | ⟨ekASk, ss, kemCt, out, hout, rfl⟩⟩
      · exact ⟨hV, by simp⟩
      · exact ⟨hV, by simp⟩
      · have hFresh : hst.base.sessions.any (fun e => e.sid == .sendNoOPK u i) = false := by
          unfold preCheckKeyInd at hPre
          cases h : hst.base.sessions.any (fun e => e.sid == .sendNoOPK u i)
          · rfl
          · rw [h] at hPre; simp at hPre
        rcases out with ⟨resp, none | base'⟩
        · exact ⟨hV, by simp [applyShCrFinish]⟩
        · exact ⟨finishKeyIndBase_validKeyIndEc S P (.sendNoOPK u i) trivial bundle uEntry ekASk ss
          kemCt hst.base hV hFresh (resp, some base') hout base' rfl, by simp [applyShCrFinish]⟩
  | acceptOPK k j o hdr =>
    dsimp only [pqxdhKeyIndShCrCachedImpl] at hx
    unfold runShCrAcceptGeneric at hx
    simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hx
    rcases hx with ⟨y, hy, hx⟩
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hVz :=
      pqxdhKeyIndCachedImpl_validKeyIndEcC_step true S P (.acceptOPK k j o hdr) hst.base hV z hz
    rcases mem_support_recordAcceptKemGeneric P KeyIndState.spkBundles isNoneKeyIndResp k j hdr z.1
      { hst with base := z.2 } x hx with
      rfl | ⟨_, _, _, _, _, rfl⟩
    · exact ⟨hVz, by simp⟩
    · exact ⟨hVz, by simp⟩
  | acceptNoOPK k j l hdr =>
    dsimp only [pqxdhKeyIndShCrCachedImpl] at hx
    unfold runShCrAcceptGeneric at hx
    simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hx
    rcases hx with ⟨y, hy, hx⟩
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hVz :=
      pqxdhKeyIndCachedImpl_validKeyIndEcC_step true S P (.acceptNoOPK k j l hdr) hst.base hV z hz
    rcases mem_support_recordAcceptKemGeneric P KeyIndState.spkBundles isNoneKeyIndResp k j hdr z.1
      { hst with base := z.2 } x hx with
      rfl | ⟨_, _, _, _, _, rfl⟩
    · exact ⟨hVz, by simp⟩
    · exact ⟨hVz, by simp⟩
  | initPrin u =>
    dsimp only [pqxdhKeyIndShCrCachedImpl, liftKeyIndShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhKeyIndCachedImpl_validKeyIndEcC_step true S P (.initPrin u) hst.base hV z hz,
      by simp⟩
  | corruptIK u =>
    dsimp only [pqxdhKeyIndShCrCachedImpl, liftKeyIndShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhKeyIndCachedImpl_validKeyIndEcC_step true S P (.corruptIK u) hst.base hV z hz,
      by simp⟩
  | genOPK u j o =>
    dsimp only [pqxdhKeyIndShCrCachedImpl, liftKeyIndShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhKeyIndCachedImpl_validKeyIndEcC_step true S P (.genOPK u j o) hst.base hV z hz,
      by simp⟩
  | testSession sid =>
    dsimp only [pqxdhKeyIndShCrCachedImpl, liftKeyIndShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhKeyIndCachedImpl_validKeyIndEcC_step true S P (.testSession sid) hst.base hV z hz,
      by simp⟩
  | revealSessionKey sid =>
    dsimp only [pqxdhKeyIndShCrCachedImpl, liftKeyIndShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhKeyIndCachedImpl_validKeyIndEcC_step true S P (.revealSessionKey sid) hst.base hV z
      hz, by simp⟩
  | roQuery secrets =>
    dsimp only [pqxdhKeyIndShCrCachedImpl, liftKeyIndShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhKeyIndCachedImpl_validKeyIndEcC_step true S P (.roQuery secrets) hst.base hV z hz,
      by simp⟩
  | revealDhSecrets =>
    dsimp only [pqxdhKeyIndShCrCachedImpl, liftKeyIndShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhKeyIndCachedImpl_validKeyIndEcC_step true S P .revealDhSecrets hst.base hV z hz,
      by simp⟩
  | registerKey sk =>
    dsimp only [pqxdhKeyIndShCrCachedImpl, liftKeyIndShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhKeyIndCachedImpl_validKeyIndEcC_step true S P (.registerKey sk) hst.base hV z hz,
      by simp⟩
  | revealSpkSk u j =>
    dsimp only [pqxdhKeyIndShCrCachedImpl, liftKeyIndShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhKeyIndCachedImpl_validKeyIndEcC_step true S P (.revealSpkSk u j) hst.base hV z hz,
      by simp⟩

theorem simulateQ_liftShCrBasePrim {S : Setup} {Base α : Type} (P : Primitives)
    (m : StateT Base (OracleComp PrimBaseSpec) α)
    (mP : StateT Base ProbComp α)
    (hst : ShCrState S Base)
    (hm : simulateQ (primBaseImpl P) (m.run hst.base) = mP.run hst.base) :
    simulateQ (primBaseImpl P) ((liftShCrBasePrim m).run hst) =
      (liftShCrBase mP).run hst := by
  unfold liftShCrBasePrim liftShCrBase StateT.run
  simp only [simulateQ_bind, simulateQ_pure, hm]

theorem simulateQ_recordAcceptKemGenericPrim {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (out : Resp) (hst : ShCrState S Base) :
    simulateQ (primBaseImpl P) ((recordAcceptKemGenericPrim getBundles isNoneResp k j hdr out).run
      hst) =
      (recordAcceptKemGeneric P getBundles isNoneResp k j hdr out).run hst := by
  dsimp only [recordAcceptKemGenericPrim, recordAcceptKemGeneric, StateT.run]
  split_ifs
  · rfl
  · cases (getBundles hst.base).find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => rfl
    | some bp =>
      rcases bp with ⟨_, bEntry⟩
      dsimp only
      rw [simulateQ_bind, simulateQ_primQ_kemDecaps, pure_bind]
      cases P.kemDecaps bEntry.pqspkSk hdr.kemCt <;> rfl

theorem simulateQ_runKeyIndShCrAcceptPrim (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr) (gq : KeyIndQuery S)
    (hst : KeyIndShCrState S) (hV : ValidKeyIndEcC S P hst.base) :
    simulateQ (primBaseImpl P) ((runKeyIndShCrAcceptPrim S k j hdr gq).run hst) =
      (runShCrAcceptGeneric P KeyIndState.spkBundles isNoneKeyIndResp
        (pqxdhKeyIndCachedImpl true S P gq) k j hdr).run hst := by
  rcases validKeyIndEc_lengths_le S P hst.base hV.1 with ⟨hPrin, hSpk, hOpk, hSess⟩
  unfold runKeyIndShCrAcceptPrim runShCrAcceptGeneric
  simp only [StateT.run_bind, simulateQ_bind,
    simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhKeyIndImplPrim true S P hP gq hst.base hPrin hSpk hOpk hSess
        (validKeyIndResp_length_le S hst.base hV.2.2) hV.2.1)]
  congr 1; ext x
  exact simulateQ_recordAcceptKemGenericPrim P KeyIndState.spkBundles isNoneKeyIndResp k j hdr x.1
    x.2

theorem simulateQ_genSpkTargetKeyIndPrim (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : KeyIndShCrState S) :
    simulateQ (primBaseImpl P) ((genSpkTargetKeyIndPrim S u j).run hst) =
      (genSpkTargetGeneric P KeyIndState.principals KeyIndState.spkBundles
        (fun st bs => { st with spkBundles := bs })
        KeyIndResponse.noneResp KeyIndResponse.bundleResp u j).run hst := by
  dsimp only [genSpkTargetKeyIndPrim, genSpkTargetGeneric, StateT.run]
  split_ifs
  · rfl
  · cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => rfl
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      simp only [simulateQ_bind, simulateQ_embedUnif, mkSpkBundlePair]
      congr 1

theorem simulateQ_runKeyIndShCrGenSPKPrim (embedTarget : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : KeyIndShCrState S)
    (hV : ValidKeyIndEcC S P hst.base) :
    simulateQ (primBaseImpl P) ((runKeyIndShCrGenSPKPrim embedTarget S u j).run hst) =
      (runKeyIndShCrGenSPK embedTarget S P u j).run hst := by
  rcases validKeyIndEc_lengths_le S P hst.base hV.1 with ⟨hPrin, hSpk, hOpk, hSess⟩
  dsimp only [runKeyIndShCrGenSPKPrim, runKeyIndShCrGenSPK, runShCrGenSPKGeneric, StateT.run]
  have hBase :
      simulateQ (primBaseImpl P) ((liftShCrBasePrim (pqxdhKeyIndImplPrim true S (.genSPK u j))).run
        hst) =
      (liftShCrBase (genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
        (fun st bs => { st with spkBundles :=
          bs }) KeyIndResponse.noneResp KeyIndResponse.bundleResp u j)).run hst := by
    rw [simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhKeyIndImplPrim true S P hP (.genSPK u j) hst.base hPrin hSpk hOpk hSess
        (validKeyIndResp_length_le S hst.base hV.2.2) hV.2.1)]
    rfl
  split_ifs
  · exact hBase
  · cases hst.targetBIdx? with
    | none => exact hBase
    | some bIdx =>
      dsimp only
      split_ifs
      · exact simulateQ_genSpkTargetKeyIndPrim S P u j hst
      · exact hBase

theorem simulateQ_preCheckKeyIndPrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : KeyIndState S)
    (hV : ValidKeyIndEcC S P st) :
    simulateQ (primBaseImpl P) (preCheckKeyIndPrim S sid u bundle st) =
      pure (preCheckKeyInd S P sid u bundle st) := by
  rcases validKeyIndEc_lengths_le S P st hV.1 with ⟨hPrin, hSpk, hOpk, _⟩
  unfold preCheckKeyIndPrim preCheckKeyInd
  cases st.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => rfl
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      rw [simulateQ_bind,
          simulateQ_koskBundleOkPrim S P st.principals st.spkBundles st.opkEntries st.advKeys bundle
            hPrin hSpk hOpk hV.2.1,
          pure_bind]
      split_ifs <;> rfl
  · rfl

theorem simulateQ_checkBundleSigsPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (bundle : PreKeyBundleInput)
    (hPrin : principals.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) (checkBundleSigsPrim S principals bundle) =
      pure (checkBundleSigs P principals bundle) := by
  unfold checkBundleSigsPrim checkBundleSigs
  rw [simulateQ_bind, simulateQ_resolveSigPkPrim S P principals bundle.ikB hPrin, pure_bind]
  rfl

theorem simulateQ_finishKeyIndBasePrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (uEntry : PrincipalEntry)
    (ekASk ss kemCt : Bytes) (st : KeyIndState S)
    (hV : ValidKeyIndEcC S P st) :
    simulateQ (primBaseImpl P) (finishKeyIndBasePrim S sid bundle uEntry ekASk ss kemCt st) =
      finishKeyIndBase S P sid bundle uEntry ekASk ss kemCt st := by
  rcases validKeyIndEc_lengths_le S P st hV.1 with ⟨hPrin, hSpk, hOpk, _⟩
  have hResp := validKeyIndResp_length_le S st hV.2.2
  unfold finishKeyIndBasePrim finishKeyIndBase
  simp only [simulateQ_bind]
  rw [simulateQ_primQ_x25519Base, pure_bind,
      simulateQ_primQ_x25519, pure_bind,
      simulateQ_primQ_x25519, pure_bind,
      simulateQ_primQ_x25519, pure_bind,
      simulateQ_primQ_x25519, pure_bind]
  have h_dh4 : (bundle.opkB?.map (fun _ => P.x25519 ekASk (bundle.opkB?.map Prod.snd |>.getD []))) =
      bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk) := by
    cases bundle.opkB? <;> rfl
  rw [h_dh4, simulateQ_evalHkdfOrRoPrim]
  congr 1; ext ⟨drKeyReal, roCache'⟩
  rw [simulateQ_isHonestUncorruptedPeerPrim S P st.principals bundle.ikB hPrin, pure_bind,
      simulateQ_checkBundleProvenancePrim S P st.principals st.spkBundles st.opkEntries bundle hPrin
        hSpk hOpk, pure_bind,
      List.take_of_length_le hResp,
      simulateQ_findMPrim P _ (fun r => keyIndPartner P _ r) (fun r =>
        simulateQ_keyIndPartnerPrim P _ r) st.respSessions,
      pure_bind]
  unfold keyIndPartnerRandKey?
  cases st.respSessions.find? (fun r => keyIndPartner P _ r) with
  | some r =>
    dsimp only [Option.map]
    simp only [pure_bind, simulateQ_bind, simulateQ_pure]
    rw [simulateQ_findHonestPrincipalPrim S P st.principals bundle.ikB hPrin, pure_bind]
    rfl
  | none =>
    dsimp only [Option.map]
    simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_pure]
    congr 1; ext drKeyRand
    rw [simulateQ_findHonestPrincipalPrim S P st.principals bundle.ikB hPrin, pure_bind]
    rfl

theorem simulateQ_postKemKeyIndPrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (uEntry : PrincipalEntry)
    (hst : KeyIndShCrState S) (ss kemCt : Bytes)
    (hV : ValidKeyIndEcC S P hst.base) :
    simulateQ (primBaseImpl P) (postKemKeyIndPrim S sid bundle uEntry hst ss kemCt) =
      postKem2 sid bundle uEntry (finishKeyIndBase S P sid bundle) hst ss kemCt := by
  unfold postKemKeyIndPrim postKem2
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_embedUnif,
    simulateQ_finishKeyIndBasePrim S P sid bundle uEntry _ ss kemCt hst.base hV,
    map_eq_bind_pure_comp]
  rfl

theorem simulateQ_runKeyIndShCrInitiatePrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (hst : KeyIndShCrState S) (hV : ValidKeyIndEcC S P hst.base) :
    simulateQ (primBaseImpl P) ((runKeyIndShCrInitiatePrim S sid u bundle).run hst) =
      (runKeyIndShCrInitiate true S P sid u bundle).run hst := by
  rcases validKeyIndEc_lengths_le S P hst.base hV.1 with ⟨hPrin, _, _, _⟩
  dsimp only [runKeyIndShCrInitiatePrim, runKeyIndShCrInitiate, runShCrInitiate2, StateT.run]
  rw [simulateQ_bind, simulateQ_preCheckKeyIndPrim S P sid u bundle hst.base hV, pure_bind]
  cases preCheckKeyInd S P sid u bundle hst.base with
  | none => rfl
  | some uEntry =>
    dsimp only
    simp only [simulateQ_bind, simulateQ_embedUnif]
    congr 1; ext ekASk
    congr 1; ext kemCoins
    rw [simulateQ_checkBundleSigsPrim S P hst.base.principals bundle hPrin, pure_bind]
    split_ifs
    · rfl
    · rw [simulateQ_bind, simulateQ_primQ_kemEncaps, pure_bind]
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => rfl
      | some sc =>
        rcases sc with ⟨ss, kemCt⟩
        dsimp only
        rw [simulateQ_bind,
          simulateQ_finishKeyIndBasePrim S P sid bundle uEntry ekASk ss kemCt hst.base hV,
            map_eq_bind_pure_comp]
        rfl

theorem simulateQ_pqxdhKeyIndShCrPrimImpl (embedTarget : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (gq : KeyIndQuery S) (hst : KeyIndShCrState S)
    (hV : ValidKeyIndEcC S P hst.base) :
    simulateQ (primBaseImpl P) ((pqxdhKeyIndShCrPrimImpl embedTarget S gq).run hst) =
      (pqxdhKeyIndShCrCachedImpl embedTarget S P gq).run hst := by
  rcases validKeyIndEc_lengths_le S P hst.base hV.1 with ⟨hPrin, hSpk, hOpk, hSess⟩
  cases gq with
  | genSPK u j => exact simulateQ_runKeyIndShCrGenSPKPrim embedTarget S P hP u j hst hV
  | initiateOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrPrimImpl, pqxdhKeyIndShCrCachedImpl]
    split_ifs
    · rfl
    · exact simulateQ_runKeyIndShCrInitiatePrim S P (.sendOPK u i) u bundle hst hV
  | initiateNoOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrPrimImpl, pqxdhKeyIndShCrCachedImpl]
    split_ifs
    · rfl
    · exact simulateQ_runKeyIndShCrInitiatePrim S P (.sendNoOPK u i) u bundle hst hV
  | acceptOPK k j o hdr =>
    exact simulateQ_runKeyIndShCrAcceptPrim S P hP k j hdr (.acceptOPK k j o hdr) hst hV
  | acceptNoOPK k j l hdr =>
    exact simulateQ_runKeyIndShCrAcceptPrim S P hP k j hdr (.acceptNoOPK k j l hdr) hst hV
  | initPrin u =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhKeyIndImplPrim true S P hP (.initPrin u) hst.base hPrin hSpk hOpk hSess
        (validKeyIndResp_length_le S hst.base hV.2.2) hV.2.1)
  | corruptIK u =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhKeyIndImplPrim true S P hP (.corruptIK u) hst.base hPrin hSpk hOpk hSess
        (validKeyIndResp_length_le S hst.base hV.2.2) hV.2.1)
  | genOPK u j o =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhKeyIndImplPrim true S P hP (.genOPK u j o) hst.base hPrin hSpk hOpk hSess
        (validKeyIndResp_length_le S hst.base hV.2.2) hV.2.1)
  | testSession sid =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhKeyIndImplPrim true S P hP (.testSession sid) hst.base hPrin hSpk hOpk hSess
        (validKeyIndResp_length_le S hst.base hV.2.2) hV.2.1)
  | revealSessionKey sid =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhKeyIndImplPrim true S P hP (.revealSessionKey sid) hst.base hPrin hSpk hOpk
        hSess (validKeyIndResp_length_le S hst.base hV.2.2) hV.2.1)
  | roQuery secrets =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhKeyIndImplPrim true S P hP (.roQuery secrets) hst.base hPrin hSpk hOpk hSess
        (validKeyIndResp_length_le S hst.base hV.2.2) hV.2.1)
  | revealDhSecrets =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhKeyIndImplPrim true S P hP .revealDhSecrets hst.base hPrin hSpk hOpk hSess
        (validKeyIndResp_length_le S hst.base hV.2.2) hV.2.1)
  | registerKey sk =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhKeyIndImplPrim true S P hP (.registerKey sk) hst.base hPrin hSpk hOpk hSess
        (validKeyIndResp_length_le S hst.base hV.2.2) hV.2.1)
  | revealSpkSk u j =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhKeyIndImplPrim true S P hP (.revealSpkSk u j) hst.base hPrin hSpk hOpk hSess
        (validKeyIndResp_length_le S hst.base hV.2.2) hV.2.1)

theorem simulateQ_isWinningKemShCrCtPrim (P : Primitives) (pk sk chosenPk ct ss candCt : Bytes) :
    simulateQ (primBaseImpl P) (isWinningKemShCrCtPrim pk sk chosenPk ct ss candCt) =
      pure (isWinningKemShCrCt P pk sk chosenPk ct ss candCt) := rfl

theorem simulateQ_extractCollidingKemCtPrim (N : ℕ) (P : Primitives)
    (pk sk chosenPk ct ss : Bytes) (recvRecs : List RecvKemRecord)
    (hLen : recvRecs.length ≤ N) :
    simulateQ (primBaseImpl P) (extractCollidingKemCtPrim N pk sk chosenPk ct ss recvRecs) =
      pure (extractCollidingKemCt P pk sk chosenPk ct ss recvRecs) := by
  unfold extractCollidingKemCtPrim extractCollidingKemCt
  rw [List.take_of_length_le hLen, simulateQ_bind,
      simulateQ_findMPrim P _ (fun r => isWinningKemShCrCt P pk sk chosenPk ct ss r.kemCt)
        (fun r => simulateQ_isWinningKemShCrCtPrim P pk sk chosenPk ct ss r.kemCt) recvRecs,
      pure_bind]
  cases recvRecs.find? (fun r => isWinningKemShCrCt P pk sk chosenPk ct ss r.kemCt) <;> rfl

noncomputable def PausedShCrData.toPaused {S : Setup} (P : Primitives)
    (d : PausedShCrData S) : PausedShCrKem S (KeyIndState S) where
  bundle := d.bundle
  resume := fun ss kemCt =>
    postKem2 d.sid d.bundle d.uEntry (finishKeyIndBase S P d.sid d.bundle) d.hst ss kemCt >>= fun y
      =>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) +
          pqxdhKeyIndShCrCachedImpl true S P) (d.cont y.1)).run y.2

noncomputable abbrev _root_.SignalPqxdh.Security.RoKem.PausedShCrData.toPaused {S : Setup} (P :
  Primitives)
    (d : PausedShCrData S) : PausedShCrKem S (KeyIndState S) :=
  PausedShCrData.toPaused P d

@[simp] theorem PausedShCrData.toPaused_bundle {S : Setup} (P : Primitives)
    (d : PausedShCrData S) : (PausedShCrData.toPaused P d).bundle = d.bundle := rfl

noncomputable def tryPauseKeyIndQueryData (S : Setup) (P : Primitives)
    (sIdx : Nat) (gq : KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) : Option (PausedShCrData S) :=
  match gq, cont with
  | .initiateOPK u i bundle, cont =>
    if bundle.opkB?.isNone then none
    else
      match preCheckKeyInd S P (.sendOPK u i) u bundle hst.base with
      | none => none
      | some uEntry =>
        if !checkBundleSigs P hst.base.principals bundle then none
        else if hst.sendCount == sIdx then
          some { sid := .sendOPK u i, bundle := bundle, uEntry := uEntry, hst := hst, cont := cont }
        else none
  | .initiateNoOPK u i bundle, cont =>
    if bundle.opkB?.isSome then none
    else
      match preCheckKeyInd S P (.sendNoOPK u i) u bundle hst.base with
      | none => none
      | some uEntry =>
        if !checkBundleSigs P hst.base.principals bundle then none
        else if hst.sendCount == sIdx then
          some { sid := .sendNoOPK u i, bundle := bundle, uEntry := uEntry, hst := hst, cont :=
            cont }
        else none
  | _, _ => none

theorem simulateQ_tryPauseKeyIndQueryPrim (S : Setup) (P : Primitives) (sIdx : Nat) (gq :
  KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S)
    (hV : ValidKeyIndEcC S P hst.base) :
    simulateQ (primBaseImpl P) (tryPauseKeyIndQueryPrim S sIdx gq cont hst) =
      pure (tryPauseKeyIndQueryData S P sIdx gq cont hst) := by
  rcases validKeyIndEc_lengths_le S P hst.base hV.1 with ⟨hPrin, _, _, _⟩
  cases gq with
  | initiateOPK u i bundle =>
    dsimp only [tryPauseKeyIndQueryPrim, tryPauseKeyIndQueryData]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [simulateQ_bind, simulateQ_preCheckKeyIndPrim S P (.sendOPK u i) u bundle hst.base hV,
        pure_bind]
      cases preCheckKeyInd S P (.sendOPK u i) u bundle hst.base with
      | none => rfl
      | some uEntry =>
        dsimp only
        rw [simulateQ_bind, simulateQ_checkBundleSigsPrim S P hst.base.principals bundle hPrin,
          pure_bind]
        split_ifs <;> rfl
    · rfl
  | initiateNoOPK u i bundle =>
    dsimp only [tryPauseKeyIndQueryPrim, tryPauseKeyIndQueryData]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [simulateQ_bind, simulateQ_preCheckKeyIndPrim S P (.sendNoOPK u i) u bundle hst.base hV,
        pure_bind]
      cases preCheckKeyInd S P (.sendNoOPK u i) u bundle hst.base with
      | none => rfl
      | some uEntry =>
        dsimp only
        rw [simulateQ_bind, simulateQ_checkBundleSigsPrim S P hst.base.principals bundle hPrin,
          pure_bind]
        split_ifs <;> rfl
    · rfl
  | _ => rfl

theorem map_toPaused_tryPauseKeyIndQueryData (S : Setup) (P : Primitives) (sIdx : Nat) (gq :
  KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) :
    (tryPauseKeyIndQueryData S P sIdx gq cont hst).map (PausedShCrData.toPaused P) =
      tryPauseKeyIndQuery S P sIdx gq cont hst := by
  cases gq with
  | initiateOPK u i bundle =>
    dsimp only [tryPauseKeyIndQueryData, tryPauseKeyIndQuery, tryPause2]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases preCheckKeyInd S P (.sendOPK u i) u bundle hst.base with
      | none => rfl
      | some uEntry =>
        dsimp only
        split_ifs <;> rfl
    · rfl
  | initiateNoOPK u i bundle =>
    dsimp only [tryPauseKeyIndQueryData, tryPauseKeyIndQuery, tryPause2]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases preCheckKeyInd S P (.sendNoOPK u i) u bundle hst.base with
      | none => rfl
      | some uEntry =>
        dsimp only
        split_ifs <;> rfl
    · rfl
  | _ => rfl

theorem tryPauseKeyIndQueryData_some_props (S : Setup) (P : Primitives) (sIdx : Nat) (gq :
  KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (d : PausedShCrData S)
    (hSome : tryPauseKeyIndQueryData S P sIdx gq cont hst = some d) :
    d.hst = hst ∧
    IsSendSessionId S d.sid ∧
    d.hst.base.sessions.any (fun e => e.sid == d.sid) = false ∧
    (∀ f, (∀ out, IsQueryBoundP (cont out) (fun q => isGameQuery q = true) f) →
      ∀ out, IsQueryBoundP (d.cont out) (fun q => isGameQuery q = true) f) := by
  cases gq with
  | initiateOPK u i bundle =>
    dsimp only [tryPauseKeyIndQueryData] at hSome
    cases h_opk : bundle.opkB?.isNone <;> rw [h_opk] at hSome
    · simp only [Bool.false_eq_true, ↓reduceIte] at hSome
      cases hPre : preCheckKeyInd S P (.sendOPK u i) u bundle hst.base <;> rw [hPre] at hSome
      · cases hSome
      · dsimp only at hSome
        split_ifs at hSome
        injection hSome with hd
        subst hd
        refine ⟨rfl, trivial, ?_, fun f hf out => hf out⟩
        unfold preCheckKeyInd at hPre
        cases h : hst.base.sessions.any (fun e => e.sid == .sendOPK u i)
        · rfl
        · rw [h] at hPre; simp at hPre
    · simp at hSome
  | initiateNoOPK u i bundle =>
    dsimp only [tryPauseKeyIndQueryData] at hSome
    cases h_opk : bundle.opkB?.isSome <;> rw [h_opk] at hSome
    · simp only [Bool.false_eq_true, ↓reduceIte] at hSome
      cases hPre : preCheckKeyInd S P (.sendNoOPK u i) u bundle hst.base <;> rw [hPre] at hSome
      · cases hSome
      · dsimp only at hSome
        split_ifs at hSome
        injection hSome with hd
        subst hd
        refine ⟨rfl, trivial, ?_, fun f hf out => hf out⟩
        unfold preCheckKeyInd at hPre
        cases h : hst.base.sessions.any (fun e => e.sid == .sendNoOPK u i)
        · rfl
        · rw [h] at hPre; simp at hPre
    · simp at hSome
  | genSPK _ _ => cases hSome
  | acceptOPK _ _ _ _ => cases hSome
  | acceptNoOPK _ _ _ _ => cases hSome
  | initPrin _ => cases hSome
  | corruptIK _ => cases hSome
  | genOPK _ _ _ => cases hSome
  | testSession _ => cases hSome
  | revealSessionKey _ => cases hSome
  | roQuery _ => cases hSome
  | revealDhSecrets => cases hSome
  | registerKey _ => cases hSome
  | revealSpkSk _ _ => cases hSome

theorem simulateQ_runWithFuelKeyIndShCrPrim (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (fuel : ℕ)
    (hV : ValidKeyIndEcC S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    simulateQ (primBaseImpl P) (runWithFuelKeyIndShCrPrim S oa hst fuel) =
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyIndShCrCachedImpl true S P) oa).run hst :=
          by
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b =>
    simp [runWithFuelKeyIndShCrPrim]
  | query_bind q oa ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    cases q with
    | inl uq =>
      rcases hb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      simp only [runWithFuelKeyIndShCrPrim, OracleComp.construct_query_bind,
        simulateQ_bind, simulateQ_embedUnif, StateT.run_bind,
        QueryImpl.simulateQ_add_query_left, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self,
        bind_assoc, pure_bind]
      exact bind_congr (fun u => ih u hst fuel hV (h_cont u))
    | inr gq =>
      rcases hb with ⟨h_abs | h_pos, h_cont⟩
      · exfalso; exact h_abs rfl
      · cases fuel with
        | zero => omega
        | succ f =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          simp only [runWithFuelKeyIndShCrPrim, OracleComp.construct_query_bind,
            simulateQ_bind, simulateQ_pqxdhKeyIndShCrPrimImpl true S P hP gq hst hV,
            StateT.run_bind, QueryImpl.simulateQ_add_query_right]
          refine bind_congr_of_support ((pqxdhKeyIndShCrCachedImpl true S P gq).run hst) _ _ (fun x
            hx => ?_)
          have hVx :=
            (pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs true S P gq hst hV x hx).1
          exact ih x.1 x.2 f hVx (h_cont x.1)

theorem simulateQ_pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs (embedTarget : Bool)
    (S : Setup) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (fuel : ℕ)
    (hV : ValidKeyIndEcC S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyIndShCrCachedImpl embedTarget S P
    ∀ x ∈ support ((simulateQ fullImpl oa).run hst),
      ValidKeyIndEcC S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + fuel := by
  intro fullImpl
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b =>
    intro x hx
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hV, Nat.le_add_right _ _⟩
  | query_bind q oa ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    cases q with
    | inl uq =>
      rcases hb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      dsimp only [fullImpl]
      intro x hx
      rw [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨u, _, hx⟩
      exact ih u hst fuel hV (h_cont u) x hx
    | inr gq =>
      rcases hb with ⟨h_abs | h_pos, h_cont⟩
      · exfalso; exact h_abs rfl
      · cases fuel with
        | zero => omega
        | succ f =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          dsimp only [fullImpl]
          intro x hx
          rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨y, hy, hx⟩
          have ⟨hVy, hRecy⟩ :=
            pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P gq hst hV y hy
          have ⟨hVx, hRecx⟩ := ih y.1 y.2 f hVy (h_cont y.1) x hx
          exact ⟨hVx, by omega⟩

def ValidPausedShCrData (S : Setup) (P : Primitives) (N : ℕ) (d : PausedShCrData S) : Prop :=
  ValidKeyIndEcC S P d.hst.base ∧
  IsSendSessionId S d.sid ∧
  d.hst.base.sessions.any (fun e => e.sid == d.sid) = false ∧
  ∃ f, d.hst.recvKemRecs.length + f ≤ N ∧
    ∀ out, IsQueryBoundP (d.cont out) (fun q => isGameQuery q = true) f

theorem simulateQ_stepUntilShCrFuelKeyIndPrim (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx : ℕ)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (fuel : ℕ)
    (hV : ValidKeyIndEcC S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    (Sum.map id (PausedShCrData.toPaused P) <$>
      simulateQ (primBaseImpl P) (stepUntilShCrFuelKeyIndPrim S sIdx oa hst fuel) =
      stepUntilShCr (pqxdhKeyIndShCrCachedImpl true S P) (tryPauseKeyIndQuery S P sIdx) oa hst) ∧
    (∀ res ∈ support (simulateQ (primBaseImpl P) (stepUntilShCrFuelKeyIndPrim S sIdx oa hst fuel)),
      match res with
      | Sum.inl done => done.2.recvKemRecs.length ≤ hst.recvKemRecs.length + fuel
      | Sum.inr d    => ValidPausedShCrData S P (hst.recvKemRecs.length + fuel) d) := by
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b' =>
    refine ⟨?_, ?_⟩
    · simp [stepUntilShCrFuelKeyIndPrim, stepUntilShCr]
    · intro res hres
      simp only [stepUntilShCrFuelKeyIndPrim, OracleComp.construct_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hres
      subst hres
      exact Nat.le_add_right _ _
  | query_bind q oa ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    cases q with
    | inl uq =>
      rcases hb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      refine ⟨?_, ?_⟩
      · rw [stepUntilShCr_query_inl]
        simp only [stepUntilShCrFuelKeyIndPrim, OracleComp.construct_query_bind,
          simulateQ_bind, simulateQ_embedUnif, map_bind]
        exact bind_congr (fun u => (ih u hst fuel hV (h_cont u)).1)
      · intro res hres
        simp only [stepUntilShCrFuelKeyIndPrim, OracleComp.construct_query_bind,
          simulateQ_bind, simulateQ_embedUnif, MonadAttach.mem_support_bind] at hres
        rcases hres with ⟨u, _, hres⟩
        exact (ih u hst fuel hV (h_cont u)).2 res hres
    | inr gq =>
      rcases hb with ⟨h_abs | h_pos, h_cont⟩
      · exfalso; exact h_abs rfl
      · cases fuel with
        | zero => omega
        | succ f =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          have h_try := simulateQ_tryPauseKeyIndQueryPrim S P sIdx gq oa hst hV
          have h_map := map_toPaused_tryPauseKeyIndQueryData S P sIdx gq oa hst
          refine ⟨?_, ?_⟩
          · rw [stepUntilShCr_query_inr]
            simp only [stepUntilShCrFuelKeyIndPrim, OracleComp.construct_query_bind,
              simulateQ_bind, h_try, pure_bind, ← h_map]
            cases h_d : tryPauseKeyIndQueryData S P sIdx gq oa hst with
            | some d =>
              simp [simulateQ_pure]
            | none =>
              simp only [Option.map_none, simulateQ_bind,
                simulateQ_pqxdhKeyIndShCrPrimImpl true S P hP gq hst hV, map_bind]
              refine bind_congr_of_support ((pqxdhKeyIndShCrCachedImpl true S P gq).run hst) _ _
                (fun x hx => ?_)
              have hVx :=
                (pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs true S P gq hst hV x hx).1
              exact (ih x.1 x.2 f hVx (h_cont x.1)).1
          · intro res hres
            simp only [stepUntilShCrFuelKeyIndPrim, OracleComp.construct_query_bind,
              simulateQ_bind, h_try, pure_bind] at hres
            cases h_d : tryPauseKeyIndQueryData S P sIdx gq oa hst with
            | some d =>
              rw [h_d] at hres
              simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hres
              subst hres
              rcases tryPauseKeyIndQueryData_some_props S P sIdx gq oa hst d h_d with
                ⟨h_hst, h_sid, h_fresh, h_cb⟩
              refine ⟨h_hst ▸ hV, h_sid, h_fresh, f, ?_, h_cb f h_cont⟩
              rw [h_hst]; omega
            | none =>
              rw [h_d] at hres
              simp only [simulateQ_bind, simulateQ_pqxdhKeyIndShCrPrimImpl true S P hP gq hst hV,
                MonadAttach.mem_support_bind] at hres
              rcases hres with ⟨x, hx, hres⟩
              have ⟨hVx, hRecx⟩ :=
                pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs true S P gq hst hV x hx
              have h_ih := (ih x.1 x.2 f hVx (h_cont x.1)).2 res hres
              cases res with
              | inl done => omega
              | inr d =>
                rcases h_ih with ⟨hVd, hSid, hFresh, f', hf', hCont⟩
                exact ⟨hVd, hSid, hFresh, f', by omega, hCont⟩

theorem simulateQ_resumePausedKeyIndPrim (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (N : ℕ) (d : PausedShCrData S) (ss kemCt : Bytes)
    (hValid : ValidPausedShCrData S P N d) :
    simulateQ (primBaseImpl P) (resumePausedKeyIndPrim S N d ss kemCt) =
      (d.toPaused P).resume ss kemCt ∧
    (∀ z ∈ support ((d.toPaused P).resume ss kemCt), z.2.recvKemRecs.length ≤ N) := by
  rcases hValid with ⟨hVd, hSid, hFresh, f, hf_le, hCont⟩
  have hf_N : f ≤ N := by omega
  have hEq : simulateQ (primBaseImpl P) (resumePausedKeyIndPrim S N d ss kemCt) =
      (d.toPaused P).resume ss kemCt := by
    unfold resumePausedKeyIndPrim _root_.SignalPqxdh.Security.RoKem.PausedShCrData.toPaused
      PausedShCrData.toPaused
    dsimp only
    rw [simulateQ_bind, simulateQ_postKemKeyIndPrim S P d.sid d.bundle d.uEntry d.hst ss kemCt hVd]
    refine bind_congr_of_support
      (postKem2 d.sid d.bundle d.uEntry (finishKeyIndBase S P d.sid d.bundle) d.hst ss kemCt) _ _
        (fun y hy => ?_)
    have hVy :=
      (postKem2_validKeyIndEc_and_recvKemRecs S P d.sid hSid d.bundle d.uEntry d.hst ss kemCt hVd
      hFresh y hy).1
    exact simulateQ_runWithFuelKeyIndShCrPrim S P hP (d.cont y.1) y.2 N hVy ((hCont y.1).mono hf_N)
  refine ⟨hEq, fun z hz => ?_⟩
  unfold _root_.SignalPqxdh.Security.RoKem.PausedShCrData.toPaused PausedShCrData.toPaused at hz
  dsimp only at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨y, hy, hz⟩
  have ⟨hVy, hRecy⟩ :=
    postKem2_validKeyIndEc_and_recvKemRecs S P d.sid hSid d.bundle d.uEntry d.hst ss kemCt hVd
    hFresh y hy
  have ⟨_, hRecz⟩ :=
    simulateQ_pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs true S P (d.cont y.1) y.2 f
    hVy (hCont y.1) z hz
  rw [hRecy] at hRecz
  omega

def shcrReductionKeyIndAt (S : Setup) (b : QueryBudget) (idx : ℕ)
    (A : KeyIndAdversary S) : KemShCrAdv where
  State := ShCrFinishState S
  choosePk := choosePkKeyIndPrimAt S b (idx / S.N_send_tot) (idx % S.N_send_tot) A
  findCollision := findCollisionKeyIndPrim S b
  q_prim := primQueryBudget S b

theorem kemShCrExp_shcrReductionKeyIndAt_eq (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (idx : ℕ) (A : KeyIndAdversary S) (hA : QueryBounded A b) :
    kemShCrExp P (shcrReductionKeyIndAt S b idx A) =
      kemShCrExpProb P (shcrChoosePkKeyIndAt S P (idx / S.N_send_tot) (idx % S.N_send_tot) A) := by
  unfold kemShCrExp shcrReductionKeyIndAt kemShCrExpProb shcrChoosePkKeyIndAt shcrChoosePkGenericAt
    choosePkKeyIndPrimAt findCollisionKeyIndPrim
  dsimp only
  congr 1; ext ⟨pk, sk⟩
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_embedUnif, bind_assoc, pure_bind]
  refine bind_congr (fun secb => ?_)
  let initSt : KeyIndShCrState S := {
    base        := KeyIndState.empty S secb
    targetBIdx? := some (idx / S.N_send_tot)
    targetPk    := pk
    targetSk    := sk
  }
  have hV0 : ValidKeyIndEcC S P initSt.base := ⟨validEcLists_nil S, (fun _ h =>
    False.elim (List.not_mem_nil h)), validKeyIndResp_empty S secb⟩
  have ⟨hSimStep, hSupStep⟩ :=
    simulateQ_stepUntilShCrFuelKeyIndPrim S P hP (idx % S.N_send_tot) A.run initSt b.q_total hV0
      hA.2.2.2.1
  have h_rec0 : initSt.recvKemRecs.length + b.q_total = b.q_total := by
    change ([] : List RecvKemRecord).length + b.q_total = b.q_total
    simp
  rw [← hSimStep, bind_map_left]
  refine bind_congr_of_support
    (simulateQ (primBaseImpl P) (stepUntilShCrFuelKeyIndPrim S (idx % S.N_send_tot) A.run initSt
      b.q_total))
    _ _ (fun res hres => ?_)
  have hValidRes := hSupStep res hres
  rw [h_rec0] at hValidRes
  cases res with
  | inl done =>
    dsimp only [Sum.map, Sum.elim, Function.comp_def, id] at hValidRes ⊢
    congr 1; ext r
    cases hEnc : P.kemEncaps pk r with
    | none => rfl
    | some sc =>
      rcases sc with ⟨ss, ct⟩
      dsimp only
      rw [pure_bind,
          simulateQ_extractCollidingKemCtPrim b.q_total P pk sk pk ct ss done.2.recvKemRecs
            hValidRes,
          pure_bind]
      exact kemShCrWin_pure_eq_of_cwf P hP hEnc
  | inr d =>
    simp only [Sum.map, Sum.elim, Function.comp_def, PausedShCrData.toPaused_bundle] at hValidRes ⊢
    congr 1; ext r
    cases hEnc : P.kemEncaps d.bundle.pqspkB r with
    | none => rfl
    | some sc =>
      rcases sc with ⟨ss, ct⟩
      dsimp only
      rcases simulateQ_resumePausedKeyIndPrim S P hP b.q_total d ss ct hValidRes with ⟨hSimRes,
        hSupRes⟩
      rw [simulateQ_bind, hSimRes, bind_assoc, bind_assoc]
      refine bind_congr_of_support ((d.toPaused P).resume ss ct) _ _ (fun z hz => ?_)
      rw [simulateQ_extractCollidingKemCtPrim b.q_total P pk sk d.bundle.pqspkB ct ss
        z.2.recvKemRecs (hSupRes z hz),
          pure_bind]
      exact kemShCrWin_pure_eq_of_cwf P hP hEnc

theorem evalDist_uniformFin_bind_true (N : ℕ) [NeZero N] (f : ℕ → ProbComp Bool) :
    𝒟[($ᵗ (Fin N) : ProbComp (Fin N)) >>= fun k => f k.val] {true} =
      ∑ k ∈ Finset.range N, 𝒟[f k] {true} * (N : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace (Fin N) := ⊤
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
      (Measurable.of_discrete).aemeasurable,
    MeasureTheory.lintegral_fintype]
  simp_rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun k => 𝒟[f k] {true} * (N : ℝ≥0∞)⁻¹) N)

theorem mul_toReal_uniformFin_bind_eq_sum (N : ℕ) [NeZero N] (f : ℕ → ProbComp Bool) :
    (N : ℝ) * (𝒟[($ᵗ (Fin N) : ProbComp (Fin N)) >>= fun k => f k.val] {true}).toReal =
      ∑ k ∈ Finset.range N, (𝒟[f k] {true}).toReal := by
  rw [evalDist_uniformFin_bind_true]
  have hfin : ∀ k ∈ Finset.range N, 𝒟[f k] {true} * (N : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    intro k _
    exact ENNReal.mul_ne_top (MeasureTheory.measure_ne_top _ {true})
      (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N)))
  rw [ENNReal.toReal_sum hfin]
  have hterm : ∀ k ∈ Finset.range N,
      (𝒟[f k] {true} * (N : ℝ≥0∞)⁻¹).toReal = (𝒟[f k] {true}).toReal * (N : ℝ)⁻¹ := by
    intro k _
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← mul_assoc,
    mul_comm (N : ℝ), mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N)), mul_one]

theorem mul_toReal_sampleIndexRange_bind_eq_sum (N : ℕ) (f : ℕ → ProbComp Bool) :
    (N : ℝ) * (𝒟[sampleIndexRange N >>= f] {true}).toReal =
      ∑ k ∈ Finset.range N, (𝒟[f k] {true}).toReal := by
  unfold sampleIndexRange
  split_ifs with h
  · let : NeZero N := ⟨Nat.ne_of_gt h⟩
    simp only [bind_assoc, pure_bind]
    exact mul_toReal_uniformFin_bind_eq_sum N f
  · have h0 : N = 0 := Nat.eq_zero_of_not_pos h
    subst h0
    simp

theorem mul_kemShCr_shcrReductionKeyInd_eq_sum (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    ((S.N_spk_tot * S.N_send_tot : ℕ) : ℝ) * KemShCrReal P (shcrReductionKeyInd S b A) =
      ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
        KemShCrReal P (shcrReductionKeyIndAt S b idx A.1) := by
  have hSwap :
      𝒟[kemShCrExp P (shcrReductionKeyInd S b A)] =
      𝒟[sampleIndexRange (S.N_spk_tot * S.N_send_tot) >>= fun idx =>
        kemShCrExp P (shcrReductionKeyIndAt S b idx A.1)] := by
    unfold kemShCrExp shcrReductionKeyInd shcrReductionKeyIndCore shcrReductionKeyIndAt
    dsimp only
    simp only [simulateQ_bind, simulateQ_embedUnif, bind_assoc]
    rw [OracleComp.evalDist_bind_bind_swap]
  unfold KemShCrReal KemShCr
  rw [hSwap]
  exact mul_toReal_sampleIndexRange_bind_eq_sum (S.N_spk_tot * S.N_send_tot)
    (fun idx => kemShCrExp P (shcrReductionKeyIndAt S b idx A.1))

theorem badKemShCrProbKeyInd_le_kemShCr (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    badKemShCrProbKeyInd S P A.1 ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionKeyInd S b A) := by
  calc badKemShCrProbKeyInd S P A.1
      ≤ ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot), badKemShCrProbKeyIndAt S P idx A.1 :=
        badKemShCrProbKeyInd_le_sum S P A.1
    _ ≤ ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
          KemShCrReal P (shcrReductionKeyIndAt S b idx A.1) := by
        refine Finset.sum_le_sum (fun idx _ => ?_)
        unfold KemShCrReal KemShCr
        rw [kemShCrExp_shcrReductionKeyIndAt_eq S P hP b idx A.1 A.2]
        exact badKemShCrProbKeyIndAt_le_kemShCrProb S P idx A.1
    _ = ((S.N_spk_tot * S.N_send_tot : ℕ) : ℝ) * KemShCrReal P (shcrReductionKeyInd S b A) :=
        (mul_kemShCr_shcrReductionKeyInd_eq_sum S P b A).symm
    _ = (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionKeyInd S b A) := by
        push_cast; ring

/-- Bounds `|keyIndAdvG2 - keyIndAdvG3|` via `shcrReductionKeyInd` and the PQSPK public-key
    collision bound. -/
theorem keyInd_hop_G2_G3_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    |keyIndAdvG2 S P A.1 - keyIndAdvG3 S P A.1| ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionKeyInd S b A) +
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  have h1 : |keyIndAdvG2 S P A.1 - keyIndAdvG2_5 S P A.1| ≤
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 :=
    le_trans (keyInd_hop_kemColl_le_prob S P A.1) (kemCollProbKeyInd_le true S P hP A.1)
  have h2 : |keyIndAdvG2_5 S P A.1 - keyIndAdvG3 S P A.1| ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionKeyInd S b A) := by
    rw [keyIndAdvG2_5_eq_ShCr S P A.1]
    exact le_trans (keyInd_hop_badKemShCr_le_prob S P A.1)
      (badKemShCrProbKeyInd_le_kemShCr S P hP b A)
  have htri : |keyIndAdvG2 S P A.1 - keyIndAdvG3 S P A.1| ≤
      |keyIndAdvG2 S P A.1 - keyIndAdvG2_5 S P A.1| +
        |keyIndAdvG2_5 S P A.1 - keyIndAdvG3 S P A.1| := by
    have : keyIndAdvG2 S P A.1 - keyIndAdvG3 S P A.1 =
        (keyIndAdvG2 S P A.1 - keyIndAdvG2_5 S P A.1) +
          (keyIndAdvG2_5 S P A.1 - keyIndAdvG3 S P A.1) := by ring
    rw [this]
    exact abs_add_le _ _
  set_option exponentiation.threshold 512 in
  linarith

end Proofs.SignalPqxdh.Security
