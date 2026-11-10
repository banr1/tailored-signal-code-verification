/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyCoupling -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.SigHop1Key -- proof-setup: allow-public-import
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Creation-Order Active One-Key `KeyInd` `GapSigEufCma` Hop (`G0 -> G1` and `G0 -> G2`)

Proves the creation-order `G0_1 -> G1` `GapSigEufCma` bound and combined `G0 -> G1` / `G0 -> G2`
hop bounds for the activity-bounded one-key `KeyInd` game via `sigReductionKeyInd1KeyActive`.
-/


set_option autoImplicit false

open scoped ENNReal BigOperators
open OracleSpec OracleComp
open SignalPqxdh (Setup Primitives Bytes KeyIndQuery KeyIndResponse KeyIndState KeyIndAdversary
  keyIndSpec QueryBudget BoundedAdv QueryBounded PrincipalEntry SpkBundleEntry PreKeyBundleInput
  SessionId KeyIndInitiatorEntry activeIdCount activeDhCount activeSendCount pqxdhKeyIndImpl
  pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal sampleScalar32 CryptoWellFormedPrimitivesδ
  isKeyIndOnlineQuery isGameQuery findHonestPrincipal isHonestUncorruptedPeer primBaseImpl
  GapSigEufCma KeyInd1KeyRoAdvantageReal GapSigEufCmaReal gapSigEufCmaExp)
open SignalPqxdh.Security (keyInd1KeyAdvG0 keyInd1KeyAdvG0_1 keyInd1KeyAdvG1 keyInd1KeyAdvG2
  keyInd1KeyAdvG0_eq keyInd1KeyAdvG1_eq_G2 keyInd1Key_hop_G0_1_G1_le_noCollProb runKeyInd1KeySim
  badSigNoCollProbKeyInd1Key hasBadSigKeyInd hasBadSigKeyIndAt noPrinPkColl CleanPeers
  cleanPeers_nil cleanPeers_cons_principal cleanPeers_corrupt cleanPeers_cons_of_before
  badPeersKeyInd ValidPrincipals validPrincipals_cons validPrincipals_corrupt keyIndSigLens
  SigGameLens findHonestPrincipal_eq_some_of_noPrinPkColl peerPartyIdx
  evalDist_simulateQ_preSample_slot_eq liftFgBase KeyIndFgCutoffState pqxdhKeyIndFgImpl
  pqxdhKeyInd1KeyFgPreImpl pqxdhKeyInd1KeyFgPreImpl_safe_step fg1KeyPreInitPrin
  mem_support_liftFgBase mem_support_pqxdhKeyIndFgImpl_base Sig1KeyRel sig1KeyRel_empty
  sig1KeyRel_weaken_rem sig1Key_step_coupling Sig1KeyWon sig1KeyWinBool one_le_evalDist_sig1KeyWon
  gapSigEufCmaFullImpl gapSigEufCmaExp_eq_fullImpl any_peerPartyIdx_eq_false_of_cleanPeers
  bundleSignedMessages toReal_any_range_le_sum length_lt_of_nodup_lt InitPostKeyInd
  pqxdhKeyIndImpl_initiateOPK_pres pqxdhKeyIndImpl_initiateNoOPK_pres pqxdhKeyIndCachedImpl
  pqxdhKeyIndCachedImpl_commutes_cache pqxdhKeyIndImpl_other_pres cacheKeyIndAdvKeys CommutesRel
  SpksPreserved HasKeyIndState clearFgTargetSign clearPrincipalsTargetSign
  length_clearPrincipalsTargetSign any_idx_clearPrincipalsTargetSign embedPrim
  extractBundleForgeryPrim isHonestUncorruptedPeerPrim simulateQ_isHonestUncorruptedPeerPrim
  simulateQ_extractBundleForgeryPrim findHonestPrincipal_of_isHonestUncorruptedPeer_eq_some
  simulateQ_unifSigDdh_run simulateQ_primSigDdhQ_run simulateQ_embedPrim_sigDdh_run
  simulateQ_embedGdhSigDdh_run runWithSigDdhStep_pure runWithSigDdhStep_query_inl
  runWithSigDdhStep_query_inr)
open SignalPqxdh.Security.RoKem (sampleIndexRange)
open Proofs.SignalPqxdh.Security (mul_toReal_sampleIndexRange_bind_eq_sum)
open SignalPqxdh.Security.Sig1Key (SigDdhSimSpec unifSigDdh primSigDdhQ sigChalQ embedGdhSigDdh
  Sig1KeySimState sig1KeyStep runWithSigDdhStep)
open SignalPqxdh.Security.FgGapDh (FgKeyIndSimState fgKeyIndStep)
open Proofs.SignalPqxdh.Security.FgGapDh (simulateQ_run_query_inl simulateQ_run_query_inr
  evalDist_bind_true_eq_zero_of_support evalDist_bind_true_mono_of_support StateT_run_mk
  erasePrincipalEntryFg erasePrincipalsFg erasePrincipalsFg_length any_idx_erasePrincipalsFg
  deadDh1 length_of_mem_support_sampleScalar32)
open Proofs.SignalPqxdh.Security.FgGapDh.Ik (eraseStateFgIk prinTargetIsV)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (activeSigBudget)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow (optNatMatches
  extractBundleForgeryActivePrim Sig1KeyActiveSimState sig1KeyTargetGenSpk sig1KeyActiveStep
  sigReductionKeyInd1KeyActiveRunAt sigReductionKeyInd1KeyActiveAt sigReductionKeyInd1KeyActive)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveSigHop

public section
/-- The principal ID initialized at 0-based creation ordinal `ord` (`principals.reverse[ord]?`). -/
@[expose] def prinAtOrd? (ord : ℕ) (principals : List (Nat × PrincipalEntry)) : Option ℕ :=
  (principals.reverse[ord]?).map Prod.fst

/-- Per-creation-ordinal `badSig` predicate attributing a forged bundle to `prinAtOrd? ord`. -/
@[expose] def hasBadSigKeyIndAtOrd (S : Setup) (P : Primitives) (ord : ℕ) (st : KeyIndState S) : Bool :=
  match prinAtOrd? ord st.principals with | some kIdx => hasBadSigKeyIndAt S P kIdx st | none => false

theorem prinAtOrd?_of_length_le {ord : ℕ} {principals : List (Nat × PrincipalEntry)}
    (hLen : principals.length ≤ ord) : prinAtOrd? ord principals = none := by
  unfold prinAtOrd?; rw [List.getElem?_eq_none (by simpa using hLen)]; rfl

theorem prinAtOrd?_cons_eq {ord u : ℕ} {entry : PrincipalEntry}
    {principals : List (Nat × PrincipalEntry)} (hEq : principals.length = ord) :
    prinAtOrd? ord ((u, entry) :: principals) = some u := by
  unfold prinAtOrd?; rw [List.reverse_cons, List.getElem?_append_right (by simp [hEq])]; simp [hEq]

theorem prinAtOrd?_cons_of_lt {ord u : ℕ} {entry : PrincipalEntry}
    {principals : List (Nat × PrincipalEntry)} (hLt : ord < principals.length) :
    prinAtOrd? ord ((u, entry) :: principals) = prinAtOrd? ord principals := by
  unfold prinAtOrd?; rw [List.reverse_cons, List.getElem?_append_left (by simpa using hLt)]

theorem prinAtOrd?_map_fst_eq {ord : ℕ} (f : Nat × PrincipalEntry → Nat × PrincipalEntry)
    (hf : ∀ x, (f x).1 = x.1) (principals : List (Nat × PrincipalEntry)) :
    prinAtOrd? ord (principals.map f) = prinAtOrd? ord principals := by
  unfold prinAtOrd?; rw [← List.map_reverse, List.getElem?_map, Option.map_map]
  congr 1; funext x; exact hf x

theorem mem_of_prinAtOrd?_eq_some {ord kIdx : ℕ} {principals : List (Nat × PrincipalEntry)}
    (h : prinAtOrd? ord principals = some kIdx) : ∃ entry, (kIdx, entry) ∈ principals := by
  rcases Option.map_eq_some_iff.mp h with ⟨⟨_, entry⟩, hGet, rfl⟩
  exact ⟨entry, List.mem_reverse.mp (List.mem_of_getElem? hGet)⟩

theorem hasBadSigKeyInd_eq_any_ord (S : Setup) (P : Primitives) (st : KeyIndState S) (n : ℕ)
    (hClean : CleanPeers S P S.N_id st.principals (badPeersKeyInd st))
    (hLen : st.principals.length ≤ n) :
    (hasBadSigKeyInd st && noPrinPkColl P st.principals) =
      (List.range n).any (fun ord => hasBadSigKeyIndAtOrd S P ord st) := by
  apply Bool.eq_iff_iff.mpr; simp only [List.any_eq_true, List.mem_range]; constructor
  · intro hLHS
    simp only [hasBadSigKeyInd, HasKeyIndState.toKeyIndState, Bool.and_eq_true, List.any_eq_true] at hLHS
    rcases hLHS with ⟨⟨s, hs, hfresh, hbad⟩, hnp⟩
    have hPeerMem : s.peerIkPk ∈ badPeersKeyInd st := by
      simp only [badPeersKeyInd, List.mem_map, List.mem_filter, Bool.and_eq_true]
      exact ⟨s, ⟨hs, hfresh, hbad⟩, rfl⟩
    rcases hClean s.peerIkPk hPeerMem with ⟨kIdx, entry, hMemP, hkLt, _, hPow⟩
    have hFind := findHonestPrincipal_eq_some_of_noPrinPkColl P st.principals kIdx entry s.peerIkPk
      hnp hMemP (beq_iff_eq.mp hPow).symm
    have hParty : peerPartyIdx S P st.principals s.peerIkPk = kIdx := by
      unfold peerPartyIdx; simp [hFind, hkLt]
    have hBadAt : hasBadSigKeyIndAt S P kIdx st = true := by
      unfold hasBadSigKeyIndAt SigGameLens.badAt keyIndSigLens
      simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq]; exact ⟨⟨s.peerIkPk, hPeerMem, hParty⟩, hnp⟩
    rcases List.mem_iff_getElem?.mp (List.mem_reverse.mpr hMemP) with ⟨ord, hGet⟩
    have hOrdLtRev : ord < st.principals.reverse.length := by
      by_contra hGe; rw [List.getElem?_eq_none (Nat.le_of_not_lt hGe)] at hGet; cases hGet
    rw [List.length_reverse] at hOrdLtRev
    exact ⟨ord, Nat.lt_of_lt_of_le hOrdLtRev hLen, by simp [hasBadSigKeyIndAtOrd, prinAtOrd?, hGet, hBadAt]⟩
  · rintro ⟨ord, _, hOrdBad⟩; unfold hasBadSigKeyIndAtOrd at hOrdBad
    cases hPO : prinAtOrd? ord st.principals with
    | none => rw [hPO] at hOrdBad; cases hOrdBad
    | some kIdx =>
      rw [hPO] at hOrdBad
      unfold hasBadSigKeyIndAt SigGameLens.badAt keyIndSigLens badPeersKeyInd at hOrdBad
      simp only [Bool.and_eq_true, List.any_eq_true, List.mem_map, List.mem_filter] at hOrdBad
      rcases hOrdBad with ⟨⟨_, ⟨s, ⟨hs, hfresh, hbad⟩, rfl⟩, _⟩, hnp⟩
      simp only [hasBadSigKeyInd, HasKeyIndState.toKeyIndState, Bool.and_eq_true, List.any_eq_true]
      exact ⟨⟨s, hs, hfresh, hbad⟩, hnp⟩

/-! ## Reachability of `CleanPeers` and `principals.length ≤ activeIdCount` -/

private theorem principals_length_le_N_id {S : Setup} {principals : List (Nat × PrincipalEntry)}
    (hVP : ValidPrincipals S principals) : principals.length ≤ S.N_id := by
  cases principals with
  | nil => exact Nat.zero_le _
  | cons kv rest =>
    have hLt : (rest.map Prod.fst).length < S.N_id :=
      length_lt_of_nodup_lt kv.1 hVP.2 fun y hy => by
        rcases List.mem_map.mp (show y ∈ (kv :: rest).map Prod.fst from hy) with ⟨p, hp, rfl⟩
        exact hVP.1 p hp
    simp only [List.length_map] at hLt; simp only [List.length_cons]; omega

private theorem pqxdhKeyIndImpl_other_pres_local (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S)
    (h1 : ∀ u, q ≠ .initPrin u) (h2 : ∀ u, q ≠ .corruptIK u) (h3 : ∀ u j, q ≠ .genSPK u j)
    (h4 : ∀ u i b, q ≠ .initiateOPK u i b) (h5 : ∀ u i b, q ≠ .initiateNoOPK u i b) :
    ∀ x ∈ support ((pqxdhKeyIndImpl true S P q).run st),
      x.2.principals = st.principals ∧ SpksPreserved S st.spkBundles x.2.spkBundles ∧
      badPeersKeyInd x.2 = badPeersKeyInd st := fun x hx => by
  have hcomm := pqxdhKeyIndCachedImpl_commutes_cache true S P q st; unfold CommutesRel at hcomm
  have hmem : (x.1, cacheKeyIndAdvKeys S P x.2) ∈
      support ((pqxdhKeyIndCachedImpl true S P q).run (cacheKeyIndAdvKeys S P st)) := by
    rw [hcomm, support_map]; exact ⟨x, hx, rfl⟩
  simpa [cacheKeyIndAdvKeys, badPeersKeyInd] using
    pqxdhKeyIndImpl_other_pres true S P q (cacheKeyIndAdvKeys S P st) h1 h2 h3 h4 h5 _ hmem

private theorem pqxdhKeyIndImpl1KeyRo_clean_step (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S) (hVP : ValidPrincipals S st.principals)
    (hClean : CleanPeers S P S.N_id st.principals (badPeersKeyInd st)) :
    ∀ x ∈ support ((pqxdhKeyIndImpl1KeyRo S P q).run st),
      ValidPrincipals S x.2.principals ∧ CleanPeers S P S.N_id x.2.principals (badPeersKeyInd x.2) ∧
      x.2.principals.length ≤
        st.principals.length + @ite _ (isKeyIndOnlineQuery (.inr q)) (Classical.propDecidable _) 1 0 := by
  intro x hx
  have hInitPost {bnd} (hp : InitPostKeyInd P bnd st x.2) {n : ℕ} :
      ValidPrincipals S x.2.principals ∧ CleanPeers S P S.N_id x.2.principals (badPeersKeyInd x.2) ∧
      x.2.principals.length ≤ st.principals.length + n := by
    rcases hp with ⟨hPrinEq, _, hBpEq | ⟨_, hBpCons, _, _, hFresh, _⟩⟩
    · rw [hPrinEq, hBpEq]; exact ⟨hVP, hClean, by omega⟩
    · rw [hPrinEq, hBpCons]
      exact ⟨hVP, cleanPeers_cons_of_before S P S.N_id st.principals (badPeersKeyInd st) bnd.ikB
        (fun p hp => ⟨hVP.1 p hp, Nat.ne_of_lt (hVP.1 p hp)⟩) hClean hFresh, by omega⟩
  cases q with
  | initPrin u =>
    have hOn : isKeyIndOnlineQuery (Sum.inr (KeyIndQuery.initPrin u)) := trivial
    simp only [hOn, ↓reduceIte]; unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal at hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
    cases hAny : st.principals.any (fun (idx, _) => idx == u.val) with
    | true =>
      rw [hAny] at hx; simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨hVP, hClean, by simp⟩
    | false =>
      rw [hAny] at hx
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨sk0, _, rfl⟩
      exact ⟨(validPrincipals_cons S u _ st.principals hVP hAny).1,
        cleanPeers_cons_principal S P S.N_id u.val _ st.principals (badPeersKeyInd st) hClean, by simp⟩
  | corruptIK u =>
    rcases (keyIndSigLens S).mem_support_realCorruptIK u st x hx with ⟨_, hN⟩ | ⟨_, _, _, hSm⟩
    · rw [(Prod.mk.inj hN).2]; exact ⟨hVP, hClean, by omega⟩
    · dsimp only [keyIndSigLens] at hSm; rw [(Prod.mk.inj hSm).2]
      exact ⟨validPrincipals_corrupt S u.val st.principals hVP,
        cleanPeers_corrupt S P S.N_id u.val st.principals (badPeersKeyInd st) hClean, by simp⟩
  | genSPK u j =>
    rcases (keyIndSigLens S).mem_support_realGenSPK P u j st x hx with hN | ⟨_, _, _, _, _, _, hSm⟩
    · rw [(Prod.mk.inj hN).2]; exact ⟨hVP, hClean, by omega⟩
    · dsimp only [keyIndSigLens] at hSm; rw [(Prod.mk.inj hSm).2]; exact ⟨hVP, hClean, by simp⟩
  | initiateOPK u i bnd => exact hInitPost (pqxdhKeyIndImpl_initiateOPK_pres true S P u i bnd st x hx)
  | initiateNoOPK u i bnd => exact hInitPost (pqxdhKeyIndImpl_initiateNoOPK_pres true S P u i bnd st x hx)
  | genOPK _ _ _ | acceptOPK _ _ _ _ | acceptNoOPK _ _ _ _ | testSession _
  | revealSessionKey _ | roQuery _ | revealDhSecrets | registerKey _ | revealSpkSk _ _ =>
    rcases pqxdhKeyIndImpl_other_pres_local S P _ st
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) x hx with ⟨hPrinEq, _, hBpEq⟩
    rw [hPrinEq, hBpEq]; exact ⟨hVP, hClean, by omega⟩

private theorem simulateQ_1Key_clean_and_online_le {S : Setup} {α : Type} (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (remOn : ℕ)
    (hOn : IsQueryBoundP oa isKeyIndOnlineQuery remOn) (st : KeyIndState S)
    (hVP : ValidPrincipals S st.principals)
    (hClean : CleanPeers S P S.N_id st.principals (badPeersKeyInd st)) :
    ∀ x ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndState S) ProbComp) + pqxdhKeyIndImpl1KeyRo S P) oa).run st),
      ValidPrincipals S x.2.principals ∧ CleanPeers S P S.N_id x.2.principals (badPeersKeyInd x.2) ∧
      x.2.principals.length ≤ st.principals.length + remOn := by
  induction oa using OracleComp.inductionOn generalizing remOn st with
  | pure _ =>
    intro x hx; simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact ⟨hVP, hClean, by simp⟩
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hOn
    cases q with
    | inl uq =>
      rcases hOn with ⟨_, hCont⟩
      simp only [show ¬ isKeyIndOnlineQuery (S := S) (Sum.inl uq) from id, ↓reduceIte] at hCont
      intro x hx; simp only [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨u, _, hx'⟩; exact ih u remOn (hCont u) st hVP hClean x hx'
    | inr gq =>
      intro x hx; simp only [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨y, hy, hx'⟩
      have hStep := pqxdhKeyIndImpl1KeyRo_clean_step S P gq st hVP hClean y hy
      by_cases hqOn : isKeyIndOnlineQuery (Sum.inr gq)
      · rcases hOn with ⟨hAbs | hPos, hCont⟩
        · exact False.elim (hAbs hqOn)
        · cases remOn with
          | zero => omega
          | succ remOn' =>
            simp only [hqOn, ↓reduceIte, Nat.add_sub_cancel] at hCont hStep
            rcases ih y.1 remOn' (hCont y.1) y.2 hStep.1 hStep.2.1 x hx' with ⟨h1, h2, _⟩
            exact ⟨h1, h2, by omega⟩
      · rcases hOn with ⟨_, hCont⟩; simp only [hqOn, ↓reduceIte] at hCont hStep
        rcases ih y.1 remOn (hCont y.1) y.2 hStep.1 hStep.2.1 x hx' with ⟨h1, h2, _⟩
        exact ⟨h1, h2, by omega⟩

@[expose] noncomputable def badSigProbKeyInd1KeyAtOrd (S : Setup) (P : Primitives) (ord : ℕ)
    (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyInd1KeySim S P A >>= fun (_, _, finalSt) =>
    pure (hasBadSigKeyIndAtOrd S P ord finalSt)] {true}).toReal

theorem badSigNoCollProbKeyInd1Key_le_sum_ord (S : Setup) (b : QueryBudget) (P : Primitives)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    badSigNoCollProbKeyInd1Key S P A.1 ≤
      ∑ ord ∈ Finset.range (activeIdCount S b.q_on), badSigProbKeyInd1KeyAtOrd S P ord A.1 := by
  unfold badSigNoCollProbKeyInd1Key badSigProbKeyInd1KeyAtOrd
  have hCongr :
      𝒟[runKeyInd1KeySim S P A.1 >>= fun (_, _, s) => pure (hasBadSigKeyInd s && noPrinPkColl P s.principals)] =
      𝒟[runKeyInd1KeySim S P A.1 >>= fun (_, _, s) =>
          pure ((List.range (activeIdCount S b.q_on)).any fun ord => hasBadSigKeyIndAtOrd S P ord s)] := by
    refine OracleComp.evalDist_bind_congr_of_support (runKeyInd1KeySim S P A.1) _ _ fun ⟨secb, b', s⟩ hr => ?_
    unfold runKeyInd1KeySim at hr
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hr
    rcases hr with ⟨secb0, _, ⟨b0, st0⟩, hSim, hEq⟩
    rcases Prod.mk.inj hEq with ⟨rfl, hEq2⟩; rcases Prod.mk.inj hEq2 with ⟨rfl, rfl⟩
    rcases simulateQ_1Key_clean_and_online_le P A.1.run b.q_on A.2.2.2.2.2 (KeyIndState.empty S secb)
      ⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩ (cleanPeers_nil S P S.N_id [])
      (b', s) hSim with ⟨hVP, hClean, hLenOn⟩
    have hLenAct : s.principals.length ≤ activeIdCount S b.q_on :=
      Nat.le_min.mpr ⟨by simpa [KeyIndState.empty] using hLenOn, principals_length_le_N_id hVP⟩
    dsimp only; rw [hasBadSigKeyInd_eq_any_ord S P s (activeIdCount S b.q_on) hClean hLenAct]
  rw [hCongr]
  exact toReal_any_range_le_sum (runKeyInd1KeySim S P A.1) (activeIdCount S b.q_on)
    fun ord (_, _, s) => hasBadSigKeyIndAtOrd S P ord s

/-! ## Pre-sampled creation-order game -/

@[expose] noncomputable def fg1KeyActivePreInitPrin (ord : ℕ) (optSk : Option Bytes)
    (S : Setup) (P : Primitives) (u : Fin S.N_id) : StateT (KeyIndState S) ProbComp KeyIndResponse := do
  let st ← get
  if st.principals.any (fun (idx, _) => idx == u.val) then return .noneResp
  let sk ← liftM (match optSk with
    | some sk0 => if st.principals.length == ord then pure sk0 else sampleScalar32
    | none => sampleScalar32)
  let pk := P.x25519Base sk
  let entry : PrincipalEntry :=
    { secIKA0 := sk, ikAPk := pk, secIKAsign := sk, ikSignPk := pk, corrupted := false }
  set { st with principals := (u.val, entry) :: st.principals }
  return .initPrinResp pk pk

@[expose] noncomputable def pqxdhKeyInd1KeyActiveFgPreImpl (ord : ℕ) (optSk : Option Bytes)
    (S : Setup) (P : Primitives) : QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp)
  | .initPrin u => liftFgBase (fg1KeyActivePreInitPrin ord optSk S P u)
  | q           => pqxdhKeyIndFgImpl S P q

@[expose] def hasFiredOrd {S : Setup} (ord : ℕ) (hst : KeyIndFgCutoffState S) : Bool :=
  decide (ord < hst.base.principals.length)

private theorem pqxdhKeyIndFgImpl_principals_len_and_ord {S : Setup} (P : Primitives) (ord : ℕ)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) (hq : ∀ u, q ≠ .initPrin u)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgImpl S P q).run hst)) :
    x.2.base.principals.length = hst.base.principals.length ∧
      prinAtOrd? ord x.2.base.principals = prinAtOrd? ord hst.base.principals := by
  have hb := mem_support_pqxdhKeyIndFgImpl_base P q hst x hx
  cases q with
  | initPrin u => exact False.elim (hq u rfl)
  | corruptIK u =>
    rcases (keyIndSigLens S).mem_support_realCorruptIK u hst.base (x.1, x.2.base) hb with
      ⟨_, hN⟩ | ⟨_, _, _, hSm⟩
    · rw [(Prod.mk.inj hN).2]; exact ⟨rfl, rfl⟩
    · dsimp only [keyIndSigLens] at hSm; rw [(Prod.mk.inj hSm).2]
      refine ⟨by simp, prinAtOrd?_map_fst_eq _ (fun ⟨i, _⟩ => ?_) hst.base.principals⟩
      by_cases h : (i == u.val) = true <;> simp [h]
  | genSPK u j =>
    rcases (keyIndSigLens S).mem_support_realGenSPK P u j hst.base (x.1, x.2.base) hb with
      hN | ⟨_, _, _, _, _, _, hSm⟩
    · rw [(Prod.mk.inj hN).2]; exact ⟨rfl, rfl⟩
    · dsimp only [keyIndSigLens] at hSm; rw [(Prod.mk.inj hSm).2]; exact ⟨rfl, rfl⟩
  | initiateOPK u i bnd =>
    rw [(pqxdhKeyIndImpl_initiateOPK_pres true S P u i bnd hst.base (x.1, x.2.base) hb).1]; exact ⟨rfl, rfl⟩
  | initiateNoOPK u i bnd =>
    rw [(pqxdhKeyIndImpl_initiateNoOPK_pres true S P u i bnd hst.base (x.1, x.2.base) hb).1]; exact ⟨rfl, rfl⟩
  | genOPK _ _ _ | acceptOPK _ _ _ _ | acceptNoOPK _ _ _ _ | testSession _
  | revealSessionKey _ | roQuery _ | revealDhSecrets | registerKey _ | revealSpkSk _ _ =>
    rw [(pqxdhKeyIndImpl_other_pres_local S P _ hst.base (fun _ h => by cases h) (fun _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (x.1, x.2.base) hb).1]
    exact ⟨rfl, rfl⟩

private theorem pqxdhKeyInd1KeyActiveFgPreImpl_none_step_base {S : Setup} (ord : ℕ) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) :
    Prod.map id KeyIndFgCutoffState.base <$> (pqxdhKeyInd1KeyActiveFgPreImpl ord none S P q).run hst =
      (pqxdhKeyIndImpl1KeyRo S P q).run hst.base := by
  cases q with
  | initPrin u =>
    unfold pqxdhKeyInd1KeyActiveFgPreImpl fg1KeyActivePreInitPrin liftFgBase
      pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    cases hst.base.principals.any (fun (idx, _) => idx == u.val) <;>
      simp [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure, map_eq_bind_pure_comp, bind_assoc]
  | _ =>
    unfold pqxdhKeyInd1KeyActiveFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl1KeyRo
    simp [map_eq_bind_pure_comp, bind_assoc]

private theorem pqxdhKeyInd1KeyActiveFgPreImpl_none_sim_base {S : Setup} {α : Type} (ord : ℕ)
    (P : Primitives) (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S) :
    Prod.map id KeyIndFgCutoffState.base <$>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) + pqxdhKeyInd1KeyActiveFgPreImpl ord none S P) oa).run hst =
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndState S) ProbComp) + pqxdhKeyIndImpl1KeyRo S P) oa).run hst.base := by
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure _ => simp [StateT.run_pure]
  | query_bind q k ih =>
    cases q with
    | inl _ => simp only [simulateQ_run_query_inl, map_bind]; congr 1; ext u; exact ih u hst
    | inr gq =>
      simp only [simulateQ_run_query_inr, map_bind,
        ← pqxdhKeyInd1KeyActiveFgPreImpl_none_step_base ord P gq hst, bind_map_left]
      congr 1; ext y; exact ih y.1 y.2

private theorem pqxdhKeyInd1KeyActiveFgPreImpl_initPrin_mem_support {S : Setup} (ord : ℕ)
    (optSk : Option Bytes) (P : Primitives) (u : Fin S.N_id) (hst : KeyIndFgCutoffState S)
    {x : KeyIndResponse × KeyIndFgCutoffState S}
    (hx : x ∈ support ((pqxdhKeyInd1KeyActiveFgPreImpl ord optSk S P (.initPrin u)).run hst)) :
    x.2.base = hst.base ∨
    ∃ entry, x.2.base = { hst.base with principals := (u.val, entry) :: hst.base.principals } := by
  unfold pqxdhKeyInd1KeyActiveFgPreImpl fg1KeyActivePreInitPrin at hx
  rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val) with
  | true =>
    rw [hAny] at hb; simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hb
    exact Or.inl (Prod.mk.inj hb).2
  | false =>
    rw [hAny] at hb
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hb
    rcases hb with ⟨_, _, hEq⟩; exact Or.inr ⟨_, (Prod.mk.inj hEq).2⟩

private theorem pqxdhKeyInd1KeyActiveFgPreImpl_preserves_hasFiredOrd {S : Setup} (ord : ℕ)
    (optSk : Option Bytes) (P : Primitives) (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyInd1KeyActiveFgPreImpl ord optSk S P q).run hst))
    (hFired : hasFiredOrd ord hst = true) : hasFiredOrd ord x.2 = true := by
  have hLt : ord < hst.base.principals.length := of_decide_eq_true hFired
  cases q with
  | initPrin u =>
    unfold hasFiredOrd
    rcases pqxdhKeyInd1KeyActiveFgPreImpl_initPrin_mem_support ord optSk P u hst hx with hB | ⟨_, hB⟩
    · rw [hB]; exact decide_eq_true hLt
    · rw [hB]; simp only [List.length_cons, decide_eq_true_eq]; omega
  | _ =>
    unfold hasFiredOrd
    rw [(pqxdhKeyIndFgImpl_principals_len_and_ord P ord _ hst (fun _ h => by cases h) x hx).1]
    exact decide_eq_true hLt

theorem evalDist_runKeyInd1KeySim_eq_activePreSample {S : Setup} (ord : ℕ) (P : Primitives)
    (A : KeyIndAdversary S) (obs : KeyIndState S → Bool) :
    let fullPre (sk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) + pqxdhKeyInd1KeyActiveFgPreImpl ord (some sk) S P
    𝒟[do let sk ← sampleScalar32; let secb ← $ᵗ Bool
         let (_, finalHst) ← (simulateQ (fullPre sk) A.run).run (KeyIndFgCutoffState.empty S secb)
         pure (obs finalHst.base)] =
    𝒟[runKeyInd1KeySim S P A >>= fun (_, _, finalSt) => pure (obs finalSt)] := by
  intro fullPre
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  unfold runKeyInd1KeySim; simp only [bind_assoc, pure_bind]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ fun secb _ => ?_
  have hPre :
      𝒟[sampleScalar32 >>= fun sk => (simulateQ (fullPre sk) A.run).run (KeyIndFgCutoffState.empty S secb)
          >>= fun x => pure (obs x.2.base)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) + pqxdhKeyInd1KeyActiveFgPreImpl ord none S P)
          A.run).run (KeyIndFgCutoffState.empty S secb) >>= fun x => pure (obs x.2.base)] := by
    refine evalDist_simulateQ_preSample_slot_eq sampleScalar32 (fun s => hasFiredOrd ord s = true)
      (pqxdhKeyInd1KeyActiveFgPreImpl ord none S P) (fun sk => pqxdhKeyInd1KeyActiveFgPreImpl ord (some sk) S P)
      (fun q s hFired => ⟨?_, fun x hx =>
        pqxdhKeyInd1KeyActiveFgPreImpl_preserves_hasFiredOrd ord none P q s x hx hFired⟩)
      (fun q s _ => ?_) A.run (KeyIndFgCutoffState.empty S secb) (fun x => pure (obs x.2.base))
    · intro sk; cases q with
      | initPrin u =>
        have hNe := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt (of_decide_eq_true hFired))
        unfold pqxdhKeyInd1KeyActiveFgPreImpl fg1KeyActivePreInitPrin liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hNe]
      | _ => rfl
    · cases q with
      | initPrin u =>
        unfold pqxdhKeyInd1KeyActiveFgPreImpl fg1KeyActivePreInitPrin liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.principals.any (fun (idx, _) => idx == u.val) with
        | true => exact Or.inl fun _ => rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hSlot : (s.base.principals.length == ord) = true
          · refine Or.inr ⟨fun _ => ?_, fun _ _ hx => ?_⟩
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure,
                StateT.run_monadLift, monadLift_self, StateT.run_set, pure_bind, bind_assoc]
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
                monadLift_self, StateT.run_set, pure_bind, support_pure, Set.mem_singleton_iff] at hx
              have hEqLen := beq_iff_eq.mp hSlot; unfold hasFiredOrd; rw [(Prod.mk.inj hx).2]
              simp only [List.length_cons, decide_eq_true_eq]; omega
          · exact Or.inl fun _ => by simp [hSlot]
      | _ => exact Or.inl fun _ => rfl
  rw [hPre, show KeyIndState.empty S secb = (KeyIndFgCutoffState.empty S secb).base from rfl,
    ← pqxdhKeyInd1KeyActiveFgPreImpl_none_sim_base ord P A.run (KeyIndFgCutoffState.empty S secb),
    bind_map_left]; rfl

@[expose] noncomputable def sig1KeyActiveWinBool {S : Setup} {α : Type} (P : Primitives) (sk : Bytes)
    (res : (α × Sig1KeyActiveSimState S) × List Bytes) : Bool :=
  sig1KeyWinBool P sk ((res.1.1, res.1.2.inner), res.2)

theorem one_le_evalDist_sig1KeyActiveWon {S : Setup} {α : Type} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) (maxLen : ℕ)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (st : Sig1KeyActiveSimState S) (msgs : List Bytes)
    (hWon : Sig1KeyWon P sk st.inner msgs) :
    1 ≤ 𝒟[(simulateQ (gapSigEufCmaFullImpl P ddh sk)
            (runWithSigDdhStep (sig1KeyActiveStep S maxLen) oa st)).run msgs >>=
          fun res => pure (sig1KeyActiveWinBool P sk res)] {true} := by
  induction oa using OracleComp.inductionOn generalizing st msgs with
  | pure _ =>
    rcases hWon with ⟨_, _, hfg, hver, hnotmem⟩
    simp [runWithSigDdhStep_pure, StateT.run_pure, sig1KeyActiveWinBool, sig1KeyWinBool, hfg, hver, hnotmem]
  | query_bind q k ih =>
    cases q with
    | inl n =>
      rw [runWithSigDdhStep_query_inl]
      have hq : (simulateQ (gapSigEufCmaFullImpl P ddh sk)
            (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl (Sum.inl n))) >>=
              fun u => runWithSigDdhStep (sig1KeyActiveStep S maxLen) (k u) st)).run msgs =
          (liftM (unifSpec.query n) >>= fun u => (simulateQ (gapSigEufCmaFullImpl P ddh sk)
              (runWithSigDdhStep (sig1KeyActiveStep S maxLen) (k u) st)).run msgs) := by
        simp [gapSigEufCmaFullImpl, primBaseImpl, QueryImpl.liftTarget,
          simulateQ_bind, StateT.run_bind, StateT.run_monadLift]
      rw [hq, bind_assoc]
      calc (1 : ℝ≥0∞) = 𝒟[liftM (unifSpec.query n) >>= fun _ => pure true] {true} := by
              rw [OracleComp.evalDist_bind_const]; simp
        _ ≤ _ := evalDist_bind_true_mono_of_support _ _ _ fun u _ => by simpa using ih u st msgs hWon
    | inr gq =>
      rcases hWon with ⟨mStar, sigStar, hfg, hver, hnotmem⟩; rw [runWithSigDdhStep_query_inr]
      have hStep : sig1KeyActiveStep S maxLen gq st = pure (.noneResp, st) := by
        unfold sig1KeyActiveStep; simp [hfg]
      rw [hStep, pure_bind]; exact ih .noneResp st msgs ⟨mStar, sigStar, hfg, hver, hnotmem⟩

private theorem pqxdhKeyInd1KeyActiveFgPreImpl_after_step_eq_static {S : Setup}
    (ord kIdx : ℕ) (optSk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) (hLt : ord < hst.base.principals.length) :
    (pqxdhKeyInd1KeyActiveFgPreImpl ord optSk S P q).run hst =
      (pqxdhKeyInd1KeyFgPreImpl kIdx none S P q).run hst := by
  cases q with
  | initPrin u =>
    have hNe := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)
    unfold pqxdhKeyInd1KeyActiveFgPreImpl pqxdhKeyInd1KeyFgPreImpl
      fg1KeyActivePreInitPrin fg1KeyPreInitPrin liftFgBase
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    cases hst.base.principals.any (fun (idx, _) => idx == u.val) with
    | true => simp
    | false =>
      cases optSk with
      | none => simp
      | some _ => simp [hNe]
  | _ => rfl

private theorem pqxdhKeyInd1KeyActiveFgPreImpl_safe_ord_step {S : Setup} (P : Primitives)
    (ord kIdx : ℕ) (optSk : Option Bytes) (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hLt : ord < hst.base.principals.length) (hOrd : prinAtOrd? ord hst.base.principals = some kIdx)
    (hSafe : (keyIndSigLens S).Safe P kIdx hst.base) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyActiveFgPreImpl ord optSk S P q).run hst),
      ord < x.2.base.principals.length ∧ prinAtOrd? ord x.2.base.principals = some kIdx ∧
      (keyIndSigLens S).Safe P kIdx x.2.base := fun x hx => by
  have hxStatic : x ∈ support ((pqxdhKeyInd1KeyFgPreImpl kIdx none S P q).run hst) := by
    rwa [← pqxdhKeyInd1KeyActiveFgPreImpl_after_step_eq_static ord kIdx optSk P q hst hLt]
  have hSafe' := pqxdhKeyInd1KeyFgPreImpl_safe_step S P kIdx none q hst hSafe x hxStatic
  cases q with
  | initPrin u =>
    rcases pqxdhKeyInd1KeyActiveFgPreImpl_initPrin_mem_support ord optSk P u hst hx with hB | ⟨_, hB⟩
    · rw [hB]; exact ⟨hLt, hOrd, hSafe⟩
    · exact ⟨by rw [hB]; simp; omega, by rw [hB, prinAtOrd?_cons_of_lt hLt]; exact hOrd, hSafe'⟩
  | _ =>
    have hPres := pqxdhKeyIndFgImpl_principals_len_and_ord P ord _ hst (fun _ h => by cases h) x hx
    exact ⟨by omega, by rw [hPres.2]; exact hOrd, hSafe'⟩

theorem evalDist_safe_active1Key_eq_zero {S : Setup} {α : Type} (P : Primitives) (ord kIdx : ℕ)
    (optSk : Option Bytes) (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (hLt : ord < hst.base.principals.length) (hOrd : prinAtOrd? ord hst.base.principals = some kIdx)
    (hSafe : (keyIndSigLens S).Safe P kIdx hst.base) :
    𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) + pqxdhKeyInd1KeyActiveFgPreImpl ord optSk S P) oa).run hst >>=
      fun (_, finalHst) => pure (hasBadSigKeyIndAtOrd S P ord finalHst.base)] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure _ =>
    have hBadF : hasBadSigKeyIndAt S P kIdx hst.base = false :=
      (keyIndSigLens S).safe_badAt_eq_false P kIdx hst.base hSafe
    simp [StateT.run_pure, hasBadSigKeyIndAtOrd, hOrd, hBadF]
  | query_bind q k ih =>
    cases q with
    | inl _ =>
      simp only [simulateQ_run_query_inl, bind_assoc]
      exact evalDist_bind_true_eq_zero_of_support _ _ fun u _ => ih u hst hLt hOrd hSafe
    | inr gq =>
      simp only [simulateQ_run_query_inr, bind_assoc]
      refine evalDist_bind_true_eq_zero_of_support _ _ fun y hy => ?_
      rcases pqxdhKeyInd1KeyActiveFgPreImpl_safe_ord_step P ord kIdx optSk gq hst hLt hOrd hSafe y hy with
        ⟨hLt', hOrd', hSafe'⟩
      exact ih y.1 y.2 hLt' hOrd' hSafe'

/-! ## Two-phase creation-order coupling (`Sig1KeyActiveRel`) -/

private noncomputable def withSupp {α : Type} (m : ProbComp α) (k : α → ProbComp Bool) (x : α) :
    ProbComp Bool := @ite _ (x ∈ support m) (Classical.propDecidable _) (k x) (pure false)

private theorem evalDist_bind_withSupp_eq {α : Type} (m : ProbComp α) (k : α → ProbComp Bool) :
    𝒟[m >>= k] = 𝒟[m >>= withSupp m k] :=
  OracleComp.evalDist_bind_congr_of_support m k (withSupp m k) fun x hx => by unfold withSupp; simp [hx]

private noncomputable def withSuppR {α : Type} (m : ProbComp α) (k : α → ProbComp Bool) (x : α) :
    ProbComp Bool := @ite _ (x ∈ support m) (Classical.propDecidable _) (k x) (pure true)

private theorem evalDist_bind_withSuppR_eq {α : Type} (m : ProbComp α) (k : α → ProbComp Bool) :
    𝒟[m >>= k] = 𝒟[m >>= withSuppR m k] :=
  OracleComp.evalDist_bind_congr_of_support m k (withSuppR m k) fun x hx => by unfold withSuppR; simp [hx]

@[expose] def toStaticSimState {S : Setup} (kIdx : ℕ) (stA : Sig1KeyActiveSimState S) : Sig1KeySimState S :=
  { stA.inner with targetParty := kIdx }

@[expose] def fromStaticSimState {S : Setup} (tp? : Option Nat) (ord : ℕ) (s : Sig1KeySimState S) :
    Sig1KeyActiveSimState S := { resolvedPrin? := tp?, inner := { s with targetParty := ord } }

@[simp] private theorem toStaticSimState_fromStaticSimState {S : Setup} (kIdx : ℕ) (tp? : Option Nat)
    (ord : ℕ) (s : Sig1KeySimState S) :
    toStaticSimState kIdx (fromStaticSimState tp? ord s) = { s with targetParty := kIdx } := rfl

private def sigBudgetSlack (S : Setup) (b : QueryBudget) : ℕ :=
  min S.N_spk_tot S.N_recv - activeSigBudget S b

private def toStaticSimStateB {S : Setup} (b : QueryBudget) (kIdx : ℕ)
    (stA : Sig1KeyActiveSimState S) : Sig1KeySimState S :=
  { stA.inner with
    targetParty := kIdx
    signBudget  := stA.inner.signBudget + sigBudgetSlack S b }

private def fromStaticSimStateB {S : Setup} (b : QueryBudget) (tp? : Option Nat) (ord : ℕ)
    (s : Sig1KeySimState S) : Sig1KeyActiveSimState S :=
  { resolvedPrin? := tp?
    inner := { s with
               targetParty := ord
               signBudget  := s.signBudget - sigBudgetSlack S b } }

private theorem toStaticSimStateB_fromStaticSimStateB {S : Setup} (b : QueryBudget)
    (kIdx : ℕ) (tp? : Option Nat) (ord : ℕ) (s : Sig1KeySimState S)
    (hGe : sigBudgetSlack S b ≤ s.signBudget) :
    toStaticSimStateB b kIdx (fromStaticSimStateB b tp? ord s) = { s with targetParty := kIdx } := by
  cases s; dsimp only [toStaticSimStateB, fromStaticSimStateB] at hGe ⊢; congr 1; omega

/-- Two-phase coupling relation between `hst` and `(stA, msgs)` via `Sig1KeyRel`. -/
@[expose] def Sig1KeyActiveRel (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (ord : ℕ) (uSk sk : Bytes)
    (huSk : uSk.length = 32) (hvSk : sk.length = 32) (rem : ℕ)
    (hst : KeyIndFgCutoffState S) (stA : Sig1KeyActiveSimState S) (msgs : List Bytes) : Prop :=
  let slack := min S.N_spk_tot S.N_recv - activeSigBudget S b
  stA.inner.targetParty = ord ∧
  min rem (stA.inner.signBudget + slack) ≤ stA.inner.signBudget ∧
  ((stA.resolvedPrin? = none ∧ hst.base.principals.length ≤ ord ∧
    Sig1KeyRel S b P hP S.N_id uSk sk huSk hvSk rem hst
      { stA.inner with targetParty := S.N_id, signBudget := stA.inner.signBudget + slack } msgs) ∨
   (∃ kIdx : ℕ, stA.resolvedPrin? = some kIdx ∧ kIdx < S.N_id ∧ ord < hst.base.principals.length ∧
    prinAtOrd? ord hst.base.principals = some kIdx ∧
    Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk rem hst
      { stA.inner with targetParty := kIdx, signBudget := stA.inner.signBudget + slack } msgs))

theorem sig1KeyActiveRel_empty (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (ord : ℕ)
    (uSk sk : Bytes) (huSk : uSk.length = 32) (hvSk : sk.length = 32) (secb : Bool) :
    Sig1KeyActiveRel S b P hP ord uSk sk huSk hvSk b.q_total (KeyIndFgCutoffState.empty S secb)
      (Sig1KeyActiveSimState.empty S b secb ord (P.sigPkGen sk)) [] := by
  have hInitEq : toStaticSimStateB b S.N_id
      (Sig1KeyActiveSimState.empty S b secb ord (P.sigPkGen sk)) =
      Sig1KeySimState.empty S secb S.N_id (P.sigPkGen sk) := by
    dsimp [toStaticSimStateB, Sig1KeyActiveSimState.empty, Sig1KeySimState.empty,
      sigBudgetSlack, activeSigBudget]
    congr 1; omega
  refine ⟨rfl, ?_, Or.inl ⟨rfl, Nat.zero_le ord, ?_⟩⟩
  · dsimp [Sig1KeyActiveSimState.empty, activeSigBudget]; omega
  · change Sig1KeyRel S b P hP S.N_id uSk sk huSk hvSk b.q_total (KeyIndFgCutoffState.empty S secb)
      (toStaticSimStateB b S.N_id (Sig1KeyActiveSimState.empty S b secb ord (P.sigPkGen sk))) []
    rw [hInitEq]; exact sig1KeyRel_empty S b P hP S.N_id uSk sk huSk hvSk secb

private theorem erasePrincipalsFg_eq_self {uIdx : ℕ} {ps : List (Nat × PrincipalEntry)}
    (hNot : ∀ kv ∈ ps, (kv.1 == uIdx) = false) : erasePrincipalsFg uIdx ps = ps := by
  unfold erasePrincipalsFg erasePrincipalEntryFg; induction ps with
  | nil => rfl
  | cons kv rest ih =>
    have hHead := hNot kv List.mem_cons_self; rcases kv with ⟨k, e⟩; dsimp only at hHead
    simp only [List.map_cons, hHead, Bool.false_eq_true, ↓reduceIte]
    exact congrArg _ (ih fun x hx => hNot x (List.mem_cons_of_mem _ hx))

private theorem clearPrincipalsTargetSign_eq_self {kIdx : ℕ} {ps : List (Nat × PrincipalEntry)}
    (hNot : ∀ kv ∈ ps, (kv.1 == kIdx) = false) : clearPrincipalsTargetSign kIdx ps = ps := by
  unfold clearPrincipalsTargetSign; induction ps with
  | nil => rfl
  | cons kv rest ih =>
    have hHead := hNot kv List.mem_cons_self; rcases kv with ⟨k, e⟩; dsimp only at hHead
    simp only [List.map_cons, hHead, Bool.false_eq_true, ↓reduceIte]
    exact congrArg _ (ih fun x hx => hNot x (List.mem_cons_of_mem _ hx))

private theorem sig1KeyRel_retarget_of_not_mem {S : Setup} {b : QueryBudget} {P : Primitives}
    {hP : CryptoWellFormedPrimitivesδ P} {uSk sk : Bytes} {huSk : uSk.length = 32} {hvSk : sk.length = 32}
    {rem : ℕ} {hst : KeyIndFgCutoffState S} {stA : Sig1KeyActiveSimState S} {msgs : List Bytes}
    (u : Fin S.N_id) (hAny : hst.base.principals.any (fun (idx, _) => idx == u.val) = false)
    (hRel : Sig1KeyRel S b P hP S.N_id uSk sk huSk hvSk rem hst (toStaticSimStateB b S.N_id stA) msgs) :
    Sig1KeyRel S b P hP u.val uSk sk huSk hvSk rem hst (toStaticSimStateB b u.val stA) msgs := by
  rcases hRel with ⟨hFgNone, _, hPk, ⟨st0, hClear, hInv⟩, _, hClean, hBud, hMsgs, _⟩
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, _, hPrins, hSpks, hOpks, hSess⟩
  have hNotN : ∀ kv ∈ hst.base.principals, (kv.1 == S.N_id) = false := fun kv hkv =>
    beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (hValidEc.1.1 kv hkv))
  have hNotU : ∀ kv ∈ hst.base.principals, (kv.1 == u.val) = false := fun kv hkv => by
    cases hEq : (kv.1 == u.val) with
    | false => rfl
    | true => rw [List.any_eq_true.mpr ⟨kv, hkv, hEq⟩] at hAny; cases hAny
  have hEraseEq : eraseStateFgIk S.N_send_tot u.val hst.base = eraseStateFgIk S.N_send_tot S.N_id hst.base := by
    unfold eraseStateFgIk; rw [erasePrincipalsFg_eq_self hNotU, erasePrincipalsFg_eq_self hNotN]
  have hSt0Prins : st0.base.principals = hst.base.principals := by
    rw [hBaseEq]; dsimp only [eraseStateFgIk]; exact erasePrincipalsFg_eq_self hNotN
  have hClearEq : clearFgTargetSign u.val st0 = clearFgTargetSign S.N_id st0 := by
    unfold clearFgTargetSign
    rw [hSt0Prins, clearPrincipalsTargetSign_eq_self hNotU, clearPrincipalsTargetSign_eq_self hNotN]
  have hBsmNil : bundleSignedMessages S.N_id hst.base.spkBundles = [] := by
    unfold bundleSignedMessages
    have hFilt : hst.base.spkBundles.filter (fun ((u0, _), _) => u0 == S.N_id) = [] :=
      List.filter_eq_nil_iff.mpr fun ⟨⟨u0, _⟩, _⟩ he => by
        simp [beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (hValidEc.2.1.1 _ he).1)]
    rw [hFilt]; rfl
  have hDeadU : deadDh1 u.val hst = false := by
    unfold deadDh1; cases hF : hst.base.principals.find? (fun (u0, _) => u0 == u.val) with
    | none => rfl
    | some kv =>
      have hEq := List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hF
      rw [hNotU kv (List.mem_of_find?_eq_some hF)] at hEq; cases hEq
  have hTgtVU : prinTargetIsV u.val (P.x25519Base sk) hst = true :=
    List.all_eq_true.mpr fun ⟨k0, e0⟩ hkv => by simp [hNotU (k0, e0) hkv]
  have hCleanU : CleanPeers S P u.val hst.base.principals (badPeersKeyInd hst.base) := fun ikB hikB => by
    rcases hClean ikB hikB with ⟨u0, e0, hMem0, hu0Lt, _, hPow0⟩
    refine ⟨u0, e0, hMem0, hu0Lt, fun hu0Eq => ?_, hPow0⟩
    have hFU := hNotU (u0, e0) hMem0; simp [hu0Eq] at hFU
  refine ⟨hFgNone, rfl, hPk, ⟨st0, ?_, ?_⟩, hDeadU, hCleanU, ?_, ?_, ?_⟩
  · dsimp only [toStaticSimStateB] at hClear ⊢; rw [hClearEq]; exact hClear
  · refine ⟨hBaseEq.trans hEraseEq.symm, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc,
      hTgtVU, fun kv hkv => ⟨(hPrins kv hkv).1, (hPrins kv hkv).2.1, fun hEq => ?_⟩, hSpks, hOpks, hSess⟩
    rw [hNotU kv hkv] at hEq; cases hEq
  · dsimp only [toStaticSimStateB] at hBud ⊢; rw [hBsmNil] at hBud
    simp only [List.length_nil, Nat.add_zero] at hBud; omega
  · intro m hm; have hmNil := hMsgs m hm; rw [hBsmNil] at hmNil; exact False.elim (List.not_mem_nil hmNil)
  · intro kv hkv hEq; rw [hNotU kv hkv] at hEq; cases hEq

private theorem sig1KeyRel_sim_principals_props {S : Setup} {b : QueryBudget} {P : Primitives}
    {hP : CryptoWellFormedPrimitivesδ P} {kIdx : ℕ} {uSk sk : Bytes} {huSk : uSk.length = 32}
    {hvSk : sk.length = 32} {rem : ℕ} {hst : KeyIndFgCutoffState S} {stA : Sig1KeyActiveSimState S}
    {msgs : List Bytes}
    (hRel : Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk rem hst (toStaticSimStateB b kIdx stA) msgs) :
    stA.inner.fg.base.principals.length = hst.base.principals.length ∧
    (∀ v, stA.inner.fg.base.principals.any (fun (idx, _) => idx == v) =
      hst.base.principals.any (fun (idx, _) => idx == v)) ∧
    stA.inner.fg.base.principals.length ≤ S.N_dh ∧
    (∀ kv ∈ stA.inner.fg.base.principals, kv.1 < S.N_id) := by
  rcases hRel with ⟨_, _, _, ⟨st0, hClear, hInv⟩, _, _, _, _, _⟩
  rcases hInv with ⟨hBaseEq, _, _, _, _, hValidEc, _, _, _, _, _⟩; dsimp only [toStaticSimStateB] at hClear
  have hPrinsEq : stA.inner.fg.base.principals =
      clearPrincipalsTargetSign kIdx (erasePrincipalsFg kIdx hst.base.principals) := by
    rw [hClear]; dsimp only [clearFgTargetSign]; rw [hBaseEq]; rfl
  have hLenEq : stA.inner.fg.base.principals.length = hst.base.principals.length := by
    rw [hPrinsEq, length_clearPrincipalsTargetSign, erasePrincipalsFg_length]
  have hLenNid := principals_length_le_N_id hValidEc.1
  have hNidLeDh : S.N_id ≤ S.N_dh := by unfold Setup.N_dh; omega
  refine ⟨hLenEq, fun v => by rw [hPrinsEq, any_idx_clearPrincipalsTargetSign, any_idx_erasePrincipalsFg],
    by omega, fun kv hkv => ?_⟩
  rw [hPrinsEq] at hkv; unfold clearPrincipalsTargetSign erasePrincipalsFg at hkv
  rcases List.mem_map.mp hkv with ⟨⟨i1, e1⟩, hkv1, hEq1⟩
  rcases List.mem_map.mp hkv1 with ⟨⟨i0, e0⟩, hkv0, hEq0⟩
  have hFst1 : kv.1 = i1 := by by_cases h : (i1 == kIdx) = true <;> simp [h] at hEq1 <;> rw [← hEq1]
  simp at hEq0; rw [hFst1, ← hEq0.1]; exact hValidEc.1.1 (i0, e0) hkv0

private theorem simulateQ_extractBundleForgeryActivePrim_none {S : Setup} (P : Primitives)
    (targetPk : Bytes) (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (bundle : PreKeyBundleInput)
    (prevForgery : Option (Bytes × Bytes)) (hLen : principals.length ≤ S.N_dh)
    (hLt : ∀ kv ∈ principals, kv.1 < S.N_id) :
    simulateQ (primBaseImpl P)
      (extractBundleForgeryActivePrim S none targetPk principals spkBundles bundle prevForgery) =
    simulateQ (primBaseImpl P)
      (extractBundleForgeryPrim S S.N_id targetPk principals spkBundles bundle prevForgery) := by
  unfold extractBundleForgeryActivePrim extractBundleForgeryPrim
  simp only [simulateQ_bind, simulateQ_isHonestUncorruptedPeerPrim S P principals bundle.ikB hLen, pure_bind]
  congr 1; ext v1; congr 1; ext v2; simp only [simulateQ_pure]; congr 1
  cases prevForgery with
  | some _ => rfl
  | none =>
    cases hPeer : isHonestUncorruptedPeer P principals bundle.ikB with
    | none => rfl
    | some k =>
      rcases findHonestPrincipal_of_isHonestUncorruptedPeer_eq_some P principals bundle.ikB hPeer with ⟨e, _, hm, _⟩
      simp [beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (hLt (k, e) hm))]

private theorem extractBundleForgeryActivePrim_some_eq {S : Setup} (k0 : ℕ) (targetPk : Bytes)
    (principals : List (Nat × PrincipalEntry)) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput) (prevForgery : Option (Bytes × Bytes)) :
    extractBundleForgeryActivePrim S (some k0) targetPk principals spkBundles bundle prevForgery =
      extractBundleForgeryPrim S k0 targetPk principals spkBundles bundle prevForgery := by
  unfold extractBundleForgeryActivePrim extractBundleForgeryPrim
  congr 1; ext peer?; congr 1; ext v1; congr 1; ext v2; cases prevForgery <;> cases peer? <;> rfl

private theorem sig1KeyTargetGenSpk_eq_static {S : Setup} (b : QueryBudget) (ord kIdx maxLen rem : ℕ)
    (u : Fin S.N_id) (j : Fin S.N_recv) (stA : Sig1KeyActiveSimState S)
    (hOrd : stA.inner.targetParty = ord) (hFg : stA.inner.forgery = none)
    (hEq : (u.val == kIdx) = true)
    (hMin : min (rem + 1) (stA.inner.signBudget + sigBudgetSlack S b) ≤ stA.inner.signBudget) :
    (do let (out, inner') ← sig1KeyTargetGenSpk S u j stA.inner; return (out, { stA with inner := inner' })) =
    Prod.map id (fromStaticSimStateB b stA.resolvedPrin? ord) <$>
      sig1KeyStep S maxLen (.genSPK u j) (toStaticSimStateB b kIdx stA) := by
  rcases stA with ⟨tp, ⟨fg, tP, tPk, sb, forg⟩⟩; dsimp only at hOrd hFg hMin; subst tP forg
  unfold sig1KeyTargetGenSpk sig1KeyStep toStaticSimStateB fromStaticSimStateB; dsimp only
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hEq]
  cases fg.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases fg.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp
    | some p =>
      rcases p with ⟨_, _⟩
      cases sb with
      | zero =>
        have hSlack0 : sigBudgetSlack S b = 0 := by omega
        simp [hSlack0]
      | succ sb' =>
        have hAdd : sb' + 1 + sigBudgetSlack S b = (sb' + sigBudgetSlack S b) + 1 := by omega
        rw [hAdd]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
          Prod.map_apply, id_eq, Nat.add_sub_cancel]

private theorem simulateQ_map_fromStaticB {S : Setup} (b : QueryBudget) (P : Primitives) (sk : Bytes)
    (tp' : Option Nat) (ord : ℕ) (msgs : List Bytes)
    {c1 : OracleComp SigDdhSimSpec (KeyIndResponse × Sig1KeyActiveSimState S)}
    {c2 : OracleComp SigDdhSimSpec (KeyIndResponse × Sig1KeySimState S)}
    (h : c1 = Prod.map id (fromStaticSimStateB b tp' ord) <$> c2) :
    (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk) c1).run msgs =
      (fun res => ((res.1.1, fromStaticSimStateB b tp' ord res.1.2), res.2)) <$>
      (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk) c2).run msgs := by
  rw [h, simulateQ_map, StateT.run_map]; rfl

private theorem simulateQ_sig1KeyActiveStep_non_initPrin {S : Setup} (b : QueryBudget)
    (P : Primitives) (sk : Bytes) (ord maxLen rem : ℕ) (gq : KeyIndQuery S) (hq : ∀ u, gq ≠ .initPrin u)
    (stA : Sig1KeyActiveSimState S) (msgs : List Bytes) (hOrd : stA.inner.targetParty = ord)
    (hFg : stA.inner.forgery = none) (hTp : stA.resolvedPrin? = none ∨ ∃ k0 < S.N_id, stA.resolvedPrin? = some k0)
    (hLen : stA.inner.fg.base.principals.length ≤ S.N_dh)
    (hLt : ∀ kv ∈ stA.inner.fg.base.principals, kv.1 < S.N_id)
    (hMin : min (rem + 1) (stA.inner.signBudget + sigBudgetSlack S b) ≤ stA.inner.signBudget) :
    let kIdx := stA.resolvedPrin?.getD S.N_id
    (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk) (sig1KeyActiveStep S maxLen gq stA)).run msgs =
      (fun res => ((res.1.1, fromStaticSimStateB b stA.resolvedPrin? ord res.1.2), res.2)) <$>
      (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
        (sig1KeyStep S maxLen gq (toStaticSimStateB b kIdx stA))).run msgs := by
  intro kIdx
  have hExtEq : ∀ bnd,
      simulateQ (primBaseImpl P) (extractBundleForgeryActivePrim S stA.resolvedPrin? stA.inner.targetPk
          stA.inner.fg.base.principals stA.inner.fg.base.spkBundles bnd none) =
      simulateQ (primBaseImpl P) (extractBundleForgeryPrim S kIdx stA.inner.targetPk
          stA.inner.fg.base.principals stA.inner.fg.base.spkBundles bnd none) := fun bnd => by
    rcases hTp with hN | ⟨k0, _, hS⟩
    · simp only [hN, kIdx, Option.getD_none]
      exact simulateQ_extractBundleForgeryActivePrim_none P _ _ _ bnd none hLen hLt
    · simp only [hS, kIdx, Option.getD_some, extractBundleForgeryActivePrim_some_eq]
  cases gq with
  | initPrin u => exact False.elim (hq u rfl)
  | genSPK u j =>
    have hMatch : optNatMatches stA.resolvedPrin? u.val = (u.val == kIdx) := by
      rcases hTp with hN | ⟨k0, _, hS⟩
      · simp [hN, kIdx, beq_eq_false_iff_ne.mpr (Nat.ne_of_lt u.isLt)]
      · simp [hS, kIdx]
    refine simulateQ_map_fromStaticB b P sk stA.resolvedPrin? ord msgs ?_
    cases hEq : (u.val == kIdx) with
    | true =>
      have hLHS : sig1KeyActiveStep S maxLen (.genSPK u j) stA =
          (do let (out, inner') ← sig1KeyTargetGenSpk S u j stA.inner; return (out, { stA with inner := inner' })) := by
        unfold sig1KeyActiveStep; simp [hFg, hMatch, hEq]
      rw [hLHS]; exact sig1KeyTargetGenSpk_eq_static b ord kIdx maxLen rem u j stA hOrd hFg hEq hMin
    | false =>
      rcases stA with ⟨tp, ⟨fg, tP, tPk, sb, forg⟩⟩; dsimp only at hOrd hFg hMatch; subst tP forg
      unfold sig1KeyActiveStep sig1KeyStep toStaticSimStateB fromStaticSimStateB
      simp [hMatch, hEq, map_eq_bind_pure_comp]
  | initiateOPK u i bnd | initiateNoOPK u i bnd =>
    have hEB := hExtEq bnd
    rcases stA with ⟨tp, ⟨fg, tP, tPk, sb, forg⟩⟩; dsimp only at hOrd hFg hEB; subst tP forg
    unfold sig1KeyActiveStep sig1KeyStep toStaticSimStateB fromStaticSimStateB; dsimp only
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, StateT.run_bind,
      simulateQ_embedPrim_sigDdh_run, map_bind, bind_map_left, hEB]
    congr 1; ext forg'; cases forg'.isSome <;>
      simp [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc]
  | corruptIK _ | genOPK _ _ _ | acceptOPK _ _ _ _ | acceptNoOPK _ _ _ _ | testSession _
  | revealSessionKey _ | roQuery _ | revealDhSecrets | registerKey _ | revealSpkSk _ _ =>
    refine simulateQ_map_fromStaticB b P sk stA.resolvedPrin? ord msgs ?_
    rcases stA with ⟨tp, ⟨fg, tP, tPk, sb, forg⟩⟩; dsimp only at hOrd hFg; subst tP forg
    unfold sig1KeyActiveStep sig1KeyStep toStaticSimStateB fromStaticSimStateB; simp [map_eq_bind_pure_comp]

private theorem fg1KeyActivePreInitPrin_eq_static {S : Setup} (P : Primitives) (ord kIdx : ℕ)
    (sk : Bytes) (u : Fin S.N_id) (hst : KeyIndFgCutoffState S)
    (hCond : hst.base.principals.any (fun (idx, _) => idx == u.val) = true ∨
      (hst.base.principals.length == ord) = (u.val == kIdx)) :
    (pqxdhKeyInd1KeyActiveFgPreImpl ord (some sk) S P (.initPrin u)).run hst =
      (pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P (.initPrin u)).run hst := by
  unfold pqxdhKeyInd1KeyActiveFgPreImpl pqxdhKeyInd1KeyFgPreImpl fg1KeyActivePreInitPrin fg1KeyPreInitPrin liftFgBase
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
  rcases hCond with hAny | hEqB
  · simp [hAny]
  · cases hst.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hEqB]

private theorem pqxdhKeyInd1KeyFgPreImpl_initPrin_mem_support {S : Setup} (P : Primitives)
    (kIdx : ℕ) (optSk : Option Bytes) (u : Fin S.N_id) (hst : KeyIndFgCutoffState S)
    {r : KeyIndResponse} {hst' : KeyIndFgCutoffState S}
    (hx : (r, hst') ∈ support ((pqxdhKeyInd1KeyFgPreImpl kIdx optSk S P (.initPrin u)).run hst)) :
    (hst.base.principals.any (fun (idx, _) => idx == u.val) = true ∧ hst'.base = hst.base) ∨
    (hst.base.principals.any (fun (idx, _) => idx == u.val) = false ∧
      ∃ entry, hst'.base = { hst.base with principals := (u.val, entry) :: hst.base.principals }) := by
  unfold pqxdhKeyInd1KeyFgPreImpl fg1KeyPreInitPrin at hx
  rcases mem_support_liftFgBase _ hst (r, hst') hx with ⟨hb, _⟩
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val) with
  | true =>
    rw [hAny] at hb; simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hb
    exact Or.inl ⟨rfl, (Prod.mk.inj hb).2⟩
  | false =>
    rw [hAny] at hb
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hb
    rcases hb with ⟨_, _, hEq⟩; exact Or.inr ⟨rfl, _, (Prod.mk.inj hEq).2⟩

private theorem sig1KeyActiveStep_initPrin_eq_static {S : Setup} (b : QueryBudget) (ord kIdx maxLen : ℕ)
    (tp' : Option Nat) (u : Fin S.N_id) (stA : Sig1KeyActiveSimState S)
    (hOrd : stA.inner.targetParty = ord) (hFg : stA.inner.forgery = none)
    (hCond : (stA.inner.fg.base.principals.any (fun (idx, _) => idx == u.val) = true ∧ tp' = stA.resolvedPrin?) ∨
      (stA.inner.fg.base.principals.any (fun (idx, _) => idx == u.val) = false ∧
        (stA.inner.fg.base.principals.length == ord) = (u.val == kIdx) ∧
        tp' = if u.val == kIdx then some u.val else stA.resolvedPrin?)) :
    sig1KeyActiveStep S maxLen (.initPrin u) stA =
      Prod.map id (fromStaticSimStateB b tp' ord) <$>
        sig1KeyStep S maxLen (.initPrin u) (toStaticSimStateB b kIdx stA) := by
  rcases stA with ⟨tp, ⟨fg, tP, tPk, sb, forg⟩⟩; dsimp only at hOrd hFg hCond; subst tP forg
  unfold sig1KeyActiveStep sig1KeyStep toStaticSimStateB fromStaticSimStateB; dsimp only
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rcases hCond with ⟨hAny, rfl⟩ | ⟨hAnyF, hEqB, rfl⟩
  · simp [hAny]
  · simp [hAnyF, hEqB, map_eq_bind_pure_comp, bind_assoc]

private theorem sig1KeyStep_signBudget_mem_support {S : Setup} (P : Primitives) (sk : Bytes)
    (maxLen : ℕ) (gq : KeyIndQuery S) (stS : Sig1KeySimState S) (msgs : List Bytes)
    {res : (KeyIndResponse × Sig1KeySimState S) × List Bytes}
    (hMem : res ∈ support ((simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
      (sig1KeyStep S maxLen gq stS)).run msgs)) :
    res.1.2.signBudget = stS.signBudget ∨
      (1 ≤ stS.signBudget ∧ res.1.2.signBudget + 1 = stS.signBudget) := by
  unfold sig1KeyStep at hMem
  cases hFg : stS.forgery.isSome with
  | true =>
    rw [hFg] at hMem
    simp only [↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hMem
    subst hMem; exact Or.inl rfl
  | false =>
    rw [hFg] at hMem; simp only [Bool.false_eq_true, ↓reduceIte] at hMem
    cases gq with
    | initPrin u =>
      dsimp only at hMem
      cases hAny : stS.fg.base.principals.any (fun x => x.1 == u.val) with
      | true =>
        rw [hAny] at hMem
        simp only [↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hMem
        subst hMem; exact Or.inl rfl
      | false =>
        rw [hAny] at hMem
        simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind, StateT.run_bind,
          simulateQ_pure, StateT.run_pure, MonadAttach.mem_support_bind, support_pure,
          Set.mem_singleton_iff] at hMem
        rcases hMem with ⟨_, _, _, _, hEq⟩; subst hEq; exact Or.inl rfl
    | genSPK u j =>
      dsimp only at hMem
      cases hTgt : (u.val == stS.targetParty) with
      | false =>
        rw [hTgt] at hMem
        simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind, StateT.run_bind,
          simulateQ_pure, StateT.run_pure, MonadAttach.mem_support_bind, support_pure,
          Set.mem_singleton_iff] at hMem
        rcases hMem with ⟨⟨_, _⟩, _, hEq⟩; subst hEq; exact Or.inl rfl
      | true =>
        rw [hTgt] at hMem; simp only [↓reduceIte] at hMem
        cases hDup : stS.fg.base.spkBundles.any (fun x => x.1 == (u.val, j.val)) with
        | true =>
          rw [hDup] at hMem
          simp only [↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hMem
          subst hMem; exact Or.inl rfl
        | false =>
          rw [hDup] at hMem; simp only [Bool.false_eq_true, ↓reduceIte] at hMem
          cases hFind : stS.fg.base.principals.find? (fun x => x.1 == u.val) with
          | none =>
            rw [hFind] at hMem
            simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hMem
            subst hMem; exact Or.inl rfl
          | some kv =>
            rcases kv with ⟨_, uEntry⟩; rw [hFind] at hMem; dsimp only at hMem
            cases hSb : stS.signBudget with
            | zero =>
              rw [hSb] at hMem
              simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hMem
              subst hMem; exact Or.inl hSb
            | succ sb' =>
              rw [hSb] at hMem
              simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
                MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hMem
              rcases hMem with ⟨_, _, _, _, _, _, _, _, ⟨_, _⟩, _, _, _, hEq⟩
              subst hEq; exact Or.inr ⟨by omega, rfl⟩
    | initiateOPK u i bnd | initiateNoOPK u i bnd =>
      simp only [simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hMem
      rcases hMem with ⟨⟨forgery', msgs1⟩, _, hMem2⟩
      cases hFs : forgery'.isSome with
      | true =>
        rw [hFs] at hMem2
        simp only [↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hMem2
        subst hMem2; exact Or.inl rfl
      | false =>
        rw [hFs] at hMem2
        simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind, StateT.run_bind,
          simulateQ_pure, StateT.run_pure, MonadAttach.mem_support_bind, support_pure,
          Set.mem_singleton_iff] at hMem2
        rcases hMem2 with ⟨⟨_, _⟩, _, hEq⟩; subst hEq; exact Or.inl rfl
    | corruptIK _ | genOPK _ _ _ | acceptOPK _ _ _ _ | acceptNoOPK _ _ _ _ | testSession _
    | revealSessionKey _ | roQuery _ | revealDhSecrets | registerKey _ | revealSpkSk _ _ =>
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hMem
      rcases hMem with ⟨⟨_, _⟩, _, hEq⟩; subst hEq; exact Or.inl rfl

private theorem apply_static_coupling {S : Setup} (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (ord kIdx : ℕ) (tp' : Option Nat)
    (uSk sk : Bytes) (huSk : uSk.length = 32) (hvSk : sk.length = 32) (gq : KeyIndQuery S) (rem : ℕ)
    (hst : KeyIndFgCutoffState S) (stA : Sig1KeyActiveSimState S) (msgs : List Bytes)
    (hMin : min (rem + 1) (stA.inner.signBudget + sigBudgetSlack S b) ≤ stA.inner.signBudget)
    (hm1 : (pqxdhKeyInd1KeyActiveFgPreImpl ord (some sk) S P gq).run hst =
      (pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P gq).run hst)
    (hm2 : (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk) (sig1KeyActiveStep S b.q_total gq stA)).run msgs =
      (fun res => ((res.1.1, fromStaticSimStateB b tp' ord res.1.2), res.2)) <$>
      (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
        (sig1KeyStep S b.q_total gq (toStaticSimStateB b kIdx stA))).run msgs)
    (hRelS : Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk (rem + 1) hst (toStaticSimStateB b kIdx stA) msgs)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : (KeyIndResponse × Sig1KeyActiveSimState S) × List Bytes → ProbComp Bool)
    (hSafeBr : ∀ r hst', (r, hst') ∈ support ((pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P gq).run hst) →
      (keyIndSigLens S).Safe P kIdx hst'.base → 𝒟[k1 (r, hst')] {true} = 0)
    (hWonBr : ∀ r stA' msgs', Sig1KeyWon P sk stA'.inner msgs' → 1 ≤ 𝒟[k2 ((r, stA'), msgs')] {true})
    (hContBr : ∀ r hst' stS' msgs', (r, hst') ∈ support ((pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P gq).run hst) →
      min rem ((fromStaticSimStateB b tp' ord stS').inner.signBudget + sigBudgetSlack S b) ≤
        (fromStaticSimStateB b tp' ord stS').inner.signBudget →
      Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk rem hst'
        (toStaticSimStateB b kIdx (fromStaticSimStateB b tp' ord stS')) msgs' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 ((r, fromStaticSimStateB b tp' ord stS'), msgs')] {true}) :
    𝒟[(pqxdhKeyInd1KeyActiveFgPreImpl ord (some sk) S P gq).run hst >>= k1] {true} ≤
    𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
        (sig1KeyActiveStep S b.q_total gq stA)).run msgs >>= k2] {true} := by
  let mS := (pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P gq).run hst
  let mR := (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
    (sig1KeyStep S b.q_total gq (toStaticSimStateB b kIdx stA))).run msgs
  let kR : (KeyIndResponse × Sig1KeySimState S) × List Bytes → ProbComp Bool :=
    fun res => k2 ((res.1.1, fromStaticSimStateB b tp' ord res.1.2), res.2)
  rw [hm1, evalDist_bind_withSupp_eq mS k1, hm2, bind_map_left, evalDist_bind_withSuppR_eq mR kR]
  refine sig1Key_step_coupling S b P hP kIdx uSk sk huSk hvSk gq rem hst (toStaticSimStateB b kIdx stA) msgs
    hRelS (withSupp mS k1) (withSuppR mR kR)
    (fun r hst' hSafe => ?_)
    (fun r stS' msgs' hWon => ?_)
    fun r hst' stS' msgs' hRel' => ?_
  · unfold withSupp; split_ifs with hx
    · exact hSafeBr r hst' hx hSafe
    · simp
  · unfold withSuppR; split_ifs with hy
    · exact hWonBr r (fromStaticSimStateB b tp' ord stS') msgs' hWon
    · simp
  · unfold withSuppR; split_ifs with hy
    · unfold withSupp; split_ifs with hx
      · have hBudStep := sig1KeyStep_signBudget_mem_support P sk b.q_total gq
          (toStaticSimStateB b kIdx stA) msgs hy
        dsimp only [toStaticSimStateB] at hBudStep
        have hGeSlack : sigBudgetSlack S b ≤ stS'.signBudget := by omega
        have hMin' : min rem ((fromStaticSimStateB b tp' ord stS').inner.signBudget + sigBudgetSlack S b) ≤
            (fromStaticSimStateB b tp' ord stS').inner.signBudget := by
          dsimp only [fromStaticSimStateB]; omega
        refine hContBr r hst' stS' msgs' hx hMin' ?_
        rw [toStaticSimStateB_fromStaticSimStateB b kIdx tp' ord stS' hGeSlack]
        have hP0 := hRel'.2.1; cases stS'; dsimp at hP0; subst hP0; exact hRel'
      · simp
    · simp

private theorem sig1KeyActive_step_no_retarget {S : Setup} (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (ord kIdx : ℕ) (uSk sk : Bytes)
    (huSk : uSk.length = 32) (hvSk : sk.length = 32) (gq : KeyIndQuery S) (rem : ℕ)
    (hst : KeyIndFgCutoffState S) (stA : Sig1KeyActiveSimState S) (msgs : List Bytes)
    (hOrd : stA.inner.targetParty = ord)
    (hMin : min (rem + 1) (stA.inner.signBudget + sigBudgetSlack S b) ≤ stA.inner.signBudget)
    (hTp : (stA.resolvedPrin? = none ∧ kIdx = S.N_id) ∨ (kIdx < S.N_id ∧ stA.resolvedPrin? = some kIdx))
    (hRelS : Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk (rem + 1) hst (toStaticSimStateB b kIdx stA) msgs)
    (hNoRet : ∀ u : Fin S.N_id, gq = .initPrin u →
      hst.base.principals.any (fun (idx, _) => idx == u.val) = false → hst.base.principals.length ≠ ord ∧ u.val ≠ kIdx)
    (PInv : KeyIndState S → Prop) (hInv0 : PInv hst.base)
    (hInitInv : ∀ u : Fin S.N_id, ∀ entry, gq = .initPrin u →
      hst.base.principals.any (fun (idx, _) => idx == u.val) = false →
      PInv { hst.base with principals := (u.val, entry) :: hst.base.principals })
    (hPresInv : ∀ base', base'.principals.length = hst.base.principals.length →
      prinAtOrd? ord base'.principals = prinAtOrd? ord hst.base.principals → PInv base')
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : (KeyIndResponse × Sig1KeyActiveSimState S) × List Bytes → ProbComp Bool)
    (hSafeK : ∀ r hst', PInv hst'.base → (keyIndSigLens S).Safe P kIdx hst'.base → 𝒟[k1 (r, hst')] {true} = 0)
    (hWon : ∀ r stA' msgs', Sig1KeyWon P sk stA'.inner msgs' → 1 ≤ 𝒟[k2 ((r, stA'), msgs')] {true})
    (hContK : ∀ r hst' stS' msgs', PInv hst'.base →
      min rem ((fromStaticSimStateB b stA.resolvedPrin? ord stS').inner.signBudget + sigBudgetSlack S b) ≤
        (fromStaticSimStateB b stA.resolvedPrin? ord stS').inner.signBudget →
      Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk rem hst'
        (toStaticSimStateB b kIdx (fromStaticSimStateB b stA.resolvedPrin? ord stS')) msgs' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 ((r, fromStaticSimStateB b stA.resolvedPrin? ord stS'), msgs')] {true}) :
    𝒟[(pqxdhKeyInd1KeyActiveFgPreImpl ord (some sk) S P gq).run hst >>= k1] {true} ≤
    𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
        (sig1KeyActiveStep S b.q_total gq stA)).run msgs >>= k2] {true} := by
  rcases sig1KeyRel_sim_principals_props hRelS with ⟨hSimLen, hSimAny, hSimDh, hSimLt⟩
  by_cases hIsInit : ∃ u, gq = .initPrin u
  · rcases hIsInit with ⟨u, rfl⟩
    have hCond : hst.base.principals.any (fun (idx, _) => idx == u.val) = true ∨
        (hst.base.principals.any (fun (idx, _) => idx == u.val) = false ∧
         (hst.base.principals.length == ord) = false ∧ (u.val == kIdx) = false) := by
      cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val) with
      | true => exact Or.inl rfl
      | false => exact Or.inr ⟨rfl, beq_eq_false_iff_ne.mpr (hNoRet u rfl hAny).1,
          beq_eq_false_iff_ne.mpr (hNoRet u rfl hAny).2⟩
    have hm1 := fg1KeyActivePreInitPrin_eq_static P ord kIdx sk u hst (hCond.imp id fun ⟨_, h1, h2⟩ => h1.trans h2.symm)
    have hm2 := simulateQ_map_fromStaticB b P sk stA.resolvedPrin? ord msgs
      (sig1KeyActiveStep_initPrin_eq_static b ord kIdx b.q_total stA.resolvedPrin? u stA hOrd hRelS.1
        (by rcases hCond with hAny | ⟨hAnyF, h1, h2⟩
            · exact Or.inl ⟨by rw [hSimAny]; exact hAny, rfl⟩
            · exact Or.inr ⟨by rw [hSimAny]; exact hAnyF, by rw [hSimLen, h1, h2], by simp [h2]⟩))
    have hSupp : ∀ r hst', (r, hst') ∈ support ((pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P (.initPrin u)).run hst) →
        PInv hst'.base := fun r hst' hx => by
      rcases pqxdhKeyInd1KeyFgPreImpl_initPrin_mem_support P kIdx (some sk) u hst hx with ⟨_, hB⟩ | ⟨hAnyF, entry, hB⟩
      · rw [hB]; exact hInv0
      · rw [hB]; exact hInitInv u entry rfl hAnyF
    exact apply_static_coupling b P hP ord kIdx stA.resolvedPrin? uSk sk huSk hvSk (.initPrin u) rem hst stA msgs
      hMin hm1 hm2 hRelS k1 k2 (fun r hst' hx hSf => hSafeK r hst' (hSupp r hst' hx) hSf) hWon
      fun r hst' stS' msgs' hx hMin' hRel' => hContK r hst' stS' msgs' (hSupp r hst' hx) hMin' hRel'
  · have hNoInit : ∀ u, gq ≠ .initPrin u := fun u hu => hIsInit ⟨u, hu⟩
    have hm1 : (pqxdhKeyInd1KeyActiveFgPreImpl ord (some sk) S P gq).run hst =
        (pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P gq).run hst := by
      cases gq with | initPrin u => exact False.elim (hNoInit u rfl) | _ => rfl
    have hGetD : stA.resolvedPrin?.getD S.N_id = kIdx := by rcases hTp with ⟨hN, rfl⟩ | ⟨_, hS⟩ <;> simp [*]
    have hm2 := simulateQ_sig1KeyActiveStep_non_initPrin b P sk ord b.q_total rem gq hNoInit stA msgs hOrd hRelS.1
      (hTp.imp And.left fun ⟨hk, hS⟩ => ⟨kIdx, hk, hS⟩) hSimDh hSimLt hMin
    dsimp only at hm2; rw [hGetD] at hm2
    have hSupp : ∀ r hst', (r, hst') ∈ support ((pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P gq).run hst) →
        PInv hst'.base := fun r hst' hx => by
      have hFgSupp : (r, hst') ∈ support ((pqxdhKeyIndFgImpl S P gq).run hst) := by
        cases gq with | initPrin u => exact False.elim (hNoInit u rfl) | _ => exact hx
      have hPres := pqxdhKeyIndFgImpl_principals_len_and_ord P ord gq hst hNoInit (r, hst') hFgSupp
      exact hPresInv hst'.base hPres.1 hPres.2
    exact apply_static_coupling b P hP ord kIdx stA.resolvedPrin? uSk sk huSk hvSk gq rem hst stA msgs
      hMin hm1 hm2 hRelS k1 k2 (fun r hst' hx hSf => hSafeK r hst' (hSupp r hst' hx) hSf) hWon
      fun r hst' stS' msgs' hx hMin' hRel' => hContK r hst' stS' msgs' (hSupp r hst' hx) hMin' hRel'

theorem sig1KeyActive_step_coupling (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (ord : ℕ) (uSk sk : Bytes)
    (huSk : uSk.length = 32) (hvSk : sk.length = 32) (gq : KeyIndQuery S) (rem : ℕ)
    (hst : KeyIndFgCutoffState S) (stA : Sig1KeyActiveSimState S) (msgs : List Bytes)
    (hRel : Sig1KeyActiveRel S b P hP ord uSk sk huSk hvSk (rem + 1) hst stA msgs)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : (KeyIndResponse × Sig1KeyActiveSimState S) × List Bytes → ProbComp Bool)
    (hSafe : ∀ r hst' kIdx, ord < hst'.base.principals.length → prinAtOrd? ord hst'.base.principals = some kIdx →
      (keyIndSigLens S).Safe P kIdx hst'.base → 𝒟[k1 (r, hst')] {true} = 0)
    (hWon : ∀ r stA' msgs', Sig1KeyWon P sk stA'.inner msgs' → 1 ≤ 𝒟[k2 ((r, stA'), msgs')] {true})
    (hCont : ∀ r hst' stA' msgs', Sig1KeyActiveRel S b P hP ord uSk sk huSk hvSk rem hst' stA' msgs' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 ((r, stA'), msgs')] {true}) :
    𝒟[(pqxdhKeyInd1KeyActiveFgPreImpl ord (some sk) S P gq).run hst >>= k1] {true} ≤
    𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
        (sig1KeyActiveStep S b.q_total gq stA)).run msgs >>= k2] {true} := by
  rcases hRel with ⟨hOrd, hMin, ⟨hTp, hLenLe, hRelS⟩ | ⟨kIdx, hTp, hkLt, hOrdLt, hPrinOrd, hRelS⟩⟩
  · by_cases hRet : ∃ u : Fin S.N_id, gq = .initPrin u ∧
        hst.base.principals.any (fun (idx, _) => idx == u.val) = false ∧ hst.base.principals.length = ord
    · rcases hRet with ⟨u, rfl, hAnyF, hLenEq⟩
      rcases sig1KeyRel_sim_principals_props hRelS with ⟨hSimLen, hSimAny, _, _⟩
      have hm1 := fg1KeyActivePreInitPrin_eq_static P ord u.val sk u hst (Or.inr (by simp [hLenEq]))
      have hm2 := simulateQ_map_fromStaticB b P sk (some u.val) ord msgs
        (sig1KeyActiveStep_initPrin_eq_static b ord u.val b.q_total (some u.val) u stA hOrd hRelS.1
          (Or.inr ⟨by rw [hSimAny]; exact hAnyF, by simp [hSimLen, hLenEq], by simp⟩))
      have hSuppU : ∀ r hst', (r, hst') ∈ support
            ((pqxdhKeyInd1KeyFgPreImpl u.val (some sk) S P (.initPrin u)).run hst) →
          ord < hst'.base.principals.length ∧ prinAtOrd? ord hst'.base.principals = some u.val := fun r hst' hx => by
        rcases pqxdhKeyInd1KeyFgPreImpl_initPrin_mem_support P u.val (some sk) u hst hx with ⟨hT, _⟩ | ⟨_, _, hB⟩
        · rw [hAnyF] at hT; cases hT
        · rw [hB]; exact ⟨by simp [hLenEq], prinAtOrd?_cons_eq hLenEq⟩
      exact apply_static_coupling b P hP ord u.val (some u.val) uSk sk huSk hvSk (.initPrin u) rem hst stA msgs
        hMin hm1 hm2 (sig1KeyRel_retarget_of_not_mem u hAnyF hRelS) k1 k2
        (fun r hst' hx hSf => hSafe r hst' u.val (hSuppU r hst' hx).1 (hSuppU r hst' hx).2 hSf) hWon
        fun r hst' stS' msgs' hx hMin' hRel' => hCont r hst' (fromStaticSimStateB b (some u.val) ord stS') msgs'
          ⟨rfl, hMin', Or.inr ⟨u.val, rfl, u.isLt, (hSuppU r hst' hx).1, (hSuppU r hst' hx).2, hRel'⟩⟩
    · exact sig1KeyActive_step_no_retarget b P hP ord S.N_id uSk sk huSk hvSk gq rem hst stA msgs
        hOrd hMin (Or.inl ⟨hTp, rfl⟩) hRelS (fun u hGq hAny => ⟨fun hE => hRet ⟨u, hGq, hAny, hE⟩, Nat.ne_of_lt u.isLt⟩)
        (fun base => base.principals.length ≤ ord) hLenLe
        (fun u _ hGq hAny => by have : hst.base.principals.length ≠ ord := fun hE => hRet ⟨u, hGq, hAny, hE⟩; simp; omega)
        (fun _ hL _ => by rw [hL]; exact hLenLe) k1 k2
        (fun _ _ _ ⟨hVP', ⟨ek, hek⟩, _⟩ => False.elim (Nat.lt_irrefl _ (hVP'.1 _ hek))) hWon
        fun r hst' stS' msgs' hLe' hMin' hRel' =>
          hCont r hst' (fromStaticSimStateB b stA.resolvedPrin? ord stS') msgs' ⟨rfl, hMin', Or.inl ⟨hTp, hLe', hRel'⟩⟩
  · exact sig1KeyActive_step_no_retarget b P hP ord kIdx uSk sk huSk hvSk gq rem hst stA msgs
      hOrd hMin (Or.inr ⟨hkLt, hTp⟩) hRelS
      (fun u _ hAny => ⟨Nat.ne_of_gt hOrdLt, fun hEq => by
        rcases mem_of_prinAtOrd?_eq_some hPrinOrd with ⟨e0, hMem0⟩
        have hT : hst.base.principals.any (fun (idx, _) => idx == u.val) = true :=
          List.any_eq_true.mpr ⟨(kIdx, e0), hMem0, by simp [hEq]⟩
        rw [hAny] at hT; cases hT⟩)
      (fun base => ord < base.principals.length ∧ prinAtOrd? ord base.principals = some kIdx) ⟨hOrdLt, hPrinOrd⟩
      (fun _ _ _ _ => ⟨by simp; omega, by rw [prinAtOrd?_cons_of_lt hOrdLt]; exact hPrinOrd⟩)
      (fun _ hL hPO => ⟨by omega, hPO.trans hPrinOrd⟩) k1 k2
      (fun r hst' ⟨hLt', hPO'⟩ hSf => hSafe r hst' kIdx hLt' hPO' hSf) hWon
      fun r hst' stS' msgs' ⟨hLt', hPO'⟩ hMin' hRel' =>
        hCont r hst' (fromStaticSimStateB b stA.resolvedPrin? ord stS') msgs'
          ⟨rfl, hMin', Or.inr ⟨kIdx, hTp, hkLt, hLt', hPO', hRel'⟩⟩

/-! ## Simulation induction and active `G0 -> G1` / `G0 -> G2` bounds -/

theorem evalDist_simulateQ_sig1KeyActive_le {S : Setup} {α : Type}
    (b : QueryBudget) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (ord : ℕ) (uSk sk : Bytes) (huSk : uSk.length = 32) (hvSk : sk.length = 32)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (rem : ℕ)
    (hQb : IsQueryBoundP oa (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) rem)
    (hst : KeyIndFgCutoffState S) (stA : Sig1KeyActiveSimState S) (msgs : List Bytes)
    (hRel : Sig1KeyActiveRel S b P hP ord uSk sk huSk hvSk rem hst stA msgs) :
    𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) + pqxdhKeyInd1KeyActiveFgPreImpl ord (some sk) S P) oa).run hst >>=
      fun (_, finalHst) => pure (hasBadSigKeyIndAtOrd S P ord finalHst.base)] {true} ≤
    𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
        (runWithSigDdhStep (sig1KeyActiveStep S b.q_total) oa stA)).run msgs >>=
      fun res => pure (sig1KeyActiveWinBool P sk res)] {true} := by
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndFgCutoffState S) ProbComp) +
    pqxdhKeyInd1KeyActiveFgPreImpl ord (some sk) S P
  induction oa using OracleComp.inductionOn generalizing rem hst stA msgs with
  | pure _ =>
    rcases hRel with ⟨_, _, ⟨_, hLenLe, _⟩ | ⟨kIdx, _, _, _, hPrinOrd, hRelS⟩⟩
    · simp [StateT.run_pure, hasBadSigKeyIndAtOrd, prinAtOrd?_of_length_le hLenLe]
    · have hBadF : hasBadSigKeyIndAt S P kIdx hst.base = false :=
        any_peerPartyIdx_eq_false_of_cleanPeers S P kIdx hst.base.principals (badPeersKeyInd hst.base) hRelS.2.2.2.2.2.1
      simp [StateT.run_pure, hasBadSigKeyIndAtOrd, hPrinOrd, hBadF]
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hQb
    cases q with
    | inl n =>
      rcases hQb with ⟨_, h_cont⟩; simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      rw [runWithSigDdhStep_query_inl]
      have hqR : (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
            (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl (Sum.inl n))) >>=
              fun u => runWithSigDdhStep (sig1KeyActiveStep S b.q_total) (k u) stA)).run msgs =
          (liftM (unifSpec.query n) >>= fun u => (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
              (runWithSigDdhStep (sig1KeyActiveStep S b.q_total) (k u) stA)).run msgs) := by
        simp [gapSigEufCmaFullImpl, primBaseImpl, QueryImpl.liftTarget,
          simulateQ_bind, StateT.run_bind, StateT.run_monadLift]
      simp only [simulateQ_run_query_inl, hqR, bind_assoc]
      exact evalDist_bind_true_mono_of_support _ _ _ fun u _ => ih u rem (h_cont u) hst stA msgs hRel
    | inr gq =>
      rcases hQb with ⟨h_abs | h_pos, h_cont⟩
      · exact False.elim (h_abs rfl)
      · cases rem with
        | zero => omega
        | succ rem' =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          rw [simulateQ_run_query_inr, runWithSigDdhStep_query_inr]
          simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
          exact sig1KeyActive_step_coupling S b P hP ord uSk sk huSk hvSk gq rem' hst stA msgs hRel
            (fun y => (simulateQ impl (k y.1)).run y.2 >>= fun (_, s) => pure (hasBadSigKeyIndAtOrd S P ord s.base))
            (fun z => (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
                (runWithSigDdhStep (sig1KeyActiveStep S b.q_total) (k z.1.1) z.1.2)).run z.2 >>=
              fun res => pure (sig1KeyActiveWinBool P sk res))
            (fun r hst' kIdx hLt' hOrd' hSf => evalDist_safe_active1Key_eq_zero P ord kIdx (some sk) (k r) hst' hLt' hOrd' hSf)
            (fun r stA' msgs' hWon => one_le_evalDist_sig1KeyActiveWon P P.isValidDhTriple sk b.q_total (k r) stA' msgs' hWon)
            fun r hst' stA' msgs' hRel' => ih r rem' (h_cont r) hst' stA' msgs' hRel'

theorem badSigProbKeyInd1KeyAtOrd_le_gapSigEufCma (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (ord : ℕ) (A : BoundedAdv (KeyIndAdversary S) b) :
    badSigProbKeyInd1KeyAtOrd S P ord A.1 ≤
      GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyActiveAt ord S b A) := by
  unfold badSigProbKeyInd1KeyAtOrd GapSigEufCmaReal GapSigEufCma
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runKeyInd1KeySim_eq_activePreSample ord P A.1 (hasBadSigKeyIndAtOrd S P ord),
    gapSigEufCmaExp_eq_fullImpl]
  unfold sigReductionKeyInd1KeyActiveAt sigReductionKeyInd1KeyActiveRunAt; dsimp only
  let uSk : Bytes := List.replicate 32 0
  have huSk : uSk.length = 32 := by simp [uSk]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ fun sk hSk => ?_
  have hvSk : sk.length = 32 := length_of_mem_support_sampleScalar32 hSk
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_unifSigDdh_run,
    simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ fun secb _ => ?_
  exact evalDist_simulateQ_sig1KeyActive_le b P hP ord uSk sk huSk hvSk A.1.run b.q_total A.2.2.2.2.1
    (KeyIndFgCutoffState.empty S secb) (Sig1KeyActiveSimState.empty S b secb ord (P.sigPkGen sk)) []
    (sig1KeyActiveRel_empty S b P hP ord uSk sk huSk hvSk secb)

theorem sum_gapSigEufCma_sigReductionKeyInd1KeyActiveAt_eq
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    (∑ ord ∈ Finset.range (activeIdCount S b.q_on),
      GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyActiveAt ord S b A)) =
    (activeIdCount S b.q_on : ℝ) *
      GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyActive S b A) := by
  by_cases hn : activeIdCount S b.q_on = 0
  · simp [hn]
  · have hSwap : 𝒟[gapSigEufCmaExp P P.isValidDhTriple (sigReductionKeyInd1KeyActive S b A)] =
        𝒟[sampleIndexRange (activeIdCount S b.q_on) >>= fun ord =>
          gapSigEufCmaExp P P.isValidDhTriple (sigReductionKeyInd1KeyActiveAt ord S b A)] := by
      simp only [gapSigEufCmaExp_eq_fullImpl]
      unfold sigReductionKeyInd1KeyActive sigReductionKeyInd1KeyActiveAt; dsimp only
      simp only [hn, ↓reduceIte, simulateQ_bind, StateT.run_bind, simulateQ_unifSigDdh_run,
        bind_map_left, bind_assoc]
      rw [OracleComp.evalDist_bind_bind_swap]
    unfold GapSigEufCmaReal GapSigEufCma; rw [hSwap]
    exact (mul_toReal_sampleIndexRange_bind_eq_sum (activeIdCount S b.q_on)
      fun ord => gapSigEufCmaExp P P.isValidDhTriple (sigReductionKeyInd1KeyActiveAt ord S b A)).symm

/-- Activity-bounded union bound on `badSigNoCollProbKeyInd1Key` via creation-order guessing. -/
theorem badSigNoCollProbKeyInd1Key_le_gapSigEufCma_active
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    badSigNoCollProbKeyInd1Key S P A.1 ≤ (activeIdCount S b.q_on : ℝ) *
      GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyActive S b A) := by
  calc badSigNoCollProbKeyInd1Key S P A.1
      ≤ ∑ ord ∈ Finset.range (activeIdCount S b.q_on), badSigProbKeyInd1KeyAtOrd S P ord A.1 :=
        badSigNoCollProbKeyInd1Key_le_sum_ord S b P A
    _ ≤ ∑ ord ∈ Finset.range (activeIdCount S b.q_on),
          GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyActiveAt ord S b A) :=
        Finset.sum_le_sum fun ord _ => badSigProbKeyInd1KeyAtOrd_le_gapSigEufCma S b P hP ord A
    _ = (activeIdCount S b.q_on : ℝ) *
          GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyActive S b A) :=
        sum_gapSigEufCma_sigReductionKeyInd1KeyActiveAt_eq S P b A

/-- Activity-bounded one-key Hop `G0_1 -> G1` bound via `sigReductionKeyInd1KeyActive`. -/
theorem keyInd1Key_hop_G0_1_G1_active_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    |keyInd1KeyAdvG0_1 S P A.1 - keyInd1KeyAdvG1 S P A.1| ≤ (activeIdCount S b.q_on : ℝ) *
      GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyActive S b A) :=
  (keyInd1Key_hop_G0_1_G1_le_noCollProb S P A.1).trans
    (badSigNoCollProbKeyInd1Key_le_gapSigEufCma_active S P hP b A)

theorem keyInd1Key_hop_G0_1_G2_active_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    |keyInd1KeyAdvG0_1 S P A.1 - keyInd1KeyAdvG2 S P A.1| ≤ (activeIdCount S b.q_on : ℝ) *
      GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyActive S b A) := by
  rw [← keyInd1KeyAdvG1_eq_G2 S P A.1]; exact keyInd1Key_hop_G0_1_G1_active_le S P hP b A

theorem keyInd1Key_hop_G0_G1_active_of_ecColl (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    {ecCollBound : ℝ} (hColl : |keyInd1KeyAdvG0 S P A.1 - keyInd1KeyAdvG0_1 S P A.1| ≤ ecCollBound) :
    |KeyInd1KeyRoAdvantageReal S P A.1 - keyInd1KeyAdvG1 S P A.1| ≤
      (activeIdCount S b.q_on : ℝ) *
        GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyActive S b A) + ecCollBound := by
  rw [← keyInd1KeyAdvG0_eq S P A.1]
  have h01_1 := keyInd1Key_hop_G0_1_G1_active_le S P hP b A
  have hTri := abs_sub_le (keyInd1KeyAdvG0 S P A.1) (keyInd1KeyAdvG0_1 S P A.1) (keyInd1KeyAdvG1 S P A.1)
  linarith

/-- Activity-bounded one-key Hop `G0 -> G2` bound combining `sigReductionKeyInd1KeyActive` with an
    EC public-key collision bound. -/
theorem keyInd1Key_hop_G0_G2_active_of_ecColl (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    {ecCollBound : ℝ} (hColl : |keyInd1KeyAdvG0 S P A.1 - keyInd1KeyAdvG0_1 S P A.1| ≤ ecCollBound) :
    |KeyInd1KeyRoAdvantageReal S P A.1 - keyInd1KeyAdvG2 S P A.1| ≤
      (activeIdCount S b.q_on : ℝ) *
        GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyActive S b A) + ecCollBound := by
  rw [← keyInd1KeyAdvG1_eq_G2 S P A.1]; exact keyInd1Key_hop_G0_G1_active_of_ecColl S P hP b A hColl

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveSigHop
