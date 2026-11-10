/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Specifications.Game.ModelIface
public import Computational.Proofs.SpecLemmas.Game.BhShallowHelpers -- proof-setup: allow-public-import
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1 -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.AtomicTablesHonest -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHaltedEval -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHaltedInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PqxdhSimTypes -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.M3Interfaces -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Soundness

/-!
# Clamped Prefix and Handshake Invariants

Defines per-instance clamped driver invariants (`HaltedPrefixSimInvInst` and
`HaltedKindRealSimInvInst`) preserved across `pqxdhKeyIndImpl1KeyReal` handshake and Double Ratchet
session steps, together with coupled one-stage simulation for `pqxdhKeyInd1KeyExpForHandshake`.
-/

public section

set_option autoImplicit false

open scoped ENNReal BigOperators

namespace Computational.Proofs.E2E.Dsl.CompositionHaltedPrefixInv

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface GameCodec Env Expr Comp Mid CostedReduction
  TwoStageCostedReduction runFuel atomicSig atomicE2EOps e2eKeyIndTargetIface e2eSessionTargetIface
  keyIndQT keyIndQenc keyIndRenc prefixCtxT sidT sidV smQT smQenc)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (BHModelInst BHE2EDrvState BHE2ESmResp BHTargetQuery BHTargetResp
  BHPrefixCtx BhShallowRed BhShallowTwoStageRed Bytes ModelDriverInstanceMeta SampledSessionKey
  bhBaseMirror bhDrvKiQueryOk bhE2EDrvInstClean bhE2EFinishStartSpk
  bhE2EGuard bhE2EInstIkACorr bhE2EMirror bhFwdU bhIsBobRecvSMQuery
  bhLiftP bhNoOpkRespPromoted bhPackSmResp
  bhShallowCheckExtSm bhShallowCommitExtSm bhShallowFinishPrefix bhShallowImplOfHandle
  bhShallowRunFuel bhShallowRunFuel_pure bhShallowRunFuel_query_inl
  bhShallowRunFuel_query_inr_zero bhShallowRunFuel_query_inr_succ
  bhShallowStepPostLocal bhShallowStepPreNonCtl
  bhTargetGameSpec bhTargetQenc bhTargetRdec e2eTargetGameCodec isSmTargetQuery
  pqxdhKeyIndExpForHandshake stageOneAsProbComp)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (SessionHaltTracker
  bhClassifyTarget bhClassifyTargetOnly
  bhE2ELocalStartSessionTracked bhE2EStepLocalSmSessionTracked
  bhE2EStepLocalSmSessionTracked_eq_filter bhPrefixHandlePostWithSessionTracked
  bhPrefixHandlePreWithSessionTracked bhPrefixRedWithSessionTracked
  bhShallowStepPostLocalSessionTracked bhShallowStepPreCtlSessionTracked
  bhShallowStepPreNonCtlSessionTracked)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness (HaltedPausedInv
  HaltedTargetAdvPerInstanceBounded ValidSimTrackInv
  bhKindRedWithHalted_eq_bhKindRedWithTracked bhPrefixRedWithHalted_eq_bhPrefixRedWithSessionTracked)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst (HaltedKindSimInvInst
  isQueryBoundP_min isSendKiQuery nextSendDone nextSessDone)
open Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst (StepBudgetOkInst StepNextInvInst
  TwoStageAtomicSimSpecInst isKiQ isSendQ isSendQ_inl_inl isSessQ isStartQ nextSessRem
  stepBudgetOkInst_of_bounds twoStage_stage12_comp_eq_inst)
open Computational.Proofs.E2E.Dsl.KindRedHalted (HaltedKindSubprograms bhKindHandleWithHalted
  bhKindRedWithHalted drvKindHaltedEnc drvKindHaltedTy kindHandleHalted_eval_ctl
  kindHandleHalted_eval_ki kindHandleHalted_eval_sm kindRedHalted packAtomicSmRespEnc)
open Computational.Proofs.E2E.Dsl.KindRedHaltedEval (atomicKindRespEnc
  e2eTargetGameCodec_rdec_atomicKindRespEnc)
open Computational.Proofs.E2E.Dsl.PrefixRedHalted (HaltedPrefixSubprograms bhPrefixHandlePostWithHalted
  bhPrefixHandlePreWithHalted bhPrefixRedWithHalted bhShallowStepPostLocalHalted
  bhShallowStepPreCtlHalted bhShallowStepPreNonCtlHalted drvHaltedEnc drvHaltedTy
  prefixHandlePostHalted_eval_ctl prefixHandlePostHalted_eval_ki prefixHandlePostHalted_eval_sm
  prefixHandlePreHalted_eval_ctl prefixHandlePreHalted_eval_ki prefixHandlePreHalted_eval_sm
  prefixKiStepHaltedC prefixRedHalted prefixRedHalted_stage1Queries)
open Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval (atomicGameRespEnc atomicPrefixCtxEnc
  atomicSessionTargetIface_fwdU_eq_bhFwdU e2eTargetGameCodec_rdec_atomicGameRespEnc
  mapMidEnc mapOut1Enc mapPreEnc mem_support_of_mem_support_stageOneAsProbComp)
open Computational.Proofs.E2E.Dsl.PrefixRedHaltedInst (ValidHaltedPrefixSubprogramsInst)
open Computational.Proofs.E2E.Dsl.M3Interfaces (DrvMetaAligned DrvMirrorBounded
  DrvQueryBounded DrvSessionsBounded KeyIndReachBounded
  bhExtSmStep bhFilterSmQuery bhPromoteSlotK)

private theorem st_run_pure {σ : Type} {m : Type → Type} [Monad m] {α : Type}
    (a : α) (s : σ) : (pure a : StateT σ m α).run s = pure (a, s) := rfl

private theorem st_run_get_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (k : σ → StateT σ m α) (s : σ) : (MonadState.get >>= k).run s = (k s).run s :=
  pure_bind (s, s) _

private theorem st_run_getOf_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (k : σ → StateT σ m α) (s : σ) : (MonadStateOf.get >>= k).run s = (k s).run s :=
  pure_bind (s, s) _

private theorem st_run_set_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (s' : σ) (k : PUnit → StateT σ m α) (s : σ) :
    (MonadStateOf.set s' >>= k).run s = (k PUnit.unit).run s' :=
  pure_bind (PUnit.unit, s') _

private theorem st_run_set {σ : Type} {m : Type → Type} [Monad m] (s' s : σ) :
    (MonadStateOf.set s' : StateT σ m PUnit).run s = pure (PUnit.unit, s') := rfl

private theorem st_run_lift {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (x : m α) (s : σ) :
    (liftM x : StateT σ m α).run s = (fun a => (a, s)) <$> x := by
  change (x >>= fun a => pure (a, s)) = (fun a => (a, s)) <$> x
  rw [map_eq_bind_pure_comp]; rfl

private theorem st_run_lift_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (x : m α) (k : α → StateT σ m β) (s : σ) :
    ((liftM x : StateT σ m α) >>= k).run s = (x >>= fun a => (k a).run s) := by
  change ((x >>= fun a => pure (a, s)) >>= fun p => (k p.1).run p.2) = _
  simp only [LawfulMonad.bind_assoc, pure_bind]

private theorem st_run_ite {σ : Type} {m : Type → Type} {α : Type}
    (c : Prop) [Decidable c] (a b : StateT σ m α) (s : σ) :
    (if c then a else b).run s = if c then a.run s else b.run s := by
  split_ifs <;> rfl

/-- Joint driver, tracker, and `pqxdhKeyIndImpl1KeyReal` state invariant for `bhPrefixRedWithSessionTracked`. -/
structure HaltedPrefixSimInvInst {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (TrackInv : ℕ → τ → Prop)
    (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget)
    (qStart : ℕ) (qs : ℕ → ℕ)
    (qKiDone qSendDone qStartDone : ℕ) (qSessDone : ℕ → ℕ)
    (σH : BHE2EDrvState S ℓ × List τ) : Prop where
  base : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH
  st_list : PqxdhSimTypes.stListBounded S qKiDone σH.1.st
  bundles_le_st : σH.1.bundles.length ≤ σH.1.st.spkBundles.length
  tested_le_start : (σH.1.st.sessions.filter (·.tested)).length ≤ qStartDone
  sends_init : ∀ e ∈ σH.1.sends, PqxdhSimTypes.isInitSid e.1 = true
  resp_untested : ∀ r ∈ σH.1.st.respSessions,
    r.tested = false ∧ PqxdhSimTypes.isInitSid r.sid = false

theorem HaltedPrefixSimInvInst.stListBounded_qTotal {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    PqxdhSimTypes.stListBounded S b.q_total σH.1.st :=
  h.st_list.mono h.base.ki_le

theorem HaltedPrefixSimInvInst.bundles_length_le {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    σH.1.bundles.length ≤ min b.q_total S.N_spk_tot :=
  Nat.le_trans h.bundles_le_st h.stListBounded_qTotal.spkBundles_le

theorem HaltedPrefixSimInvInst.drvMirrorBounded_clamped {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    DrvMirrorBounded b.q_total (min b.q_total S.N_spk_tot) b.q_total b.q_total b.q_total
      (min qStart (min b.q_total S.N_send_tot)) σH.1 where
  prins_le := Nat.le_trans h.base.mirror.prins_le h.base.ki_le
  bundles_le := h.bundles_length_le
  opks_le := Nat.le_trans h.base.mirror.opks_le h.base.ki_le
  sends_le := Nat.le_trans h.base.mirror.sends_le h.base.ki_le
  corrPrins_le := Nat.le_trans h.base.mirror.corrPrins_le h.base.ki_le
  insts_le := h.base.insts_length_le
  instMeta_le := h.base.instMeta_length_le
  revSpks_le := Nat.le_trans h.base.mirror.revSpks_le h.base.ki_le

theorem HaltedPrefixSimInvInst.tested_length_le {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    (σH.1.st.sessions.filter (·.tested)).length ≤ min qStart (min b.q_total S.N_send_tot) := by
  have h1 : (σH.1.st.sessions.filter (·.tested)).length ≤ qStartDone := h.tested_le_start
  have h2 : qStartDone ≤ min qStart S.N_send_tot := h.base.start_le
  have h3 : (σH.1.st.sessions.filter (·.tested)).length ≤ σH.1.st.sessions.length :=
    List.length_filter_le _ _
  have h4 : σH.1.st.sessions.length ≤ min b.q_total S.N_send_tot :=
    h.stListBounded_qTotal.sessions_le
  omega

theorem HaltedPrefixSimInvInst.respSessions_untested {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    ∀ r ∈ σH.1.st.respSessions, r.tested = false :=
  fun r hr => (h.resp_untested r hr).1

theorem HaltedPrefixSimInvInst.empty {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (TrackInv : ℕ → τ → Prop) (C : Crypto) (K : MlKem)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (secb : Bool) :
    HaltedPrefixSimInvInst (S := S) (ℓ := ℓ) TrackInv C K b qStart qs 0 0 0 (fun _ => 0)
      (({ b := secb } : BHE2EDrvState S ℓ), ([] : List τ)) where
  base := HaltedKindSimInvInst.empty TrackInv C K b qStart qs secb
  st_list := PqxdhSimTypes.stListBounded.empty S 0 false
  bundles_le_st := Nat.zero_le _
  tested_le_start := Nat.zero_le _
  sends_init := by intro _ h; nomatch h
  resp_untested := by intro _ h; nomatch h

theorem HaltedPrefixSimInvInst.setBit {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ} (flip : Bool)
    (h : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone
      ({ σH.1 with b := flip }, σH.2) where
  base := h.base.setBit flip
  st_list := h.st_list
  bundles_le_st := h.bundles_le_st
  tested_le_start := h.tested_le_start
  sends_init := h.sends_init
  resp_untested := h.resp_untested

private theorem length_filter_tested_map_set {S : SignalPqxdh.Setup}
    (sid : SignalPqxdh.SessionId S) :
    ∀ (l : List (SignalPqxdh.KeyIndInitiatorEntry S)),
      (l.map SignalPqxdh.KeyIndInitiatorEntry.sid).Nodup →
      ((l.map (fun s => if s.sid == sid then { s with tested := true } else s)).filter
        (·.tested)).length ≤ (l.filter (·.tested)).length + 1
  | [], _ => by simp
  | a :: as, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases hnd with ⟨hnotmem, hnd_as⟩
    simp only [List.map_cons]
    split_ifs with hbeq
    · have ha_eq : a.sid = sid := beq_iff_eq.mp hbeq
      have htail : as.map (fun s => if s.sid == sid then { s with tested := true } else s) = as := by
        conv_rhs => rw [← List.map_id as]
        apply List.map_congr_left
        intro x hx
        have hne : (x.sid == sid) = false :=
          beq_eq_false_iff_ne.mpr fun hxs =>
            hnotmem ((hxs.trans ha_eq.symm) ▸ List.mem_map_of_mem hx)
        simp [hne]
      rw [htail]
      cases htest : a.tested <;>
        simp only [List.filter_cons, htest, ↓reduceIte, Bool.false_eq_true, List.length_cons] <;>
        omega
    · have ih := length_filter_tested_map_set sid as hnd_as
      cases htest : a.tested <;>
        simp only [List.filter_cons, htest, ↓reduceIte, Bool.false_eq_true, List.length_cons] <;>
        omega

private theorem filter_tested_map_eq {S : SignalPqxdh.Setup}
    (f : SignalPqxdh.KeyIndInitiatorEntry S → SignalPqxdh.KeyIndInitiatorEntry S) :
    ∀ (l : List (SignalPqxdh.KeyIndInitiatorEntry S)),
      (∀ s ∈ l, (f s).tested = s.tested) →
      ((l.map f).filter (·.tested)).length = (l.filter (·.tested)).length
  | [], _ => rfl
  | a :: as, hf => by
    have ha := hf a List.mem_cons_self
    have ih := filter_tested_map_eq f as (fun s hs => hf s (List.mem_cons_of_mem _ hs))
    simp only [List.map_cons, List.filter_cons, ha]
    split_ifs <;> simp [ih]

private theorem sends_init_mirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {σ : BHE2EDrvState S ℓ} (hs : ∀ e ∈ σ.sends, PqxdhSimTypes.isInitSid e.1 = true)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    ∀ e ∈ (bhE2EMirror σ kq kr).sends, PqxdhSimTypes.isInitSid e.1 = true := by
  intro e he
  cases kq <;> cases kr <;>
    simp only [bhE2EMirror, bhBaseMirror, List.mem_cons] at he
  all_goals
    first
    | exact hs e he
    | (rcases he with rfl | he' <;> [rfl; exact hs _ he'])

set_option linter.unusedSimpArgs false in
private theorem runKeyIndInitiate_false_extra {S : SignalPqxdh.Setup} {P : SignalPqxdh.Primitives}
    {sid : SignalPqxdh.SessionId S} {u : Fin S.N_id}
    {bundle : SignalPqxdh.PreKeyBundleInput} {st : SignalPqxdh.KeyIndState S}
    {out : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hmem : out ∈ support ((SignalPqxdh.runKeyIndInitiate false S P sid u bundle).run st)) :
    out.2.spkBundles = st.spkBundles ∧
      (out.2.sessions.filter (·.tested)).length = (st.sessions.filter (·.tested)).length ∧
      out.2.respSessions = st.respSessions := by
  unfold SignalPqxdh.runKeyIndInitiate SignalPqxdh.evalHkdfOrRo at hmem
  simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
    LawfulMonad.bind_assoc] at hmem
  by_cases hdup : (st.sessions.any (fun e => e.sid == sid)) = true
  · simp only [hdup, ite_true, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨rfl, rfl, rfl⟩
  · simp only [hdup, ite_false] at hmem
    rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
    · rw [hfind] at hmem; dsimp only at hmem
      simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨rfl, rfl, rfl⟩
    · rw [hfind] at hmem; dsimp only at hmem
      simp only [st_run_ite, st_run_pure] at hmem
      by_cases hkosk :
          (!SignalPqxdh.koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle) = true
      · simp only [hkosk, ite_true, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨rfl, rfl, rfl⟩
      · simp only [hkosk, Bool.false_eq_true, ↓reduceIte, ite_false, st_run_lift_bind, st_run_ite,
          st_run_pure, LawfulMonad.bind_assoc, MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨ekASk, _, kemCoins, _, hmem⟩
        by_cases hsig : (!(P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
            (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
            (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
        · simp only [hsig, ↓reduceIte, ite_true, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact ⟨rfl, rfl, rfl⟩
        · simp only [hsig, Bool.false_eq_true, ↓reduceIte, ite_false] at hmem
          rcases henc : P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
          · rw [henc] at hmem; dsimp only at hmem
            simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact ⟨rfl, rfl, rfl⟩
          · rw [henc] at hmem; dsimp only at hmem
            simp only [Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc, pure_bind,
              st_run_get_bind, st_run_getOf_bind, st_run_lift_bind, st_run_lift, st_run_set_bind,
              st_run_pure, map_pure, MonadAttach.mem_support_bind, support_pure,
              Set.mem_singleton_iff, exists_eq_left] at hmem
            rcases hkr : SignalPqxdh.keyIndPartnerRandKey? P st.respSessions _ with _ | drKeyRand
            · rw [hkr] at hmem; dsimp only at hmem
              simp only [st_run_lift_bind, st_run_set_bind, LawfulMonad.bind_assoc,
                MonadAttach.mem_support_bind] at hmem
              rcases hmem with ⟨dkR, _, hmem⟩
              split at hmem <;>
                · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                  subst hmem; exact ⟨rfl, rfl, rfl⟩
            · rw [hkr] at hmem; dsimp only at hmem
              simp only [pure_bind, st_run_set_bind, LawfulMonad.bind_assoc] at hmem
              split at hmem <;>
                · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                  subst hmem; exact ⟨rfl, rfl, rfl⟩

set_option linter.unusedSimpArgs false in
private theorem pqxdhStep_nonTest_extra {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {σ : BHE2EDrvState S ℓ}
    (hBundles : σ.bundles.length ≤ σ.st.spkBundles.length)
    (hResp : ∀ r ∈ σ.st.respSessions,
      r.tested = false ∧ PqxdhSimTypes.isInitSid r.sid = false)
    (kq : SignalPqxdh.KeyIndQuery S) (hnotTest : ∀ sid, kq ≠ .testSession sid)
    {kr : SignalPqxdh.KeyIndResponse} {st' : SignalPqxdh.KeyIndState S}
    (hmem : (kr, st') ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run σ.st)) :
    (bhE2EMirror { σ with st := st' } kq kr).bundles.length ≤ st'.spkBundles.length ∧
      (st'.sessions.filter (·.tested)).length = (σ.st.sessions.filter (·.tested)).length ∧
      (∀ r ∈ st'.respSessions, r.tested = false ∧ PqxdhSimTypes.isInitSid r.sid = false) := by
  have hNonGen : ∀ {st1 : SignalPqxdh.KeyIndState S},
      (∀ u j, kq ≠ .genSPK u j) →
      σ.st.spkBundles.length ≤ st1.spkBundles.length →
      (bhE2EMirror { σ with st := st1 } kq kr).bundles.length ≤ st1.spkBundles.length := by
    intro st1 hng hle
    have hbeq : (bhE2EMirror { σ with st := st1 } kq kr).bundles = σ.bundles := by
      cases kq with
      | genSPK u j => exact absurd rfl (hng u j)
      | _ => cases kr <;> rfl
    rw [hbeq]
    exact hBundles.trans hle
  cases kq with
  | testSession sid => exact absurd rfl (hnotTest sid)
  | initPrin u =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hdup : (σ.st.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp only [hdup, ite_true, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hBundles, rfl, hResp⟩
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, ite_false, st_run_lift_bind, st_run_set_bind,
        st_run_pure, LawfulMonad.bind_assoc, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨sec, _, rfl, rfl⟩
      exact ⟨hBundles, rfl, hResp⟩
  | roQuery secrets =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.evalHkdfOrRo at hmem
    simp only [Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc, pure_bind,
      st_run_get_bind, st_run_getOf_bind, st_run_lift_bind, st_run_lift, st_run_set_bind,
      st_run_pure, map_pure, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff, exists_eq_left, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hBundles, rfl, hResp⟩
  | revealDhSecrets =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal at hmem
    simp only [st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hBundles, rfl, hResp⟩
  | corruptIK u =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
    rcases hfind : σ.st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, entry⟩
    · rw [hfind] at hmem; dsimp only at hmem
      simp only [st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hBundles, rfl, hResp⟩
    · rw [hfind] at hmem; dsimp only at hmem
      simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hBundles, rfl, hResp⟩
  | genSPK u j =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hdup : (σ.st.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp only [hdup, ↓reduceIte, ite_true, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hBundles, rfl, hResp⟩
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, ite_false] at hmem
      rcases hfind : σ.st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
      · rw [hfind] at hmem; dsimp only at hmem
        simp only [st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨hBundles, rfl, hResp⟩
      · rw [hfind] at hmem; dsimp only at hmem
        simp only [st_run_lift_bind, st_run_lift, st_run_set_bind, st_run_pure,
          LawfulMonad.bind_assoc, map_eq_bind_pure_comp, Function.comp_def,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨spkSk, _, rSpk, _, ⟨pqPk, pqSk⟩, _, rPq, _, rfl, rfl⟩
        exact ⟨Nat.succ_le_succ hBundles, rfl, hResp⟩
  | genOPK u j o =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hdup : (σ.st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp only [hdup, ↓reduceIte, ite_true, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hBundles, rfl, hResp⟩
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, ite_false, st_run_lift_bind, st_run_set_bind,
        st_run_pure, LawfulMonad.bind_assoc, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨opkSk, _, rfl, rfl⟩
      exact ⟨hBundles, rfl, hResp⟩
  | initiateOPK u i bundle =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hopk : bundle.opkB?.isNone = true
    · simp only [hopk, ite_true, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hBundles, rfl, hResp⟩
    · simp only [hopk, ite_false] at hmem
      obtain ⟨hspk, hsess, hresp⟩ := runKeyIndInitiate_false_extra hmem
      exact ⟨hNonGen (fun _ _ h => nomatch h) (by rw [hspk]), hsess, hresp ▸ hResp⟩
  | initiateNoOPK u i bundle =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hopk : bundle.opkB?.isSome = true
    · simp only [hopk, ite_true, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hBundles, rfl, hResp⟩
    · simp only [hopk, ite_false] at hmem
      obtain ⟨hspk, hsess, hresp⟩ := runKeyIndInitiate_false_extra hmem
      exact ⟨hNonGen (fun _ _ h => nomatch h) (by rw [hspk]), hsess, hresp ▸ hResp⟩
  | acceptOPK k j o hdr =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl
      SignalPqxdh.evalHkdfOrRo SignalPqxdh.recordKeyIndResp at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    have hId : (kr, st') = (.noneResp, σ.st) →
        (bhE2EMirror { σ with st := st' } (.acceptOPK k j o hdr) kr).bundles.length ≤
          st'.spkBundles.length ∧
        (st'.sessions.filter (·.tested)).length = (σ.st.sessions.filter (·.tested)).length ∧
        (∀ r ∈ st'.respSessions, r.tested = false ∧ PqxdhSimTypes.isInitSid r.sid = false) := by
      rintro ⟨rfl, rfl⟩; exact ⟨hBundles, rfl, hResp⟩
    by_cases hhdr : (!(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == some (UInt32.ofNat o.val) &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32)) = true
    · simp only [hhdr, ite_true, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
    · simp only [hhdr, ite_false] at hmem
      by_cases hused : (σ.st.usedRecvOPK.contains (k.val, j.val, o.val)) = true
      · simp only [hused, ite_true, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
      · simp only [hused, ite_false] at hmem
        by_cases hkosk : (!SignalPqxdh.koskSenderOk P σ.st.principals σ.st.advKeys hdr.ikAPk) = true
        · simp only [hkosk, ite_true, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
        · simp only [hkosk, ite_false] at hmem
          rcases hp : σ.st.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
          · rw [hp] at hmem; dsimp only at hmem
            simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
          · rw [hp] at hmem; dsimp only at hmem
            rcases hb : σ.st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bEntry⟩
            · rw [hb] at hmem; dsimp only at hmem
              simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
            · rw [hb] at hmem; dsimp only at hmem
              rcases ho : σ.st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
                _ | ⟨_, oEntry⟩
              · rw [ho] at hmem; dsimp only at hmem
                simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
              · rw [ho] at hmem; dsimp only at hmem
                simp only [st_run_ite, st_run_pure] at hmem
                by_cases hcons : oEntry.consumed = true
                · simp only [hcons, ite_true, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
                · simp only [hcons, ite_false] at hmem
                  rcases hacc : SignalPqxdh.Model.acceptKeys P _ with _ | dk0
                  · rw [hacc] at hmem; dsimp only at hmem
                    simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
                  · rw [hacc] at hmem; dsimp only at hmem
                    rcases hdec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss
                    · rw [hdec] at hmem; dsimp only at hmem
                      simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
                    · rw [hdec] at hmem; dsimp only at hmem
                      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
                        LawfulMonad.bind_assoc, pure_bind, st_run_get_bind, st_run_getOf_bind,
                        st_run_lift_bind, st_run_lift, st_run_set_bind, st_run_set,
                        st_run_pure, map_pure, MonadAttach.mem_support_bind, support_pure,
                        Set.mem_singleton_iff, exists_eq_left] at hmem
                      have hFinish : ∀ {rNew : SignalPqxdh.KeyIndRespEntry S},
                          rNew.tested = false → PqxdhSimTypes.isInitSid rNew.sid = false →
                          st'.spkBundles = σ.st.spkBundles →
                          st'.sessions = σ.st.sessions →
                          st'.respSessions = rNew :: σ.st.respSessions →
                          (bhE2EMirror { σ with st := st' } (.acceptOPK k j o hdr) kr).bundles.length ≤
                            st'.spkBundles.length ∧
                          (st'.sessions.filter (·.tested)).length =
                            (σ.st.sessions.filter (·.tested)).length ∧
                          (∀ r ∈ st'.respSessions,
                            r.tested = false ∧ PqxdhSimTypes.isInitSid r.sid = false) := by
                        intro rNew ht hi hspk hsess hresp
                        refine ⟨hNonGen (fun _ _ h => nomatch h) (by rw [hspk]), by rw [hsess], ?_⟩
                        intro r hr
                        rw [hresp, List.mem_cons] at hr
                        rcases hr with rfl | hr'
                        · exact ⟨ht, hi⟩
                        · exact hResp r hr'
                      rcases hpart : σ.st.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s _) with
                        _ | partner
                      · rw [hpart] at hmem; dsimp only at hmem
                        simp only [st_run_lift_bind, st_run_set_bind, LawfulMonad.bind_assoc,
                          MonadAttach.mem_support_bind] at hmem
                        rcases hmem with ⟨dkR, _, hmem⟩
                        split at hmem <;>
                          · simp only [st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                            rcases hmem with ⟨rfl, rfl⟩
                            exact hFinish rfl rfl rfl rfl rfl
                      · rw [hpart] at hmem; dsimp only at hmem
                        simp only [pure_bind, st_run_set_bind, LawfulMonad.bind_assoc] at hmem
                        split at hmem <;>
                          · simp only [st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                            rcases hmem with ⟨rfl, rfl⟩
                            exact hFinish rfl rfl rfl rfl rfl
  | acceptNoOPK k j l hdr =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl
      SignalPqxdh.evalHkdfOrRo SignalPqxdh.recordKeyIndResp at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    have hId : (kr, st') = (.noneResp, σ.st) →
        (bhE2EMirror { σ with st := st' } (.acceptNoOPK k j l hdr) kr).bundles.length ≤
          st'.spkBundles.length ∧
        (st'.sessions.filter (·.tested)).length = (σ.st.sessions.filter (·.tested)).length ∧
        (∀ r ∈ st'.respSessions, r.tested = false ∧ PqxdhSimTypes.isInitSid r.sid = false) := by
      rintro ⟨rfl, rfl⟩; exact ⟨hBundles, rfl, hResp⟩
    by_cases hhdr : (!(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == none &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32)) = true
    · simp only [hhdr, ite_true, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
    · simp only [hhdr, ite_false] at hmem
      by_cases hused : (σ.st.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
      · simp only [hused, ite_true, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
      · simp only [hused, ite_false] at hmem
        by_cases hkosk : (!SignalPqxdh.koskSenderOk P σ.st.principals σ.st.advKeys hdr.ikAPk) = true
        · simp only [hkosk, ite_true, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
        · simp only [hkosk, ite_false] at hmem
          rcases hp : σ.st.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
          · rw [hp] at hmem; dsimp only at hmem
            simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
          · rw [hp] at hmem; dsimp only at hmem
            rcases hb : σ.st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bEntry⟩
            · rw [hb] at hmem; dsimp only at hmem
              simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
            · rw [hb] at hmem; dsimp only at hmem
              rcases hacc : SignalPqxdh.Model.acceptKeys P _ with _ | dk0
              · rw [hacc] at hmem; dsimp only at hmem
                simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
              · rw [hacc] at hmem; dsimp only at hmem
                rcases hdec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss
                · rw [hdec] at hmem; dsimp only at hmem
                  simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem; exact hId hmem
                · rw [hdec] at hmem; dsimp only at hmem
                  simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
                    LawfulMonad.bind_assoc, pure_bind, st_run_get_bind, st_run_getOf_bind,
                    st_run_lift_bind, st_run_lift, st_run_set_bind, st_run_set,
                    st_run_pure, map_pure, MonadAttach.mem_support_bind, support_pure,
                    Set.mem_singleton_iff, exists_eq_left] at hmem
                  have hFinish : ∀ {rNew : SignalPqxdh.KeyIndRespEntry S},
                      rNew.tested = false → PqxdhSimTypes.isInitSid rNew.sid = false →
                      st'.spkBundles = σ.st.spkBundles →
                      st'.sessions = σ.st.sessions →
                      st'.respSessions = rNew :: σ.st.respSessions →
                      (bhE2EMirror { σ with st := st' } (.acceptNoOPK k j l hdr) kr).bundles.length ≤
                        st'.spkBundles.length ∧
                      (st'.sessions.filter (·.tested)).length =
                        (σ.st.sessions.filter (·.tested)).length ∧
                      (∀ r ∈ st'.respSessions,
                        r.tested = false ∧ PqxdhSimTypes.isInitSid r.sid = false) := by
                    intro rNew ht hi hspk hsess hresp
                    refine ⟨hNonGen (fun _ _ h => nomatch h) (by rw [hspk]), by rw [hsess], ?_⟩
                    intro r hr
                    rw [hresp, List.mem_cons] at hr
                    rcases hr with rfl | hr'
                    · exact ⟨ht, hi⟩
                    · exact hResp r hr'
                  rcases hpart : σ.st.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s _) with
                    _ | partner
                  · rw [hpart] at hmem; dsimp only at hmem
                    simp only [st_run_lift_bind, st_run_set_bind, LawfulMonad.bind_assoc,
                      MonadAttach.mem_support_bind] at hmem
                    rcases hmem with ⟨dkR, _, hmem⟩
                    split at hmem <;>
                      · simp only [st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                        rcases hmem with ⟨rfl, rfl⟩
                        exact hFinish rfl rfl rfl rfl rfl
                  · rw [hpart] at hmem; dsimp only at hmem
                    simp only [pure_bind, st_run_set_bind, LawfulMonad.bind_assoc] at hmem
                    split at hmem <;>
                      · simp only [st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                        rcases hmem with ⟨rfl, rfl⟩
                        exact hFinish rfl rfl rfl rfl rfl
  | revealSessionKey sid =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
    rcases hs : σ.st.sessions.find? (fun e => e.sid == sid) with _ | e
    · rw [hs] at hmem; dsimp only at hmem
      rcases hr : σ.st.respSessions.find? (fun r => r.sid == sid) with _ | r
      · rw [hr] at hmem; dsimp only at hmem
        simp only [st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨hBundles, rfl, hResp⟩
      · rw [hr] at hmem; dsimp only at hmem
        simp only [st_run_ite, st_run_pure] at hmem
        by_cases hrt : r.tested = true
        · simp only [hrt, ite_true, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩
          exact ⟨hBundles, rfl, hResp⟩
        · simp only [hrt, ite_false, st_run_set_bind, st_run_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩
          refine ⟨hNonGen (fun _ _ h => nomatch h) (le_refl _), rfl, ?_⟩
          intro r' hr'
          rcases List.mem_map.mp hr' with ⟨r₀, hr₀, hEq⟩
          split_ifs at hEq <;> subst hEq <;> exact hResp r₀ hr₀
    · rw [hs] at hmem; dsimp only at hmem
      simp only [st_run_ite, st_run_pure] at hmem
      by_cases het : e.tested = true
      · simp only [het, ite_true, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨hBundles, rfl, hResp⟩
      · simp only [het, ite_false, st_run_set_bind, st_run_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        refine ⟨hNonGen (fun _ _ h => nomatch h) (le_refl _), ?_, hResp⟩
        exact filter_tested_map_eq _ σ.st.sessions fun s _ => by split_ifs <;> rfl
  | revealSpkSk u j =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
    rcases hb : σ.st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with _ | ⟨_, bEntry⟩
    · rw [hb] at hmem; dsimp only at hmem
      simp only [st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hBundles, rfl, hResp⟩
    · rw [hb] at hmem; dsimp only at hmem
      simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hNonGen (fun _ _ h => nomatch h) (by simp), rfl, hResp⟩
  | registerKey sk =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
    rcases hreg : SignalPqxdh.registerAdvKey P σ.st.advKeys sk with _ | ⟨pk, advKeys'⟩
    · rw [hreg] at hmem; dsimp only at hmem
      simp only [st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hBundles, rfl, hResp⟩
    · rw [hreg] at hmem; dsimp only at hmem
      simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hNonGen (fun _ _ h => nomatch h) (le_refl _), rfl, hResp⟩

theorem HaltedPrefixSimInvInst.kiStep_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {TrackInv : ℕ → τ → Prop}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH)
    (kq : SignalPqxdh.KeyIndQuery S)
    (hKiNext : qKiDone + 1 ≤ b.q_total)
    (hSendNext : nextSendDone qSendDone kq ≤ S.N_send_tot)
    {out : BHTargetResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support
      (bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT
        σH.1 (.inl (.inl kq)))) :
    HaltedPrefixSimInvInst TrackInv C K b qStart qs
      (qKiDone + 1) (nextSendDone qSendDone kq) qStartDone qSessDone (out.2, σH.2) ∧
      (∀ k, HaltedPausedInv k σH → HaltedPausedInv k (out.2, σH.2)) := by
  rcases σH with ⟨σ, tracks⟩
  dsimp only [bhShallowStepPreNonCtl] at hout
  have hpure : out ∈ support (pure (.inl (.inl .noneResp), σ) :
      ProbComp (BHTargetResp ℓ × BHE2EDrvState S ℓ)) →
      HaltedPrefixSimInvInst TrackInv C K b qStart qs
        (qKiDone + 1) (nextSendDone qSendDone kq) qStartDone qSessDone (out.2, tracks) ∧
        (∀ k, HaltedPausedInv k (σ, tracks) → HaltedPausedInv k (out.2, tracks)) := by
    simp only [support_pure, Set.mem_singleton_iff]
    rintro rfl
    exact ⟨{
      base := h.base.kiSkip_preserves kq hKiNext hSendNext
      st_list := h.st_list.mono (Nat.le_succ _)
      bundles_le_st := h.bundles_le_st
      tested_le_start := h.tested_le_start
      sends_init := h.sends_init
      resp_untested := h.resp_untested
    }, fun _ hk => hk⟩
  split_ifs at hout with hok hprom
  · exact hpure hout
  · exact hpure hout
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨kr, st'⟩, hstep, rfl⟩
    have hnotTest : ∀ sid, kq ≠ .testSession sid := by
      intro sid hEq; subst hEq
      exact hok (by simp [bhDrvKiQueryOk])
    have hst' := PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_preserves_stListBounded kq h.st_list hstep
    have hKi' : KeyIndReachBounded S (qKiDone + 1) st' := ⟨hst'.setup, hst'.advKeys_le⟩
    obtain ⟨hBase', hPaused'⟩ := h.base.kiMirror_preserves kq kr st' hKiNext hSendNext hKi'
    obtain ⟨hBund', hTestEq, hResp'⟩ :=
      pqxdhStep_nonTest_extra h.bundles_le_st h.resp_untested kq hnotTest hstep
    have hStEq : (bhE2EMirror { σ with st := st' } kq kr).st = st' := by
      cases kq <;> cases kr <;> rfl
    exact ⟨{
      base := hBase'
      st_list := by dsimp only; rw [hStEq]; exact hst'
      bundles_le_st := by dsimp only; rw [hStEq]; exact hBund'
      tested_le_start := by dsimp only; rw [hStEq, hTestEq]; exact h.tested_le_start
      sends_init := sends_init_mirror h.sends_init kq kr
      resp_untested := by dsimp only; rw [hStEq]; exact hResp'
    }, hPaused'⟩

set_option linter.unusedSimpArgs false in
theorem HaltedPrefixSimInvInst.localStartSessionTracked_preserves
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrackInv : ℕ → τ → Prop} (hT : ValidSimTrackInv T TrackInv)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH)
    (hStartNext : qStartDone + 1 ≤ min qStart S.N_send_tot)
    (sid : SignalPqxdh.SessionId S)
    {out : Option ℕ × (BHE2EDrvState S ℓ × List τ)}
    (hout : out ∈ support
      (bhE2ELocalStartSessionTracked T.init (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
        C K bMode? σH sid)) :
    HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone (qStartDone + 1) qSessDone out.2 ∧
      (∀ k, HaltedPausedInv k σH → HaltedPausedInv k out.2) := by
  rcases σH with ⟨σ, tracks⟩
  unfold bhE2ELocalStartSessionTracked at hout
  dsimp only at hout
  cases hg : bhE2EGuard σ sid with
  | none =>
    simp only [hg, support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact ⟨{
      base := { h.base with
        start_le := hStartNext
        insts_le_start := Nat.le_succ_of_le h.base.insts_le_start
        mirror := h.base.mirror.mono (le_refl _) (le_refl _) (le_refl _)
          (le_refl _) (le_refl _) (Nat.le_succ _) }
      st_list := h.st_list
      bundles_le_st := h.bundles_le_st
      tested_le_start := Nat.le_succ_of_le h.tested_le_start
      sends_init := h.sends_init
      resp_untested := h.resp_untested
    }, fun _ hk => hk⟩
  | some val =>
    rcases val with ⟨_, _, ⟨u, j⟩⟩
    have hInitSid : PqxdhSimTypes.isInitSid sid = true := by
      unfold bhE2EGuard at hg
      split_ifs at hg
      rcases hfind : σ.sends.find? (fun (s, _, _) => s == sid) with _ | sendEntry
      · simp [hfind] at hg
      · have hmem := List.mem_of_find?_eq_some hfind
        have hbeq : (sendEntry.1 == sid) = true := by simpa using List.find?_some hfind
        have heq : sendEntry.1 = sid := beq_iff_eq.mp hbeq
        exact heq ▸ h.sends_init sendEntry hmem
    simp only [hg, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨kr1, st1⟩, h1, ⟨kr2, st2⟩, h2, ac, -, rfl⟩
    change SignalPqxdh.KeyIndResponse at kr1 kr2
    have hst1 := PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_testSession_preserves_stListBounded
      sid h.st_list h1
    have hst2 := PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_revealSpkSk_preserves_stListBounded
      u j hst1 h2
    have hTest1 :
        st1.spkBundles = σ.st.spkBundles ∧
        (st1.sessions.filter (·.tested)).length ≤ qStartDone + 1 ∧
        st1.respSessions = σ.st.respSessions := by
      unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at h1
      simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
        LawfulMonad.bind_assoc] at h1
      by_cases htest : (!SignalPqxdh.isKeyIndSessionTestable σ.st sid) = true
      · simp only [htest, ite_true, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h1
        rcases h1 with ⟨_, rfl⟩
        exact ⟨rfl, Nat.le_succ_of_le h.tested_le_start, rfl⟩
      · simp only [htest, ite_false] at h1
        rcases hs : σ.st.sessions.find? (fun e => e.sid == sid) with _ | e
        · rw [hs] at h1; dsimp only at h1
          rcases hr : σ.st.respSessions.find? (fun r => r.sid == sid) with _ | r
          · rw [hr] at h1; dsimp only at h1
            simp only [st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h1
            rcases h1 with ⟨_, rfl⟩
            exact ⟨rfl, Nat.le_succ_of_le h.tested_le_start, rfl⟩
          · exfalso
            have hr_mem := List.mem_of_find?_eq_some hr
            have hr_eq : r.sid = sid := beq_iff_eq.mp (by simpa using List.find?_some hr)
            have hfalse := hr_eq ▸ (h.resp_untested r hr_mem).2
            rw [hInitSid] at hfalse
            exact Bool.noConfusion hfalse
        · rw [hs] at h1; dsimp only at h1
          simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h1
          rcases h1 with ⟨_, rfl⟩
          exact ⟨rfl, (length_filter_tested_map_set sid σ.st.sessions
            h.st_list.setup.sessions_nodup).trans (Nat.succ_le_succ h.tested_le_start), rfl⟩
    have hRev2 :
        st2.spkBundles.length = st1.spkBundles.length ∧
        st2.sessions = st1.sessions ∧
        st2.respSessions = st1.respSessions := by
      unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at h2
      simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at h2
      rcases hb : st1.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with _ | ⟨_, bEntry⟩
      · rw [hb] at h2; dsimp only at h2
        simp only [st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
        rcases h2 with ⟨_, rfl⟩
        exact ⟨rfl, rfl, rfl⟩
      · rw [hb] at h2; dsimp only at h2
        simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
        rcases h2 with ⟨_, rfl⟩
        exact ⟨by simp, rfl, rfl⟩
    have hBaseSt2 : HaltedKindSimInvInst TrackInv C K b qStart qs
        qKiDone qSendDone qStartDone qSessDone ({ σ with st := st2 }, tracks) :=
      { h.base with
        subsetSends := h.base.subsetSends.of_sids_sends_eq rfl rfl
        mirror := ⟨h.base.mirror.prins_le, h.base.mirror.bundles_le, h.base.mirror.opks_le,
          h.base.mirror.sends_le, h.base.mirror.corrPrins_le, h.base.mirror.insts_le,
          h.base.mirror.instMeta_le, h.base.mirror.revSpks_le⟩
        kiReach := ⟨hst2.setup, hst2.advKeys_le⟩ }
    have hFin := hBaseSt2.finishStartSpkTracked_preserves hT C K bMode? hStartNext sid kr1 kr2 ac
    dsimp only [Computational.Proofs.E2E.Dsl.KindRedHalted.bhE2EFinishStartSpkTracked] at hFin
    set p := bhE2EFinishStartSpk C K bMode? { σ with st := st2 } sid kr1 kr2 ac
    have hpFields : p.2.st = st2 ∧ p.2.bundles = σ.bundles ∧ p.2.sends = σ.sends := by
      dsimp only [p, bhE2EFinishStartSpk]
      rcases bhE2EGuard { σ with st := st2 } sid with _ | ⟨_, _, ⟨_, _⟩⟩
      · exact ⟨rfl, rfl, rfl⟩
      · cases kr1 <;> cases kr2 <;> try exact ⟨rfl, rfl, rfl⟩
        dsimp only; split_ifs <;> exact ⟨rfl, rfl, rfl⟩
    rcases hpFields with ⟨hpSt, hpBund, hpSends⟩
    rcases hTest1 with ⟨hSpk1, hTested1, hResp1⟩
    rcases hRev2 with ⟨hSpk2, hSess2, hResp2⟩
    let tracks' := match p.1, kr1 with
      | some _, .drKeyResp dk => tracks ++ [T.init (CryptoVerification.E2E.bhKeySOf dk ac)]
      | _, _ => tracks
    have hGoal : HaltedPrefixSimInvInst TrackInv C K b qStart qs
        qKiDone qSendDone (qStartDone + 1) qSessDone (p.2, tracks') ∧
        (∀ k, HaltedPausedInv k (σ, tracks) → HaltedPausedInv k (p.2, tracks')) :=
      ⟨{
        base := hFin.1
        st_list := by dsimp only; rw [hpSt]; exact hst2
        bundles_le_st := by dsimp only; rw [hpBund, hpSt, hSpk2, hSpk1]; exact h.bundles_le_st
        tested_le_start := by dsimp only; rw [hpSt, hSess2]; exact hTested1
        sends_init := by dsimp only; rw [hpSends]; exact h.sends_init
        resp_untested := by dsimp only; rw [hpSt, hResp2, hResp1]; exact h.resp_untested
      }, hFin.2⟩
    dsimp only [tracks'] at hGoal
    rcases hpEq : p with ⟨idx?, σ'⟩
    rw [hpEq] at hGoal
    dsimp only at hGoal ⊢
    cases idx? <;> cases kr1 <;> exact hGoal

theorem HaltedPrefixSimInvInst.stepLocalSmSessionTracked_preserves
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrackInv : ℕ → τ → Prop} (hT : ValidSimTrackInv T TrackInv)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH)
    (i : ℕ) (hSessNext : i < qStart → qSessDone i + 1 ≤ qs i)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ)}
    (hout : out ∈ support (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)) :
    HaltedPrefixSimInvInst TrackInv C K b qStart qs
      qKiDone qSendDone qStartDone (nextSessDone qStart qSessDone i) out.2 ∧
      (∀ k, HaltedPausedInv k σH → HaltedPausedInv k out.2) := by
  obtain ⟨hBase', hPaused'⟩ :=
    h.base.stepLocalSmSessionTracked_preserves hT C K qep decT encT i hSessNext sq hout
  have hSame : out.2.1.st = σH.1.st ∧ out.2.1.bundles = σH.1.bundles ∧ out.2.1.sends = σH.1.sends := by
    rw [bhE2EStepLocalSmSessionTracked_eq_filter] at hout
    by_cases hcl : (!bhE2EDrvInstClean σH.1 i) = true
    · simp only [hcl, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact ⟨rfl, rfl, rfl⟩
    · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
      cases hm1 : σH.1.insts[i]? with
      | none =>
        simp only [hm1, support_pure, Set.mem_singleton_iff] at hout
        subst hout; exact ⟨rfl, rfl, rfl⟩
      | some d =>
        cases hm2 : σH.1.instMeta[i]? with
        | none =>
          simp only [hm1, hm2, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact ⟨rfl, rfl, rfl⟩
        | some im =>
          simp only [hm1, hm2] at hout
          by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σH.1 d) = true
          · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
            subst hout; exact ⟨rfl, rfl, rfl⟩
          · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
            cases hgs : d.gs with
            | none =>
              simp only [hgs, support_pure, Set.mem_singleton_iff] at hout
              subst hout; exact ⟨rfl, rfl, rfl⟩
            | some _ =>
              cases hflt :
                  Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhFilterSmQuery d im sq with
              | none =>
                simp only [hgs, hflt, support_pure, Set.mem_singleton_iff] at hout
                subst hout; exact ⟨rfl, rfl, rfl⟩
              | some _ =>
                simp only [hgs, hflt, mem_support_bind_iff] at hout
                rcases hout with ⟨⟨⟨_, _⟩, _⟩, -, hret⟩
                simp only [support_pure, Set.mem_singleton_iff] at hret
                subst hret; exact ⟨rfl, rfl, rfl⟩
  rcases hSame with ⟨hSt, hBund, hSends⟩
  exact ⟨{
    base := hBase'
    st_list := by rw [hSt]; exact h.st_list
    bundles_le_st := by rw [hBund, hSt]; exact h.bundles_le_st
    tested_le_start := by rw [hSt]; exact h.tested_le_start
    sends_init := by rw [hSends]; exact h.sends_init
    resp_untested := by rw [hSt]; exact h.resp_untested
  }, hPaused'⟩

theorem HaltedPrefixSimInvInst.promoteSlotK_paused_preserves
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σ' : BHE2EDrvState S ℓ} {tracks' : List τ}
    (h : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone
      (σ', tracks'))
    {k : ℕ} (hk : k < σ'.insts.length) :
    let insts' := σ'.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d)
    let σ_p : BHE2EDrvState S ℓ := { σ' with insts := insts', paused := true }
    HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone
      (σ_p, tracks') ∧
      HaltedPausedInv k (σ_p, tracks') := by
  obtain ⟨hBase', hPaused'⟩ := h.base.promoteSlotK_paused_preserves hk
  exact ⟨{
    base := hBase'
    st_list := h.st_list
    bundles_le_st := h.bundles_le_st
    tested_le_start := h.tested_le_start
    sends_init := h.sends_init
    resp_untested := h.resp_untested
  }, hPaused'⟩

theorem HaltedPrefixSimInvInst.commitExtSm_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrackInv : ℕ → τ → Prop} (hT : ValidSimTrackInv T TrackInv)
    {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {k : ℕ} {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH)
    (hPaused : HaltedPausedInv k σH)
    (hSessNext : k < qStart → qSessDone k + 1 ≤ qs k)
    (sq' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (sr : BHE2ESmResp ℓ) :
    let σ1 := (bhShallowCommitExtSm k σH.1 sq' sr).2
    HaltedPrefixSimInvInst TrackInv C K b qStart qs
      qKiDone qSendDone qStartDone (nextSessDone qStart qSessDone k) (σ1, σH.2) ∧
      HaltedPausedInv k (σ1, σH.2) := by
  obtain ⟨hBase', hPaused'⟩ := h.base.commitExtSm_preserves hT hPaused hSessNext sq' sr
  rcases σH with ⟨σ, tracks⟩
  dsimp only at hBase' hPaused' ⊢
  set σ1 := (bhShallowCommitExtSm k σ sq' sr).2
  have hSame : σ1.st = σ.st ∧ σ1.bundles = σ.bundles ∧ σ1.sends = σ.sends := by
    dsimp only [σ1, bhShallowCommitExtSm]
    split_ifs
    · exact ⟨rfl, rfl, rfl⟩
    · cases σ.insts[k]? <;> cases σ.instMeta[k]?
      · exact ⟨rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩
      · dsimp only; split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  rcases hSame with ⟨hSt, hBund, hSends⟩
  exact ⟨{
    base := hBase'
    st_list := by dsimp only; rw [hSt]; exact h.st_list
    bundles_le_st := by dsimp only; rw [hBund, hSt]; exact h.bundles_le_st
    tested_le_start := by dsimp only; rw [hSt]; exact h.tested_le_start
    sends_init := by dsimp only; rw [hSends]; exact h.sends_init
    resp_untested := by dsimp only; rw [hSt]; exact h.resp_untested
  }, hPaused'⟩

end Computational.Proofs.E2E.Dsl.CompositionHaltedPrefixInv
