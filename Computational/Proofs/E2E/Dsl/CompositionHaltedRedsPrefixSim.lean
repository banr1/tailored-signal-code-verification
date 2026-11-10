/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Specifications.Game.ModelIface
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1 -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedPrefixInv -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecOnline -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHalted -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedPrefixEval -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst
import Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst
import Computational.Proofs.E2E.Dsl.M3Interfaces
import Computational.Proofs.E2E.Dsl.PqxdhSimTypes

/-!
# Online-Clamped Two-Stage Prefix Reduction Simulation

Instantiates `TwoStageAtomicSimSpecOnline` for `prefixRedHalted` at `onlineClampedBudget b` and
proves Stage-1 and Stage-2 equivalence (`prefixEval_clamped_bOn_eq_of_valid_inst`) with
`bhPrefixRedWithSessionTracked` across all slots `k`.
-/

public section

set_option autoImplicit false

open scoped ENNReal BigOperators

namespace Computational.Proofs.E2E.Dsl.CompositionHaltedRedsPrefixSim

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Env Expr Comp atomicSig atomicE2EOps e2eSessionTargetIface
  keyIndQT keyIndQenc sidT sidV smQT smQenc)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (BHE2EDrvState BHE2ESmResp BHPrefixCtx BHTargetQuery BHTargetResp
  BhShallowTwoStageRed Bytes SampledSessionKey bhBaseMirror bhDrvKiQueryOk
  bhE2EDrvInstClean bhE2EFinishStartSpk bhE2EGuard bhE2EInstIkACorr bhE2EMirror
  bhIsBobRecvSMQuery bhLiftP bhShallowCheckExtSm bhShallowRunFuel bhShallowRunFuel_pure
  bhShallowRunFuel_query_inl bhShallowRunFuel_query_inr_zero bhShallowRunFuel_query_inr_succ
  bhShallowStepPreNonCtl bhTargetGameSpec bhTargetQenc bhTargetRdec
  e2eTargetGameCodec stageOneAsProbComp)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (SessionHaltTracker
  bhClassifyTarget bhClassifyTargetOnly
  bhE2ELocalStartSessionTracked bhE2EStepLocalSmSessionTracked
  bhE2EStepLocalSmSessionTracked_eq_filter bhFilterSmQuery bhPrefixHandlePreWithSessionTracked
  bhPrefixRedWithSessionTracked bhShallowStepPreCtlSessionTracked
  bhShallowStepPreNonCtlSessionTracked)
open Computational.Proofs.E2E.Dsl.M3Interfaces (bhPromoteSlotK)
open Computational.Proofs.E2E.Dsl.PrefixRedHalted
  (HaltedPrefixSubprograms drvHaltedTy drvHaltedEnc prefixRedHalted
   prefixHandlePreHalted_eval_ki prefixHandlePostHalted_eval_ki
   prefixRedHalted_stage1Queries bhPrefixRedWithHalted bhPrefixHandlePreWithHalted
   bhPrefixHandlePostWithHalted bhShallowStepPreNonCtlHalted bhShallowStepPostLocalHalted)
open Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval
  (atomicGameRespEnc atomicPrefixCtxEnc mapPreEnc mem_support_of_mem_support_stageOneAsProbComp)
open Computational.Proofs.E2E.Dsl.PrefixRedHaltedInst (ValidHaltedPrefixSubprogramsInst)
open Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind (onlineClampedBudget)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness
  (HaltedPausedInv HaltedTargetAdvPerInstanceBounded
   bhPrefixRedWithHalted_eq_bhPrefixRedWithSessionTracked)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst
  (isQueryBoundP_min HaltedKindSimInvInst)
open Computational.Proofs.E2E.Dsl.CompositionHaltedPrefixInv (HaltedPrefixSimInvInst)
open Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst
  (isSendQ isStartQ isSessQ isSendQ_inl_inl)
open Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecOnline
  (isOnlineKiQ isOnlineKiQ_of_ne_roQuery isQueryBoundP_isOnlineKiQ_bOn unpack_qb
   TwoStageAtomicSimSpecOnline twoStage_stage12_comp_eq_online evalDist_twoStage_stage12_eq_online)

private theorem pqxdhKeyIndImpl1KeyReal_roQuery_eq_st {S : SignalPqxdh.Setup}
    {P : SignalPqxdh.Primitives} {sec : SignalPqxdh.Bytes} {st st' : SignalPqxdh.KeyIndState S}
    {kr : SignalPqxdh.KeyIndResponse}
    (hmem : (kr, st') ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.roQuery sec)).run st)) :
    ∃ rc, st' = { st with roCache := rc } := by
  unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl
    SignalPqxdh.evalHkdfOrRo at hmem
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_set,
    StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  rcases hmem with ⟨w, _, _, rfl⟩
  exact ⟨w.2, rfl⟩

private theorem bhShallowStepPreNonCtl_roQuery_drv_preserves
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {TrackInv : ℕ → τ → Prop}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH)
    (sec : SignalPqxdh.Bytes)
    {out : BHTargetResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support
      (bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT
        σH.1 (.inl (.inl (.roQuery sec))))) :
    HaltedPrefixSimInvInst TrackInv C K b qStart qs
      qKiDone qSendDone qStartDone qSessDone (out.2, σH.2) ∧
    (∀ k, HaltedPausedInv k σH → HaltedPausedInv k (out.2, σH.2)) := by
  rcases σH with ⟨σ, tracks⟩
  dsimp only [bhShallowStepPreNonCtl] at hout
  split_ifs at hout
  · simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout
    exact ⟨h, fun _ hp => hp⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout
    exact ⟨h, fun _ hp => hp⟩
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨kr, st'⟩, hstep, rfl⟩
    have hSetup' :=
      (PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_preserves_setupBounded (.roQuery sec)
        h.st_list.setup hstep).1
    rcases pqxdhKeyIndImpl1KeyReal_roQuery_eq_st hstep with ⟨rc, rfl⟩
    dsimp only
    have hMir : bhE2EMirror { σ with st := { σ.st with roCache := rc } } (.roQuery sec) kr =
        { σ with st := { σ.st with roCache := rc } } := by
      cases kr <;> rfl
    rw [hMir]
    have hStList : PqxdhSimTypes.stListBounded S qKiDone { σ.st with roCache := rc } :=
      ⟨hSetup', h.st_list.principals_fuel_le, h.st_list.spkBundles_fuel_le,
        h.st_list.opkEntries_fuel_le, h.st_list.sessions_fuel_le,
        h.st_list.respSessions_fuel_le, h.st_list.usedRecvOPK_fuel_le,
        h.st_list.usedRecvNoOPK_fuel_le, h.st_list.seenKyberBaseKeys_fuel_le,
        h.st_list.advKeys_le⟩
    have hKiReach : M3Interfaces.KeyIndReachBounded S qKiDone { σ.st with roCache := rc } :=
      ⟨hSetup', hStList.advKeys_le⟩
    exact ⟨{
      base := {
        ki_le := h.base.ki_le
        send_le := h.base.send_le
        start_le := h.base.start_le
        sess_le := h.base.sess_le
        sends_le_ki := h.base.sends_le_ki
        sends_le_send := h.base.sends_le_send
        insts_le_start := h.base.insts_le_start
        subsetSends := h.base.subsetSends.of_sids_sends_eq rfl rfl
        mirror := ⟨h.base.mirror.prins_le, h.base.mirror.bundles_le, h.base.mirror.opks_le,
          h.base.mirror.sends_le, h.base.mirror.corrPrins_le, h.base.mirror.insts_le,
          h.base.mirror.instMeta_le, h.base.mirror.revSpks_le⟩
        metaAligned := h.base.metaAligned
        kiReach := hKiReach
        tracks_len := h.base.tracks_len
        slot_reach := h.base.slot_reach
        slot_track := h.base.slot_track
      }
      st_list := hStList
      bundles_le_st := h.bundles_le_st
      tested_le_start := h.tested_le_start
      sends_init := h.sends_init
      resp_untested := h.resp_untested
    }, fun k hp => ⟨hp.1, hp.2⟩⟩

private theorem atomicLiftP_map_loc {ℓ : ℕ} {Pt α β : Type} (f : α → β) (p : ProbComp α) :
    (e2eSessionTargetIface ℓ Pt).liftP (f <$> p) =
      f <$> (e2eSessionTargetIface ℓ Pt).liftP p := by
  simp [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP, bhLiftP]

private theorem prefixKiStepHaltedC_eval_eq_loc
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop}
    {b0 : SignalPqxdh.QueryBudget} {qStart qInst qep : ℕ} {qs : ℕ → ℕ}
    (hValid : ValidHaltedPrefixSubprogramsInst subs T TrackInv b0 qStart qInst qep)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List SessH}
    (hInv : HaltedPrefixSimInvInst TrackInv C K b0 qStart qs qKiDone qSendDone qStartDone qSessDone σH)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvHaltedTy subs))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (kq : SignalPqxdh.KeyIndQuery S)
    (hσH : σHE.eval ρ = drvHaltedEnc subs σH)
    (hkq : kqE.eval ρ = keyIndQenc kq) :
    (PrefixRedHalted.prefixKiStepHaltedC subs b0 σHE kqE).eval ρ =
      (e2eSessionTargetIface ℓ Pt).liftP
        ((fun out => (atomicGameRespEnc out.1, drvHaltedEnc subs (out.2, σH.2))) <$>
          bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
            C K qep decT encT σH.1 (.inl (.inl kq))) := by
  dsimp only [PrefixRedHalted.prefixKiStepHaltedC, Comp.eval]
  rw [pure_bind]
  let ρ1 : Env (Ty.prod (drvHaltedTy subs) (keyIndQT (ℓ := ℓ) (Pt := Pt) S) :: Γ) :=
    .cons ((Expr.pair σHE kqE).eval ρ) ρ
  have h1 : (subs.kiStepC b0 (.fst (.fst .v0)) (.snd .v0)).eval ρ1 = _ :=
    hValid.kiStepC_eval hP hInv.drvMirrorBounded_clamped.prins_le
      hInv.base.instMeta_length_le hInv.stListBounded_qTotal
      (.fst (.fst .v0)) (.snd .v0) ρ1 kq
      (by simp [ρ1, Expr.eval, Expr.v0, hσH, drvHaltedEnc])
      (by simp [ρ1, Expr.eval, Expr.v0, hkq])
  change ((subs.kiStepC b0 (.fst (.fst .v0)) (.snd .v0)).eval ρ1 >>= _) = _
  rw [h1, atomicLiftP_map_loc, bind_map_left, atomicLiftP_map_loc]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  exact bind_congr fun ⟨_, _⟩ => by simp [Expr.eval, Expr.v0, Expr.v1, hσH, drvHaltedEnc]

/-- Instantiation of `TwoStageAtomicSimSpecOnline` for `prefixRedHalted` at `onlineClampedBudget b`. -/
@[expose] def prefixRedHalted_twoStageSimSpecOnline
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop}
    {b : SignalPqxdh.QueryBudget} {qStart qInst qep k : ℕ} {qs : ℕ → ℕ}
    (hValid : ValidHaltedPrefixSubprogramsInst subs T TrackInv (onlineClampedBudget b) qStart qInst qep)
    (hqInst : Finset.sup (Finset.range qStart) qs ≤ qInst)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (hPromoteK : ∀ {σH : BHE2EDrvState S ℓ × List SessH},
      σH.1.insts.length ≤ min qStart (min (onlineClampedBudget b).q_total S.N_send_tot) →
      ∀ {Γ} (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
        (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
        (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy) (ρ : Env Γ) (idx? : Option ℕ),
        kE.eval ρ = k → idxOptE.eval ρ = idx? → σE.eval ρ = subs.drvEnc σH.1 →
        (subs.promoteSlotKC qStart kE idxOptE σE).eval ρ =
          match bhPromoteSlotK k idx? σH.1 with
          | .inl ans => pure (.inl (ans.1, subs.drvEnc ans.2))
          | .inr (ctx, p, σ_p) => pure (.inr (atomicPrefixCtxEnc ctx, (p, subs.drvEnc σ_p)))) :
    TwoStageAtomicSimSpecOnline S Pt ℓ (atomicE2EOps ℓ P C K decT encT) b qStart qs
      (BHE2EDrvState S ℓ × List SessH) (Option ℕ) where
  toTwoStageAtomicSimSpecInst :=
    CompositionHaltedPrefixEval.prefixRedHalted_twoStageSimSpecInst hValid hqInst hP hPromoteK
  roPre_eq {_ _ _ _ σH} hInv sec := by
    dsimp only [CompositionHaltedPrefixEval.prefixRedHalted_twoStageSimSpecInst,
      prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
    rw [prefixHandlePreHalted_eval_ki]
    dsimp only [bhPrefixHandlePreWithHalted, bhShallowStepPreNonCtlHalted, bhTargetQenc]
    let ρ_ki : Env [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
        Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
        drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
      .cons (keyIndQenc (.roQuery sec)) (.cons (.inl (keyIndQenc (.roQuery sec)))
        (.cons (drvHaltedEnc subs σH) (.cons (.inl (.inl (keyIndQenc (.roQuery sec)))) .nil)))
    rw [prefixKiStepHaltedC_eval_eq_loc hValid hP hInv .v2 .v0 ρ_ki (.roQuery sec) rfl rfl]
    rw [atomicLiftP_map_loc, bind_map_left]
    simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
      bhLiftP, simulateQ_bind, simulateQ_pure, map_bind, map_pure, bind_assoc, pure_bind,
      mapPreEnc]
  roPre_inv {_ _ _ _ σH} hInv sec res hres := by
    dsimp only [CompositionHaltedPrefixEval.prefixRedHalted_twoStageSimSpecInst,
      bhPrefixRedWithHalted, bhPrefixHandlePreWithHalted,
      bhShallowStepPreNonCtlHalted, bhTargetQenc] at hres
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
    rcases hres with ⟨⟨r, σH1⟩, h1, rfl⟩
    have h1p := KindRedHaltedEval.mem_support_of_bhLiftP _ h1
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h1p
    rcases h1p with ⟨⟨r', σ'⟩, hki, hpair⟩
    cases hpair
    exact (bhShallowStepPreNonCtl_roQuery_drv_preserves P C K qep decT encT hInv sec hki).1
  roPost_eq {_ _ _ _ σH} hInv _ sec := by
    dsimp only [CompositionHaltedPrefixEval.prefixRedHalted_twoStageSimSpecInst,
      prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
    rw [prefixHandlePostHalted_eval_ki]
    dsimp only [bhPrefixHandlePostWithHalted, bhShallowStepPostLocalHalted, bhTargetQenc]
    let ρ_ki : Env [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
        Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
        drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
      .cons (keyIndQenc (.roQuery sec)) (.cons (.inl (keyIndQenc (.roQuery sec)))
        (.cons (drvHaltedEnc subs σH) (.cons (.inl (.inl (keyIndQenc (.roQuery sec)))) .nil)))
    rw [prefixKiStepHaltedC_eval_eq_loc hValid hP hInv .v2 .v0 ρ_ki (.roQuery sec) rfl rfl]
    rw [atomicLiftP_map_loc]
    simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
      bhLiftP, simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind, CryptoVerification.E2E.bhShallowStepPostLocal,
      bhShallowStepPreNonCtl, Prod.map]
  roPost_inv {_ _ _ _ σH} hInv hPaused sec p hp := by
    dsimp only [CompositionHaltedPrefixEval.prefixRedHalted_twoStageSimSpecInst,
      bhPrefixRedWithHalted, bhPrefixHandlePostWithHalted,
      bhShallowStepPostLocalHalted, bhTargetQenc] at hp
    have hp' := KindRedHaltedEval.mem_support_of_bhLiftP _ hp
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp'
    rcases hp' with ⟨⟨r', σ'⟩, hki, rfl⟩
    obtain ⟨hInv', hPau'⟩ :=
      bhShallowStepPreNonCtl_roQuery_drv_preserves P C K qep decT encT hInv sec hki
    exact ⟨hPau' k hPaused, hInv'⟩

private theorem map_set_eq_self_local {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : ℕ) (x d : α), l[i]? = some d → f x = f d → (l.set i x).map f = l.map f
  | [], _, _, _, h, _ => nomatch h
  | _ :: _, 0, _, _, h, hf => by cases h; simp [hf]
  | a :: as, i + 1, x, d, h, hf => by
    simp only [List.getElem?_cons_succ, List.set_cons_succ, List.map_cons] at h ⊢
    exact congrArg (f a :: ·) (map_set_eq_self_local f as i x d h hf)

private theorem mem_support_of_stageOneAsProbComp_local {ℓ : ℕ} {α : Type}
    (oa : OracleComp
      (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α)
    {x : α} (hx : x ∈ support (stageOneAsProbComp oa)) : x ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ => simpa [stageOneAsProbComp] using hx
  | query_bind q mx ih =>
    unfold stageOneAsProbComp at hx
    rw [simulateQ_query_bind, mem_support_bind_iff] at hx
    rcases hx with ⟨u, -, hxu⟩
    rw [mem_support_bind_iff]
    exact ⟨u, mem_support_query q u, ih u hxu⟩

private def shallowInstsBoundInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (qKiDone qStartDone : ℕ) (σ : BHE2EDrvState S ℓ) : Prop :=
  σ.sends.length ≤ qKiDone ∧ σ.insts.length ≤ qStartDone ∧ (σ.insts.map (·.sid)).Nodup ∧
    (∀ s ∈ σ.insts.map (·.sid), s ∈ σ.sends.map Prod.fst)

private theorem shallowInstsBoundInv_insts_le {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {qKiDone qStartDone : ℕ} {b_on : SignalPqxdh.QueryBudget} {qStart : ℕ} {σ : BHE2EDrvState S ℓ}
    (hInv : shallowInstsBoundInv qKiDone qStartDone σ)
    (hKi : qKiDone ≤ b_on.q_total) (hSt : qStartDone ≤ min qStart S.N_send_tot) :
    σ.insts.length ≤ min qStart (min b_on.q_total S.N_send_tot) := by
  have hSub : σ.insts.length ≤ σ.sends.length := by
    simpa only [List.length_map] using hInv.2.2.1.length_le_of_subset hInv.2.2.2
  have := le_trans hSub (le_trans hInv.1 hKi)
  have := le_trans hInv.2.1 hSt
  omega

private theorem shallowInstsBoundInv_mirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {qKiDone qStartDone : ℕ} {σ : BHE2EDrvState S ℓ}
    (hInv : shallowInstsBoundInv qKiDone qStartDone σ) (st' : SignalPqxdh.KeyIndState S)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    shallowInstsBoundInv (qKiDone + 1) qStartDone (bhE2EMirror { σ with st := st' } kq kr) := by
  rcases hInv with ⟨hsends, hinsts, hnodup, hsub⟩
  refine ⟨?_, hinsts, hnodup, fun s hs => ?_⟩
  · cases kq <;> cases kr <;> simp only [bhE2EMirror, bhBaseMirror, List.length_cons] <;> omega
  · cases kq <;> cases kr <;>
      simp only [bhE2EMirror, bhBaseMirror, List.map_cons, List.mem_cons] at hs ⊢
    all_goals first | exact hsub s hs | exact Or.inr (hsub s hs)

private theorem shallowInstsBoundInv_finishStartSpk {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (bm? : Option Bool) {qKiDone qStartDone : ℕ} {σ : BHE2EDrvState S ℓ}
    (hInv : shallowInstsBoundInv qKiDone qStartDone σ) (st2 : SignalPqxdh.KeyIndState S)
    (sid : SignalPqxdh.SessionId S) (rTest rSpk : SignalPqxdh.KeyIndResponse)
    (spkCoins : BitVec 256) :
    shallowInstsBoundInv qKiDone (qStartDone + 1)
      (bhE2EFinishStartSpk C K bm? { σ with st := st2 } sid rTest rSpk spkCoins).2 := by
  rcases hInv with ⟨hsends, hinsts, hnodup, hsub⟩
  have hmono : shallowInstsBoundInv qKiDone (qStartDone + 1) { σ with st := st2 } :=
    ⟨hsends, Nat.le_succ_of_le hinsts, hnodup, hsub⟩
  unfold bhE2EFinishStartSpk
  cases hg : bhE2EGuard { σ with st := st2 } sid with
  | none => exact hmono
  | some val =>
    rcases val with ⟨_, _, _⟩; dsimp only
    cases rTest <;> cases rSpk <;> dsimp only
    all_goals try exact hmono
    split_ifs with hmatch
    · dsimp only; unfold bhE2EGuard at hg
      by_cases hany : σ.insts.any (fun d => d.sid == sid) = true
      · simp [hany] at hg
      · simp only [hany, Bool.false_eq_true, ↓reduceIte] at hg
        cases hfind : σ.sends.find? (fun (s, _, _) => s == sid) with
        | none => simp [hfind] at hg
        | some sendEntry =>
          have hnotmem : sid ∉ σ.insts.map (·.sid) := fun hmem => by
            rcases List.mem_map.mp hmem with ⟨d, hd, rfl⟩
            exact hany (List.any_eq_true.mpr ⟨d, hd, beq_self_eq_true _⟩)
          have hinSends : sid ∈ σ.sends.map Prod.fst := by
            have hf := List.mem_of_find?_eq_some hfind
            have hbeq : (sendEntry.1 == sid) = true := by simpa using List.find?_some hfind
            have heq : sendEntry.1 = sid := beq_iff_eq.mp hbeq
            rw [← heq]
            exact List.mem_map_of_mem (f := Prod.fst) hf
          refine ⟨hsends, by simp only [List.length_append, List.length_singleton]; omega, ?_,
            fun s hs => ?_⟩
          · rw [List.map_append, List.map_singleton, List.nodup_append]
            exact ⟨hnodup, List.nodup_singleton _, fun x hx y hy hxy => by
              rw [List.mem_singleton] at hy; subst hy; subst hxy; exact hnotmem hx⟩
          · rw [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton] at hs
            rcases hs with hs | rfl
            · exact hsub s hs
            · exact hinSends
    · exact hmono

private theorem shallowInstsBoundInv_stepLocalSm {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {qKiDone qStartDone : ℕ} {σH : BHE2EDrvState S ℓ × List τ}
    (hInv : shallowInstsBoundInv qKiDone qStartDone σH.1)
    (i : ℕ) (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ)}
    (hout : out ∈ support (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)) :
    shallowInstsBoundInv qKiDone qStartDone out.2.1 := by
  rw [bhE2EStepLocalSmSessionTracked_eq_filter] at hout
  by_cases hclean : (!bhE2EDrvInstClean σH.1 i) = true
  · simp only [hclean, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
    subst hout; exact hInv
  · simp only [hclean, Bool.false_eq_true, ↓reduceIte] at hout
    cases hm1 : σH.1.insts[i]? with
    | none =>
      simp only [hm1, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact hInv
    | some d =>
      cases hm2 : σH.1.instMeta[i]? with
      | none =>
        simp only [hm1, hm2, support_pure, Set.mem_singleton_iff] at hout
        subst hout; exact hInv
      | some im =>
        simp only [hm1, hm2] at hout
        by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σH.1 d) = true
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact ⟨hInv.1, hInv.2.1, hInv.2.2.1, hInv.2.2.2⟩
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none =>
            simp only [hgs, support_pure, Set.mem_singleton_iff] at hout
            subst hout; exact hInv
          | some _ =>
            cases hflt : bhFilterSmQuery d im sq with
            | none =>
              simp only [hgs, hflt, support_pure, Set.mem_singleton_iff] at hout
              subst hout; exact hInv
            | some _ =>
              simp only [hgs, hflt, mem_support_bind_iff] at hout
              rcases hout with ⟨⟨⟨_, gs'⟩, _⟩, -, hret⟩
              simp only [support_pure, Set.mem_singleton_iff] at hret
              subst hret
              have hmap :=
                map_set_eq_self_local (·.sid) σH.1.insts i { d with gs := some gs' } d hm1 rfl
              rcases hInv with ⟨hsends, hinsts, hnodup, hsub⟩
              exact ⟨hsends, by simpa only [List.length_set] using hinsts,
                by rwa [hmap], by rwa [hmap]⟩

private theorem bhPrefixRedWithSessionTracked_run1_eq_and_done_online
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b_on : SignalPqxdh.QueryBudget) (qStart : ℕ) {k₁ k₂ : ℕ}
    (hk₁ : min qStart (min b_on.q_total S.N_send_tot) ≤ k₁)
    (hk₂ : min qStart (min b_on.q_total S.N_send_tot) ≤ k₂)
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α) :
    ∀ (f qKiDone qKiRem qStartDone qStartRem : ℕ) (drv : BHE2EDrvState S ℓ × List τ),
      oa.IsQueryBoundP isOnlineKiQ qKiRem →
      oa.IsQueryBoundP isStartQ qStartRem →
      qKiDone + qKiRem ≤ b_on.q_total → qStartDone + qStartRem ≤ min qStart S.N_send_tot →
      shallowInstsBoundInv qKiDone qStartDone drv.1 →
      (bhPrefixRedWithSessionTracked T P ki C K qep decT encT k₁).run1 dflt oa f drv =
        (bhPrefixRedWithSessionTracked T P ki C K qep decT encT k₂).run1 dflt oa f drv ∧
      ∀ m ∈ support ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k₁).run1 dflt oa f drv),
        ∃ b_out s_out, m = .done b_out s_out := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro _ _ _ _ _ drv _ _ _ _ _
    simp only [BhShallowTwoStageRed.run1_pure]
    exact ⟨trivial, fun m hm => ⟨a, drv, by simpa [support_pure] using hm⟩⟩
  | query_bind q mx ih =>
    intro f qKiDone qKiRem qStartDone qStartRem drv hqKi hqSt hKiSum hStSum hInv
    rw [isQueryBoundP_query_bind_iff] at hqKi hqSt
    cases q with
    | inl _ =>
      simp only [BhShallowTwoStageRed.run1_query_inl]
      have hKiSub : ∀ u, (mx u).IsQueryBoundP isOnlineKiQ qKiRem :=
        fun u => (hqKi.2 u).mono (by simp [isOnlineKiQ, bhClassifyTarget])
      have hStSub : ∀ u, (mx u).IsQueryBoundP isStartQ qStartRem :=
        fun u => (hqSt.2 u).mono (by simp [isStartQ, bhClassifyTarget])
      refine ⟨bind_congr fun u => (ih u f qKiDone qKiRem qStartDone qStartRem drv
          (hKiSub u) (hStSub u) hKiSum hStSum hInv).1, fun m hm => ?_⟩
      rw [mem_support_bind_iff] at hm
      rcases hm with ⟨u, -, hmu⟩
      exact (ih u f qKiDone qKiRem qStartDone qStartRem drv
        (hKiSub u) (hStSub u) hKiSum hStSum hInv).2 m hmu
    | inr t =>
      cases f with
      | zero =>
        simp only [BhShallowTwoStageRed.run1_query_inr_zero]
        exact ⟨trivial, fun m hm => ⟨dflt, drv, by simpa [support_pure] using hm⟩⟩
      | succ f' =>
        simp only [BhShallowTwoStageRed.run1_query_inr_succ]
        rcases t with (kq | ctl) | ⟨i, sq⟩
        · have hStSub : ∀ u, (mx u).IsQueryBoundP isStartQ qStartRem :=
            fun u => (hqSt.2 u).mono (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly])
          dsimp only [bhPrefixRedWithSessionTracked, bhPrefixHandlePreWithSessionTracked, bhTargetQenc]
          by_cases hro : ∃ sec, kq = .roQuery sec
          · rcases hro with ⟨sec, rfl⟩
            have hKiSub : ∀ u, (mx u).IsQueryBoundP isOnlineKiQ qKiRem :=
              fun u => (hqKi.2 u).mono (by simp [isOnlineKiQ, bhClassifyTarget, bhClassifyTargetOnly])
            have hStepInv : ∀ res ∈ support (bhLiftP
                (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
                (bhShallowStepPreNonCtlSessionTracked T P ki C K qep decT encT drv
                  (.inl (.inl (.roQuery sec))))),
                shallowInstsBoundInv qKiDone qStartDone res.2.1 := fun res hres => by
              have hraw := KindRedHaltedEval.mem_support_of_bhLiftP _ hres
              unfold bhShallowStepPreNonCtlSessionTracked at hraw
              dsimp only at hraw; split_ifs at hraw
              · simp only [support_pure, Set.mem_singleton_iff] at hraw; subst hraw; exact hInv
              · simp only [support_pure, Set.mem_singleton_iff] at hraw; subst hraw; exact hInv
              · rw [mem_support_bind_iff] at hraw
                rcases hraw with ⟨⟨kr, st'⟩, -, hret⟩
                simp only [support_pure, Set.mem_singleton_iff] at hret; subst hret
                have hMir : bhE2EMirror { drv.1 with st := st' } (.roQuery sec) kr =
                    { drv.1 with st := st' } := by cases kr <;> rfl
                dsimp only; rw [hMir]
                exact ⟨hInv.1, hInv.2.1, hInv.2.2.1, hInv.2.2.2⟩
            simp only [bind_assoc, pure_bind]
            refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun res hres =>
                (ih _ f' qKiDone qKiRem qStartDone qStartRem res.2
                  (hKiSub _) (hStSub _) hKiSum hStSum (hStepInv res hres)).1, fun m hm => ?_⟩
            rw [mem_support_bind_iff] at hm
            rcases hm with ⟨res, hres, hm'⟩
            exact (ih _ f' qKiDone qKiRem qStartDone qStartRem res.2
              (hKiSub _) (hStSub _) hKiSum hStSum (hStepInv res hres)).2 m hm'
          · have hne : ∀ sec, kq ≠ .roQuery sec := fun sec hk => hro ⟨sec, hk⟩
            have hon : isOnlineKiQ (S := S) (ℓ := ℓ) (.inr (.inl (.inl kq))) :=
              isOnlineKiQ_of_ne_roQuery hne
            have hKiPos : 0 < qKiRem := hqKi.1.resolve_left (fun h => h hon)
            have hKiSub : ∀ u, (mx u).IsQueryBoundP isOnlineKiQ (qKiRem - 1) :=
              fun u => (hqKi.2 u).mono (by split_ifs; exact le_rfl)
            have hStepInv : ∀ res ∈ support (bhLiftP
                (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
                (bhShallowStepPreNonCtlSessionTracked T P ki C K qep decT encT drv (.inl (.inl kq)))),
                shallowInstsBoundInv (qKiDone + 1) qStartDone res.2.1 := fun res hres => by
              have hraw := KindRedHaltedEval.mem_support_of_bhLiftP _ hres
              unfold bhShallowStepPreNonCtlSessionTracked at hraw
              dsimp only at hraw; split_ifs at hraw
              · simp only [support_pure, Set.mem_singleton_iff] at hraw; subst hraw
                exact ⟨Nat.le_succ_of_le hInv.1, hInv.2.1, hInv.2.2.1, hInv.2.2.2⟩
              · simp only [support_pure, Set.mem_singleton_iff] at hraw; subst hraw
                exact ⟨Nat.le_succ_of_le hInv.1, hInv.2.1, hInv.2.2.1, hInv.2.2.2⟩
              · rw [mem_support_bind_iff] at hraw
                rcases hraw with ⟨⟨kr, st'⟩, -, hret⟩
                simp only [support_pure, Set.mem_singleton_iff] at hret; subst hret
                exact shallowInstsBoundInv_mirror hInv st' kq kr
            simp only [bind_assoc, pure_bind]
            refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun res hres =>
                (ih _ f' (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem res.2
                  (hKiSub _) (hStSub _) (by omega) hStSum (hStepInv res hres)).1, fun m hm => ?_⟩
            rw [mem_support_bind_iff] at hm
            rcases hm with ⟨res, hres, hm'⟩
            exact (ih _ f' (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem res.2
              (hKiSub _) (hStSub _) (by omega) hStSum (hStepInv res hres)).2 m hm'
        · cases ctl with | _ sid =>
          have hStPos : 0 < qStartRem :=
            hqSt.1.resolve_left (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly])
          have hKiSub : ∀ u, (mx u).IsQueryBoundP isOnlineKiQ qKiRem :=
            fun u => (hqKi.2 u).mono (by simp [isOnlineKiQ, bhClassifyTarget, bhClassifyTargetOnly])
          have hStSub : ∀ u, (mx u).IsQueryBoundP isStartQ (qStartRem - 1) :=
            fun u => (hqSt.2 u).mono (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly])
          dsimp only [bhPrefixRedWithSessionTracked, bhPrefixHandlePreWithSessionTracked, bhTargetQenc]
          have hLocInv : ∀ ans ∈ support (bhLiftP
              (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
              (bhE2ELocalStartSessionTracked T.init ki C K (some true) drv sid)),
              shallowInstsBoundInv qKiDone (qStartDone + 1) ans.2.1 := fun ans hans => by
            have hraw := KindRedHaltedEval.mem_support_of_bhLiftP _ hans
            unfold bhE2ELocalStartSessionTracked at hraw; dsimp only at hraw
            cases hg : bhE2EGuard drv.1 sid with
            | none =>
              simp only [hg, support_pure, Set.mem_singleton_iff] at hraw; subst hraw
              exact ⟨hInv.1, Nat.le_succ_of_le hInv.2.1, hInv.2.2.1, hInv.2.2.2⟩
            | some val =>
              rcases val with ⟨_, _, ⟨_, _⟩⟩; simp only [hg, mem_support_bind_iff] at hraw
              rcases hraw with ⟨⟨kr1, _⟩, -, ⟨kr2, st2⟩, -, ac, -, hret⟩
              simp only [support_pure, Set.mem_singleton_iff] at hret; subst hret
              exact shallowInstsBoundInv_finishStartSpk C K (some true) hInv st2 sid kr1 kr2 ac
          have hCtlEq : ∀ k_idx, min qStart (min b_on.q_total S.N_send_tot) ≤ k_idx →
              bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
                (bhShallowStepPreCtlSessionTracked T.init ki C K k_idx drv sid) =
              (bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
                (bhE2ELocalStartSessionTracked T.init ki C K (some true) drv sid) >>=
                fun ans => pure (Sum.inl (ans.1, ans.2))) := fun k_idx hk_idx => by
            unfold bhShallowStepPreCtlSessionTracked; simp only [bhLiftP, simulateQ_bind]
            refine OracleComp.bind_congr_of_forall_mem_support _ fun ans hans => ?_
            have hLen : ans.2.1.insts.length ≤ min qStart (min b_on.q_total S.N_send_tot) :=
              shallowInstsBoundInv_insts_le (hLocInv ans hans) (by omega) (by omega)
            have hNotLt : ¬ k_idx < ans.2.1.insts.length := by omega
            rcases ans with ⟨_, ⟨_, _⟩⟩; dsimp only at hNotLt ⊢
            simp only [hNotLt, ↓reduceIte, simulateQ_pure]
          rw [hCtlEq k₁ hk₁, hCtlEq k₂ hk₂]; simp only [bind_assoc, pure_bind]
          refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ans hans =>
              (ih _ f' qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) ans.2
                (hKiSub _) (hStSub _) hKiSum (by omega) (hLocInv ans hans)).1, fun m hm => ?_⟩
          rw [mem_support_bind_iff] at hm
          rcases hm with ⟨ans, hans, hm'⟩
          exact (ih _ f' qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) ans.2
            (hKiSub _) (hStSub _) hKiSum (by omega) (hLocInv ans hans)).2 m hm'
        · have hKiSub : ∀ u, (mx u).IsQueryBoundP isOnlineKiQ qKiRem :=
            fun u => (hqKi.2 u).mono (by simp [isOnlineKiQ, bhClassifyTarget, bhClassifyTargetOnly])
          have hStSub : ∀ u, (mx u).IsQueryBoundP isStartQ qStartRem :=
            fun u => (hqSt.2 u).mono (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly])
          dsimp only [bhPrefixRedWithSessionTracked, bhPrefixHandlePreWithSessionTracked,
            bhShallowStepPreNonCtlSessionTracked, bhTargetQenc]
          have hSmInv : ∀ (res : BHTargetResp ℓ × (BHE2EDrvState S ℓ × List τ)),
              res ∈ support (bhLiftP
                (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
                (do let (sr, σH') ← bhE2EStepLocalSmSessionTracked T C K qep decT encT drv i sq
                    return ((Sum.inr sr : BHTargetResp ℓ), σH'))) →
              shallowInstsBoundInv qKiDone qStartDone res.2.1 := fun res hres => by
            have hraw := KindRedHaltedEval.mem_support_of_bhLiftP _ hres
            rw [mem_support_bind_iff] at hraw
            rcases hraw with ⟨out, hout, hret⟩
            simp only [support_pure, Set.mem_singleton_iff] at hret; subst hret
            exact shallowInstsBoundInv_stepLocalSm T C K qep decT encT hInv i sq hout
          simp only [bind_assoc, pure_bind]
          refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun res hres =>
              (ih _ f' qKiDone qKiRem qStartDone qStartRem res.2
                (hKiSub _) (hStSub _) hKiSum hStSum (hSmInv res hres)).1, fun m hm => ?_⟩
          rw [mem_support_bind_iff] at hm
          rcases hm with ⟨res, hres, hm'⟩
          exact (ih _ f' qKiDone qKiRem qStartDone qStartRem res.2
            (hKiSub _) (hStSub _) hKiSum hStSum (hSmInv res hres)).2 m hm'

/-- Stage-1 and Stage-2 equivalence for `bhPrefixRedWithSessionTracked` between clamped slot `nInst`
and any slot `k ≥ nInst`. -/
theorem bhPrefixRedWithSessionTracked_stage12_eq_of_ge_nInst_online
    {τ β : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs)
    {k : ℕ} (hk_ge : min qStart (min (onlineClampedBudget b).q_total S.N_send_tot) ≤ k)
    (qTot : ℕ) (flip : Bool)
    (game2 : IdentityKey → IdentityKey → BitVec 256 →
      OracleComp
        (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool →
      ProbComp β) :
    let nInst := min qStart (min (onlineClampedBudget b).q_total S.N_send_tot)
    (stageOneAsProbComp
        ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT nInst).eval1
          (fun _ => B_A) () qTot false) >>=
      fun o => game2 o.1.idA o.1.idB o.1.spkCoins
        ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT nInst).eval2 o.2 flip qTot false)) =
    (stageOneAsProbComp
        ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1
          (fun _ => B_A) () qTot false) >>=
      fun o => game2 o.1.idA o.1.idB o.1.spkCoins
        ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2 o.2 flip qTot false)) := by
  dsimp only
  set nInst := min qStart (min (onlineClampedBudget b).q_total S.N_send_tot)
  have hOnMin := isQueryBoundP_isOnlineKiQ_bOn hB
  have hStMin := isQueryBoundP_min B_A isStartQ hB.2.2.2.2.2.2.1 hB.2.2.2.2.2.1
  have hInitInv : shallowInstsBoundInv 0 0 ({} : BHE2EDrvState S ℓ) :=
    ⟨Nat.zero_le _, Nat.zero_le _, List.nodup_nil, fun _ h => nomatch h⟩
  obtain ⟨hRun1Eq, hRun1Done⟩ :=
    bhPrefixRedWithSessionTracked_run1_eq_and_done_online T P ki C K qep decT encT
      (onlineClampedBudget b) qStart (le_refl nInst) hk_ge false B_A qTot
      0 (onlineClampedBudget b).q_total 0 (min qStart S.N_send_tot) ({}, [])
      hOnMin hStMin (by omega) (by omega) hInitInv
  have hEval1Eq :
      (bhPrefixRedWithSessionTracked T P ki C K qep decT encT nInst).eval1
        (fun _ => B_A) () qTot false =
      (bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1
        (fun _ => B_A) () qTot false := by
    have hInit : ∀ m, (bhPrefixRedWithSessionTracked T P ki C K qep decT encT m).init () =
        pure ((), ({}, [])) := fun _ => rfl
    dsimp only [BhShallowTwoStageRed.eval1]
    rw [hInit nInst, hInit k, pure_bind, pure_bind]
    dsimp only
    rw [hRun1Eq]
    rfl
  have hEval1Done : ∀ o ∈ support (stageOneAsProbComp
      ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1
        (fun _ => B_A) () qTot false)),
      ∃ b_out s_out, o.2 = .done b_out s_out := fun o ho => by
    rw [← hEval1Eq] at ho
    have hraw := mem_support_of_stageOneAsProbComp_local _ ho
    simp only [BhShallowTwoStageRed.eval1, mem_support_bind_iff] at hraw
    rcases hraw with ⟨⟨_, s0⟩, hs0, m, hm, htail⟩
    have hs0' : s0 = ({}, []) := by
      simp only [bhPrefixRedWithSessionTracked, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hs0
      exact hs0.2
    subst hs0'
    obtain ⟨b_out, s_out, rfl⟩ := hRun1Done m hm
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at htail
    rcases htail with ⟨_, -, rfl⟩
    exact ⟨b_out, s_out, rfl⟩
  rw [hEval1Eq]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun o ho => ?_
  obtain ⟨b_out, s_out, hm⟩ := hEval1Done o ho
  rw [hm]
  rfl

/-- Stage-1 and Stage-2 equivalence between `prefixRedHalted` at `onlineClampedBudget b` (with
clamped slot) and `bhPrefixRedWithSessionTracked` at slot `k` for all `k : ℕ`. -/
theorem prefixEval_clamped_bOn_eq_of_valid_inst
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop}
    {b : SignalPqxdh.QueryBudget} {qStart qInst qep k : ℕ} {qs : ℕ → ℕ}
    (hValid : ValidHaltedPrefixSubprogramsInst subs T TrackInv (onlineClampedBudget b) qStart qInst qep)
    (hqInst : Finset.sup (Finset.range qStart) qs ≤ qInst)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (hPromoteNInst : ∀ {σH : BHE2EDrvState S ℓ × List SessH},
      σH.1.insts.length ≤ min qStart (min (onlineClampedBudget b).q_total S.N_send_tot) →
      ∀ {Γ} (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
        (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
        (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy) (ρ : Env Γ) (idx? : Option ℕ),
        kE.eval ρ = min qStart (min (onlineClampedBudget b).q_total S.N_send_tot) →
        idxOptE.eval ρ = idx? → σE.eval ρ = subs.drvEnc σH.1 →
        (subs.promoteSlotKC qStart kE idxOptE σE).eval ρ =
          match bhPromoteSlotK (min qStart (min (onlineClampedBudget b).q_total S.N_send_tot)) idx? σH.1 with
          | .inl ans => pure (.inl (ans.1, subs.drvEnc ans.2))
          | .inr (ctx, p, σ_p) => pure (.inr (atomicPrefixCtxEnc ctx, (p, subs.drvEnc σ_p))))
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs)
    {β : Type}
    (game2 : IdentityKey → IdentityKey → BitVec 256 →
      OracleComp
        (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool →
      ProbComp β)
    (qTot : ℕ) (flip : Bool) :
    let b_on := onlineClampedBudget b
    let nInst := min qStart (min b_on.q_total S.N_send_tot)
    let R := prefixRedHalted subs b_on qStart qInst qep (min k nInst)
    let R_sh := bhPrefixRedWithSessionTracked T P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
      C K qep decT encT k
    (stageOneAsProbComp (R.eval1 (fun _ => B_A) () qTot false) >>= fun o =>
      game2 o.1.1 o.1.2.1 o.1.2.2 (R.eval2 o.2 flip qTot false)) =
    (stageOneAsProbComp (R_sh.eval1 (fun _ => B_A) () qTot false) >>= fun o =>
      game2 o.1.idA o.1.idB o.1.spkCoins (R_sh.eval2 o.2 flip qTot false)) := by
  dsimp only
  set b_on := onlineClampedBudget b
  set nInst := min qStart (min b_on.q_total S.N_send_tot)
  by_cases hlt : k < nInst
  · have hmin : min k nInst = k := Nat.min_eq_left (Nat.le_of_lt hlt)
    rw [hmin]
    have hSim := twoStage_stage12_comp_eq_online
      (prefixRedHalted_twoStageSimSpecOnline hValid hqInst hP
        (fun {_} hInstLen {_} kE idxOptE σE ρ idx? hkE hidx hσ =>
          hValid.promoteSlotKC_eval hInstLen kE idxOptE σE ρ k idx? hlt hkE hidx hσ))
      B_A hB game2 qTot qTot false flip
    dsimp only [prefixRedHalted_twoStageSimSpecOnline,
      CompositionHaltedPrefixEval.prefixRedHalted_twoStageSimSpecInst] at hSim
    rwa [bhPrefixRedWithHalted_eq_bhPrefixRedWithSessionTracked] at hSim
  · have hk_ge : nInst ≤ k := Nat.not_lt.mp hlt
    have hmin : min k nInst = nInst := Nat.min_eq_right hk_ge
    rw [hmin]
    have hSim := twoStage_stage12_comp_eq_online
      (prefixRedHalted_twoStageSimSpecOnline hValid hqInst hP hPromoteNInst)
      B_A hB game2 qTot qTot false flip
    dsimp only [prefixRedHalted_twoStageSimSpecOnline,
      CompositionHaltedPrefixEval.prefixRedHalted_twoStageSimSpecInst] at hSim
    rw [bhPrefixRedWithHalted_eq_bhPrefixRedWithSessionTracked] at hSim
    exact hSim.trans (bhPrefixRedWithSessionTracked_stage12_eq_of_ge_nInst_online
      T P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT
      b qStart qs B_A hB hk_ge qTot flip game2)

end Computational.Proofs.E2E.Dsl.CompositionHaltedRedsPrefixSim
