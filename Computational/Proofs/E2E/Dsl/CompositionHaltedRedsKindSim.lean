/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Proofs.LibsignalCli.MainHaltedKeyInd -- proof-setup: allow-public-import
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHalted -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHaltedInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst
import Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst
import Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecOnline
import Computational.Proofs.E2E.Dsl.HaltedStartSessionSim
import Computational.Proofs.E2E.Dsl.KindRedHaltedEval
import Computational.Proofs.E2E.Dsl.M3Interfaces
import Computational.Proofs.E2E.Dsl.PqxdhSimTypes

/-!
# Online-Clamped Handshake Reduction Equivalence

Proves `ProbComp` equivalence (`clamped_bOn_kindRealExp_eq`) in `pqxdhKeyInd1KeyRealExp` between
`kindRedHalted` at `onlineClampedBudget b` and `bhKindRedWithTracked` under
`pqxdhKeyIndImpl1KeyReal`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Computational.Proofs.E2E.Dsl.CompositionHaltedRedsKindSim

open scoped BigOperators
open OracleComp OracleSpec
open _root_.ReductionDsl (Sig Ops Iface Ty Env Expr Comp UniformSamplerTag AtomicBaseUnif
  E2EKeyIndTag BV256 FinT atomicSig atomicE2EOps e2eKeyIndTargetIface sidT sidV
  keyIndQT keyIndQenc keyIndRT keyIndRenc smQT smQenc)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (BHE2EDrvState BHModelInst Bytes SampledSessionKey BHE2ESmResp
  BHTargetQuery BHTargetResp BhShallowRed bhShallowImplOfHandle bhTargetGameSpec
  e2eTargetGameCodec bhTargetQenc bhTargetRdec
  bhLiftP bhFwdU bhDrvKiQueryOk bhNoOpkRespPromoted bhE2EMirror bhE2EGuard
  bhE2EFinishStartSpk bhE2EDrvWon configRefuseEarlyBobCorr paramsIdsWithSpqr sessionSchemeFixedSpk)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack)
open Computational.Proofs.LibsignalCli.MainHaltedKeyInd (bhKindRedWithTracked)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (SessionHaltTracker
  bhClassifyTarget bhClassifyTargetOnly
  bhE2EStepLocalSmSessionTracked bhE2EStepLocalSmSessionTracked_eq_filter bhFilterSmQuery
  oracleImplRSessionTracked)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness (HaltedTargetAdvPerInstanceBounded
  kemFailSessionTracker)
open Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind (onlineClampedBudget)
open Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecOnline
  (isOnlineKiQ isOnlineKiQ_of_ne_roQuery isQueryBoundP_isOnlineKiQ_bOn
   OneStageAtomicSimSpecOnline oneStage_eval_eq_online)

private theorem st_run_get_bind_loc {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (k : σ → StateT σ m α) (s : σ) :
    (MonadState.get >>= k).run s = (k s).run s := pure_bind (s, s) _

private theorem st_run_getOf_bind_loc {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (k : σ → StateT σ m α) (s : σ) :
    (MonadStateOf.get >>= k).run s = (k s).run s := pure_bind (s, s) _

private theorem st_run_lift_bind_loc {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (x : m α) (k : α → StateT σ m β) (s : σ) :
    ((liftM x : StateT σ m α) >>= k).run s = (x >>= fun a => (k a).run s) := by
  change ((x >>= fun a => pure (a, s)) >>= fun p => (k p.1).run p.2) = (x >>= fun a => (k a).run s)
  simp only [LawfulMonad.bind_assoc, pure_bind]

private theorem comp_eval_bind_loc {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))} {a b : Ty (atomicSig ℓ Pt)}
    (c1 : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ a)
    (c2 : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) (a :: Γ) b)
    (ρ : Env Γ) :
    (Comp.bind c1 c2).eval ρ = (c1.eval ρ >>= fun x => c2.eval (.cons x ρ)) := rfl

private theorem atomicKeyIndLiftP_map_loc {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α β : Type}
    (f : α → β) (p : ProbComp α) :
    (e2eKeyIndTargetIface S ℓ Pt).liftP (f <$> p) =
      f <$> (e2eKeyIndTargetIface S ℓ Pt).liftP p := by
  simp [KindRedHaltedEval.atomicKeyIndTargetIface_liftP_eq_bhLiftP, bhLiftP]

private def kiNoOpkPromoted_loc {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) : SignalPqxdh.KeyIndQuery S → Bool
  | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u
  | _ => false

private theorem eval_query_keyInd_loc {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (qE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (kq : SignalPqxdh.KeyIndQuery S)
    (hq : qE.eval ρ = keyIndQenc kq) :
    (Comp.query (O := atomicE2EOps ℓ P C K decT encT)
      (I := e2eKeyIndTargetIface S ℓ Pt) E2EKeyIndTag.keyInd qE).eval ρ =
      keyIndRenc <$>
        (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
          OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) := by
  dsimp only [Comp.eval, e2eKeyIndTargetIface]
  rw [hq, KindRedHalted.keyIndQdec_keyIndQenc]

private theorem comp_eval_bind_sample_bv256_loc {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))} {b : Ty (atomicSig ℓ Pt)}
    (c2 : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt)
      (BV256 (ℓ := ℓ) (Pt := Pt) :: Γ) b)
    (ρ : Env Γ) :
    (Comp.bind (.sample (I := e2eKeyIndTargetIface S ℓ Pt)
      (UniformSamplerTag.base AtomicBaseUnif.bv256) .unit) c2).eval ρ =
      (bhLiftP (G := SignalPqxdh.keyIndSpec S) ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
        fun bv => c2.eval (.cons bv ρ)) := by
  dsimp only [Comp.eval, e2eKeyIndTargetIface, _root_.ReductionDsl.atomicBaseSamplers,
    _root_.ReductionDsl.unifSamplers]
  rw [KindRedHaltedEval.atomicKeyIndTargetIface_liftP_eq_bhLiftP]
  rfl

private theorem comp_eval_caseOpt_loc {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))} {a b : Ty (atomicSig ℓ Pt)}
    (e : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt a))
    (cN : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ b)
    (cS : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) (a :: Γ) b)
    (ρ : Env Γ) :
    (Comp.caseOpt e cN cS).eval ρ =
      match e.eval ρ with
      | none => cN.eval ρ
      | some x => cS.eval (.cons x ρ) := by
  dsimp only [Comp.eval]
  cases e.eval ρ <;> rfl

private def bhKindHandleWithHaltedClamped {S : SignalPqxdh.Setup} {ℓ : ℕ} {SessH : Type}
    (nSpk nOpk : ℕ)
    (initTrack : SampledSessionKey → SessH)
    (stepLocalSmH : BHE2EDrvState S ℓ × List SessH → ℕ →
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain →
      ProbComp (BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List SessH)))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (σH : BHE2EDrvState S ℓ × List SessH) (q : BHTargetQuery S ℓ (BitVec 512)) :
    OracleComp (unifSpec + SignalPqxdh.keyIndSpec S)
      (BHTargetResp ℓ × (BHE2EDrvState S ℓ × List SessH)) :=
  match q with
  | .inl (.inl kq) =>
    if bhDrvKiQueryOk P σH.1.toModelDriverBase kq &&
        !(match kq with | .corruptIK u => bhNoOpkRespPromoted σH.1.instMeta u | _ => false) then do
      let kr ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
      return (.inl (.inl kr), (HaltedStartSessionSim.bhE2EMirrorClamped nSpk nOpk σH.1 kq kr, σH.2))
    else
      pure (.inl (.inl .noneResp), σH)
  | .inl (.inr sid) =>
    match (bhE2EGuard σH.1 sid).map (fun (_, _, uj) => uj) with
    | none => pure (.inl (.inr none), σH)
    | some (u, j) => do
      let ts ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr (.testSession sid))) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
      let sk ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr (.revealSpkSk u j))) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
      let bv ← bhLiftP (G := SignalPqxdh.keyIndSpec S) ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let fin := KindRedHalted.bhE2EFinishStartSpkTracked initTrack C K (some σH.1.b) σH sid ts sk bv
      return (.inl (.inr fin.1), fin.2)
  | .inr (i, sq) => do
    let res ← bhLiftP (G := SignalPqxdh.keyIndSpec S) (stepLocalSmH σH i sq)
    return (.inr res.1, res.2)

private def bhKindRedWithHaltedClamped {S : SignalPqxdh.Setup} {ℓ : ℕ} {SessH : Type}
    (nSpk nOpk : ℕ)
    (initTrack : SampledSessionKey → SessH)
    (stepLocalSmH : BHE2EDrvState S ℓ × List SessH → ℕ →
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain →
      ProbComp (BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List SessH)))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) :
    BhShallowRed (bhTargetGameSpec S ℓ (BitVec 512))
      (unifSpec + SignalPqxdh.keyIndSpec S)
      Unit Bool Unit Bool (BHE2EDrvState S ℓ × List SessH) where
  init _ := do
    let drvH ← bhLiftP (G := SignalPqxdh.keyIndSpec S)
      (do let b ← ($ᵗ Bool : ProbComp Bool)
          return (({ b := b } : BHE2EDrvState S ℓ), ([] : List SessH)))
    return ((), drvH)
  impl := bhShallowImplOfHandle bhTargetQenc bhTargetRdec
    (bhKindHandleWithHaltedClamped nSpk nOpk initTrack stepLocalSmH P C K)
  finish drvH aOut := pure (aOut == drvH.1.b || bhE2EDrvWon drvH.1 drvH.1.b)

private structure ClampedKindInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget)
    (qStart : ℕ) (qs : ℕ → ℕ)
    (qKiDone qSendDone qStartDone : ℕ) (qSessDone : ℕ → ℕ)
    (σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes)) : Prop where
  base : CompositionHaltedWitnessInst.HaltedKindSimInvInst
    (PrefixRedHaltedInst.KemBridgeTrackInvLocal C.F K)
    C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH
  bundles_clamped : σH.1.bundles.length ≤ min b.q_total S.N_spk_tot
  opks_clamped : σH.1.opks.length ≤ min b.q_total S.N_opk_tot

private theorem ClampedKindInv.drvMirrorBounded {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget}
    {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes)}
    (h : ClampedKindInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    M3Interfaces.DrvMirrorBounded b.q_total
      (min b.q_total S.N_spk_tot) (min b.q_total S.N_opk_tot)
      (min b.q_total S.N_send_tot) b.q_total (min qStart (min b.q_total S.N_send_tot)) σH.1 :=
  ⟨h.base.mirror.prins_le.trans h.base.ki_le,
   h.bundles_clamped,
   h.opks_clamped,
   h.base.sends_length_le,
   h.base.mirror.corrPrins_le.trans h.base.ki_le,
   h.base.insts_length_le,
   h.base.instMeta_length_le,
   h.base.mirror.revSpks_le.trans h.base.ki_le⟩

private theorem finishStartSpkTracked_bundles_opks_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {SessH : Type}
    (initT : SampledSessionKey → SessH) (C : Crypto) (K : MlKem) (bm : Option Bool)
    (σH : BHE2EDrvState S ℓ × List SessH) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) :
    (KindRedHalted.bhE2EFinishStartSpkTracked initT C K bm σH sid kr1 kr2 ac).2.1.bundles =
        σH.1.bundles ∧
      (KindRedHalted.bhE2EFinishStartSpkTracked initT C K bm σH sid kr1 kr2 ac).2.1.opks =
        σH.1.opks := by
  dsimp only [KindRedHalted.bhE2EFinishStartSpkTracked]
  unfold bhE2EFinishStartSpk
  rcases bhE2EGuard σH.1 sid with _ | ⟨_, _, _, _⟩
  · exact ⟨rfl, rfl⟩
  · cases kr1 <;> cases kr2 <;> dsimp only <;> try exact ⟨rfl, rfl⟩
    split_ifs <;> exact ⟨rfl, rfl⟩

private theorem stepLocalSmSessionTracked_bundles_opks_eq
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt τ : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : BHE2EDrvState S ℓ × List τ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ)}
    (hout : out ∈ support (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)) :
    out.2.1.bundles = σH.1.bundles ∧ out.2.1.opks = σH.1.opks := by
  rw [bhE2EStepLocalSmSessionTracked_eq_filter] at hout
  split_ifs at hout with hcl
  · simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
  · rcases hd : σH.1.insts[i]? with _ | d
    · simp only [hd, support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
    · rcases him : σH.1.instMeta[i]? with _ | im
      · simp only [hd, him, support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
      · simp only [hd, him] at hout
        split_ifs at hout with hcorr
        · simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
        · rcases hgs : d.gs with _ | gs
          · simp only [hgs, support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
          · rcases hflt : bhFilterSmQuery d im sq with _ | q'
            · simp only [hgs, hflt, support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
            · simp only [hgs, hflt, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
              rcases hout with ⟨⟨⟨_, _⟩, _⟩, -, rfl⟩
              exact ⟨rfl, rfl⟩

private theorem kindHandle_eval_ki_clamped {Pt : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (smStep : KindRedHaltedInst.HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT
      (PrefixRedHaltedInst.KemBridgeTrackInvLocal C.F K))
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (b0 : SignalPqxdh.QueryBudget) (qStart qep : ℕ) (qs : ℕ → ℕ)
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes)}
    (hInv : ClampedKindInv C K b0 qStart qs qKiDone qSendDone qStartDone qSessDone σH)
    (kq : SignalPqxdh.KeyIndQuery S) :
    let qInst := Finset.sup (Finset.range qStart) qs
    let subs := KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b0
    let T := kemFailSessionTracker (ℓ := ℓ) C.F K
    let nSpk := min b0.q_total S.N_spk_tot
    let nOpk := min b0.q_total S.N_opk_tot
    (KindRedHalted.kindRedHalted subs b0 qStart qInst qep).handle.eval
      (.cons (KindRedHalted.drvKindHaltedEnc subs σH)
        (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inl kq))) .nil)) =
      Prod.map KindRedHaltedEval.atomicKindRespEnc (KindRedHalted.drvKindHaltedEnc subs) <$>
        bhKindHandleWithHaltedClamped nSpk nOpk T.init
          (bhE2EStepLocalSmSessionTracked T C K qep decT encT)
          P C K σH (bhTargetQenc (.inl (.inl kq))) := by
  dsimp only [KindRedHalted.kindRedHalted]
  set qInst := Finset.sup (Finset.range qStart) qs
  set subs := KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b0
  set T := kemFailSessionTracker (ℓ := ℓ) C.F K
  set nSpk := min b0.q_total S.N_spk_tot
  set nOpk := min b0.q_total S.N_opk_tot
  rw [KindRedHalted.kindHandleHalted_eval_ki]
  have hRhsEq :
      bhKindHandleWithHaltedClamped nSpk nOpk T.init
        (bhE2EStepLocalSmSessionTracked T C K qep decT encT)
        P C K σH (bhTargetQenc (.inl (.inl kq))) =
      if (bhDrvKiQueryOk P σH.1.toModelDriverBase kq && !kiNoOpkPromoted_loc σH.1 kq) = true then
        do
          let kr ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
            OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
          pure ((.inl (.inl kr) : BHTargetResp ℓ),
            (HaltedStartSessionSim.bhE2EMirrorClamped nSpk nOpk σH.1 kq kr, σH.2))
      else
        pure ((.inl (.inl .noneResp) : BHTargetResp ℓ), σH) := by
    cases kq <;> rfl
  rw [hRhsEq]
  let ρ_ki : Env [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      KindRedHalted.drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
    .cons (keyIndQenc kq) (.cons (.inl (keyIndQenc kq))
      (.cons (KindRedHalted.drvKindHaltedEnc subs σH) (.cons (.inl (.inl (keyIndQenc kq))) .nil)))
  have hokE : (subs.kiQueryOkE b0 qStart (.fst .v2) .v0).eval ρ_ki =
      (bhDrvKiQueryOk P σH.1.toModelDriverBase kq && !kiNoOpkPromoted_loc σH.1 kq) := by
    have hdE : (Expr.fst (O := atomicE2EOps ℓ P C K decT encT) .v2).eval ρ_ki =
        HaltedStartSessionSim.drvEnc (Pt := Pt) σH.1 := rfl
    have hqE : (Expr.v0 : Expr (atomicE2EOps ℓ P C K decT encT) _ _).eval ρ_ki =
        keyIndQenc kq := rfl
    exact (HaltedStartSessionSim.kiQueryOkClampedE_eval b0 qStart hP (.fst .v2) .v0 ρ_ki
      hdE hqE (hInv.base.mirror.prins_le.trans hInv.base.ki_le)
      hInv.base.instMeta_length_le).trans (by cases kq <;> rfl)
  dsimp only [ρ_ki] at hokE
  rw [hokE]
  cases hok : (bhDrvKiQueryOk P σH.1.toModelDriverBase kq && !kiNoOpkPromoted_loc σH.1 kq)
  · simp [Prod.map, KindRedHaltedEval.atomicKindRespEnc, keyIndRenc,
      KindRedHalted.drvKindHaltedEnc]
  · simp only [↓reduceIte]
    have hq := eval_query_keyInd_loc (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      .v0 ρ_ki kq rfl
    dsimp only [ρ_ki] at hq
    rw [hq]
    simp only [bind_map_left, map_bind, map_pure]
    refine bind_congr fun kr => ?_
    have hm : (subs.mirrorE (.fst .v3) .v1 .v0).eval (.cons (keyIndRenc kr) ρ_ki) =
        subs.drvEnc (HaltedStartSessionSim.bhE2EMirrorClamped nSpk nOpk σH.1 kq kr) := by
      dsimp only [subs, KindRedHaltedInst.mkKindSubprogramsHaltedClamped, nSpk, nOpk]
      exact HaltedStartSessionSim.mirrorClampedE_eval b0 (.fst .v3) .v1 .v0
        (.cons (keyIndRenc kr) ρ_ki) σH.1 kq kr rfl rfl rfl
    dsimp only [ρ_ki] at hm
    rw [hm]
    rfl

private def clampedKindOneStageSimSpecOnline {Pt : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (smStep : KindRedHaltedInst.HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT
      (PrefixRedHaltedInst.KemBridgeTrackInvLocal C.F K))
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (b : SignalPqxdh.QueryBudget) (qStart qep : ℕ) (qs : ℕ → ℕ) :
    OneStageAtomicSimSpecOnline S Pt ℓ
      (atomicE2EOps ℓ P C K decT encT) b qStart qs
      (BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes)) :=
  let b0 := onlineClampedBudget b
  let qInst := Finset.sup (Finset.range qStart) qs
  let subs := KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b0
  let T := kemFailSessionTracker (ℓ := ℓ) C.F K
  let nSpk := min b0.q_total S.N_spk_tot
  let nOpk := min b0.q_total S.N_opk_tot
  { R := KindRedHalted.kindRedHalted subs b0 qStart qInst qep
    handleRef := bhKindHandleWithHaltedClamped nSpk nOpk T.init
      (bhE2EStepLocalSmSessionTracked T C K qep decT encT) P C K
    R_ref := bhKindRedWithHaltedClamped nSpk nOpk T.init
      (bhE2EStepLocalSmSessionTracked T C K qep decT encT) P C K
    drvEnc := KindRedHalted.drvKindHaltedEnc subs
    Inv := ClampedKindInv C K b0 qStart qs
    impl_eq := rfl
    init_eq := by
      dsimp only [KindRedHalted.kindRedHalted, bhKindRedWithHaltedClamped, Comp.eval, subs,
        KindRedHaltedInst.mkKindSubprogramsHaltedClamped]
      rw [HaltedStartSessionSim.initKindC_eval, atomicKeyIndLiftP_map_loc, bind_map_left]
      dsimp only [KindRedHaltedEval.atomicKeyIndTargetIface_liftP_eq_bhLiftP, bhLiftP]
      simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
      rfl
    init_inv := fun us hus => by
      dsimp only [bhKindRedWithHaltedClamped] at hus
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hus
      rcases hus with ⟨drvH, hdrvH, rfl⟩
      have hdrvP := KindRedHaltedEval.mem_support_of_bhLiftP _ hdrvH
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hdrvP
      rcases hdrvP with ⟨secb, -, rfl⟩
      exact ⟨CompositionHaltedWitnessInst.HaltedKindSimInvInst.empty _ C K b0 qStart qs secb,
        Nat.zero_le _, Nat.zero_le _⟩
    step_eq := fun {qKiDone qSendDone qStartDone qSessDone σH} hInv t hBud => by
      rcases t with (kq | ctl) | ⟨i, sq⟩
      · exact kindHandle_eval_ki_clamped smStep hP b0 qStart qep qs hInv kq
      · clear hBud
        dsimp only [KindRedHalted.kindRedHalted]
        cases ctl with | startDR sid =>
        rw [KindRedHalted.kindHandleHalted_eval_ctl]
        dsimp only [bhKindHandleWithHaltedClamped, bhTargetQenc]
        let Γ_ctl : List (Ty (atomicSig ℓ Pt)) :=
          [sidT (ℓ := ℓ) (Pt := Pt) S,
            Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
            KindRedHalted.drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
        let ρ_ctl : Env Γ_ctl :=
          .cons (sidV sid) (.cons (.inr (sidV sid))
            (.cons (KindRedHalted.drvKindHaltedEnc subs σH) (.cons (.inl (.inr (sidV sid))) .nil)))
        dsimp only [KindRedHalted.kindStartStepHaltedC]
        rw [comp_eval_bind_loc]
        have hRet : (Comp.ret (I := e2eKeyIndTargetIface S ℓ Pt)
            (Expr.pair (O := atomicE2EOps ℓ P C K decT encT) .v2 .v0)).eval ρ_ctl =
            pure (KindRedHalted.drvKindHaltedEnc subs σH, sidV sid) := rfl
        dsimp only [ρ_ctl] at hRet
        rw [hRet, pure_bind, comp_eval_caseOpt_loc]
        let Γ1 := Ty.prod (KindRedHalted.drvKindHaltedTy subs) (sidT (ℓ := ℓ) (Pt := Pt) S) :: Γ_ctl
        let ρ1 : Env Γ1 := .cons (KindRedHalted.drvKindHaltedEnc subs σH, sidV sid) ρ_ctl
        have hprep : (subs.prepStartSpkE b0 qStart (.fst (.fst .v0)) (.snd .v0)).eval ρ1 =
            (bhE2EGuard σH.1 sid).map (fun (_, _, uj) => uj) := by
          dsimp only [subs, KindRedHaltedInst.mkKindSubprogramsHaltedClamped]
          exact HaltedStartSessionSim.prepStartSpkClampedE_eval b0 qStart (.fst (.fst .v0)) (.snd .v0)
            ρ1 σH.1 sid rfl rfl hInv.drvMirrorBounded
        dsimp only [ρ1, ρ_ctl] at hprep
        rw [hprep]
        rcases hguard : bhE2EGuard σH.1 sid with _ | ⟨_, _, u, j⟩
        · dsimp only [Option.map, Comp.eval]
          simp [Expr.eval, Expr.v0, Prod.map, KindRedHaltedEval.atomicKindRespEnc]
        · dsimp only [Option.map]
          let Γ2 := Ty.prod (FinT (ℓ := ℓ) (Pt := Pt) S.N_id)
            (FinT (ℓ := ℓ) (Pt := Pt) S.N_recv) :: Γ1
          let ρ2 : Env Γ2 := .cons (u, j) ρ1
          rw [comp_eval_bind_loc]
          have htsQ : (KindRedHalted.mkAtomicTestSessionE
              (O := atomicE2EOps ℓ P C K decT encT) (.snd .v1)).eval ρ2 =
              keyIndQenc (.testSession sid) := by
            simp [ρ2, ρ1, Expr.eval, Expr.v1]
          have hq1 := eval_query_keyInd_loc (KindRedHalted.mkAtomicTestSessionE (.snd .v1))
            ρ2 (.testSession sid) htsQ
          dsimp only [ρ2, ρ1, ρ_ctl] at hq1
          rw [hq1]
          simp only [bind_map_left, map_bind, bind_assoc]
          refine bind_congr fun ts => ?_
          let Γ3 := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ2
          let ρ3 : Env Γ3 := .cons (keyIndRenc ts) ρ2
          rw [comp_eval_bind_loc]
          have hskQ : (KindRedHalted.mkAtomicRevealSpkSkE
              (O := atomicE2EOps ℓ P C K decT encT) .v1).eval ρ3 =
              keyIndQenc (.revealSpkSk u j) := by
            simp [ρ3, ρ2, Expr.eval, Expr.v1]
          have hq2 := eval_query_keyInd_loc (KindRedHalted.mkAtomicRevealSpkSkE .v1)
            ρ3 (.revealSpkSk u j) hskQ
          dsimp only [ρ3, ρ2, ρ1, ρ_ctl] at hq2
          rw [hq2]
          simp only [bind_map_left, bind_assoc]
          refine bind_congr fun sk => ?_
          let Γ4 := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ3
          let ρ4 : Env Γ4 := .cons (keyIndRenc sk) ρ3
          have hsmp := comp_eval_bind_sample_bv256_loc
            (subs.finishStartSpkHaltedC b0 qStart (.some (subs.drvBitE (.fst (.fst .v4))))
              (.fst .v4) (.snd .v4) .v2 .v1 .v0) ρ4
          refine (congrArg (fun m => m >>= fun v =>
            pure ((.inl (.inr v.1) : (e2eTargetGameCodec S ℓ Pt).R.denote), v.2)) hsmp).trans ?_
          dsimp only [ρ4, ρ3, ρ2, ρ1, ρ_ctl]
          simp only [bind_assoc]
          refine bind_congr fun bv => ?_
          let Γ5 := BV256 (ℓ := ℓ) (Pt := Pt) :: Γ4
          let ρ5 : Env Γ5 := .cons bv ρ4
          have hbit : (Expr.some (subs.drvBitE (.fst (.fst .v4)))).eval ρ5 = some σH.1.b := by
            dsimp only [Expr.eval]
            exact congrArg some (subs.drvBitE_eval (.fst (.fst .v4)) ρ5 σH.1 rfl)
          have hfin : (subs.finishStartSpkHaltedC b0 qStart (.some (subs.drvBitE (.fst (.fst .v4))))
              (.fst .v4) (.snd .v4) .v2 .v1 .v0).eval ρ5 =
              pure (let p := KindRedHalted.bhE2EFinishStartSpkTracked T.init C K (some σH.1.b)
                      σH sid ts sk bv
                    (p.1, KindRedHalted.drvKindHaltedEnc subs p.2)) := by
            dsimp only [subs, KindRedHaltedInst.mkKindSubprogramsHaltedClamped,
              KindRedHalted.drvKindHaltedEnc, KindRedHalted.bhE2EFinishStartSpkTracked, T]
            have hσH5 : (Expr.fst (O := atomicE2EOps ℓ P C K decT encT) .v4).eval ρ5 =
                (HaltedStartSessionSim.drvEnc (Pt := Pt) σH.1,
                  σH.2.map HaltedStartSessionSim.sessHEnc) := rfl
            have hs5 : (Expr.snd (O := atomicE2EOps ℓ P C K decT encT) .v4).eval ρ5 = sidV sid := rfl
            have hts5 : (Expr.v2 : Expr (atomicE2EOps ℓ P C K decT encT) Γ5 _).eval ρ5 = keyIndRenc ts := rfl
            have hsk5 : (Expr.v1 : Expr (atomicE2EOps ℓ P C K decT encT) Γ5 _).eval ρ5 = keyIndRenc sk := rfl
            refine (HaltedStartSessionSim.finishStartSpkHaltedClampedC_eval b0 qStart
              (.some (HaltedStartSessionSim.drvBitE (.fst (.fst .v4))))
              (.fst .v4) (.snd .v4) .v2 .v1 .v0 ρ5 σH sid ts sk
              hσH5 hs5 hts5 hsk5 hInv.base.tracks_length_le hInv.drvMirrorBounded).trans ?_
            exact congrArg (fun bm =>
              let res := bhE2EFinishStartSpk C K bm σH.1 sid ts sk bv
              let tracks' := match res.1, ts with
                | some _, .drKeyResp dk =>
                  σH.2 ++ [(kemFailSessionTracker (ℓ := ℓ) C.F K).init
                    (CryptoVerification.E2E.bhKeySOf dk bv)]
                | _, _ => σH.2
              (pure (res.1, (HaltedStartSessionSim.drvEnc (Pt := Pt) res.2,
                tracks'.map (HaltedStartSessionSim.sessHEnc (ℓ := ℓ) (Pt := Pt)))) :
                OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)) hbit
          dsimp only [ρ5, ρ4, ρ3, ρ2, ρ1, ρ_ctl] at hfin
          rw [hfin]
          simp [Prod.map, KindRedHaltedEval.atomicKindRespEnc]
      · clear hBud
        dsimp only [KindRedHalted.kindRedHalted]
        rw [KindRedHalted.kindHandleHalted_eval_sm]
        dsimp only [bhKindHandleWithHaltedClamped, bhTargetQenc]
        let ρ_sm : Env [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)),
            KindRedHalted.drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
          .cons (i, smQenc sq) (.cons (KindRedHalted.drvKindHaltedEnc subs σH)
            (.cons (.inr (i, smQenc sq)) .nil))
        have hHalted := hInv.base.toHaltedSimInv
          (PrefixRedHaltedInst.kemBridgeTrackInvLocal_validSimTrackInv C.F K)
        have hσSm : (Expr.v1 : Expr (atomicE2EOps ℓ P C K decT encT) _ _).eval ρ_sm =
            (HaltedStartSessionSim.drvEnc (Pt := Pt) σH.1,
              σH.2.map HaltedStartSessionSim.sessHEnc) := rfl
        have hiSm : (Expr.fst (O := atomicE2EOps ℓ P C K decT encT) .v0).eval ρ_sm = i := rfl
        have hsqSm : (Expr.snd (O := atomicE2EOps ℓ P C K decT encT) .v0).eval ρ_sm = smQenc sq := rfl
        have hsm := smStep.stepC_eval b0 qStart qInst qep
          hInv.base.insts_length_le hInv.base.metaAligned
          (hInv.base.mirror.corrPrins_le.trans hInv.base.ki_le)
          (hInv.base.mirror.revSpks_le.trans hInv.base.ki_le)
          (hInv.base.mirror.prins_le.trans hInv.base.ki_le)
          hHalted.sessions hInv.base.epoch_bounded
          hInv.base.tracks_length_le hHalted.tracks_inv
          .v1 (.fst .v0) (.snd .v0) ρ_sm i sq hσSm hiSm hsqSm
        refine (congrArg (fun m => m >>= fun v =>
          pure ((.inr v.1 : (e2eTargetGameCodec S ℓ Pt).R.denote), v.2)) hsm).trans ?_
        rw [atomicKeyIndLiftP_map_loc, bind_map_left]
        simp [KindRedHaltedEval.atomicKeyIndTargetIface_liftP_eq_bhLiftP, bhLiftP,
          Prod.map, KindRedHaltedEval.atomicKindRespEnc, KindRedHalted.drvKindHaltedEnc,
          subs, KindRedHaltedInst.mkKindSubprogramsHaltedClamped, T]
    step_inv := fun {qKiDone qSendDone qStartDone qSessDone σH} hInv t hBud rs hrs => by
      rcases t with (kq | ctl) | ⟨i, sq⟩
      · dsimp only [bhKindHandleWithHaltedClamped, bhTargetQenc,
          CompositionHaltedSimSpecInst.StepNextInvInst] at hrs ⊢
        have hSendNext : CompositionHaltedWitnessInst.nextSendDone qSendDone kq ≤ S.N_send_tot := by
          dsimp only [CompositionHaltedWitnessInst.nextSendDone]
          split_ifs with hsk
          · exact hBud.2 hsk
          · exact hInv.base.send_le
        split_ifs at hrs with hok
        · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrs
          rcases hrs with ⟨kr, -, rfl⟩
          have hUnclamped := (CompositionHaltedWitnessInst.HaltedKindSimInvInst.kiMirror_preserves
            (σ := σH.1) (tracks := σH.2) hInv.base kq kr σH.1.st hBud.1 hSendNext
            (hInv.base.kiReach.mono (Nat.le_succ _))).1
          have hMirClamp2 :
              (HaltedStartSessionSim.bhE2EMirrorClamped nSpk nOpk σH.1 kq kr).bundles.length ≤ nSpk ∧
              (HaltedStartSessionSim.bhE2EMirrorClamped nSpk nOpk σH.1 kq kr).opks.length ≤ nOpk := by
            have hm := HaltedStartSessionSim.drvMirrorBounded_bhE2EMirrorClamped
              (nP' := b0.q_total + 1) (nSend' := min b0.q_total S.N_send_tot + 1)
              (nC' := b0.q_total + 1)
              hInv.drvMirrorBounded kq kr
              (fun _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
              (Nat.le_succ _) (Nat.le_succ _) (le_refl _)
            exact ⟨hm.bundles_le, hm.opks_le⟩
          have hMirQ : M3Interfaces.DrvQueryBounded (qKiDone + 1) qStartDone
              (HaltedStartSessionSim.bhE2EMirrorClamped nSpk nOpk σH.1 kq kr) := by
            refine ⟨hUnclamped.mirror.prins_le, ?_, ?_, hUnclamped.mirror.sends_le,
              hUnclamped.mirror.corrPrins_le, hUnclamped.mirror.insts_le,
              hUnclamped.mirror.instMeta_le, hUnclamped.mirror.revSpks_le⟩
            · dsimp only [HaltedStartSessionSim.bhE2EMirrorClamped]
              split_ifs
              · exact hUnclamped.mirror.bundles_le
              · exact hInv.base.mirror.bundles_le.trans (Nat.le_succ _)
            · dsimp only [HaltedStartSessionSim.bhE2EMirrorClamped]
              split_ifs
              · exact hUnclamped.mirror.opks_le
              · exact hInv.base.mirror.opks_le.trans (Nat.le_succ _)
          exact ⟨{
            ki_le := hUnclamped.ki_le
            send_le := hUnclamped.send_le
            start_le := hUnclamped.start_le
            sess_le := hUnclamped.sess_le
            sends_le_ki := hUnclamped.sends_le_ki
            sends_le_send := hUnclamped.sends_le_send
            insts_le_start := hUnclamped.insts_le_start
            subsetSends := hUnclamped.subsetSends.of_sids_sends_eq rfl rfl
            mirror := hMirQ
            metaAligned := hUnclamped.metaAligned
            kiReach := hUnclamped.kiReach
            tracks_len := hUnclamped.tracks_len
            slot_reach := hUnclamped.slot_reach
            slot_track := hUnclamped.slot_track
          }, hMirClamp2.1, hMirClamp2.2⟩
        · simp only [support_pure, Set.mem_singleton_iff] at hrs
          subst hrs
          exact ⟨CompositionHaltedWitnessInst.HaltedKindSimInvInst.kiSkip_preserves
            hInv.base kq hBud.1 hSendNext, hInv.bundles_clamped, hInv.opks_clamped⟩
      · cases ctl with | startDR sid =>
        dsimp only [bhKindHandleWithHaltedClamped, bhTargetQenc,
          CompositionHaltedSimSpecInst.StepNextInvInst] at hrs ⊢
        rcases hguard : (bhE2EGuard σH.1 sid).map (fun (_, _, uj) => uj) with _ | ⟨u, j⟩
        · rw [hguard] at hrs
          simp only [support_pure, Set.mem_singleton_iff] at hrs
          subst hrs
          exact ⟨{
            ki_le := hInv.base.ki_le
            send_le := hInv.base.send_le
            start_le := hBud
            sess_le := hInv.base.sess_le
            sends_le_ki := hInv.base.sends_le_ki
            sends_le_send := hInv.base.sends_le_send
            insts_le_start := hInv.base.insts_le_start.trans (Nat.le_succ _)
            subsetSends := hInv.base.subsetSends
            mirror := hInv.base.mirror.mono (le_refl _) (le_refl _) (le_refl _)
              (le_refl _) (le_refl _) (Nat.le_succ _)
            metaAligned := hInv.base.metaAligned
            kiReach := hInv.base.kiReach
            tracks_len := hInv.base.tracks_len
            slot_reach := hInv.base.slot_reach
            slot_track := hInv.base.slot_track
          }, hInv.bundles_clamped, hInv.opks_clamped⟩
        · rw [hguard] at hrs
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrs
          rcases hrs with ⟨ts, -, sk, -, bv, -, rfl⟩
          have hFinBase := (CompositionHaltedWitnessInst.HaltedKindSimInvInst.finishStartSpkTracked_preserves
            (PrefixRedHaltedInst.kemBridgeTrackInvLocal_validSimTrackInv C.F K)
            C K (some σH.1.b) (σ₀ := σH.1) (tracks := σH.2) hInv.base hBud sid ts sk bv).1
          obtain ⟨hbEq, hoEq⟩ := finishStartSpkTracked_bundles_opks_eq T.init C K (some σH.1.b)
            σH sid ts sk bv
          exact ⟨hFinBase, hbEq ▸ hInv.bundles_clamped, hoEq ▸ hInv.opks_clamped⟩
      · dsimp only [bhKindHandleWithHaltedClamped, bhTargetQenc,
          CompositionHaltedSimSpecInst.StepNextInvInst] at hrs ⊢
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrs
        rcases hrs with ⟨⟨sr, σH'⟩, h1, rfl⟩
        have hsm := KindRedHaltedEval.mem_support_of_bhLiftP _ h1
        have hSmBase := (CompositionHaltedWitnessInst.HaltedKindSimInvInst.stepLocalSmSessionTracked_preserves
          (PrefixRedHaltedInst.kemBridgeTrackInvLocal_validSimTrackInv C.F K)
          C K qep decT encT hInv.base i hBud sq hsm).1
        obtain ⟨hbEq, hoEq⟩ := stepLocalSmSessionTracked_bundles_opks_eq T C K qep decT encT
          σH i sq hsm
        exact ⟨hSmBase, hbEq ▸ hInv.bundles_clamped, hoEq ▸ hInv.opks_clamped⟩
    finish_eq := fun {_ _ _ _ σ_out} hInv b_out => by
      dsimp only [KindRedHalted.kindRedHalted, bhKindRedWithHaltedClamped, Comp.eval,
        subs, KindRedHaltedInst.mkKindSubprogramsHaltedClamped]
      let ρ_f : Env [KindRedHalted.drvKindHaltedTy subs, .bool] :=
        .cons (KindRedHalted.drvKindHaltedEnc subs σ_out) (.cons b_out .nil)
      have hd_f : (Expr.fst (O := atomicE2EOps ℓ P C K decT encT) .v0).eval ρ_f =
          HaltedStartSessionSim.drvEnc (Pt := Pt) σ_out.1 := rfl
      exact congrArg pure (HaltedStartSessionSim.finishKindClampedE_eval b0 qStart (.fst .v0) .v1 ρ_f
        hd_f hInv.base.insts_length_le)
    ro_eq := fun hInv sec =>
      kindHandle_eval_ki_clamped smStep hP b0 qStart qep qs hInv (.roQuery sec)
    ro_inv := fun {_ _ _ _ σH} hInv sec rs hrs => by
      dsimp only [bhKindHandleWithHaltedClamped, bhTargetQenc] at hrs
      split_ifs at hrs with hok
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrs
        rcases hrs with ⟨kr, -, rfl⟩
        have hMirRo : HaltedStartSessionSim.bhE2EMirrorClamped nSpk nOpk σH.1 (.roQuery sec) kr =
            σH.1 :=
          (HaltedStartSessionSim.bhE2EMirrorClamped_eq_of_lt σH.1 (.roQuery sec) kr
            (fun h _ => nomatch h) (fun h _ => nomatch h)).trans (by cases kr <;> rfl)
        dsimp only
        rw [hMirRo]
        exact hInv
      · simp only [support_pure, Set.mem_singleton_iff] at hrs
        subst hrs
        exact hInv }

private def StMono {S : SignalPqxdh.Setup} (st₀ st : SignalPqxdh.KeyIndState S) : Prop :=
  st₀.spkBundles.length ≤ st.spkBundles.length ∧ st₀.opkEntries.length ≤ st.opkEntries.length

private theorem stMono_refl {S : SignalPqxdh.Setup} (st : SignalPqxdh.KeyIndState S) :
    StMono st st := ⟨le_rfl, le_rfl⟩

private theorem stateT_mono_pure {S : SignalPqxdh.Setup} {α : Type} (a : α)
    {st₀ st : SignalPqxdh.KeyIndState S} (h : StMono st₀ st) :
    ∀ out ∈ support ((pure a : StateT (SignalPqxdh.KeyIndState S) ProbComp α).run st),
      StMono st₀ out.2 := by
  intro out hout
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
  subst hout; exact h

private theorem stateT_mono_bind {S : SignalPqxdh.Setup} {α β : Type}
    (m : StateT (SignalPqxdh.KeyIndState S) ProbComp α)
    (f : α → StateT (SignalPqxdh.KeyIndState S) ProbComp β)
    {st₀ st : SignalPqxdh.KeyIndState S}
    (hm : ∀ p ∈ support (m.run st), StMono st₀ p.2)
    (hf : ∀ a st1, StMono st₀ st1 → ∀ out ∈ support ((f a).run st1), StMono st₀ out.2) :
    ∀ out ∈ support ((m >>= f).run st), StMono st₀ out.2 := by
  intro out hout
  simp only [StateT.run_bind, mem_support_bind_iff] at hout
  rcases hout with ⟨p, hp, hout⟩
  exact hf p.1 p.2 (hm p hp) out hout

private theorem stateT_mono_getOf {S : SignalPqxdh.Setup} {α : Type}
    (f : SignalPqxdh.KeyIndState S → StateT (SignalPqxdh.KeyIndState S) ProbComp α)
    {st₀ st : SignalPqxdh.KeyIndState S}
    (hf : ∀ out ∈ support ((f st).run st), StMono st₀ out.2) :
    ∀ out ∈ support ((MonadStateOf.get >>= f).run st), StMono st₀ out.2 := by
  simpa only [st_run_getOf_bind_loc] using hf

private theorem stateT_mono_lift {S : SignalPqxdh.Setup} {α : Type} (x : ProbComp α)
    {st₀ st : SignalPqxdh.KeyIndState S} (h : StMono st₀ st) :
    ∀ out ∈ support ((liftM x : StateT (SignalPqxdh.KeyIndState S) ProbComp α).run st),
      StMono st₀ out.2 := by
  intro out hout
  change out ∈ support (x >>= fun a => pure (a, st)) at hout
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
  rcases hout with ⟨_, -, rfl⟩
  exact h

private theorem stateT_mono_set {S : SignalPqxdh.Setup}
    {st₀ st st' : SignalPqxdh.KeyIndState S} (h : StMono st₀ st') :
    ∀ out ∈ support ((MonadStateOf.set st' : StateT (SignalPqxdh.KeyIndState S) ProbComp PUnit).run st),
      StMono st₀ out.2 := by
  intro out hout
  change out ∈ support (pure (PUnit.unit, st')) at hout
  simp only [support_pure, Set.mem_singleton_iff] at hout
  subst hout; exact h

set_option linter.unusedSimpArgs false in
private theorem recordKeyIndResp_stMono {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (r : SignalPqxdh.KeyIndRespEntry S) {st₀ st : SignalPqxdh.KeyIndState S} (h : StMono st₀ st) :
    ∀ out ∈ support ((SignalPqxdh.recordKeyIndResp S P r).run st), StMono st₀ out.2 := by
  intro out hmem
  unfold SignalPqxdh.recordKeyIndResp at hmem
  simp only [st_run_get_bind_loc, st_run_getOf_bind_loc, LawfulMonad.bind_assoc] at hmem
  rcases hpart : st.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s r) with _ | s
  · rw [hpart] at hmem; dsimp only at hmem
    simp only [st_run_lift_bind_loc, StateT.run_set, support_pure, mem_support_bind_iff,
      Set.mem_singleton_iff] at hmem
    rcases hmem with ⟨_, -, rfl⟩; exact h
  · rw [hpart] at hmem; dsimp only at hmem
    simp only [pure_bind, StateT.run_set, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact h

private theorem runKeyIndInitiate_stMono {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id) (bundle : SignalPqxdh.PreKeyBundleInput)
    {st₀ st : SignalPqxdh.KeyIndState S} (h : StMono st₀ st) :
    ∀ out ∈ support ((SignalPqxdh.runKeyIndInitiate false S P sid u bundle).run st),
      StMono st₀ out.2 := by
  dsimp only [SignalPqxdh.runKeyIndInitiate]
  refine stateT_mono_getOf _ ?_
  by_cases hc1 : (st.sessions.any (fun e => e.sid == sid)) = true
  · simp only [hc1, ↓reduceIte]; exact stateT_mono_pure _ h
  · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
    split
    · next uEntry =>
      by_cases hc2 : (!SignalPqxdh.koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle) = true
      · simp only [hc2, ↓reduceIte]; exact stateT_mono_pure _ h
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h) fun ekASk _ h1 => ?_
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h1) fun kemCoins _ h2 => ?_
        by_cases hc3 : (!(P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
            (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
          P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
            (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
        · simp only [hc3, ↓reduceIte]; exact stateT_mono_pure _ h2
        · simp only [hc3, Bool.false_eq_true, ↓reduceIte]
          split
          · refine stateT_mono_bind _ _ (stateT_mono_lift _ h2) fun ⟨drKeyReal, roCache'⟩ _ h3 => ?_
            split
            · refine stateT_mono_bind _ _ (stateT_mono_pure _ h3) fun _ _ _ => ?_
              refine stateT_mono_bind _ _ (stateT_mono_set ⟨h.1, h.2⟩) fun _ _ h4 => ?_
              split <;> exact stateT_mono_pure _ h4
            · refine stateT_mono_bind _ _ (stateT_mono_lift _ h3) fun _ _ _ => ?_
              refine stateT_mono_bind _ _ (stateT_mono_set ⟨h.1, h.2⟩) fun _ _ h4 => ?_
              split <;> exact stateT_mono_pure _ h4
          · exact stateT_mono_pure _ h2
    · exact stateT_mono_pure _ h

set_option linter.unusedSimpArgs false in
private theorem pqxdh1KeyReal_stMono {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (kq : SignalPqxdh.KeyIndQuery S) (st : SignalPqxdh.KeyIndState S) :
    ∀ out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st), StMono st out.2 := by
  have h0 := stMono_refl st
  cases kq with
  | initPrin u =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : (st.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ _ => ?_
      exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | roQuery secrets =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal; dsimp only
    refine stateT_mono_getOf _ ?_
    refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun ⟨_, _⟩ _ _ => ?_
    exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | revealDhSecrets =>
    exact stateT_mono_pure _ h0
  | corruptIK u =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    split
    · exact stateT_mono_pure _ h0
    · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | genSPK u j =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : (st.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      split
      · refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ h0 => ?_
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ h0 => ?_
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun ⟨_, _⟩ _ h0 => ?_
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ _ => ?_
        refine stateT_mono_bind _ _ (stateT_mono_set ⟨Nat.le_succ _, le_rfl⟩) fun _ _ h5 =>
          stateT_mono_pure _ h5
      · exact stateT_mono_pure _ h0
  | genOPK u j o =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : (st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ _ => ?_
      refine stateT_mono_bind _ _ (stateT_mono_set ⟨le_rfl, Nat.le_succ _⟩) fun _ _ h2 =>
        stateT_mono_pure _ h2
  | initiateOPK u i bundle =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : bundle.opkB?.isNone = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_stMono P (.sendOPK u i) u bundle h0
  | initiateNoOPK u i bundle =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : bundle.opkB?.isSome = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_stMono P (.sendNoOPK u i) u bundle h0
  | acceptOPK k j o hdr =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc1 : (!(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == some (UInt32.ofNat o.val) &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32)) = true
    · simp only [hc1, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
      by_cases hc2 : (st.usedRecvOPK.contains (k.val, j.val, o.val)) = true
      · simp only [hc2, ↓reduceIte]; exact stateT_mono_pure _ h0
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        by_cases hc3 : (!SignalPqxdh.koskSenderOk P st.principals st.advKeys hdr.ikAPk) = true
        · simp only [hc3, ↓reduceIte]; exact stateT_mono_pure _ h0
        · simp only [hc3, Bool.false_eq_true, ↓reduceIte]
          split
          · split
            · split
              · split_ifs
                · exact stateT_mono_pure _ h0
                · split
                  · split
                    · refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun ⟨_, _⟩ _ _ => ?_
                      refine stateT_mono_bind _ _ (stateT_mono_set ⟨le_rfl, by simp⟩) fun _ _ h2 => ?_
                      refine stateT_mono_bind _ _ (recordKeyIndResp_stMono P _ h2) fun _ _ h3 => ?_
                      split <;> exact stateT_mono_pure _ h3
                    · exact stateT_mono_pure _ h0
                  · exact stateT_mono_pure _ h0
              · exact stateT_mono_pure _ h0
            · exact stateT_mono_pure _ h0
          · exact stateT_mono_pure _ h0
  | acceptNoOPK k j l hdr =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc1 : (!(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == none &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32)) = true
    · simp only [hc1, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
      by_cases hc2 : (st.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
      · simp only [hc2, ↓reduceIte]; exact stateT_mono_pure _ h0
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        by_cases hc3 : (!SignalPqxdh.koskSenderOk P st.principals st.advKeys hdr.ikAPk) = true
        · simp only [hc3, ↓reduceIte]; exact stateT_mono_pure _ h0
        · simp only [hc3, Bool.false_eq_true, ↓reduceIte]
          split
          · split
            · split
              · split
                · refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun ⟨_, _⟩ _ _ => ?_
                  refine stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => ?_
                  refine stateT_mono_bind _ _ (recordKeyIndResp_stMono P _ h2) fun _ _ h3 => ?_
                  split <;> exact stateT_mono_pure _ h3
                · exact stateT_mono_pure _ h0
              · exact stateT_mono_pure _ h0
            · exact stateT_mono_pure _ h0
          · exact stateT_mono_pure _ h0
  | testSession sid =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : (!SignalPqxdh.isKeyIndSessionTestable st sid) = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      split
      · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
      · split
        · exact stateT_mono_pure _ h0
        · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | revealSessionKey sid =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    split
    · split_ifs
      · exact stateT_mono_pure _ h0
      · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
    · split
      · exact stateT_mono_pure _ h0
      · split_ifs
        · exact stateT_mono_pure _ h0
        · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | revealSpkSk u j =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    split
    · exact stateT_mono_pure _ h0
    · refine stateT_mono_bind _ _ (stateT_mono_set ⟨by simp, le_rfl⟩) fun _ _ h2 =>
        stateT_mono_pure _ h2
  | registerKey sk =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    split
    · exact stateT_mono_pure _ h0
    · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2

set_option linter.unusedSimpArgs false in
private theorem pqxdh1KeyReal_genSPK_succ {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (st : SignalPqxdh.KeyIndState S)
    {out : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hmem : out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.genSPK u j)).run st))
    (hresp : out.1 matches .bundleResp ..) :
    out.2.spkBundles.length = st.spkBundles.length + 1 := by
  unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
  simp only [st_run_get_bind_loc, st_run_getOf_bind_loc, LawfulMonad.bind_assoc] at hmem
  by_cases hc : (st.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
  · simp only [hc, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; nomatch hresp
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hp : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
    · rw [hp] at hmem; dsimp only at hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; nomatch hresp
    · rw [hp] at hmem; dsimp only at hmem
      simp only [st_run_lift_bind_loc, StateT.run_set, StateT.run_pure, pure_bind,
        LawfulMonad.bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
      rcases hmem with ⟨_, -, _, -, ⟨_, _⟩, -, _, -, rfl⟩
      simp

set_option linter.unusedSimpArgs false in
private theorem pqxdh1KeyReal_genOPK_succ {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (st : SignalPqxdh.KeyIndState S)
    {out : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hmem : out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.genOPK u j o)).run st))
    (hresp : out.1 matches .pkResp ..) :
    out.2.opkEntries.length = st.opkEntries.length + 1 := by
  unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
  simp only [st_run_get_bind_loc, st_run_getOf_bind_loc, LawfulMonad.bind_assoc] at hmem
  by_cases hc : (st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
  · simp only [hc, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; nomatch hresp
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
    simp only [st_run_lift_bind_loc, StateT.run_set, StateT.run_pure, pure_bind,
      LawfulMonad.bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    rcases hmem with ⟨_, -, rfl⟩
    simp

private theorem st_run_lift_loc {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (x : m α) (s : σ) :
    (liftM x : StateT σ m α).run s = (fun a => (a, s)) <$> x := by
  change (x >>= fun a => pure (a, s)) = (fun a => (a, s)) <$> x
  rw [map_eq_bind_pure_comp]; rfl

private theorem simulateQ_kiImpl_bhFwdU {S : SignalPqxdh.Setup} {P : SignalPqxdh.Primitives}
    (n : unifSpec.Domain) (kiSt : SignalPqxdh.KeyIndState S) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SignalPqxdh.KeyIndState S) ProbComp) + SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
      (bhFwdU (G := SignalPqxdh.keyIndSpec S) n)).run kiSt =
      (fun u => (u, kiSt)) <$> ($ᵗ Fin (n + 1) : ProbComp (Fin (n + 1))) := by
  let kiImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (SignalPqxdh.KeyIndState S) ProbComp) + SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
  have h1 : simulateQ kiImpl (bhFwdU (G := SignalPqxdh.keyIndSpec S) n) = kiImpl (.inl n) := by
    change (kiImpl (.inl n) >>= fun u => pure u) = kiImpl (.inl n)
    exact bind_pure _
  rw [h1]
  exact st_run_lift_loc ($ᵗ Fin (n + 1) : ProbComp (Fin (n + 1))) kiSt

private theorem simulateQ_kiImpl_bhLiftP {S : SignalPqxdh.Setup} {P : SignalPqxdh.Primitives}
    {α : Type} (p : ProbComp α) (kiSt : SignalPqxdh.KeyIndState S) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SignalPqxdh.KeyIndState S) ProbComp) + SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
      (bhLiftP (G := SignalPqxdh.keyIndSpec S) p)).run kiSt =
      (fun a => (a, kiSt)) <$> p := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp [bhLiftP, simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    have h1 : bhLiftP (G := SignalPqxdh.keyIndSpec S) (liftM (OracleSpec.query q) >>= mx) =
        (bhFwdU q >>= fun u => bhLiftP (mx u)) := by
      simp [bhLiftP, simulateQ_bind]
    rw [h1]
    simp only [simulateQ_bind, StateT.run_bind]
    rw [simulateQ_kiImpl_bhFwdU q kiSt, bind_map_left, map_bind]
    refine bind_congr fun u => ?_
    exact ih u

private theorem simulateQ_kiImpl_clamped_eq_online {Pt : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b0 : SignalPqxdh.QueryBudget) :
    let T := kemFailSessionTracker (ℓ := ℓ) C.F K
    let stepSm := bhE2EStepLocalSmSessionTracked T C K qep decT encT
    let nSpk := min b0.q_total S.N_spk_tot
    let nOpk := min b0.q_total S.N_opk_tot
    let kiImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SignalPqxdh.KeyIndState S) ProbComp) + SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    let implC := bhShallowImplOfHandle bhTargetQenc bhTargetRdec
      (bhKindHandleWithHaltedClamped nSpk nOpk T.init stepSm P C K)
    let implU := bhShallowImplOfHandle bhTargetQenc bhTargetRdec
      (KindRedHalted.bhKindHandleWithHalted T.init stepSm P C K)
    ∀ {α : Type} (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (qKiDone qKiRem : ℕ)
      (σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes))
      (kiSt : SignalPqxdh.KeyIndState S),
      oa.IsQueryBoundP isOnlineKiQ qKiRem →
      qKiDone + qKiRem ≤ b0.q_total →
      PqxdhSimTypes.KeyIndSetupBounded S kiSt →
      σH.1.bundles.length ≤ qKiDone →
      σH.1.bundles.length ≤ kiSt.spkBundles.length →
      σH.1.opks.length ≤ qKiDone →
      σH.1.opks.length ≤ kiSt.opkEntries.length →
      (simulateQ kiImpl ((simulateQ implC oa).run σH)).run kiSt =
        (simulateQ kiImpl ((simulateQ implU oa).run σH)).run kiSt := by
  intro T stepSm nSpk nOpk kiImpl implC implU α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro _ _ _ _ _ _ _ _ _ _ _
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    intro qKiDone qKiRem σH kiSt hQb hqKi hSetup hBundQ hBundSt hOpkQ hOpkSt
    rw [isQueryBoundP_query_bind_iff] at hQb
    have hStepL : (simulateQ implC (liftM (OracleSpec.query q) >>= mx)).run σH =
        ((implC q).run σH >>= fun p => (simulateQ implC (mx p.1)).run p.2) := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
    have hStepR : (simulateQ implU (liftM (OracleSpec.query q) >>= mx)).run σH =
        ((implU q).run σH >>= fun p => (simulateQ implU (mx p.1)).run p.2) := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
    rw [hStepL, hStepR]
    cases q with
    | inl n =>
      have hC : (implC (.inl n)).run σH = (bhFwdU n >>= fun u => pure (u, σH)) := rfl
      have hU : (implU (.inl n)).run σH = (bhFwdU n >>= fun u => pure (u, σH)) := rfl
      rw [hC, hU]
      simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind]
      have hFwd := simulateQ_kiImpl_bhFwdU (S := S) (P := P) n kiSt
      dsimp only [kiImpl]
      rw [hFwd, bind_map_left, bind_map_left]
      refine bind_congr fun u => ?_
      exact ih u qKiDone qKiRem σH kiSt
        ((hQb.2 u).mono (by simp [isOnlineKiQ, bhClassifyTarget]))
        hqKi hSetup hBundQ hBundSt hOpkQ hOpkSt
    | inr t =>
      have hC : (implC (.inr t)).run σH =
          (bhKindHandleWithHaltedClamped nSpk nOpk T.init stepSm P C K σH (bhTargetQenc t) >>=
            fun rs => pure (bhTargetRdec t rs.1, rs.2)) := rfl
      have hU : (implU (.inr t)).run σH =
          (KindRedHalted.bhKindHandleWithHalted T.init stepSm P C K σH (bhTargetQenc t) >>=
            fun rs => pure (bhTargetRdec t rs.1, rs.2)) := rfl
      rw [hC, hU]
      simp only [bind_assoc, pure_bind]
      rcases t with (kq | ctl) | ⟨i, sq⟩
      · have hLHS : bhKindHandleWithHaltedClamped nSpk nOpk T.init stepSm P C K σH
            (bhTargetQenc (.inl (.inl kq))) =
            (if bhDrvKiQueryOk P σH.1.toModelDriverBase kq && !kiNoOpkPromoted_loc σH.1 kq then do
              let kr ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
                OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
              return (.inl (.inl kr),
                (HaltedStartSessionSim.bhE2EMirrorClamped nSpk nOpk σH.1 kq kr, σH.2))
            else pure (.inl (.inl .noneResp), σH)) := rfl
        have hRHS : KindRedHalted.bhKindHandleWithHalted T.init stepSm P C K σH
            (bhTargetQenc (.inl (.inl kq))) =
            (if bhDrvKiQueryOk P σH.1.toModelDriverBase kq && !kiNoOpkPromoted_loc σH.1 kq then do
              let kr ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
                OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
              return (.inl (.inl kr), (bhE2EMirror σH.1 kq kr, σH.2))
            else pure (.inl (.inl .noneResp), σH)) := rfl
        rw [hLHS, hRHS]
        by_cases hro : ∃ sec, kq = .roQuery sec
        · rcases hro with ⟨sec, rfl⟩
          have hNextQb : ∀ v, (mx v).IsQueryBoundP isOnlineKiQ qKiRem :=
            fun v => (hQb.2 v).mono (by simp [isOnlineKiQ, bhClassifyTarget, bhClassifyTargetOnly])
          by_cases hok : (bhDrvKiQueryOk P σH.1.toModelDriverBase (.roQuery sec) &&
              !kiNoOpkPromoted_loc σH.1 (.roQuery sec)) = true
          · simp only [hok, ↓reduceIte, bind_assoc, pure_bind, simulateQ_bind, simulateQ_query,
              OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind]
            have hKiStep : (kiImpl (.inr (.roQuery sec))).run kiSt =
                (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.roQuery sec)).run kiSt := rfl
            rw [hKiStep]
            refine bind_congr_of_forall_mem_support _ fun ⟨kr, kiSt'⟩ hmem => ?_
            have hSetup' : PqxdhSimTypes.KeyIndSetupBounded S kiSt' :=
              (PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_preserves_setupBounded
                (.roQuery sec) hSetup hmem).1
            obtain ⟨hSpkLe, hOpkLe⟩ := pqxdh1KeyReal_stMono P (.roQuery sec) kiSt (kr, kiSt') hmem
            have hMirC : HaltedStartSessionSim.bhE2EMirrorClamped nSpk nOpk σH.1 (.roQuery sec) kr =
                σH.1 :=
              (HaltedStartSessionSim.bhE2EMirrorClamped_eq_of_lt σH.1 (.roQuery sec) kr
                (fun h _ => nomatch h) (fun h _ => nomatch h)).trans (by cases kr <;> rfl)
            have hMirU : bhE2EMirror σH.1 (.roQuery sec) kr = σH.1 := by cases kr <;> rfl
            rw [hMirC, hMirU]
            exact ih _ qKiDone qKiRem σH kiSt' (hNextQb _) hqKi hSetup'
              hBundQ (hBundSt.trans hSpkLe) hOpkQ (hOpkSt.trans hOpkLe)
          · simp only [hok]
            exact ih _ qKiDone qKiRem σH kiSt (hNextQb _) hqKi hSetup
              hBundQ hBundSt hOpkQ hOpkSt
        · have hne : ∀ sec, kq ≠ .roQuery sec := fun sec hk => hro ⟨sec, hk⟩
          have hp : isOnlineKiQ (S := S) (ℓ := ℓ) (.inr (.inl (.inl kq))) :=
            isOnlineKiQ_of_ne_roQuery hne
          have hpos : 0 < qKiRem := hQb.1.resolve_left (fun h => h hp)
          have hqKi' : (qKiDone + 1) + (qKiRem - 1) ≤ b0.q_total := by omega
          have hNextQb : ∀ v, (mx v).IsQueryBoundP isOnlineKiQ (qKiRem - 1) :=
            fun v => (hQb.2 v).mono (by split_ifs; exact le_rfl)
          by_cases hok : (bhDrvKiQueryOk P σH.1.toModelDriverBase kq &&
              !kiNoOpkPromoted_loc σH.1 kq) = true
          · simp only [hok, ↓reduceIte, bind_assoc, pure_bind, simulateQ_bind, simulateQ_query,
              OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind]
            have hKiStep : (kiImpl (.inr kq)).run kiSt =
                (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run kiSt := rfl
            rw [hKiStep]
            refine bind_congr_of_forall_mem_support _ fun ⟨kr, kiSt'⟩ hmem => ?_
            have hSetup' : PqxdhSimTypes.KeyIndSetupBounded S kiSt' :=
              (PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_preserves_setupBounded kq hSetup hmem).1
            obtain ⟨hSpkLe, hOpkLe⟩ := pqxdh1KeyReal_stMono P kq kiSt (kr, kiSt') hmem
            have hMirEq : HaltedStartSessionSim.bhE2EMirrorClamped nSpk nOpk σH.1 kq kr =
                bhE2EMirror σH.1 kq kr :=
              HaltedStartSessionSim.bhE2EMirrorClamped_eq_of_lt σH.1 kq kr
                (fun hg hb => by
                  cases kq with
                  | genSPK u j =>
                    cases kr with
                    | bundleResp _ =>
                      have h1 := pqxdh1KeyReal_genSPK_succ P u j kiSt hmem rfl
                      have h2 := hSetup'.spkBundles_le
                      dsimp only [nSpk] at *; omega
                    | _ => cases hb
                  | _ => cases hg)
                (fun hg hpk => by
                  cases kq with
                  | genOPK u j o =>
                    cases kr with
                    | pkResp _ =>
                      have h1 := pqxdh1KeyReal_genOPK_succ P u j o kiSt hmem rfl
                      have h2 := hSetup'.opkEntries_le
                      dsimp only [nOpk] at *; omega
                    | _ => cases hpk
                  | _ => cases hg)
            rw [hMirEq]
            have hBundNext : (bhE2EMirror σH.1 kq kr).bundles.length ≤ qKiDone + 1 ∧
                (bhE2EMirror σH.1 kq kr).bundles.length ≤ kiSt'.spkBundles.length := by
              cases kq with
              | genSPK u j =>
                cases kr with
                | bundleResp bnd =>
                  have h1 := pqxdh1KeyReal_genSPK_succ P u j kiSt hmem rfl
                  simp only [bhE2EMirror, CryptoVerification.E2E.bhBaseMirror, List.length_cons]
                  dsimp only at h1; omega
                | _ =>
                  simp only [bhE2EMirror, CryptoVerification.E2E.bhBaseMirror]
                  exact ⟨hBundQ.trans (Nat.le_succ _), hBundSt.trans hSpkLe⟩
              | _ =>
                cases kr <;>
                  · simp only [bhE2EMirror, CryptoVerification.E2E.bhBaseMirror]
                    exact ⟨hBundQ.trans (Nat.le_succ _), hBundSt.trans hSpkLe⟩
            have hOpkNext : (bhE2EMirror σH.1 kq kr).opks.length ≤ qKiDone + 1 ∧
                (bhE2EMirror σH.1 kq kr).opks.length ≤ kiSt'.opkEntries.length := by
              cases kq with
              | genOPK u j o =>
                cases kr with
                | pkResp pk =>
                  have h1 := pqxdh1KeyReal_genOPK_succ P u j o kiSt hmem rfl
                  simp only [bhE2EMirror, CryptoVerification.E2E.bhBaseMirror, List.length_cons]
                  dsimp only at h1; omega
                | _ =>
                  simp only [bhE2EMirror, CryptoVerification.E2E.bhBaseMirror]
                  exact ⟨hOpkQ.trans (Nat.le_succ _), hOpkSt.trans hOpkLe⟩
              | _ =>
                cases kr <;>
                  · simp only [bhE2EMirror, CryptoVerification.E2E.bhBaseMirror]
                    exact ⟨hOpkQ.trans (Nat.le_succ _), hOpkSt.trans hOpkLe⟩
            exact ih _ (qKiDone + 1) (qKiRem - 1) (bhE2EMirror σH.1 kq kr, σH.2) kiSt'
              (hNextQb _) hqKi' hSetup' hBundNext.1 hBundNext.2 hOpkNext.1 hOpkNext.2
          · simp only [hok]
            exact ih _ (qKiDone + 1) (qKiRem - 1) σH kiSt (hNextQb _) hqKi' hSetup
              (hBundQ.trans (Nat.le_succ _)) hBundSt (hOpkQ.trans (Nat.le_succ _)) hOpkSt
      · cases ctl with | startDR sid =>
        have hNextQb : ∀ v, (mx v).IsQueryBoundP isOnlineKiQ qKiRem :=
          fun v => (hQb.2 v).mono (by simp [isOnlineKiQ, bhClassifyTarget, bhClassifyTargetOnly])
        dsimp only [bhKindHandleWithHaltedClamped, KindRedHalted.bhKindHandleWithHalted, bhTargetQenc]
        rcases hguard : (bhE2EGuard σH.1 sid).map (fun (_, _, uj) => uj) with _ | ⟨u, j⟩
        · rw [hguard]
          simp only [pure_bind]
          exact ih _ qKiDone qKiRem σH kiSt (hNextQb _) hqKi hSetup
            hBundQ hBundSt hOpkQ hOpkSt
        · rw [hguard]
          simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_query,
            OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind]
          have hKi1 : (kiImpl (.inr (.testSession sid))).run kiSt =
              (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.testSession sid)).run kiSt := rfl
          rw [hKi1]
          refine bind_congr_of_forall_mem_support _ fun ⟨ts, kiSt1⟩ hmem1 => ?_
          have hSetup1 := (PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_preserves_setupBounded
            _ hSetup hmem1).1
          obtain ⟨hSpk1, hOpk1⟩ := pqxdh1KeyReal_stMono P _ kiSt (ts, kiSt1) hmem1
          have hKi2 : (kiImpl (.inr (.revealSpkSk u j))).run kiSt1 =
              (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.revealSpkSk u j)).run kiSt1 := rfl
          rw [hKi2]
          refine bind_congr_of_forall_mem_support _ fun ⟨sk, kiSt2⟩ hmem2 => ?_
          have hSetup2 := (PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_preserves_setupBounded
            _ hSetup1 hmem2).1
          obtain ⟨hSpk2, hOpk2⟩ := pqxdh1KeyReal_stMono P _ kiSt1 (sk, kiSt2) hmem2
          have hSmp := simulateQ_kiImpl_bhLiftP (S := S) (P := P)
            ($ᵗ BitVec 256 : ProbComp (BitVec 256)) kiSt2
          dsimp only [kiImpl]
          rw [hSmp, bind_map_left, bind_map_left]
          refine bind_congr fun bv => ?_
          obtain ⟨hbEq, hoEq⟩ := finishStartSpkTracked_bundles_opks_eq T.init C K (some σH.1.b)
            σH sid ts sk bv
          exact ih _ qKiDone qKiRem _ kiSt2 (hNextQb _) hqKi hSetup2
            (hbEq ▸ hBundQ) (hbEq ▸ (hBundSt.trans (hSpk1.trans hSpk2)))
            (hoEq ▸ hOpkQ) (hoEq ▸ (hOpkSt.trans (hOpk1.trans hOpk2)))
      · have hNextQb : ∀ v, (mx v).IsQueryBoundP isOnlineKiQ qKiRem :=
          fun v => (hQb.2 v).mono (by simp [isOnlineKiQ, bhClassifyTarget, bhClassifyTargetOnly])
        dsimp only [bhKindHandleWithHaltedClamped, KindRedHalted.bhKindHandleWithHalted, bhTargetQenc]
        simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind]
        have hSmRun := simulateQ_kiImpl_bhLiftP (S := S) (P := P) (stepSm σH i sq) kiSt
        dsimp only [kiImpl]
        rw [hSmRun, bind_map_left, bind_map_left]
        refine bind_congr_of_forall_mem_support _ fun res hres => ?_
        obtain ⟨hbEq, hoEq⟩ := stepLocalSmSessionTracked_bundles_opks_eq T C K qep decT encT
          σH i sq hres
        exact ih _ qKiDone qKiRem res.2 kiSt (hNextQb _) hqKi hSetup
          (hbEq ▸ hBundQ) (hbEq ▸ hBundSt) (hoEq ▸ hOpkQ) (hoEq ▸ hOpkSt)

/-- Equivalence in `pqxdhKeyInd1KeyRealExp` between `kindRedHalted` at `onlineClampedBudget b` and
`bhKindRedWithTracked` under `pqxdhKeyIndImpl1KeyReal`. -/
theorem clamped_bOn_kindRealExp_eq {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (smStep : KindRedHaltedInst.HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT
      (PrefixRedHaltedInst.KemBridgeTrackInvLocal C.F K))
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs) :
    SignalPqxdh.pqxdhKeyInd1KeyRealExp S P
        ⟨(KindRedHalted.kindRedHalted
            (KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep (onlineClampedBudget b))
            (onlineClampedBudget b) qStart (Finset.sup (Finset.range qStart) qs) qep).eval
              (fun _ => B_A) ()⟩ =
      SignalPqxdh.pqxdhKeyInd1KeyRealExp S P
        ⟨(bhKindRedWithTracked (kemFailSessionTracker (ℓ := ℓ) C.F K).init
            (fun d : BHModelInst S ℓ =>
              oracleImplRSessionTracked (kemFailSessionTracker (ℓ := ℓ) C.F K)
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                  ℓ d.spkCoins)
                (2 + 1) qep (configRefuseEarlyBobCorr decT encT))
            P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K).eval (fun _ => B_A) ()⟩ := by
  set b0 := onlineClampedBudget b
  have hOn := isQueryBoundP_isOnlineKiQ_bOn hB
  have hSim1 := oneStage_eval_eq_online
    (clampedKindOneStageSimSpecOnline smStep hP b qStart qep qs) B_A hB
  dsimp only [clampedKindOneStageSimSpecOnline] at hSim1
  rw [hSim1, ← CompositionHaltedWitness.bhKindRedWithHalted_eq_bhKindRedWithTracked
    (kemFailSessionTracker (ℓ := ℓ) C.F K) P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
    C K qep decT encT]
  unfold SignalPqxdh.pqxdhKeyInd1KeyRealExp SignalPqxdh.pqxdhKeyInd1KeyExpForHandshake
  dsimp only
  refine bind_congr fun secb => ?_
  have hRunEq :
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (SignalPqxdh.KeyIndState S) ProbComp) + SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
        ((bhKindRedWithHaltedClamped (min b0.q_total S.N_spk_tot) (min b0.q_total S.N_opk_tot)
            (kemFailSessionTracker (ℓ := ℓ) C.F K).init
            (bhE2EStepLocalSmSessionTracked
              (kemFailSessionTracker (ℓ := ℓ) C.F K) C K qep decT encT)
            P C K).eval (fun _ => B_A) ())).run (SignalPqxdh.KeyIndState.empty S secb) =
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (SignalPqxdh.KeyIndState S) ProbComp) + SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
        ((KindRedHalted.bhKindRedWithHalted
            (kemFailSessionTracker (ℓ := ℓ) C.F K).init
            (bhE2EStepLocalSmSessionTracked
              (kemFailSessionTracker (ℓ := ℓ) C.F K) C K qep decT encT)
            P C K).eval (fun _ => B_A) ())).run (SignalPqxdh.KeyIndState.empty S secb) := by
    unfold BhShallowRed.eval
    dsimp only [bhKindRedWithHaltedClamped, KindRedHalted.bhKindRedWithHalted]
    simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind]
    have hInit := simulateQ_kiImpl_bhLiftP (S := S) (P := P)
      (do let b1 ← ($ᵗ Bool : ProbComp Bool)
          return (({ b := b1 } : BHE2EDrvState S ℓ), ([] : List (KemFailSessionTrack C.F Bytes))))
      (SignalPqxdh.KeyIndState.empty S secb)
    rw [hInit, bind_map_left, bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun drv0 hx => ?_
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨b1, -, rfl⟩
    have hSimRun := simulateQ_kiImpl_clamped_eq_online (Pt := Pt) P C K qep decT encT b0
      B_A 0 b0.q_total (({ b := b1 } : BHE2EDrvState S ℓ), ([] : List (KemFailSessionTrack C.F Bytes)))
      (SignalPqxdh.KeyIndState.empty S secb)
      hOn (by omega) (PqxdhSimTypes.KeyIndSetupBounded.empty S secb)
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    dsimp only at hSimRun ⊢
    rw [hSimRun]
  rw [hRunEq]

end Computational.Proofs.E2E.Dsl.CompositionHaltedRedsKindSim
