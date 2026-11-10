/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.TagSync1KeyReal
public import Computational.Proofs.LibsignalCli.PrefixCouplingWithCore
import Computational.Proofs.LibsignalCli.PrefixCouplingWith
import Computational.Proofs.SignalWireRoundTrip
import VCVio.EvalDist.Monad.Basic

/-!
# Standard-Model 1-Key Real-HKDF Prefix-Hybrid Coupling

**Checked by Lean.** Instantiates `PrefixCouplingWith` at `SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P`,
discharging the lazy `DRKey` replacement premise via `DrvTagSyncInv1KeyReal` to obtain the
unconditional `qStart`-step prefix-hybrid telescope.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped ENNReal BigOperators
open OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Prefix CryptoVerification.E2E.Signed
  ReductionDsl

namespace CryptoVerification.E2E

open CryptoVerification.E2E.Prefix1Key

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}

@[simp]
private theorem stateT_run_lift_lazy1key {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp]
private theorem stateT_run_liftM_lazy1key {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp]
private theorem bhKioDrvM_run_liftM_lazy1key {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    {α : Type} (mx : ProbComp α) (σ : BHE2EDrvState S ℓ) :
    (liftM mx : BHKioDrvM S ℓ M α).run σ = ((liftM mx : M α) >>= fun x => pure (x, σ)) := rfl

/-! ## `bhE2EDrvImplPrefixWith` and `bhKioImplPrefix` bridge -/

private theorem bhE2EMirror_with_st_lazy1key
    (σ : BHE2EDrvState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    bhE2EMirror { σ with st := st } kq kr = { bhE2EMirror σ kq kr with st := st } := by
  cases kq <;> cases kr <;> rfl

private theorem bhFinishStartSpkGen_with_st_lazy1key
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (σ : BHE2EDrvState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse) (kb : SampledSessionKey × Bool) :
    bhFinishStartSpkGen C K { σ with st := st } sid kr1 kr2 kb =
      let (idx?, σ') := bhFinishStartSpkGen C K σ sid kr1 kr2 kb
      (idx?, { σ' with st := st }) := by
  unfold bhFinishStartSpkGen
  have hG : bhE2EGuard { σ with st := st } sid = bhE2EGuard σ sid := rfl
  rw [hG]
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    cases kr1 <;> cases kr2 <;> try rfl
    dsimp only
    split_ifs <;> rfl

theorem bhE2EDrvImplGenWith_step_eq_bhKioImplGen
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkKB : ModelDriverKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σ : BHE2EDrvState S ℓ) (st : SignalPqxdh.KeyIndState S) :
    (bhE2EDrvImplGenWith ki P C K qep decT encT mkKB q).run { σ with st := st } =
      (fun ((r, σ'), st') => (r, { σ' with st := st' })) <$>
        (((bhKioImplGen P C K qep decT encT ki mkKB q).run σ).run st) := by
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · dsimp only [bhE2EDrvImplGenWith, bhKioImplGen]
    simp only [bhKioDrvM_run_liftM_lazy1key, stateT_run_liftM_lazy1key, StateT.run_bind,
      StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  · have hBase : ({ σ with st := st } : BHE2EDrvState S ℓ).toModelDriverBase = σ.toModelDriverBase := rfl
    have hMeta : ({ σ with st := st } : BHE2EDrvState S ℓ).instMeta = σ.instMeta := rfl
    by_cases hOk : bhDrvKiQueryOk P σ.toModelDriverBase kq = true
    · cases kq
      case corruptIK u =>
        dsimp only [bhE2EDrvImplGenWith, bhKioImplGen, bhKioKeyInd]
        by_cases hRef : bhNoOpkRespPromoted σ.instMeta u = true
        · simp only [hBase, hMeta, hOk, hRef, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, StateT.run_get, StateT.run_pure,
            map_eq_bind_pure_comp, Function.comp_def, pure_bind]
        · have hRefF : bhNoOpkRespPromoted σ.instMeta u = false := Bool.eq_false_iff.mpr hRef
          simp only [hBase, hMeta, hOk, hRefF, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, StateT.run_get, stateT_run_lift_lazy1key, stateT_run_liftM_lazy1key,
            StateT.run_set, StateT.run_modify, StateT.run_pure,
            map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
            bhE2EMirror_with_st_lazy1key]
      all_goals
        dsimp only [bhE2EDrvImplGenWith, bhKioImplGen, bhKioKeyInd]
        simp only [hBase, hOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, stateT_run_lift_lazy1key, stateT_run_liftM_lazy1key,
          StateT.run_set, StateT.run_modify, StateT.run_pure,
          map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
          bhE2EMirror_with_st_lazy1key]
    · dsimp only [bhE2EDrvImplGenWith, bhKioImplGen, bhKioKeyInd]
      have hOkF : bhDrvKiQueryOk P σ.toModelDriverBase kq = false := Bool.eq_false_iff.mpr hOk
      simp only [hBase, hOkF, Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get,
        StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, pure_bind]
  · dsimp only [bhE2EDrvImplGenWith, bhKioImplGen, bhKioStartGen, bhE2ELocalStartGenWith]
    have hG : bhE2EGuard { σ with st := st } sid = bhE2EGuard σ sid := rfl
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM_lazy1key, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, hG]
    cases bhE2EGuard σ sid with
    | none =>
      simp only [StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, pure_bind]
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      simp only [stateT_run_lift_lazy1key, bhKioDrvM_run_liftM_lazy1key, stateT_run_liftM_lazy1key,
        StateT.run_bind, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp,
        Function.comp_def, bind_assoc, pure_bind, bhFinishStartSpkGen_with_st_lazy1key]
  · dsimp only [bhE2EDrvImplGenWith, bhKioImplGen, bhKioSm]
    simp only [StateT.run_bind, StateT.run_get, bhKioDrvM_run_liftM_lazy1key,
      stateT_run_liftM_lazy1key, StateT.run_set, StateT.run_pure, bhE2EStepLocalSm_with_st,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

theorem simulateQ_bhE2EDrvImplPrefixWith_eq_bhKioImplPrefix {α : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkP : BHDrvPrefixKeyBitGen)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) (st : SignalPqxdh.KeyIndState S) :
    (simulateQ (bhE2EDrvImplPrefixWith ki P C K qep decT encT mkP) oa).run { σ with st := st } =
      (fun ((r, σ'), st') => (r, { σ' with st := st' })) <$>
        (((simulateQ (bhKioImplPrefix P C K qep decT encT ki mkP) oa).run σ).run st) := by
  induction oa using OracleComp.inductionOn generalizing σ st with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, StateT.run_bind,
      bhE2EDrvImplPrefixWith_run_eq_gen, bhKioImplPrefix_run_eq_gen]
    have hlen : ({ σ with st := st } : BHE2EDrvState S ℓ).insts.length = σ.insts.length := rfl
    rw [hlen, bhE2EDrvImplGenWith_step_eq_bhKioImplGen]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    congr 1; funext p; rcases p with ⟨⟨r, σ'⟩, st'⟩
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using ih r σ' st'

/-! ## `DrvTagSyncInv1KeyReal` synchronization -/

private theorem bhE2EGuard_eq_some_props_1KeyReal
    {σ : BHE2EDrvState S ℓ} {sid : SignalPqxdh.SessionId S}
    {hdr : SignalPqxdh.HandshakeHdr} {bnd : SignalPqxdh.PreKeyBundleInput}
    {u : Fin S.N_id} {j' : Fin S.N_recv}
    (hG : bhE2EGuard σ sid = some (hdr, bnd, (u, j'))) :
    (sid, bnd, hdr) ∈ (bhToDrvState σ).sends ∧
    (∃ pk, ((u, j'), pk) ∈ (bhToDrvState σ).bundles) ∧
    (∀ d ∈ (bhToDrvState σ).insts, d.hdr.ekAPk ≠ hdr.ekAPk) := by
  unfold bhE2EGuard at hG
  by_cases h1 : (σ.insts.any (fun d => d.sid == sid)) = true
  · simp [h1] at hG
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hG
    cases hs : σ.sends.find? (fun (s, _, _) => s == sid) with
    | none => simp [hs] at hG
    | some se =>
      rcases se with ⟨sid0, bnd0, hdr0⟩
      rw [hs] at hG; dsimp only at hG
      by_cases h2 : (σ.insts.any (fun d => d.hdr.ekAPk == hdr0.ekAPk)) = true
      · simp [h2] at hG
      · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hG
        cases hb : σ.bundles.find? (fun ((_, j), (spkB, pqspkB)) =>
            spkB == bnd0.spkB && pqspkB == bnd0.pqspkB &&
            hdr0.spkId == UInt32.ofNat j.val &&
            hdr0.pqspkId == UInt32.ofNat j.val) with
        | none => simp [hb] at hG
        | some be =>
          rcases be with ⟨⟨u0, j0⟩, ⟨spkB0, pqspkB0⟩⟩
          rw [hb] at hG; dsimp only at hG
          split_ifs at hG with h3
          simp only [Option.some.injEq, Prod.mk.injEq] at hG
          rcases hG with ⟨rfl, rfl, rfl, rfl⟩
          have hsid0 : sid0 = sid := by
            have h0 := List.find?_some hs
            dsimp only at h0
            exact beq_iff_eq.mp h0
          subst hsid0
          refine ⟨List.mem_of_find?_eq_some hs, ?_, ?_⟩
          · refine ⟨spkB0, ?_⟩
            dsimp only [bhToDrvState]
            exact List.mem_map.mpr ⟨((u0, j0), (spkB0, pqspkB0)), List.mem_of_find?_eq_some hb, rfl⟩
          · intro d hd hEq
            dsimp only [bhToDrvState] at hd
            rcases List.mem_map.mp hd with ⟨d0, hd0, rfl⟩
            exact h2 (List.any_eq_true.mpr ⟨d0, hd0, beq_iff_eq.mpr hEq⟩)

private theorem DrvTagSyncInv1KeyReal.congr_state
    {P : SignalPqxdh.Primitives} {ds1 ds2 : DrvState S ℓ} {lst : KeyInd1KeyLazyState S}
    (h : DrvTagSyncInv1KeyReal P ds1 lst)
    (hsends : ds2.sends = ds1.sends)
    (hbundles : ds2.bundles = ds1.bundles)
    (hinsts : ∀ d1 ∈ ds1.insts, ∃ d2 ∈ ds2.insts, d2.hdr.ekAPk = d1.hdr.ekAPk) :
    DrvTagSyncInv1KeyReal P ds2 lst where
  core := h.core
  sends_sess x hx := h.sends_sess x (hsends ▸ hx)
  bundles_spk b hb := h.bundles_spk b (hbundles ▸ hb)
  cache_insts k hk := by
    rcases h.cache_insts k hk with ⟨d1, hd1, e, he, hk_eq, hek_eq⟩
    rcases hinsts d1 hd1 with ⟨d2, hd2, hd2_eq⟩
    exact ⟨d2, hd2, e, he, hk_eq, hd2_eq.trans hek_eq⟩

private theorem bhE2EStepLocalSm_preserves_tagSync1KeyReal
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (σ : BHE2EDrvState S ℓ) (lst : KeyInd1KeyLazyState S)
    (hSync : DrvTagSyncInv1KeyReal P (bhToDrvState σ) lst)
    {p : BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hp : p ∈ support (bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    DrvTagSyncInv1KeyReal P (bhToDrvState p.2) lst := by
  have hProps : p.2.sends = σ.sends ∧ p.2.bundles = σ.bundles ∧
      ∀ d1 ∈ (bhToDrvState σ).insts, ∃ d2 ∈ (bhToDrvState p.2).insts, d2.hdr.ekAPk = d1.hdr.ekAPk := by
    have hRefl : ∀ d1 ∈ (bhToDrvState σ).insts,
        ∃ d2 ∈ (bhToDrvState σ).insts, d2.hdr.ekAPk = d1.hdr.ekAPk :=
      fun d1 hd1 => ⟨d1, hd1, rfl⟩
    rw [bhE2EStepLocalSm_eq_filter] at hp
    by_cases hClean : (!bhE2EDrvInstClean σ i) = true
    · simp only [hClean, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨rfl, rfl, hRefl⟩
    · simp only [hClean, Bool.false_eq_true, ↓reduceIte] at hp
      cases hi : σ.insts[i]? with
      | none =>
        simp only [hi, support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact ⟨rfl, rfl, hRefl⟩
      | some d =>
        cases him : σ.instMeta[i]? with
        | none =>
          simp only [hi, him, support_pure, Set.mem_singleton_iff] at hp
          subst hp; exact ⟨rfl, rfl, hRefl⟩
        | some im =>
          simp only [hi, him] at hp
          by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
          · simp only [hCorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
            subst hp; exact ⟨rfl, rfl, hRefl⟩
          · simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hp
            cases hd : d.gs with
            | none =>
              simp only [hd, support_pure, Set.mem_singleton_iff] at hp
              subst hp; exact ⟨rfl, rfl, hRefl⟩
            | some gs =>
              simp only [hd] at hp
              cases hf : bhFilterSmQuery d im sq with
              | none =>
                simp only [hf, support_pure, Set.mem_singleton_iff] at hp
                subst hp; exact ⟨rfl, rfl, hRefl⟩
              | some q' =>
                simp only [hf, support_bind, support_pure, Set.mem_iUnion,
                  Set.mem_singleton_iff] at hp
                rcases hp with ⟨⟨r, gs'⟩, _, rfl⟩
                refine ⟨rfl, rfl, fun d1 hd1 => ?_⟩
                dsimp only [bhToDrvState] at hd1 ⊢
                rcases List.mem_map.mp hd1 with ⟨d0, hd0, rfl⟩
                rcases List.mem_iff_getElem.mp hd0 with ⟨idx, hidx, rfl⟩
                by_cases hEqIdx : i = idx
                · subst hEqIdx
                  have hd_eq : σ.insts[i] = d := by
                    rw [List.getElem?_eq_getElem hidx] at hi
                    exact Option.some.inj hi
                  have hidx' : i < (σ.insts.set i { d with gs := some gs' }).length := by
                    simpa using hidx
                  refine ⟨bhToDrvInst { d with gs := some gs' },
                    List.mem_map.mpr ⟨{ d with gs := some gs' },
                      List.mem_iff_getElem.mpr ⟨i, hidx', by simp⟩, rfl⟩, ?_⟩
                  simp [bhToDrvInst, hd_eq]
                · have hidx' : idx < (σ.insts.set i { d with gs := some gs' }).length := by
                    simpa using hidx
                  refine ⟨bhToDrvInst σ.insts[idx],
                    List.mem_map.mpr ⟨σ.insts[idx],
                      List.mem_iff_getElem.mpr ⟨idx, hidx', by simp [List.getElem_set_ne hEqIdx]⟩,
                      rfl⟩, rfl⟩
  exact hSync.congr_state hProps.1 (by dsimp [bhToDrvState]; rw [hProps.2.1]) hProps.2.2

private theorem bhKioKeyInd_tagImpl1KeyReal_sync
    (P : SignalPqxdh.Primitives) (kq : SignalPqxdh.KeyIndQuery S)
    (σ : BHE2EDrvState S ℓ) (lst : KeyInd1KeyLazyState S)
    (hSync : DrvTagSyncInv1KeyReal P (bhToDrvState σ) lst)
    (rc2 : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)) :
    ((bhKioKeyInd P (pqxdhKeyIndTagImpl1KeyReal false false S P) kq).run σ).run
        { lst with randCache := rc2 } =
      (fun (r_σ, l1) => (r_σ, { l1 with randCache := rc2 })) <$>
        ((bhKioKeyInd P (pqxdhKeyIndTagImpl1KeyReal false false S P) kq).run σ).run lst ∧
    ∀ r σ' l1, ((r, σ'), l1) ∈ support
        (((bhKioKeyInd P (pqxdhKeyIndTagImpl1KeyReal false false S P) kq).run σ).run lst) →
      DrvTagSyncInv1KeyReal P (bhToDrvState σ') l1 ∧ l1.randCache = lst.randCache := by
  by_cases hOk : bhDrvKiQueryOk P σ.toModelDriverBase kq = true
  · have hNe := bhDrvKiQueryOk_ne_testSession P σ.toModelDriverBase kq hOk
    have ⟨hRunEq, hInv⟩ :=
      pqxdhKeyIndTagImpl1KeyReal_non_test_sync false P kq hNe (bhToDrvState σ) lst hSync rc2
    cases kq
    case corruptIK u =>
      dsimp only [bhKioKeyInd]
      by_cases hRef : bhNoOpkRespPromoted σ.instMeta u = true
      · simp only [hOk, hRef, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, map_pure,
          support_pure, Set.mem_singleton_iff]
        refine ⟨trivial, fun r σ' l1 hEq => ?_⟩
        rcases Prod.mk.inj hEq with ⟨hEq1, rfl⟩
        rcases Prod.mk.inj hEq1 with ⟨rfl, rfl⟩
        exact ⟨hSync, rfl⟩
      · have hRefF : bhNoOpkRespPromoted σ.instMeta u = false := Bool.eq_false_iff.mpr hRef
        simp only [hOk, hRefF, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, stateT_run_lift_lazy1key, StateT.run_modify,
          StateT.run_pure, bind_assoc, pure_bind, hRunEq]
        refine ⟨by simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind],
          fun r σ' l1 hMem => ?_⟩
        rw [support_bind] at hMem
        rcases Set.mem_iUnion₂.mp hMem with ⟨⟨r0, l0⟩, hMem0, hEq⟩
        rw [support_pure, Set.mem_singleton_iff] at hEq
        rcases Prod.mk.inj hEq with ⟨hEq1, rfl⟩
        rcases Prod.mk.inj hEq1 with ⟨rfl, rfl⟩
        rw [bhToDrvState_bhE2EMirror]
        exact hInv r l1 hMem0
    all_goals
      dsimp only [bhKioKeyInd]
      simp only [hOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_get, stateT_run_lift_lazy1key, StateT.run_modify,
        StateT.run_pure, bind_assoc, pure_bind, hRunEq]
      refine ⟨by simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind],
        fun r σ' l1 hMem => ?_⟩
      rw [support_bind] at hMem
      rcases Set.mem_iUnion₂.mp hMem with ⟨⟨r0, l0⟩, hMem0, hEq⟩
      rw [support_pure, Set.mem_singleton_iff] at hEq
      rcases Prod.mk.inj hEq with ⟨hEq1, rfl⟩
      rcases Prod.mk.inj hEq1 with ⟨rfl, rfl⟩
      rw [bhToDrvState_bhE2EMirror]
      exact hInv r l1 hMem0
  · unfold bhKioKeyInd
    have hOkF : bhDrvKiQueryOk P σ.toModelDriverBase kq = false := Bool.eq_false_iff.mpr hOk
    simp only [hOkF, Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_pure, pure_bind, map_pure, support_pure, Set.mem_singleton_iff]
    refine ⟨trivial, fun r σ' l1 hEq => ?_⟩
    rcases Prod.mk.inj hEq with ⟨hEq1, rfl⟩
    rcases Prod.mk.inj hEq1 with ⟨rfl, rfl⟩
    exact ⟨hSync, rfl⟩

private theorem bhKioSm_tagImpl1KeyReal_sync
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (σ : BHE2EDrvState S ℓ) (lst : KeyInd1KeyLazyState S)
    (hSync : DrvTagSyncInv1KeyReal P (bhToDrvState σ) lst)
    (rc2 : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)) :
    ((bhKioSm (M := StateT (KeyInd1KeyLazyState S) ProbComp) C K qep decT encT i sq).run σ).run
        { lst with randCache := rc2 } =
      (fun (r_σ, l1) => (r_σ, { l1 with randCache := rc2 })) <$>
        ((bhKioSm (M := StateT (KeyInd1KeyLazyState S) ProbComp) C K qep decT encT i sq).run σ).run lst ∧
    ∀ r σ' l1, ((r, σ'), l1) ∈ support
        (((bhKioSm (M := StateT (KeyInd1KeyLazyState S) ProbComp) C K qep decT encT i sq).run σ).run lst) →
      DrvTagSyncInv1KeyReal P (bhToDrvState σ') l1 ∧ l1.randCache = lst.randCache := by
  unfold bhKioSm
  simp only [StateT.run_bind, StateT.run_get, bhKioDrvM_run_liftM_lazy1key,
    stateT_run_liftM_lazy1key, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
  refine ⟨by simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind],
    fun r σ' l1 hMem => ?_⟩
  rw [support_bind] at hMem
  rcases Set.mem_iUnion₂.mp hMem with ⟨⟨sr, σ1⟩, hSm, hEq⟩
  rw [support_pure, Set.mem_singleton_iff] at hEq
  rcases Prod.mk.inj hEq with ⟨hEq1, rfl⟩
  rcases Prod.mk.inj hEq1 with ⟨rfl, rfl⟩
  exact ⟨bhE2EStepLocalSm_preserves_tagSync1KeyReal P C K qep decT encT i sq σ l1 hSync hSm, rfl⟩

@[simp]
private theorem bhFinishStartSpkGen_noneResp_lazy1key
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (σ : BHE2EDrvState S ℓ)
    (sid : SignalPqxdh.SessionId S) (kr2 : SignalPqxdh.KeyIndResponse) (kb : SampledSessionKey × Bool) :
    bhFinishStartSpkGen C K σ sid .noneResp kr2 kb = (none, σ) := by
  unfold bhFinishStartSpkGen
  cases bhE2EGuard σ sid <;> rfl

private theorem bhKioStartGen_tagImpl1KeyReal_of_not_fresh
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (mkKB : ModelDriverKeyBitGen)
    (sid : SignalPqxdh.SessionId S) (σ : BHE2EDrvState S ℓ) (lst : KeyInd1KeyLazyState S)
    {hdr : SignalPqxdh.HandshakeHdr} {bnd : SignalPqxdh.PreKeyBundleInput}
    {u : Fin S.N_id} {j' : Fin S.N_recv}
    (hG : bhE2EGuard σ sid = some (hdr, bnd, (u, j')))
    (hNotFresh : (!SignalPqxdh.isKeyIndSessionTestable lst.base sid) = true)
    (rc : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)) :
    ((bhKioStartGen C K (pqxdhKeyIndTagImpl1KeyReal false false S P) mkKB sid).run σ).run
        { lst with randCache := rc } =
      (do
        let (kr2, l1) ←
          (pqxdhKeyIndTagImpl1KeyReal false false S P (.revealSpkSk u j')).run
            { lst with randCache := rc }
        let _ ← mkKB .noneResp kr2
        pure ((none, σ), l1)) := by
  have hTest := pqxdhKeyIndTagImpl1KeyReal_testSession_of_not_fresh false P sid lst hNotFresh rc
  unfold bhKioStartGen
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hG, stateT_run_lift_lazy1key,
    bind_assoc, hTest]
  simp only [pure_bind, StateT.run_bind, bhKioDrvM_run_liftM_lazy1key, stateT_run_liftM_lazy1key,
    StateT.run_set, StateT.run_pure, bind_assoc, bhFinishStartSpkGen_noneResp_lazy1key]

private theorem bhKioStartGen_tagImpl1KeyReal_of_bhE2EGuard
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (sid : SignalPqxdh.SessionId S) (σ : BHE2EDrvState S ℓ) (lst : KeyInd1KeyLazyState S)
    {hdr : SignalPqxdh.HandshakeHdr} {bnd : SignalPqxdh.PreKeyBundleInput}
    {u : Fin S.N_id} {j' : Fin S.N_recv}
    (hSync : DrvTagSyncInv1KeyReal P (bhToDrvState σ) lst)
    (hG : bhE2EGuard σ sid = some (hdr, bnd, (u, j')))
    (hFresh : (!SignalPqxdh.isKeyIndSessionTestable lst.base sid) = false) :
    ∃ (rootKey spkSk : SignalPqxdh.Bytes) (base_after : SignalPqxdh.KeyIndState S),
      spkSk.length = 32 ∧
      (∀ (mkKB : ModelDriverKeyBitGen) (rc : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)),
        lst.randCache.map Prod.fst = rc.map Prod.fst →
        ((bhKioStartGen C K (pqxdhKeyIndTagImpl1KeyReal false false S P) mkKB sid).run σ).run
            { lst with randCache := rc } =
          (do
            let dk ← SignalPqxdh.sampleDRKey96
            let kb ← mkKB (.drKeyResp dk) (.spkSkResp spkSk)
            let (res, σ') := bhFinishStartSpkSucc C K σ sid hdr bnd (u, j') spkSk kb
            pure ((res, σ'), { base := base_after, randCache := (rootKey, dk) :: rc }))) ∧
      (∀ dk ∈ support SignalPqxdh.sampleDRKey96, ∀ (kb : SampledSessionKey × Bool),
        DrvTagSyncInv1KeyReal P
          (bhToDrvState (bhFinishStartSpkSucc C K σ sid hdr bnd (u, j') spkSk kb).2)
          { base := base_after, randCache := (rootKey, dk) :: lst.randCache }) := by
  rcases bhE2EGuard_eq_some_props_1KeyReal hG with ⟨hsend, hbnd, hinst⟩
  rcases tagImpl1KeyReal_startDR_steps P sid (bhToDrvState σ) lst hSync hsend hbnd hinst hFresh with
    ⟨rootKey, spkSk, base_t, base_after, hSpkLen, hTestRun, hRevRun, hSyncAfter⟩
  refine ⟨rootKey, spkSk, base_after, hSpkLen, ?_, ?_⟩
  · intro mkKB rc hrc
    unfold bhKioStartGen
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hG, stateT_run_lift_lazy1key, bind_assoc]
    rw [hTestRun rc hrc]
    simp only [bind_assoc, pure_bind, StateT.run_bind, stateT_run_lift_lazy1key]
    refine prob_bind_congr_of_support SignalPqxdh.sampleDRKey96 _ _ (fun dk hdk => ?_)
    rw [hRevRun ((rootKey, dk) :: rc)]
    simp only [pure_bind, stateT_run_lift_lazy1key, bhKioDrvM_run_liftM_lazy1key,
      stateT_run_liftM_lazy1key, StateT.run_bind, StateT.run_set, StateT.run_pure, bind_assoc,
      bhFinishStartSpkGen_eq_succ C K σ sid hG hdk hSpkLen]
  · intro dk hdk kb
    let inst_new : BHModelInst S ℓ :=
      { sid := sid, hdr := hdr, idA := bhIdKeyOf hdr.ikAPk, idB := bhIdKeyOf bnd.ikB,
        spkCoins := bhBytesWord spkSk,
        gs := some (SM.initState (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K)
            (bhIdKeyOf hdr.ikAPk) (bhIdKeyOf bnd.ikB)) ℓ
          (bhBytesWord spkSk)).sendPart kb.1 kb.2) }
    exact hSyncAfter dk hdk
      (bhToDrvState (bhFinishStartSpkSucc C K σ sid hdr bnd (u, j') spkSk kb).2)
      (bhToDrvInst inst_new)
      rfl rfl
      (by dsimp [bhToDrvState, bhFinishStartSpkSucc, inst_new]; rw [List.map_append, List.map_singleton])
      rfl

/-! ## Lazy-vs-exact coupling -/

set_option maxHeartbeats 1200000 in
private theorem evalDist_bhKioImplPrefix_tagImpl1KeyReal_Lazy_eq_Exact {α : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (b_k : Bool)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) (lst : KeyInd1KeyLazyState S)
    (rc2 : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (hSync : DrvTagSyncInv1KeyReal P (bhToDrvState σ) lst)
    (hCache : lst.randCache.map Prod.fst = rc2.map Prod.fst)
    (obs : (α × BHE2EDrvState S ℓ) × KeyInd1KeyLazyState S → ProbComp Bool)
    (hObs : ∀ x l rc, obs (x, { l with randCache := rc }) = obs (x, l)) :
    𝒟[(((simulateQ (bhKioImplPrefix P C K qep decT encT
        (pqxdhKeyIndTagImpl1KeyReal false false S P)
        (bhMkPrefixLazy k b_k)) oa).run σ).run lst) >>= obs] =
    𝒟[(((simulateQ (bhKioImplPrefix P C K qep decT encT
        (pqxdhKeyIndTagImpl1KeyReal false false S P)
        (bhMkPrefixExact k b_k)) oa).run σ).run { lst with randCache := rc2 }) >>= obs] := by
  induction oa using OracleComp.inductionOn generalizing σ lst rc2 with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact congrArg (fun z => 𝒟[z]) (hObs (x, σ) lst rc2).symm
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      bhKioImplPrefix_run_eq_gen, bhKioImplPrefix_run_eq_gen, bind_assoc, bind_assoc]
    rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
    · dsimp only [bhKioImplGen]
      simp only [bhKioDrvM_run_liftM_lazy1key, stateT_run_liftM_lazy1key, StateT.run_bind,
        StateT.run_pure, bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_congr_of_support _ _ _
        (fun x _ => ih x σ lst rc2 hSync hCache)
    · dsimp only [bhKioImplGen]
      have ⟨hRunEq, hInv⟩ := bhKioKeyInd_tagImpl1KeyReal_sync P kq σ lst hSync rc2
      rw [hRunEq]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun p hMem => ?_)
      rcases p with ⟨⟨r, σ'⟩, l1⟩
      rcases hInv r σ' l1 hMem with ⟨hSync', hl1_rc⟩
      exact ih r σ' l1 rc2 hSync' (by rw [hl1_rc, hCache])
    · dsimp only [bhKioImplGen]
      cases hG : bhE2EGuard σ sid with
      | none =>
        unfold bhKioStartGen
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hG, StateT.run_pure]
        exact ih none σ lst rc2 hSync hCache
      | some val =>
        rcases val with ⟨hdr, bnd, ⟨u, j'⟩⟩
        cases hNotFresh : (!SignalPqxdh.isKeyIndSessionTestable lst.base sid) with
        | true =>
          have hL := bhKioStartGen_tagImpl1KeyReal_of_not_fresh P C K
            (bhMkPrefixLazy k b_k σ.insts.length) sid σ lst hG hNotFresh lst.randCache
          have hR := bhKioStartGen_tagImpl1KeyReal_of_not_fresh P C K
            (bhMkPrefixExact k b_k σ.insts.length) sid σ lst hG hNotFresh rc2
          have hLst : { lst with randCache := lst.randCache } = lst := rfl
          rw [hLst] at hL
          rw [hL, hR]
          have ⟨hRevEq, hRevInv⟩ := pqxdhKeyIndTagImpl1KeyReal_non_test_sync false P
            (.revealSpkSk u j') (fun _ h => by nomatch h) (bhToDrvState σ) lst hSync rc2
          rw [hRevEq]
          simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun p hMem => ?_)
          rcases p with ⟨kr2, l1⟩
          rcases hRevInv kr2 l1 hMem with ⟨hSync', hl1_rc⟩
          rw [drvMirror_revealSpkSk] at hSync'
          have hMkEq : bhMkPrefixLazy k b_k σ.insts.length .noneResp kr2 =
              bhMkPrefixExact k b_k σ.insts.length .noneResp kr2 := rfl
          rw [hMkEq]
          exact OracleComp.evalDist_bind_congr_of_support _ _ _
            (fun _ _ => ih none σ l1 rc2 hSync' (by rw [hl1_rc, hCache]))
        | false =>
          rcases bhKioStartGen_tagImpl1KeyReal_of_bhE2EGuard P C K sid σ lst hSync hG hNotFresh with
            ⟨rootKey, spkSk, base_after, hSpkLen, hRun, hSyncAfter⟩
          have hL := hRun (bhMkPrefixLazy k b_k σ.insts.length) lst.randCache rfl
          have hR := hRun (bhMkPrefixExact k b_k σ.insts.length) rc2 hCache
          have hLst : { lst with randCache := lst.randCache } = lst := rfl
          rw [hLst] at hL
          rw [hL, hR]
          simp only [bind_assoc, pure_bind]
          by_cases hSlot : (σ.insts.length == k) = true
          · have hLazyDk : ∀ dk ∈ support SignalPqxdh.sampleDRKey96,
                bhMkPrefixLazy k b_k σ.insts.length (.drKeyResp dk) (.spkSkResp spkSk) =
                  (do
                    let _ ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
                    let k_fresh ← ($ᵗ SampledSessionKey : ProbComp SampledSessionKey)
                    return (k_fresh, b_k)) := by
              intro dk hdk
              rcases lengths_of_mem_support_sampleDRKey96 hdk with ⟨hrk, hck, hpqr⟩
              unfold bhMkPrefixLazy
              simp [hrk, hck, hpqr, hSpkLen, hSlot]
            have hExactDk : ∀ dk : SignalPqxdh.DRKey,
                bhMkPrefixExact k b_k σ.insts.length (.drKeyResp dk) (.spkSkResp spkSk) =
                  (do
                    let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
                    return (bhKeySOf dk ac, b_k)) := by
              intro dk
              unfold bhMkPrefixExact
              simp [hSlot]
            have hL_step : ∀ dk ∈ support SignalPqxdh.sampleDRKey96,
                𝒟[bhMkPrefixLazy k b_k σ.insts.length (.drKeyResp dk) (.spkSkResp spkSk) >>=
                  fun kb =>
                    let p := bhFinishStartSpkSucc C K σ sid hdr bnd (u, j') spkSk kb
                    (((simulateQ (bhKioImplPrefix P C K qep decT encT
                      (pqxdhKeyIndTagImpl1KeyReal false false S P)
                      (bhMkPrefixLazy k b_k)) (mx p.1)).run p.2).run
                        { base := base_after, randCache := (rootKey, dk) :: lst.randCache }) >>= obs] =
                𝒟[($ᵗ SampledSessionKey : ProbComp SampledSessionKey) >>= fun k_fresh =>
                  let p := bhFinishStartSpkSucc C K σ sid hdr bnd (u, j') spkSk (k_fresh, b_k)
                  (((simulateQ (bhKioImplPrefix P C K qep decT encT
                    (pqxdhKeyIndTagImpl1KeyReal false false S P)
                    (bhMkPrefixExact k b_k)) (mx p.1)).run p.2).run
                      { base := base_after, randCache := (rootKey, default) :: rc2 }) >>= obs] := by
              intro dk hdk
              rw [hLazyDk dk hdk]
              simp only [bind_assoc, pure_bind]
              rw [OracleComp.evalDist_bind_const]
              refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k_fresh _ => ?_)
              exact ih _ _ { base := base_after, randCache := (rootKey, dk) :: lst.randCache }
                ((rootKey, default) :: rc2) (hSyncAfter dk hdk (k_fresh, b_k))
                (by simp [hCache])
            have hLHS :
                𝒟[SignalPqxdh.sampleDRKey96 >>= fun dk =>
                  bhMkPrefixLazy k b_k σ.insts.length (.drKeyResp dk) (.spkSkResp spkSk) >>=
                  fun kb =>
                    let p := bhFinishStartSpkSucc C K σ sid hdr bnd (u, j') spkSk kb
                    (((simulateQ (bhKioImplPrefix P C K qep decT encT
                      (pqxdhKeyIndTagImpl1KeyReal false false S P)
                      (bhMkPrefixLazy k b_k)) (mx p.1)).run p.2).run
                        { base := base_after, randCache := (rootKey, dk) :: lst.randCache }) >>= obs] =
                𝒟[($ᵗ SampledSessionKey : ProbComp SampledSessionKey) >>= fun k_fresh =>
                  let p := bhFinishStartSpkSucc C K σ sid hdr bnd (u, j') spkSk (k_fresh, b_k)
                  (((simulateQ (bhKioImplPrefix P C K qep decT encT
                    (pqxdhKeyIndTagImpl1KeyReal false false S P)
                    (bhMkPrefixExact k b_k)) (mx p.1)).run p.2).run
                      { base := base_after, randCache := (rootKey, default) :: rc2 }) >>= obs] := by
              rw [OracleComp.evalDist_bind_congr_of_support _ _ _ hL_step,
                OracleComp.evalDist_bind_const]
            have hR_step : ∀ dk ∈ support SignalPqxdh.sampleDRKey96,
                𝒟[bhMkPrefixExact k b_k σ.insts.length (.drKeyResp dk) (.spkSkResp spkSk) >>=
                  fun kb =>
                    let p := bhFinishStartSpkSucc C K σ sid hdr bnd (u, j') spkSk kb
                    (((simulateQ (bhKioImplPrefix P C K qep decT encT
                      (pqxdhKeyIndTagImpl1KeyReal false false S P)
                      (bhMkPrefixExact k b_k)) (mx p.1)).run p.2).run
                        { base := base_after, randCache := (rootKey, dk) :: rc2 }) >>= obs] =
                𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ac =>
                  let p := bhFinishStartSpkSucc C K σ sid hdr bnd (u, j') spkSk
                    (bhKeySOf dk ac, b_k)
                  (((simulateQ (bhKioImplPrefix P C K qep decT encT
                    (pqxdhKeyIndTagImpl1KeyReal false false S P)
                    (bhMkPrefixExact k b_k)) (mx p.1)).run p.2).run
                      { base := base_after, randCache := (rootKey, default) :: rc2 }) >>= obs] := by
              intro dk hdk
              rw [hExactDk dk]
              simp only [bind_assoc, pure_bind]
              refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ac _ => ?_)
              let p := bhFinishStartSpkSucc C K σ sid hdr bnd (u, j') spkSk (bhKeySOf dk ac, b_k)
              have h1 := ih p.1 p.2
                { base := base_after, randCache := (rootKey, dk) :: lst.randCache }
                ((rootKey, dk) :: rc2) (hSyncAfter dk hdk _) (by simp [hCache])
              have h2 := ih p.1 p.2
                { base := base_after, randCache := (rootKey, dk) :: lst.randCache }
                ((rootKey, default) :: rc2) (hSyncAfter dk hdk _) (by simp [hCache])
              exact h1.symm.trans h2
            rw [hLHS, OracleComp.evalDist_bind_congr_of_support _ _ _ hR_step]
            let cont : SampledSessionKey → ProbComp Bool := fun k_fresh =>
              let p := bhFinishStartSpkSucc C K σ sid hdr bnd (u, j') spkSk (k_fresh, b_k)
              (((simulateQ (bhKioImplPrefix P C K qep decT encT
                (pqxdhKeyIndTagImpl1KeyReal false false S P)
                (bhMkPrefixExact k b_k)) (mx p.1)).run p.2).run
                  { base := base_after, randCache := (rootKey, default) :: rc2 }) >>= obs
            have hKeySOf : bhKeySOf = keySOf := rfl
            change 𝒟[($ᵗ SampledSessionKey : ProbComp SampledSessionKey) >>= cont] =
              𝒟[SignalPqxdh.sampleDRKey96 >>= fun dk =>
                ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ac =>
                  cont (bhKeySOf dk ac)]
            rw [hKeySOf]
            have hAssoc :
                (SignalPqxdh.sampleDRKey96 >>= fun dk =>
                  ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ac =>
                    cont (keySOf dk ac)) =
                ((do
                  let dk ← SignalPqxdh.sampleDRKey96
                  let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
                  return keySOf dk ac) >>= cont) := by
              simp only [bind_assoc, pure_bind]
            rw [hAssoc, evalDist_bind_of_discrete, evalDist_bind_of_discrete,
              evalDist_sampleDRKey96_keySOf_eq_select_keyS, bind_pure]
          · have hSlotF : (σ.insts.length == k) = false := Bool.eq_false_iff.mpr hSlot
            have hEqNotSlot : ∀ dk : SignalPqxdh.DRKey,
                bhMkPrefixLazy k b_k σ.insts.length (.drKeyResp dk) (.spkSkResp spkSk) =
                  bhMkPrefixExact k b_k σ.insts.length (.drKeyResp dk) (.spkSkResp spkSk) := by
              intro dk
              unfold bhMkPrefixLazy bhMkPrefixExact
              simp [hSlotF]
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun dk hdk => ?_)
            rw [hEqNotSlot dk]
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun kb _ => ?_)
            exact ih _ _ { base := base_after, randCache := (rootKey, dk) :: lst.randCache }
              ((rootKey, dk) :: rc2) (hSyncAfter dk hdk kb) (by simp [hCache])
    · dsimp only [bhKioImplGen]
      have ⟨hRunEq, hInv⟩ := bhKioSm_tagImpl1KeyReal_sync P C K qep decT encT i sq σ lst hSync rc2
      rw [hRunEq]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun p hMem => ?_)
      rcases p with ⟨⟨r, σ'⟩, l1⟩
      rcases hInv r σ' l1 hMem with ⟨hSync', hl1_rc⟩
      exact ih r σ' l1 rc2 hSync' (by rw [hl1_rc, hCache])

theorem evalDist_bhPrefixLazyFullExpWith_e2e1KeyReal_eq_bhPrefixExactFullExpWith
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhPrefixLazyFullExpWith S (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P) P C K ℓ qep
        decT encT k b_k B] =
      𝒟[bhPrefixExactFullExpWith S (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P) P C K ℓ qep
        decT encT k b_k B] := by
  let g : (Bool × BHE2EDrvState S ℓ) → Bool → ProbComp Bool :=
    fun ⟨b', σ⟩ clean =>
      if !clean then $ᵗ Bool
      else return (if bhE2EDrvWon σ true then true else if bhE2EDrvWon σ false then false else b')
  let oa_lazy :=
    (simulateQ (bhKioImplPrefix P C K qep decT encT (kioKind S)
      (bhMkPrefixLazy k b_k)) B).run {}
  let oa_exact :=
    (simulateQ (bhKioImplPrefix P C K qep decT encT (kioKind S)
      (bhMkPrefixExact k b_k)) B).run {}
  have hInit : ({} : BHE2EDrvState S ℓ) =
      { ({} : BHE2EDrvState S ℓ) with st := SignalPqxdh.KeyIndState.empty S false } := rfl
  have hCleanEq : allTestedSessionsFresh (S := S) P = composedClean (S := S) P := rfl
  have h1 :
      𝒟[bhPrefixLazyFullExpWith S (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P) P C K ℓ qep
          decT encT k b_k B] =
        𝒟[(simulateQ (kioFullImpl (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P)) oa_lazy).run
            (SignalPqxdh.KeyIndState.empty S false) >>= fun (a, st) => g a (composedClean P st)] := by
    unfold bhPrefixLazyFullExpWith bhComposedPostObs
    rw [hInit, simulateQ_bhE2EDrvImplPrefixWith_eq_bhKioImplPrefix,
      ← simulateQ_bhKioImplPrefix_kioKind_run]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, hCleanEq]
    rfl
  have h2 := evalDist_simulateQ_pqxdhKeyIndImpl1KeyReal_false_eq_tagImpl P oa_lazy g
  have h3 :
      𝒟[(simulateQ (kioFullImpl (pqxdhKeyIndTagImpl1KeyReal false false S P)) oa_lazy).run
          (KeyInd1KeyLazyState.empty S) >>= fun (a, lst) => g a (composedClean P lst.base)] =
        𝒟[(((simulateQ (bhKioImplPrefix P C K qep decT encT
            (pqxdhKeyIndTagImpl1KeyReal false false S P)
            (bhMkPrefixLazy k b_k)) B).run {}).run (KeyInd1KeyLazyState.empty S)) >>=
            fun (a, lst) => g a (composedClean P lst.base)] := by
    rw [simulateQ_bhKioImplPrefix_kioKind_run]
  have h4 := evalDist_bhKioImplPrefix_tagImpl1KeyReal_Lazy_eq_Exact P C K qep decT encT k b_k B
    {} (KeyInd1KeyLazyState.empty S) (KeyInd1KeyLazyState.empty S).randCache
    (DrvTagSyncInv1KeyReal.empty P) rfl
    (fun (a, lst) => g a (composedClean P lst.base)) (fun _ _ _ => rfl)
  have h5 :
      𝒟[(((simulateQ (bhKioImplPrefix P C K qep decT encT
          (pqxdhKeyIndTagImpl1KeyReal false false S P)
          (bhMkPrefixExact k b_k)) B).run {}).run (KeyInd1KeyLazyState.empty S)) >>=
          fun (a, lst) => g a (composedClean P lst.base)] =
        𝒟[(simulateQ (kioFullImpl (pqxdhKeyIndTagImpl1KeyReal false false S P)) oa_exact).run
            (KeyInd1KeyLazyState.empty S) >>=
              fun (a, lst) => g a (composedClean P lst.base)] := by
    rw [simulateQ_bhKioImplPrefix_kioKind_run]
  have h6 := (evalDist_simulateQ_pqxdhKeyIndImpl1KeyReal_false_eq_tagImpl P oa_exact g).symm
  have h7 :
      𝒟[(simulateQ (kioFullImpl (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P)) oa_exact).run
          (SignalPqxdh.KeyIndState.empty S false) >>= fun (a, st) => g a (composedClean P st)] =
        𝒟[bhPrefixExactFullExpWith S (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P) P C K ℓ
          qep decT encT k b_k B] := by
    unfold bhPrefixExactFullExpWith bhComposedPostObs
    rw [hInit, simulateQ_bhE2EDrvImplPrefixWith_eq_bhKioImplPrefix,
      ← simulateQ_bhKioImplPrefix_kioKind_run]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, hCleanEq]
    rfl
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

/-! ## Main prefix telescope for `pqxdhKeyIndImpl1KeyReal` -/

private def bhNormSigPkGen (P : SignalPqxdh.Primitives) : SignalPqxdh.Primitives :=
  { P with sigPkGen := P.x25519Base }

private theorem signalPqxdh_pqxdhKeyIndImpl1KeyReal_normSigPkGen
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives) :
    SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P =
      CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S (bhNormSigPkGen P) := by
  have h1 : SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P =
      SignalPqxdh.pqxdhKeyIndImpl1KeyReal S (bhNormSigPkGen P) := by
    funext q; cases q <;> rfl
  exact h1.trans (signalPqxdh_pqxdhKeyIndImpl1KeyReal_eq S (bhNormSigPkGen P) rfl)

private theorem bhE2EDrvImplPrefixWith_normSigPkGen
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (mkP : BHDrvPrefixKeyBitGen) :
    bhE2EDrvImplPrefixWith (S := S) (ℓ := ℓ) ki P C K qep decT encT mkP =
      bhE2EDrvImplPrefixWith (S := S) (ℓ := ℓ) ki (bhNormSigPkGen P) C K qep decT encT mkP := by
  have hOk : bhDrvKiQueryOk (S := S) P = bhDrvKiQueryOk (S := S) (bhNormSigPkGen P) := by
    funext base kq; cases kq <;> rfl
  funext q
  unfold bhE2EDrvImplPrefixWith bhE2EDrvImplGenWith
  simp only [hOk]

private theorem bhComposedPostObs_normSigPkGen (P : SignalPqxdh.Primitives) :
    bhComposedPostObs (S := S) (ℓ := ℓ) P =
      bhComposedPostObs (S := S) (ℓ := ℓ) (bhNormSigPkGen P) := rfl

/-- Lazy and exact prefix experiments have identical output distributions at
`SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P`. -/
theorem evalDist_bhPrefixLazyFullExpWith_1KeyReal_eq_bhPrefixExactFullExpWith
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhPrefixLazyFullExpWith S (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) P C K ℓ qep
        decT encT k b_k B] =
      𝒟[bhPrefixExactFullExpWith S (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) P C K ℓ qep
        decT encT k b_k B] := by
  have hL :
      bhPrefixLazyFullExpWith S (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) P C K ℓ qep
          decT encT k b_k B =
        bhPrefixLazyFullExpWith S
          (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S (bhNormSigPkGen P))
          (bhNormSigPkGen P) C K ℓ qep decT encT k b_k B := by
    unfold bhPrefixLazyFullExpWith
    rw [signalPqxdh_pqxdhKeyIndImpl1KeyReal_normSigPkGen,
      bhE2EDrvImplPrefixWith_normSigPkGen, bhComposedPostObs_normSigPkGen]
  have hR :
      bhPrefixExactFullExpWith S (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) P C K ℓ qep
          decT encT k b_k B =
        bhPrefixExactFullExpWith S
          (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S (bhNormSigPkGen P))
          (bhNormSigPkGen P) C K ℓ qep decT encT k b_k B := by
    unfold bhPrefixExactFullExpWith
    rw [signalPqxdh_pqxdhKeyIndImpl1KeyReal_normSigPkGen,
      bhE2EDrvImplPrefixWith_normSigPkGen, bhComposedPostObs_normSigPkGen]
  rw [hL, hR]
  exact evalDist_bhPrefixLazyFullExpWith_e2e1KeyReal_eq_bhPrefixExactFullExpWith
    S (bhNormSigPkGen P) C K ℓ qep decT encT k b_k B

/-- The `qStart`-step prefix-hybrid bound at `SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P` phrased in
terms of `Prefix1Key.bhPrefixRedWith`. -/
theorem boolBias_bhE2EExpWithKi_1KeyReal_false_le_sum_prefix_steps
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart qTot : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hQStart : B.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart)
    (hQTot : B.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot) :
    𝒟[Prefix1Key.bhE2EExpWithKi S (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) false P C K ℓ qep decT encT B].boolBias ≤
      ∑ k ∈ Finset.range qStart,
        ⨆ flip : Bool,
          𝒟[stageOneAsProbComp
              ((Prefix1Key.bhPrefixRedWith S ℓ P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT k).eval1
                (fun _ => B) () qTot false) >>=
            fun o =>
              SM.gameR
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
                  ℓ o.1.spkCoins)
                (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
                ((Prefix1Key.bhPrefixRedWith S ℓ P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT k).eval2
                  o.2 flip qTot false)].boolBias :=
  boolBias_bhE2EExpWithKi_false_le_sum_prefix_steps_of_lazyEq
    S (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) P C K ℓ qep decT encT qStart qTot B
    (fun k _ b_k => evalDist_bhPrefixLazyFullExpWith_1KeyReal_eq_bhPrefixExactFullExpWith
      S P C K ℓ qep decT encT k b_k B)
    hQStart hQTot

end CryptoVerification.E2E
