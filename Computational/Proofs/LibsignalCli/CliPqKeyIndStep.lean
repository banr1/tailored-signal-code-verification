/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.CliPqAdapterCoupling
import Computational.Proofs.LibsignalCli.CliPqKeyIndInvStep
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic

/-!
# 1-key `KeyInd` and `Unif` adapter step coupling

**Checked by Lean.** Proves step-level coupling between `bhDrvKeyInd S ℓ (modelPrims X W) false`
and `cliComposedAdapterImplWith` over `SignalPqxdh.pqxdhKeyIndImpl1KeyReal`, discharging
`CliKeyIndStepBridgeProp`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

private theorem cliDrvKeyInd_preserves_rel {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli st_cli' : SignalPqxdh.KeyIndState S} {ds_cli ds_cli' : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (kq : SignalPqxdh.KeyIndQuery S)
    (hOk : bhDrvKiQueryOk (modelPrims X W) ds_cli.toModelDriverBase kq = true)
    (kr : SignalPqxdh.KeyIndResponse)
    (hmem : ((kr, ds_cli'), st_cli') ∈ support
      (((bhDrvKeyInd S ℓ (modelPrims X W) false kq).run ds_cli).run st_cli)) :
    CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli' ds_cli'
      (σ_ad.1, σ_ad.2.1, bhBaseMirror σ_ad.2.2 kq kr)
      (bhE2EMirror
        { σ_e2e with
          st := cliReplaceSpkBundles st_cli'
            (cliUpdateSpkBundlesForQuery kq σ_e2e.st.spkBundles kr st_cli') }
        kq kr) := by
  set P := modelPrims X W
  have hXBase := modelPrims_x25519Base_eq_cli X W
  cases kq with
  | testSession _ | revealDhSecrets =>
    simp [bhDrvKiQueryOk] at hOk
  | roQuery secrets =>
    unfold bhDrvKeyInd at hmem
    simp only [stateT_lift_run_cli, stateT_monadLift_run_cli, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨⟨dk, roCache'⟩, hro, ⟨rfl, rfl⟩, rfl⟩
    obtain ⟨_, hro_eq⟩ := mem_support_evalHkdfOrRo_false_cli P st_cli.roCache secrets hro
    exact cliAdapterDrvRel_of_keyInd_step hRel (.roQuery secrets) (.drKeyResp dk)
      hRel.st_rel.secb_cli
      hRel.st_rel.spkBundles_rel
      hRel.st_rel.tested_spkRevealed
      hRel.st_rel.resp_not_tested
      { hRel.ki_inv with roCache_nil := hro_eq.trans hRel.ki_inv.roCache_nil }
      rfl rfl rfl rfl rfl
      (fun h => cliAdapterInstRel_of_st_ds_unchanged h (fun _ hx => hx) rfl)
  | initPrin u =>
    unfold bhDrvKeyInd at hmem
    simp only [Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_modify, StateT.run_pure, stateT_lift_run_cli, bind_assoc, pure_bind] at hmem
    by_cases hany : (st_cli.principals.any (fun (idx, _) => idx == u.val)) = true
    · rw [hany] at hmem; simp at hmem
      rcases hmem with ⟨⟨rfl, rfl⟩, rfl⟩
      simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.initPrin u)
    · simp only [Bool.not_eq_true] at hany
      simp only [hany, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        stateT_monadLift_run_cli, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, support_bind, support_pure,
        Set.mem_iUnion, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨secIKA0, hsec, ⟨rfl, rfl⟩, rfl⟩
      exact cliAdapterDrvRel_of_keyInd_step hRel (.initPrin u)
        (.initPrinResp (P.x25519Base secIKA0) (P.x25519Base secIKA0))
        hRel.st_rel.secb_cli
        hRel.st_rel.spkBundles_rel
        hRel.st_rel.tested_spkRevealed
        hRel.st_rel.resp_not_tested
        (cliAdapterKeyIndInv_of_initPrin hP hXBase hRel.ki_inv u secIKA0 hany
          (sampleScalar32_length_of_mem_cli hsec))
        rfl rfl rfl rfl rfl
        (fun h => cliAdapterInstRel_of_st_ds_unchanged h (fun _ hx => hx) rfl)
  | corruptIK u =>
    unfold bhDrvKeyInd at hmem
    rw [stateT_run_get_bind_cli] at hmem
    by_cases hProm : bhNoOpkRespPromoted ds_cli.instMeta u = true
    · rw [hProm] at hmem; simp at hmem
      rcases hmem with ⟨⟨rfl, rfl⟩, rfl⟩
      simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.corruptIK u)
    · simp only [Bool.not_eq_true] at hProm
      simp only [hProm, Bool.false_eq_true, ↓reduceIte] at hmem
      obtain ⟨hm, rfl⟩ := mem_support_lift_modify_bhDrvMirror_cli _ _ _ _ hmem
      unfold SignalPqxdh.pqxdhKeyIndImpl at hm
      rw [stateT_run_get_bind_cli] at hm
      rcases hfind : st_cli.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨idx, entry⟩
      · simp only [hfind, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.corruptIK u)
      · simp only [hfind, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        exact cliAdapterDrvRel_of_keyInd_step hRel (.corruptIK u)
          (.corrResp entry.secIKA0 entry.secIKAsign)
          hRel.st_rel.secb_cli
          hRel.st_rel.spkBundles_rel
          hRel.st_rel.tested_spkRevealed
          hRel.st_rel.resp_not_tested
          (cliAdapterKeyIndInv_of_corruptIK hRel.ki_inv u entry.secIKA0 entry.secIKAsign)
          rfl rfl rfl rfl rfl
          (fun h => cliAdapterInstRel_of_st_ds_unchanged h (fun _ hx => hx) rfl)
  | genSPK u j =>
    unfold bhDrvKeyInd at hmem
    obtain ⟨hm, rfl⟩ := mem_support_lift_modify_bhDrvMirror_cli _ _ _ _ hmem
    unfold SignalPqxdh.pqxdhKeyIndImpl at hm
    rw [stateT_run_get_bind_cli] at hm
    by_cases hany : (st_cli.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp only [hany, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.genSPK u j)
    · simp only [Bool.not_eq_true] at hany
      simp only [hany, Bool.false_eq_true, ↓reduceIte] at hm
      rcases hfind : st_cli.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨idx, uEntry⟩
      · simp only [hfind, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.genSPK u j)
      · obtain ⟨huEntry, _⟩ := mem_principals_of_find?_eq_some_cli hfind
        simp only [hfind, stateT_monadLift_run_cli, StateT.run_bind, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, support_bind, support_pure,
          Set.mem_iUnion, Set.mem_singleton_iff, Prod.mk.injEq] at hm
        rcases hm with ⟨spkSk, hspk, rSpk, _, ⟨pqspkPk, pqspkSk⟩, hpq, rPq, _, rfl, rfl⟩
        refine cliAdapterDrvRel_of_keyInd_step hRel (.genSPK u j) _
          hRel.st_rel.secb_cli
          (List.Forall₂.cons (CliSpkBundleRel.refl _) hRel.st_rel.spkBundles_rel)
          (fun s hs ht =>
            ⟨isSpkRevealed_cons_of_true_cli P _ _ _ (hRel.st_rel.tested_spkRevealed s hs ht).1,
             isSpkRevealed_cons_of_true_cli P _ _ _ (hRel.st_rel.tested_spkRevealed s hs ht).2⟩)
          hRel.st_rel.resp_not_tested
          (cliAdapterKeyIndInv_of_genSPK hP hXBase hRel.ki_inv u j uEntry huEntry hany
            spkSk rSpk pqspkPk pqspkSk rPq
            (sampleScalar32_length_of_mem_cli hspk)
            (sampleKemKeyGen_lengths_of_mem_cli hP hpq))
          rfl rfl rfl rfl rfl
          (fun h => cliAdapterInstRel_of_cons_spk h (fun _ hx => hx) rfl hany)
  | genOPK u j o =>
    unfold bhDrvKeyInd at hmem
    obtain ⟨hm, rfl⟩ := mem_support_lift_modify_bhDrvMirror_cli _ _ _ _ hmem
    unfold SignalPqxdh.pqxdhKeyIndImpl at hm
    rw [stateT_run_get_bind_cli] at hm
    by_cases hany : (st_cli.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp only [hany, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.genOPK u j o)
    · simp only [Bool.not_eq_true] at hany
      simp only [hany, Bool.false_eq_true, ↓reduceIte, stateT_monadLift_run_cli,
        StateT.run_bind, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, Prod.mk.injEq] at hm
      rcases hm with ⟨opkSk, hopk, rfl, rfl⟩
      exact cliAdapterDrvRel_of_keyInd_step hRel (.genOPK u j o) (.pkResp (P.x25519Base opkSk))
        hRel.st_rel.secb_cli
        hRel.st_rel.spkBundles_rel
        hRel.st_rel.tested_spkRevealed
        hRel.st_rel.resp_not_tested
        (cliAdapterKeyIndInv_of_genOPK hP hXBase hRel.ki_inv u j o hany opkSk
          (sampleScalar32_length_of_mem_cli hopk))
        rfl rfl rfl rfl rfl
        (fun h => cliAdapterInstRel_of_st_ds_unchanged h (fun _ hx => hx) rfl)
  | revealSpkSk u j =>
    unfold bhDrvKeyInd at hmem
    obtain ⟨hm, rfl⟩ := mem_support_lift_modify_bhDrvMirror_cli _ _ _ _ hmem
    unfold SignalPqxdh.pqxdhKeyIndImpl at hm
    rw [stateT_run_get_bind_cli] at hm
    rcases hfind : st_cli.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with _ | ⟨idx, bEntry⟩
    · simp only [hfind, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.revealSpkSk u j)
    · simp only [hfind, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      exact cliAdapterDrvRel_of_keyInd_step hRel (.revealSpkSk u j) (.spkSkResp bEntry.spkSk)
        hRel.st_rel.secb_cli
        (forall2_cliSpkBundles_map_reveal hRel.st_rel.spkBundles_rel (u.val, j.val))
        (fun s hs ht =>
          ⟨isSpkRevealed_map_reveal_of_true_cli P _ _ _ (hRel.st_rel.tested_spkRevealed s hs ht).1,
           isSpkRevealed_map_reveal_of_true_cli P _ _ _ (hRel.st_rel.tested_spkRevealed s hs ht).2⟩)
        hRel.st_rel.resp_not_tested
        (cliAdapterKeyIndInv_of_revealSpkSk hRel.ki_inv u j bEntry.spkSk)
        rfl rfl rfl rfl rfl
        (fun h => cliAdapterInstRel_of_map_reveal_spk h (fun _ hx => hx) (fun _ _ => rfl) rfl)
  | revealSessionKey sid =>
    unfold bhDrvKeyInd at hmem
    obtain ⟨hm, rfl⟩ := mem_support_lift_modify_bhDrvMirror_cli _ _ _ _ hmem
    unfold SignalPqxdh.pqxdhKeyIndImpl at hm
    rw [stateT_run_get_bind_cli] at hm
    rcases hfind1 : st_cli.sessions.find? (fun e => e.sid == sid) with _ | e
    · simp only [hfind1] at hm
      rcases hfind2 : st_cli.respSessions.find? (fun r => r.sid == sid) with _ | re
      · simp only [hfind2, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.revealSessionKey sid)
      · simp only [hfind2] at hm
        by_cases hT : re.tested = true
        · simp only [hT, ↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩
          simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.revealSessionKey sid)
        · simp only [Bool.not_eq_true] at hT
          simp only [hT, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩
          refine cliAdapterDrvRel_of_keyInd_step hRel (.revealSessionKey sid)
            (.drKeyResp re.drKeyReal)
            hRel.st_rel.secb_cli
            hRel.st_rel.spkBundles_rel
            hRel.st_rel.tested_spkRevealed
            (fun r' hr' => by
              rcases List.mem_map.mp hr' with ⟨r, hr, rfl⟩
              split_ifs <;> exact hRel.st_rel.resp_not_tested r hr)
            (cliAdapterKeyIndInv_of_revealRespSessionKey hRel.ki_inv sid re.drKeyReal)
            rfl rfl rfl rfl rfl
            (fun h => cliAdapterInstRel_of_st_ds_unchanged h (fun _ hx => hx) rfl)
    · simp only [hfind1] at hm
      by_cases hT : e.tested = true
      · simp only [hT, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.revealSessionKey sid)
      · simp only [Bool.not_eq_true] at hT
        simp only [hT, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        refine cliAdapterDrvRel_of_keyInd_step hRel (.revealSessionKey sid)
          (.drKeyResp e.drKeyReal)
          hRel.st_rel.secb_cli
          hRel.st_rel.spkBundles_rel
          (fun s' hs' ht' => by
            obtain ⟨s, hs, _, hspk, _, _, _, htest⟩ := mem_sessions_map_reveal_cli hs'
            rw [hspk]
            exact hRel.st_rel.tested_spkRevealed s hs (htest.symm.trans ht'))
          hRel.st_rel.resp_not_tested
          (cliAdapterKeyIndInv_of_revealSessionKey hRel.ki_inv sid e.drKeyReal)
          rfl rfl rfl rfl rfl
          (fun h => cliAdapterInstRel_of_st_ds_unchanged h (fun _ hx => hx) rfl)
  | registerKey sk =>
    unfold bhDrvKeyInd at hmem
    obtain ⟨hm, rfl⟩ := mem_support_lift_modify_bhDrvMirror_cli _ _ _ _ hmem
    unfold SignalPqxdh.pqxdhKeyIndImpl at hm
    rw [stateT_run_get_bind_cli] at hm; dsimp only at hm
    rcases hreg : SignalPqxdh.registerAdvKey P st_cli.advKeys sk with _ | ⟨pk, advKeys'⟩
    · rw [hreg] at hm
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.registerKey sk)
    · rw [hreg] at hm
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      exact cliAdapterDrvRel_of_keyInd_step hRel (.registerKey sk) (.pkResp pk)
        hRel.st_rel.secb_cli
        hRel.st_rel.spkBundles_rel
        hRel.st_rel.tested_spkRevealed
        hRel.st_rel.resp_not_tested
        { hRel.ki_inv with }
        rfl rfl rfl rfl rfl
        (fun h => cliAdapterInstRel_of_st_ds_unchanged h (fun _ hx => hx) rfl)
  | initiateOPK u i bnd =>
    simp only [bhDrvKiQueryOk, Bool.and_eq_true] at hOk
    rcases hOk with ⟨hopk, hik⟩
    have hnone : bnd.opkB?.isNone = false := by
      rcases hopk' : bnd.opkB? with _ | _
      · rw [hopk'] at hopk; cases hopk
      · rfl
    unfold bhDrvKeyInd at hmem
    rw [stateT_run_get_bind_cli] at hmem
    simp only [hnone, hik, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hmem
    simp_rw [bhDrvMirror_initiateOPK_cli] at hmem
    rcases bhRunInitiate_false_preserves_inv_cli hP hRel.ki_inv (.sendOPK u i) u bnd kr rfl hmem with
      ⟨rfl, rfl, rfl⟩ |
      ⟨hsecb, hspk, hresp, htested, htapes, hki, hbase, hcorr, hadv, hinsts, hmeta⟩
    · simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.initiateOPK u i bnd)
    · exact cliAdapterDrvRel_of_keyInd_step hRel (.initiateOPK u i bnd) kr
        (hsecb.trans hRel.st_rel.secb_cli)
        (by rw [hspk]; exact hRel.st_rel.spkBundles_rel)
        (fun s hs ht => by
          rw [hspk]
          exact hRel.st_rel.tested_spkRevealed s (htested s hs ht) ht)
        (by rw [hresp]; exact hRel.st_rel.resp_not_tested)
        hki
        (hbase.trans (bhBaseMirror_initiateOPK_cli ds_cli u i bnd kr))
        hcorr hadv hinsts hmeta
        (fun h => cliAdapterInstRel_of_st_ds_unchanged h htapes hspk)
  | initiateNoOPK u i bnd =>
    simp only [bhDrvKiQueryOk, Bool.and_eq_true] at hOk
    rcases hOk with ⟨hopk, hik⟩
    have hsome : bnd.opkB?.isSome = false := by
      rcases hopk' : bnd.opkB? with _ | _
      · rfl
      · rw [hopk'] at hopk; cases hopk
    unfold bhDrvKeyInd at hmem
    rw [stateT_run_get_bind_cli] at hmem
    simp only [hsome, hik, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hmem
    simp_rw [bhDrvMirror_initiateNoOPK_cli] at hmem
    rcases bhRunInitiate_false_preserves_inv_cli hP hRel.ki_inv (.sendNoOPK u i) u bnd kr rfl hmem with
      ⟨rfl, rfl, rfl⟩ |
      ⟨hsecb, hspk, hresp, htested, htapes, hki, hbase, hcorr, hadv, hinsts, hmeta⟩
    · simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.initiateNoOPK u i bnd)
    · exact cliAdapterDrvRel_of_keyInd_step hRel (.initiateNoOPK u i bnd) kr
        (hsecb.trans hRel.st_rel.secb_cli)
        (by rw [hspk]; exact hRel.st_rel.spkBundles_rel)
        (fun s hs ht => by
          rw [hspk]
          exact hRel.st_rel.tested_spkRevealed s (htested s hs ht) ht)
        (by rw [hresp]; exact hRel.st_rel.resp_not_tested)
        hki
        (hbase.trans (bhBaseMirror_initiateNoOPK_cli ds_cli u i bnd kr))
        hcorr hadv hinsts hmeta
        (fun h => cliAdapterInstRel_of_st_ds_unchanged h htapes hspk)
  | acceptOPK k j o hdr =>
    simp only [bhDrvKiQueryOk] at hOk
    unfold bhDrvKeyInd at hmem
    rw [stateT_run_get_bind_cli] at hmem
    simp only [hOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem
    obtain ⟨hm, rfl⟩ := mem_support_lift_modify_bhDrvMirror_cli _ _ _ _ hmem
    dsimp only [SignalPqxdh.pqxdhKeyIndImpl] at hm
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hm
    split_ifs at hm with hc1 hc2 hc3
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptOPK k j o hdr)
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptOPK k j o hdr)
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptOPK k j o hdr)
    · rcases hf1 : st_cli.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
      · simp only [hf1, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptOPK k j o hdr)
      · simp only [hf1] at hm
        rcases hf2 : st_cli.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bEntry⟩
        · simp only [hf2, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩
          simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptOPK k j o hdr)
        · simp only [hf2] at hm
          rcases hf3 : st_cli.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with _ | ⟨_, oEntry⟩
          · simp only [hf3, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
            rcases hm with ⟨rfl, rfl⟩
            simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptOPK k j o hdr)
          · simp only [hf3] at hm
            by_cases hcons : oEntry.consumed = true
            · simp only [hcons, ↓reduceIte, StateT.run_pure, support_pure,
                Set.mem_singleton_iff, Prod.mk.injEq] at hm
              rcases hm with ⟨rfl, rfl⟩
              simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptOPK k j o hdr)
            · simp only [Bool.not_eq_true] at hcons
              simp only [hcons, Bool.false_eq_true, ↓reduceIte] at hm
              rcases hacc : SignalPqxdh.Model.acceptKeys P _ with _ | dkAcc
              · rw [hacc] at hm
                simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
                rcases hm with ⟨rfl, rfl⟩
                simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptOPK k j o hdr)
              · rw [hacc] at hm; dsimp only at hm
                rcases hdec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss
                · rw [hdec] at hm
                  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
                  rcases hm with ⟨rfl, rfl⟩
                  simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptOPK k j o hdr)
                · rw [hdec] at hm; dsimp only at hm
                  simp only [stateT_monadLift_run_cli, StateT.run_bind, StateT.run_set,
                    bind_assoc, pure_bind, support_bind, Set.mem_iUnion] at hm
                  rcases hm with ⟨⟨drKey, roCache'⟩, hro, ⟨u, st₂⟩, hrec, hm⟩
                  dsimp only at hrec hm
                  obtain ⟨hreal_eq, hro_eq⟩ := mem_support_evalHkdfOrRo_false_cli P st_cli.roCache _ hro
                  have hreal : drKey.rootKey.length = 32 ∧ drKey.chainKey.length = 32 ∧
                      drKey.pqrKey.length = 32 := by
                    rw [hreal_eq]; exact hkdfDerive96_lengths_of_wf_cli hP _
                  obtain ⟨drKeyRand, hrand, hst₂⟩ :=
                    mem_support_recordKeyIndResp_cli hrec hRel.ki_inv.sessions_wf
                  have hkr_eq : st_cli' = st₂ := by
                    rcases hFHP : SignalPqxdh.findHonestPrincipal P st_cli.principals hdr.ikAPk with _ | _ <;>
                      rw [hFHP] at hm <;>
                      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm <;>
                      exact hm.2
                  rw [hkr_eq, hst₂]
                  refine cliAdapterDrvRel_of_keyInd_step hRel (.acceptOPK k j o hdr) kr
                    hRel.st_rel.secb_cli
                    hRel.st_rel.spkBundles_rel
                    hRel.st_rel.tested_spkRevealed
                    (fun r hr => by
                      rcases List.mem_cons.mp hr with rfl | htl
                      · rfl
                      · exact hRel.st_rel.resp_not_tested r htl)
                    (cliAdapterKeyIndInv_of_accept hRel.ki_inv _
                      (fun _ _ h => mem_opkEntries_map_consumed_cli h)
                      (fun _ _ h => exists_mem_opkEntries_map_consumed_cli (k.val, j.val, o.val) h)
                      _ drKeyRand hreal hrand roCache' (hro_eq.trans hRel.ki_inv.roCache_nil) _ _ _)
                    rfl rfl rfl rfl rfl
                    (fun h => cliAdapterInstRel_of_st_ds_unchanged h (fun _ hx => hx) rfl)
  | acceptNoOPK k j l hdr =>
    simp only [bhDrvKiQueryOk] at hOk
    unfold bhDrvKeyInd at hmem
    rw [stateT_run_get_bind_cli] at hmem
    simp only [hOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem
    obtain ⟨hm, rfl⟩ := mem_support_lift_modify_bhDrvMirror_cli _ _ _ _ hmem
    dsimp only [SignalPqxdh.pqxdhKeyIndImpl] at hm
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hm
    split_ifs at hm with hc1 hc2 hc3
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptNoOPK k j l hdr)
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptNoOPK k j l hdr)
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptNoOPK k j l hdr)
    · rcases hf1 : st_cli.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
      · simp only [hf1, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptNoOPK k j l hdr)
      · simp only [hf1] at hm
        rcases hf2 : st_cli.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bEntry⟩
        · simp only [hf2, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩
          simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptNoOPK k j l hdr)
        · simp only [hf2] at hm
          rcases hacc : SignalPqxdh.Model.acceptKeys P _ with _ | dkAcc
          · rw [hacc] at hm
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
            rcases hm with ⟨rfl, rfl⟩
            simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptNoOPK k j l hdr)
          · rw [hacc] at hm; dsimp only at hm
            rcases hdec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss
            · rw [hdec] at hm
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
              rcases hm with ⟨rfl, rfl⟩
              simpa using cliAdapterDrvRel_of_keyInd_noneResp hRel (.acceptNoOPK k j l hdr)
            · rw [hdec] at hm; dsimp only at hm
              simp only [stateT_monadLift_run_cli, StateT.run_bind, StateT.run_set,
                bind_assoc, pure_bind, support_bind, Set.mem_iUnion] at hm
              rcases hm with ⟨⟨drKey, roCache'⟩, hro, ⟨u, st₂⟩, hrec, hm⟩
              dsimp only at hrec hm
              obtain ⟨hreal_eq, hro_eq⟩ := mem_support_evalHkdfOrRo_false_cli P st_cli.roCache _ hro
              have hreal : drKey.rootKey.length = 32 ∧ drKey.chainKey.length = 32 ∧
                  drKey.pqrKey.length = 32 := by
                rw [hreal_eq]; exact hkdfDerive96_lengths_of_wf_cli hP _
              obtain ⟨drKeyRand, hrand, hst₂⟩ :=
                mem_support_recordKeyIndResp_cli hrec hRel.ki_inv.sessions_wf
              have hkr_eq : st_cli' = st₂ := by
                rcases hFHP : SignalPqxdh.findHonestPrincipal P st_cli.principals hdr.ikAPk with _ | _ <;>
                  rw [hFHP] at hm <;>
                  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm <;>
                  exact hm.2
              rw [hkr_eq, hst₂]
              refine cliAdapterDrvRel_of_keyInd_step hRel (.acceptNoOPK k j l hdr) kr
                hRel.st_rel.secb_cli
                hRel.st_rel.spkBundles_rel
                hRel.st_rel.tested_spkRevealed
                (fun r hr => by
                  rcases List.mem_cons.mp hr with rfl | htl
                  · rfl
                  · exact hRel.st_rel.resp_not_tested r htl)
                (cliAdapterKeyIndInv_of_accept hRel.ki_inv st_cli.opkEntries
                  (fun _ o' h => ⟨o', h, rfl, rfl⟩)
                  (fun _ o h => ⟨o, h, rfl⟩)
                  _ drKeyRand hreal hrand roCache' (hro_eq.trans hRel.ki_inv.roCache_nil) _ _ _)
                rfl rfl rfl rfl rfl
                (fun h => cliAdapterInstRel_of_st_ds_unchanged h (fun _ hx => hx) rfl)

/-- Single-step coupling for 1-key real-HKDF `KeyInd` queries `.inl (.inl (.inr kq))` between
`bhDrvKeyInd S ℓ (modelPrims X W) false` and `cliComposedAdapterImplWith` over
`SignalPqxdh.pqxdhKeyIndImpl1KeyReal`. -/
theorem cliDrvKeyInd_adapter_coupling_step {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (kq : SignalPqxdh.KeyIndQuery S) :
    cliAdapterStepCoupled X W b qStart qs_rem
      (((bhDrvKeyInd S ℓ (modelPrims X W) false kq).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W)
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S (modelPrims X W))
          W.C W.Q.K qep decT encT (Sum.inl (Sum.inl (Sum.inr kq)))).run σ_ad).run σ_e2e) := by
  set P := modelPrims X W
  rw [cliComposedAdapterImplWith_keyInd_run]
  have hOk_e2e : bhDrvKiQueryOk P σ_e2e.toModelDriverBase kq = bhDrvKiQueryOk P ds_cli.toModelDriverBase kq := by
    rw [← hRel.base_e2e_eq]
  rw [hOk_e2e]
  by_cases hOk : bhDrvKiQueryOk P ds_cli.toModelDriverBase kq = true
  · simp only [hOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hProm_e2e :
        cliKiNoOpkCorrupt σ_e2e.instMeta kq = cliKiNoOpkCorrupt ds_cli.instMeta kq := by
      rw [hRel.instMeta_eq]
    rw [hProm_e2e]
    by_cases hNoProm : cliKiNoOpkCorrupt ds_cli.instMeta kq = false
    · simp only [hNoProm, Bool.false_eq_true, ↓reduceIte]
      refine cliAdapterStepCoupled_of_proj
        (((bhDrvKeyInd S ℓ P false kq).run ds_cli).run st_cli)
        ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st_cli)
        (fun (kr, st_cli') =>
          ((kr, (σ_ad.1, σ_ad.2.1, bhBaseMirror σ_ad.2.2 kq kr)),
           bhE2EMirror
             { σ_e2e with
               st := cliReplaceSpkBundles st_cli'
                 (cliUpdateSpkBundlesForQuery kq σ_e2e.st.spkBundles kr st_cli') }
             kq kr))
        _
        (cliDrvKeyInd_proj_deq hRel.ki_inv kq hOk hNoProm)
        ?_
        (fun x hx => ⟨rfl, cliDrvKeyInd_preserves_rel hP hRel kq hOk x.1.1 hx⟩)
      rw [eq_cliReplaceSpkBundles_of_cliKeyIndStateRel hRel.st_rel,
          pqxdhKeyIndImpl1KeyReal_run_cliReplaceSpkBundles P kq st_cli σ_e2e.st.spkBundles
            hRel.st_rel.spkBundles_rel]
      simp only [bind_assoc, pure_bind]
      exact CryptoGames.Lazy.DEq.refl _
    · simp only [Bool.not_eq_false] at hNoProm
      simp only [hNoProm, ↓reduceIte, bhBaseMirror_noneResp_cli]
      have h_cli : (((bhDrvKeyInd S ℓ P false kq).run ds_cli).run st_cli) =
          pure ((.noneResp, ds_cli), st_cli) := by
        cases kq with
        | corruptIK u =>
          dsimp only [cliKiNoOpkCorrupt] at hNoProm
          unfold bhDrvKeyInd
          rw [stateT_run_get_bind_cli]
          simp [hNoProm]
        | testSession _ | revealDhSecrets | initPrin _ | genSPK _ _ | genOPK _ _ _
        | initiateOPK _ _ _ | initiateNoOPK _ _ _ | acceptOPK _ _ _ _ | acceptNoOPK _ _ _ _
        | revealSessionKey _ | registerKey _ | revealSpkSk _ _ | roQuery _ =>
          simp [cliKiNoOpkCorrupt] at hNoProm
      rw [h_cli]
      exact cliAdapterStepCoupled_ret SignalPqxdh.KeyIndResponse.noneResp st_cli ds_cli σ_ad σ_e2e hRel
  · simp only [Bool.not_eq_true] at hOk
    simp only [hOk, Bool.not_false, ↓reduceIte, bhBaseMirror_noneResp_cli]
    have h_cli : (((bhDrvKeyInd S ℓ P false kq).run ds_cli).run st_cli) =
        pure ((.noneResp, ds_cli), st_cli) := by
      cases kq with
      | testSession _ | revealDhSecrets => rfl
      | initiateOPK u i bnd =>
        simp only [bhDrvKiQueryOk, Bool.and_eq_false_imp] at hOk
        unfold bhDrvKeyInd
        rw [stateT_run_get_bind_cli]
        rcases hopk : bnd.opkB? with _ | _
        · simp
        · have hik := hOk (by rw [hopk]; rfl)
          simp [hik]
      | initiateNoOPK u i bnd =>
        simp only [bhDrvKiQueryOk, Bool.and_eq_false_imp] at hOk
        unfold bhDrvKeyInd
        rw [stateT_run_get_bind_cli]
        rcases hopk : bnd.opkB? with _ | _
        · have hik := hOk (by rw [hopk]; rfl)
          simp [hik]
        · simp
      | acceptOPK k j o hdr =>
        simp only [bhDrvKiQueryOk] at hOk
        unfold bhDrvKeyInd
        rw [stateT_run_get_bind_cli]
        simp [hOk]
      | acceptNoOPK k j l hdr =>
        simp only [bhDrvKiQueryOk] at hOk
        unfold bhDrvKeyInd
        rw [stateT_run_get_bind_cli]
        simp [hOk]
      | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | revealSessionKey _
      | registerKey _ | revealSpkSk _ _ | roQuery _ =>
        simp [bhDrvKiQueryOk] at hOk
    rw [h_cli]
    exact cliAdapterStepCoupled_ret SignalPqxdh.KeyIndResponse.noneResp st_cli ds_cli σ_ad σ_e2e hRel

/-- Discharges `CliKeyIndStepBridgeProp`. -/
theorem cliKeyIndStepBridgeProp_holds {Pt : Type}
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CliKeyIndStepBridgeProp S ℓ X W qep decT encT := by
  intro _ _ _ _ _ _ _ hRel _ _ kq
  exact cliDrvKeyInd_adapter_coupling_step hP hRel kq

end CryptoVerification.E2E
