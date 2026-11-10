/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.LocalSessionStepAux

/-!
# Local Double Ratchet Session-Step `ReductionDsl` Handlers

Bridges `bhE2EStepLocalSm` to an arbitrary `DrSessionSimIface` over `e2eOps` and `stepAIface`,
instantiating `LocalSessionStepIface` (`localSessionStepIface`) with linear state-scan cost bounds,
zero-target-query lemmas, exact `Comp.eval` equivalence, and `SmReachBounded` / `DrvSmReachInv`
preservation.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.LocalSessionStep

open Classical
open OracleSpec OracleComp

open ReductionDsl (Ty Var Expr Comp Iface Env)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (GameState)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes ModelDriverInstanceMeta BHModelInst BHE2EDrvState BHE2ESmResp
  bhDrvSessionInitPrin? bhIsBobRecvSMQuery bhIsBobAcceptSMResp bhPackSmResp
  bhE2EDrvInstClean bhE2EInstIkACorr bhE2EStepLocalSm
  paramsIdsWithSpqr sessionSchemeFixedSpk configRefuseEarlyBobCorr)
open CryptoVerification.E2E.Costed (E2EPureOp e2eSig e2eOps PB FinT GhostStT
  hdrV sidT sidV sidOfV smQT smQenc smRT)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp eval_e2ePureOp cost_e2ePureOp
  hdrOfV_hdrV sidOfV_sidV)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext stepAIface v ext_refl_wk ext_step_wk
  eval_v_refl env_get_zero env_get_succ exprCostUB_v
  eLet eCaseOpt eCaseSum eAny letV bindV caseOptV
  exprCostUB_eLet exprCostUB_eCaseOpt exprCostUB_eCaseSum exprCostUB_eAny
  orE eval_orE isSomeE eval_isSomeE liftP_pure liftP_bind)
open Computational.Proofs.E2E.Dsl.SmReachInv (SmReachBounded DrvSmReachInv
  smReachBounded_oracleImplR drvSmReachInv_bhE2EStepLocalSm)
open Computational.Proofs.E2E.Dsl.M2Interfaces (DrSessionSimIface e2eGsEnc smQdec_smQenc)
open Computational.Proofs.E2E.Dsl.M3Interfaces (e2eMirrorPrinEntryTy e2eMirrorBaseEnc
  e2eInstMetaTy e2eInstMetaEnc e2eInstMetaDec_e2eInstMetaEnc e2eModelInstTy e2eModelInstEnc
  e2eDrvStateTy e2eDrvStateEnc packSmRespEnc unpackSmRespDec
  smRenc_id_eq_packSmRespEnc smRdec_id_packSmRespEnc
  DrvMetaAligned DrvSessionsBounded bhE2EStepLocalSm_preserves LocalSessionStepIface
  respNotRevealedE eval_respNotRevealedE cost_respNotRevealedE)
open Computational.Proofs.E2E.Dsl.LocalSessionStepAux (bhFilterLocalSmQuery
  bhE2EStepLocalSm_eq_filtered emptySmRespE eval_emptySmRespE cost_emptySmRespE
  instSlotTy defaultE2eGsVal defaultInstSlotVal defaultE2eGsE eval_defaultE2eGsE cost_defaultE2eGsE
  instSlotOfModelInst encodeInstTbl tset_encodeInstTbl
  e2eInstHdrMetaTy e2eInstHdrMetaEnc encodeHdrMetaList
  zip_getElem_eq zip_set_both zip_all_and not_any_not_eq_all
  listGetOptE eval_listGetOptE cost_listGetOptE listSetE eval_listSetE cost_listSetE
  exprCostUB_e2ePureOp cost_eLet_le initPrinOptE eval_initPrinOptVal
  isBobRecvSmQueryE eval_isBobRecvSmQueryVal cost_isBobRecvSmQueryE
  isBobAcceptSmRespE eval_isBobAcceptSmRespE cost_isBobAcceptSmRespE
  setInstMetaAcceptE eval_setInstMetaAcceptVal cost_setInstMetaAcceptE
  filterLocalSmQueryE eval_filterLocalSmQueryVal cost_filterLocalSmQueryE)
open Computational.Proofs.GameHop.ReductionDsl.CostUB (exprCostUB)
open SignalPqxdh (Setup Primitives)

export M3Interfaces (packSmRespEnc unpackSmRespDec smRenc_id_eq_packSmRespEnc
  smRdec_id_packSmRespEnc bhE2EStepLocalSm_preserves)
export LocalSessionStepAux (emptySmRespE instSlotTy defaultE2eGsVal defaultInstSlotVal
  instSlotOfModelInst)
export LocalSessionStepAux (encodeInstTbl tset_encodeInstTbl e2eInstHdrMetaTy e2eInstHdrMetaEnc
  encodeHdrMetaList)
export LocalSessionStepAux (bhFilterLocalSmQuery bhE2EStepLocalSm_eq_filtered)

/-! ## Driver-state expressions -/

section DriverExprs

variable {ℓ : ℕ} {S : Setup} {Pt : Type} {P : Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "Ops'" => e2eOps ℓ P C K decT encT

private theorem foldr_corrTbl_eval :
    ∀ (xs : List (Fin S.N_id)) (j : ℕ),
      xs.foldr (fun (x : Fin S.N_id) (tbl : ℕ → Bool) (k : ℕ) =>
        if k = x.val then true else tbl k) (fun _ => false) j =
        xs.any (fun x => decide (j = x.val))
  | [], _ => rfl
  | x :: rest, j => by
    dsimp only [List.foldr_cons, List.any_cons]
    by_cases hj : j = x.val
    · simp only [hj, ↓reduceIte, decide_true, Bool.true_or]
    · simp only [hj, ↓reduceIte, decide_false, Bool.false_or, foldr_corrTbl_eval rest j]

def corrTblOfListE (nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (corrPrinsE : Expr Ops' Γ (.list (FinT S.N_id))) : Expr Ops' Γ (.tbl .bool) :=
  .foldrB nCorr corrPrinsE (.tconst (.bool false))
    (.tset .v1 (e2ePureOp (.finVal S.N_id) .v0) (.bool true))

theorem eval_corrTblOfListE_apply (nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (corrPrinsE : Expr Ops' Γ (.list (FinT S.N_id)))
    (ρ : Env Γ) (cp : List (Fin S.N_id)) (hcp : corrPrinsE.eval ρ = cp)
    (hlen : cp.length ≤ nCorr) (u : Fin S.N_id) :
    (corrTblOfListE nCorr corrPrinsE).eval ρ u.val = cp.contains u := by
  have htake : cp.take nCorr = cp := List.take_of_length_le hlen
  change List.foldr (fun (x : Fin S.N_id) (tbl : ℕ → Bool) (k : ℕ) =>
    if k = x.val then true else tbl k) (fun _ => false)
    ((corrPrinsE.eval ρ).take nCorr) u.val = cp.contains u
  rw [hcp, htake, foldr_corrTbl_eval cp u.val, List.contains_eq_any_beq]
  apply List.any_congr rfl; intro x
  by_cases hx : u = x
  · subst hx; simp
  · have hval : u.val ≠ x.val := fun hv => hx (Fin.ext hv)
    simp [hval, hx]

theorem cost_corrTblOfListE (nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (corrPrinsE : Expr Ops' Γ (.list (FinT S.N_id))) :
    (corrTblOfListE nCorr corrPrinsE).cost ≤ corrPrinsE.cost + 136 * nCorr + 4 := by
  dsimp only [corrTblOfListE, Expr.v0, Expr.v1, Expr.cost, cost_e2ePureOp, E2EPureOp.cost]; omega

def instIkACorrTblE (nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (sidE : Expr Ops' Γ (sidT S)) (ikAPkE : Expr Ops' Γ (PB 32))
    (corrTblE : Expr Ops' Γ (.tbl .bool))
    (prinsE : Expr Ops' Γ (.list (e2eMirrorPrinEntryTy S))) : Expr Ops' Γ .bool :=
  eLet (.pair sidE (.pair ikAPkE (.pair corrTblE prinsE))) fun args =>
    eLet (.fst (v args)) fun s => eLet (.fst (.snd (v args))) fun ik =>
    eLet (.fst (.snd (.snd (v args)))) fun ct => eLet (.snd (.snd (.snd (v args)))) fun pr =>
      orE (eCaseOpt (initPrinOptE (v s)) (.bool true)
            (fun u => .tget (v ct) (e2ePureOp (.finVal S.N_id) (v u))))
        (eAny nPrins (v pr) fun pe =>
          .and (e2ePureOp (.pbytesEq 32 32) (.pair (.snd (v pe)) (v ik)))
            (.tget (v ct) (e2ePureOp (.finVal S.N_id) (.fst (v pe)))))

theorem eval_instIkACorrTblE (nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (sidE : Expr Ops' Γ (sidT S)) (ikAPkE : Expr Ops' Γ (PB 32))
    (corrTblE : Expr Ops' Γ (.tbl .bool)) (prinsE : Expr Ops' Γ (.list (e2eMirrorPrinEntryTy S)))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (d : BHModelInst S ℓ)
    (hsid : sidE.eval ρ = sidV d.sid) (hik : ikAPkE.eval ρ = d.hdr.ikAPk)
    (hct : ∀ u : Fin S.N_id, corrTblE.eval ρ u.val = σ.corrPrins.contains u)
    (hpr : prinsE.eval ρ = σ.prins) (hprLen : σ.prins.length ≤ nPrins) :
    (instIkACorrTblE nPrins sidE ikAPkE corrTblE prinsE).eval ρ = bhE2EInstIkACorr σ d := by
  have htakePr : σ.prins.take nPrins = σ.prins := List.take_of_length_le hprLen
  unfold instIkACorrTblE
  simp only [eLet, eval_orE, eCaseOpt, eAny, v, ext_refl_wk, ext_step_wk, Expr.eval,
    eval_initPrinOptVal, env_get_zero, env_get_succ, eval_e2ePureOp, E2EPureOp.eval,
    hsid, hik, hpr, htakePr, sidOfV_sidV, bhE2EInstIkACorr]
  congr 1
  · cases bhDrvSessionInitPrin? d.sid with | none => rfl | some u => exact hct u
  · apply List.any_congr rfl; rintro ⟨u, _⟩; rw [hct u]

theorem cost_instIkACorrTblE (nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (sidE : Expr Ops' Γ (sidT S)) (ikAPkE : Expr Ops' Γ (PB 32))
    (corrTblE : Expr Ops' Γ (.tbl .bool)) (prinsE : Expr Ops' Γ (.list (e2eMirrorPrinEntryTy S))) :
    (instIkACorrTblE nPrins sidE ikAPkE corrTblE prinsE).cost ≤
      sidE.cost + ikAPkE.cost + corrTblE.cost + prinsE.cost + 160 * nPrins + 140 := by
  unfold instIkACorrTblE
  refine Nat.le_trans (cost_eLet_le (.pair sidE (.pair ikAPkE (.pair corrTblE prinsE))) _
    (c := 160 * nPrins + 135) ?_) ?_
  · simp only [orE, initPrinOptE, exprCostUB_eLet, exprCostUB_eCaseOpt, exprCostUB_eCaseSum,
      exprCostUB_eAny, exprCostUB_v, exprCostUB, exprCostUB_e2ePureOp, E2EPureOp.cost,
      PNat.val_ofNat]; omega
  · simp only [Expr.cost]; omega

def instIkACorrListE (nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (sidE : Expr Ops' Γ (sidT S)) (ikAPkE : Expr Ops' Γ (PB 32))
    (corrPrinsE : Expr Ops' Γ (.list (FinT S.N_id)))
    (prinsE : Expr Ops' Γ (.list (e2eMirrorPrinEntryTy S))) : Expr Ops' Γ .bool :=
  instIkACorrTblE nPrins sidE ikAPkE (corrTblOfListE nCorr corrPrinsE) prinsE

theorem eval_instIkACorrListE (nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (sidE : Expr Ops' Γ (sidT S)) (ikAPkE : Expr Ops' Γ (PB 32))
    (corrPrinsE : Expr Ops' Γ (.list (FinT S.N_id)))
    (prinsE : Expr Ops' Γ (.list (e2eMirrorPrinEntryTy S)))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (d : BHModelInst S ℓ)
    (hsid : sidE.eval ρ = sidV d.sid) (hik : ikAPkE.eval ρ = d.hdr.ikAPk)
    (hcp : corrPrinsE.eval ρ = σ.corrPrins) (hpr : prinsE.eval ρ = σ.prins)
    (hcpLen : σ.corrPrins.length ≤ nCorr) (hprLen : σ.prins.length ≤ nPrins) :
    (instIkACorrListE nCorr nPrins sidE ikAPkE corrPrinsE prinsE).eval ρ = bhE2EInstIkACorr σ d :=
  eval_instIkACorrTblE nPrins sidE ikAPkE (corrTblOfListE nCorr corrPrinsE) prinsE ρ σ d
    hsid hik (eval_corrTblOfListE_apply nCorr corrPrinsE ρ σ.corrPrins hcp hcpLen) hpr hprLen

theorem cost_instIkACorrListE (nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (sidE : Expr Ops' Γ (sidT S)) (ikAPkE : Expr Ops' Γ (PB 32))
    (corrPrinsE : Expr Ops' Γ (.list (FinT S.N_id)))
    (prinsE : Expr Ops' Γ (.list (e2eMirrorPrinEntryTy S))) :
    (instIkACorrListE nCorr nPrins sidE ikAPkE corrPrinsE prinsE).cost ≤
      sidE.cost + ikAPkE.cost + corrPrinsE.cost + prinsE.cost + 140 * nCorr + 160 * nPrins + 150 := by
  unfold instIkACorrListE
  have h1 := cost_instIkACorrTblE nPrins sidE ikAPkE (corrTblOfListE nCorr corrPrinsE) prinsE
  have h2 := cost_corrTblOfListE nCorr corrPrinsE
  omega

/-- Evaluates per-instance cleanliness `bhE2EDrvInstClean σ i` (`DEV-C17`) over `e2eDrvStateTy`. -/
def drvInstCleanDrvStateE (qStart nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (revE : Expr Ops' Γ (.list (.prod (FinT S.N_id) (FinT S.N_recv))))
    (instsE : Expr Ops' Γ (.list (e2eModelInstTy S ℓ)))
    (instMetaE : Expr Ops' Γ (.list (e2eInstMetaTy S ℓ))) (ixE : Expr Ops' Γ .nat) :
    Expr Ops' Γ .bool :=
  eLet (.pair revE (.pair instsE (.pair instMetaE ixE))) fun args =>
    eCaseOpt (listGetOptE qStart (.fst (.snd (v args))) (.snd (.snd (.snd (v args)))))
      (.bool true) fun d =>
      eCaseOpt (listGetOptE qStart (.fst (.snd (.snd (v args)))) (.snd (.snd (.snd (v args)))))
        (.bool true) fun im =>
        .and (.and (isSomeE (initPrinOptE (.fst (v d)))) (.not (.fst (.snd (v im)))))
          (respNotRevealedE nCorr (v im) (.fst (v args)))

set_option linter.unusedSimpArgs false in
theorem eval_drvInstCleanDrvStateE (qStart nCorr : ℕ) (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (hinstLen : σ.insts.length ≤ qStart) (hmetaLen : σ.instMeta.length ≤ qStart)
    (hrevLen : σ.revealedSpks.length ≤ nCorr)
    {Γ : List (Ty (e2eSig ℓ))}
    {revE : Expr Ops' Γ (.list (.prod (FinT S.N_id) (FinT S.N_recv)))}
    {instsE : Expr Ops' Γ (.list (e2eModelInstTy S ℓ))}
    {instMetaE : Expr Ops' Γ (.list (e2eInstMetaTy S ℓ))} {ixE : Expr Ops' Γ .nat} {ρ : Env Γ}
    (hrev : revE.eval ρ = σ.revealedSpks)
    (hinsts : instsE.eval ρ = σ.insts.map (e2eModelInstEnc (ℓ := ℓ)))
    (hmetas : instMetaE.eval ρ = σ.instMeta.map (e2eInstMetaEnc (ℓ := ℓ)))
    (hix : ixE.eval ρ = i) :
    (drvInstCleanDrvStateE qStart nCorr revE instsE instMetaE ixE).eval ρ =
      bhE2EDrvInstClean σ i := by
  have hI : (σ.insts.map (e2eModelInstEnc (ℓ := ℓ))).length ≤ qStart := by simp [hinstLen]
  have hM : (σ.instMeta.map (e2eInstMetaEnc (ℓ := ℓ))).length ≤ qStart := by simp [hmetaLen]
  unfold drvInstCleanDrvStateE bhE2EDrvInstClean
  simp only [eLet, eCaseOpt, Expr.eval]
  rw [eval_listGetOptE qStart _ _ _ (by simpa [v, Ext.wk, Expr.eval, Env.get, eval_v_refl,
    env_get_zero, hinsts] using hI)]
  simp only [v, Ext.wk, Expr.eval, Env.get, eval_v_refl, env_get_zero, hinsts, hix,
    List.getElem?_map]
  rcases hd : σ.insts[i]? with _ | d
  · rfl
  · simp only [Option.map]
    rw [eval_listGetOptE qStart _ _ _ (by simpa [v, Ext.wk, Expr.eval, Env.get, eval_v_refl,
      env_get_zero, hmetas] using hM)]
    simp only [v, Ext.wk, Expr.eval, Env.get, eval_v_refl, env_get_zero, hmetas, hix,
      List.getElem?_map]
    rcases him : σ.instMeta[i]? with _ | im
    · rfl
    · simp only [Option.map, Expr.eval, eval_isSomeE, eval_initPrinOptVal, v, Ext.wk, Env.get,
        eval_v_refl, env_get_zero, e2eModelInstEnc, e2eInstMetaEnc, sidOfV_sidV]
      rw [eval_respNotRevealedE nCorr _ _ _ (im := im) (revSpks := σ.revealedSpks)
        (by simp [v, Ext.wk, Expr.eval, Env.get, eval_v_refl, env_get_zero, e2eInstMetaEnc])
        (by simp [v, Ext.wk, Expr.eval, Env.get, eval_v_refl, env_get_zero, hrev]) hrevLen]
      rfl

theorem cost_drvInstCleanDrvStateE (qStart nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (revE : Expr Ops' Γ (.list (.prod (FinT S.N_id) (FinT S.N_recv))))
    (instsE : Expr Ops' Γ (.list (e2eModelInstTy S ℓ)))
    (instMetaE : Expr Ops' Γ (.list (e2eInstMetaTy S ℓ))) (ixE : Expr Ops' Γ .nat) :
    (drvInstCleanDrvStateE qStart nCorr revE instsE instMetaE ixE).cost ≤
      revE.cost + instsE.cost + instMetaE.cost + ixE.cost + 64 * qStart + 20 * nCorr + 140 := by
  let τp : Ty (e2eSig ℓ) := .prod (.list (.prod (FinT S.N_id) (FinT S.N_recv)))
    (.prod (.list (e2eModelInstTy S ℓ)) (.prod (.list (e2eInstMetaTy S ℓ)) .nat))
  have hg1 := cost_listGetOptE (ℓ := ℓ) (O := Ops') qStart (Γ := τp :: Γ)
    (.fst (.snd (.var .zero))) (.snd (.snd (.snd (.var .zero))))
  have hg2 := cost_listGetOptE (ℓ := ℓ) (O := Ops') qStart
    (Γ := e2eModelInstTy S ℓ :: τp :: Γ)
    (.fst (.snd (.snd (.var (.succ .zero))))) (.snd (.snd (.snd (.var (.succ .zero)))))
  have hrn := cost_respNotRevealedE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr
    (Γ := e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ :: τp :: Γ)
    (.var .zero) (.fst (.var (.succ (.succ .zero))))
  dsimp only [τp] at hg1 hg2 hrn
  unfold drvInstCleanDrvStateE
  dsimp only [v, Ext.wk]
  simp only [isSomeE, initPrinOptE, eLet, eCaseOpt, eCaseSum, Expr.cost,
    Computational.Proofs.E2E.Dsl.PqxdhSimTypes.cost_v] at hg1 hg2 hrn ⊢
  omega

def tblSetSlotE {Γ : List (Ty (e2eSig ℓ))} (tblE : Expr Ops' Γ (.tbl (instSlotTy ℓ)))
    (idxE : Expr Ops' Γ .nat) (valE : Expr Ops' Γ (instSlotTy ℓ)) :
    Expr Ops' Γ (.tbl (instSlotTy ℓ)) :=
  .tset tblE idxE valE

private theorem eval_tblSetSlotE {Γ : List (Ty (e2eSig ℓ))}
    (tblE : Expr Ops' Γ (.tbl (instSlotTy ℓ))) (idxE : Expr Ops' Γ .nat)
    (valE : Expr Ops' Γ (instSlotTy ℓ)) (ρ : Env Γ)
    (insts : List (BHModelInst S ℓ)) (i : ℕ) (d' : BHModelInst S ℓ)
    (htbl : tblE.eval ρ = encodeInstTbl insts) (hidx : idxE.eval ρ = i)
    (hval : valE.eval ρ = instSlotOfModelInst d') (hi : i < insts.length) :
    (tblSetSlotE tblE idxE valE).eval ρ = encodeInstTbl (insts.set i d') := by
  simp only [tblSetSlotE, Expr.eval, hidx, hval, htbl]
  exact tset_encodeInstTbl insts i d' hi

private theorem cost_tblSetSlotE {Γ : List (Ty (e2eSig ℓ))}
    (tblE : Expr Ops' Γ (.tbl (instSlotTy ℓ))) (idxE : Expr Ops' Γ .nat)
    (valE : Expr Ops' Γ (instSlotTy ℓ)) :
    (tblSetSlotE tblE idxE valE).cost ≤ tblE.cost + idxE.cost + valE.cost + 128 :=
  Nat.le_refl _

def modelInstToHmE {Γ : List (Ty (e2eSig ℓ))}
    (dE : Expr Ops' Γ (e2eModelInstTy S ℓ)) (imE : Expr Ops' Γ (e2eInstMetaTy S ℓ)) :
    Expr Ops' Γ (e2eInstHdrMetaTy S ℓ) :=
  .letE (.pair dE imE) (.pair (.fst (.fst .v0)) (.pair (.fst (.snd (.fst .v0))) (.snd .v0)))

private theorem eval_modelInstToHmE {Γ : List (Ty (e2eSig ℓ))}
    (dE : Expr Ops' Γ (e2eModelInstTy S ℓ)) (imE : Expr Ops' Γ (e2eInstMetaTy S ℓ))
    (ρ : Env Γ) (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (hd : dE.eval ρ = e2eModelInstEnc d) (him : imE.eval ρ = e2eInstMetaEnc im) :
    (modelInstToHmE dE imE).eval ρ = e2eInstHdrMetaEnc d im := by
  simp [modelInstToHmE, Expr.v0, Expr.eval, env_get_zero, hd, him, e2eModelInstEnc, e2eInstHdrMetaEnc]

private theorem cost_modelInstToHmE {Γ : List (Ty (e2eSig ℓ))}
    (dE : Expr Ops' Γ (e2eModelInstTy S ℓ)) (imE : Expr Ops' Γ (e2eInstMetaTy S ℓ)) :
    (modelInstToHmE dE imE).cost ≤ dE.cost + imE.cost + 15 := by
  dsimp only [modelInstToHmE, Expr.v0, Expr.cost]; omega

def modelInstToSlotE {Γ : List (Ty (e2eSig ℓ))}
    (dE : Expr Ops' Γ (e2eModelInstTy S ℓ)) : Expr Ops' Γ (instSlotTy ℓ) :=
  .letE dE
    (let r2 := Expr.snd (.snd .v0)
     .pair (.fst r2) (.pair (.fst (.snd r2)) (.pair (.fst (.snd (.snd r2)))
       (.caseOpt (.snd (.snd (.snd r2))) (.pair (.bool true) defaultE2eGsE)
         (.pair (.bool false) .v0)))))

private theorem eval_modelInstToSlotE {Γ : List (Ty (e2eSig ℓ))}
    (dE : Expr Ops' Γ (e2eModelInstTy S ℓ)) (ρ : Env Γ) (d : BHModelInst S ℓ)
    (hd : dE.eval ρ = e2eModelInstEnc d) :
    (modelInstToSlotE dE).eval ρ = instSlotOfModelInst d := by
  cases hgs : d.gs <;>
    simp [modelInstToSlotE, Expr.v0, Expr.eval, env_get_zero, eval_defaultE2eGsE,
      hd, hgs, e2eModelInstEnc, instSlotOfModelInst]

private theorem cost_modelInstToSlotE {Γ : List (Ty (e2eSig ℓ))}
    (dE : Expr Ops' Γ (e2eModelInstTy S ℓ)) : (modelInstToSlotE dE).cost ≤ dE.cost + 380 := by
  dsimp only [modelInstToSlotE, Expr.v0, Expr.cost]
  have hdef := cost_defaultE2eGsE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := e2eModelInstTy S ℓ :: Γ)
  omega

def slotHmToModelInstE {Γ : List (Ty (e2eSig ℓ))}
    (hmE : Expr Ops' Γ (e2eInstHdrMetaTy S ℓ)) (slE : Expr Ops' Γ (instSlotTy ℓ)) :
    Expr Ops' Γ (e2eModelInstTy S ℓ) :=
  .letE (.pair hmE slE)
    (let hm := Expr.fst .v0; let sl := Expr.snd .v0; let pfGs := Expr.snd (.snd (.snd sl))
     .pair (.fst hm) (.pair (.fst (.snd hm)) (.pair (.fst sl) (.pair (.fst (.snd sl))
       (.pair (.fst (.snd (.snd sl))) (.ite (.fst pfGs) .none (.some (.snd pfGs))))))))

private theorem eval_slotHmToModelInstE {Γ : List (Ty (e2eSig ℓ))}
    (hmE : Expr Ops' Γ (e2eInstHdrMetaTy S ℓ)) (slE : Expr Ops' Γ (instSlotTy ℓ))
    (ρ : Env Γ) (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (hhm : hmE.eval ρ = e2eInstHdrMetaEnc d im) (hsl : slE.eval ρ = instSlotOfModelInst d) :
    (slotHmToModelInstE hmE slE).eval ρ = e2eModelInstEnc d := by
  cases hgs : d.gs <;>
    simp [slotHmToModelInstE, Expr.v0, Expr.eval, env_get_zero, hhm, hsl, hgs,
      e2eInstHdrMetaEnc, instSlotOfModelInst, e2eModelInstEnc]

private theorem cost_slotHmToModelInstE {Γ : List (Ty (e2eSig ℓ))}
    (hmE : Expr Ops' Γ (e2eInstHdrMetaTy S ℓ)) (slE : Expr Ops' Γ (instSlotTy ℓ)) :
    (slotHmToModelInstE hmE slE).cost ≤ hmE.cost + slE.cost + 45 := by
  dsimp only [slotHmToModelInstE, Expr.v0, Expr.cost]; omega

attribute [local irreducible] corrTblOfListE instIkACorrTblE instIkACorrListE
  drvInstCleanDrvStateE tblSetSlotE modelInstToHmE modelInstToSlotE slotHmToModelInstE

end DriverExprs

/-! ## Slot, instance, and driver step handlers -/

section StepHandlers

variable {ℓ : ℕ} {S : Setup} {Pt : Type} {P : Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "Ops'" => e2eOps ℓ P C K decT encT
local notation "SmDom'" =>
  OracleSpec.Domain (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)

@[simp] private theorem cost_v {Γ Δ : List (Ty (e2eSig ℓ))} [Ext Γ Δ] {τ : Ty (e2eSig ℓ)}
    (x : Var Γ τ) : (v (O := Ops') (Δ := Δ) x).cost = 1 := rfl

private theorem le_add_letV {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)} {acc B : ℕ}
    (e : Expr Ops' Γ τ) (k : Var (τ :: Γ) τ → Comp Ops' I (τ :: Γ) υ)
    (hk : ∀ x, (acc + 2 + e.cost) + (k x).cost ≤ B) : acc + (letV e k).cost ≤ B := by
  have := hk .zero; dsimp only [letV, Comp.cost]; omega

private theorem le_add_letV_of {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)} {acc C₀ B : ℕ}
    (e : Expr Ops' Γ τ) (k : Var (τ :: Γ) τ → Comp Ops' I (τ :: Γ) υ) (he : e.cost ≤ C₀)
    (hk : ∀ x, (acc + 2 + C₀) + (k x).cost ≤ B) : acc + (letV e k).cost ≤ B := by
  have := hk .zero; dsimp only [letV, Comp.cost]; omega

private theorem le_add_bindV_of {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)} {acc C₀ B : ℕ}
    (c : Comp Ops' I Γ τ) (k : Var (τ :: Γ) τ → Comp Ops' I (τ :: Γ) υ) (hc : c.cost ≤ C₀)
    (hk : ∀ x, (acc + 1 + C₀) + (k x).cost ≤ B) : acc + (bindV c k).cost ≤ B := by
  have := hk .zero; dsimp only [bindV, Comp.cost]; omega

private theorem le_add_caseOptV_of {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)} {acc C₀ B : ℕ}
    (e : Expr Ops' Γ (.opt τ)) (n : Comp Ops' I Γ υ)
    (k : Var (τ :: Γ) τ → Comp Ops' I (τ :: Γ) υ) (he : e.cost ≤ C₀)
    (hn : (acc + 1 + C₀) + n.cost ≤ B) (hk : ∀ x, (acc + 1 + C₀) + (k x).cost ≤ B) :
    acc + (caseOptV e n k).cost ≤ B := by
  have := hk .zero; dsimp only [caseOptV, Comp.cost]; omega

private theorem le_add_ite {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {υ : Ty (e2eSig ℓ)} {acc B : ℕ}
    (b : Expr Ops' Γ .bool) (t f : Comp Ops' I Γ υ)
    (ht : (acc + 1 + b.cost) + t.cost ≤ B) (hf : (acc + 1 + b.cost) + f.cost ≤ B) :
    acc + (Comp.ite b t f).cost ≤ B := by
  dsimp only [Comp.cost]; omega

private theorem liftP_bind_pure {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {α β : Type} (m : ProbComp α) (f : α → β) :
    (I.liftP m >>= fun x => pure (f x)) = I.liftP (f <$> m) := by
  simp only [← liftP_pure I, ← liftP_bind I, map_eq_bind_pure_comp, Function.comp_def]

private theorem map_map_prob {α β γ : Type} (f : β → γ) (g : α → β) (m : ProbComp α) :
    f <$> (g <$> m) = (fun x => f (g x)) <$> m := by
  simp [Functor.map_map]

private theorem eval_letV {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr Ops' Γ τ) (k : Var (τ :: Γ) τ → Comp Ops' I (τ :: Γ) υ) (ρ : Env Γ) :
    (letV e k).eval ρ = (k .zero).eval (Env.cons (e.eval ρ) ρ) := by
  simp [letV, Comp.eval]

private theorem eval_bindV {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (c : Comp Ops' I Γ τ) (k : Var (τ :: Γ) τ → Comp Ops' I (τ :: Γ) υ) (ρ : Env Γ) :
    (bindV c k).eval ρ = c.eval ρ >>= fun x => (k .zero).eval (Env.cons x ρ) := rfl

private theorem eval_ite_comp {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {υ : Ty (e2eSig ℓ)}
    (b : Expr Ops' Γ .bool) (t f : Comp Ops' I Γ υ) (ρ : Env Γ) (bv : Bool) (hb : b.eval ρ = bv) :
    (Comp.ite b t f).eval ρ = if bv then t.eval ρ else f.eval ρ := by
  simp only [Comp.eval, hb]

private theorem eval_caseOptV {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr Ops' Γ (.opt τ)) (n : Comp Ops' I Γ υ)
    (s : Var (τ :: Γ) τ → Comp Ops' I (τ :: Γ) υ) (ρ : Env Γ) (ov : Option τ.denote)
    (he : e.eval ρ = ov) :
    (caseOptV e n s).eval ρ =
      Option.casesOn ov (n.eval ρ) (fun x => (s .zero).eval (Env.cons x ρ)) := by
  cases ov <;> simp [caseOptV, Comp.eval, he]

private theorem eval_isBobAcceptVal (sq : SmDom')
    (r : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq)
    {Γ : List (Ty (e2eSig ℓ))} {qE : Expr Ops' Γ smQT}
    {respE : Expr Ops' Γ (smRT GhostStT)} {ρ : Env Γ}
    (hq : qE.eval ρ = smQenc sq) (hr : respE.eval ρ = packSmRespEnc (bhPackSmResp sq r)) :
    (isBobAcceptSmRespE qE respE).eval ρ = bhIsBobAcceptSMResp sq r :=
  eval_isBobAcceptSmRespE qE respE ρ sq r hq (hr.trans (smRenc_id_eq_packSmRespEnc sq r).symm)

private theorem list_set_of_getElem? {α : Type} :
    ∀ (l : List α) (i : ℕ) (x : α), l[i]? = some x → l.set i x = l
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, h => by simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; rfl
  | y :: xs, i + 1, x, h => by
    simp only [List.getElem?_cons_succ] at h; exact congrArg (y :: ·) (list_set_of_getElem? xs i x h)

private theorem map_set_eq {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : ℕ) (x : α), (l.map f).set i (f x) = (l.set i x).map f
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | a :: as, i + 1, x => congrArg (f a :: ·) (map_set_eq f as i x)

/-- Steps an unpromoted `instSlotTy ℓ` entry via `sim.oracleStepC`, or returns `emptySmRespE`. -/
def stepInstSlotC (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (qBound qep : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (slotE : Expr Ops' Γ (instSlotTy ℓ)) (qE : Expr Ops' Γ smQT) :
    Comp Ops' (stepAIface ℓ I₀) Γ (.prod (smRT GhostStT) (instSlotTy ℓ)) :=
  letV (.pair slotE qE) fun args =>
    letV (.fst (v args)) fun sl => letV (.snd (v args)) fun q0 =>
      .ite (.fst (.snd (.snd (.snd (v sl)))))
        (.ret (.pair emptySmRespE (v sl)))
        (bindV (sim.oracleStepC I₀ qBound qep (.snd (.snd (.snd (.snd (v sl))))) (v q0)) fun res =>
          .ret (.pair (.fst (v res))
            (.pair (.fst (v sl)) (.pair (.fst (.snd (v sl)))
              (.pair (.fst (.snd (.snd (v sl)))) (.pair (.bool false) (.snd (v res))))))))

@[simp] theorem stepInstSlotC_queries (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (qBound qep : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (slotE : Expr Ops' Γ (instSlotTy ℓ)) (qE : Expr Ops' Γ smQT)
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (stepInstSlotC sim I₀ qBound qep slotE qE).queries w (fun _ => 0) = 0 := by
  simp [stepInstSlotC, letV, bindV, Comp.queries, sim.oracleStepC_queries]

theorem stepInstSlotC_cost (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (qBound qep : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (slotE : Expr Ops' Γ (instSlotTy ℓ)) (qE : Expr Ops' Γ smQT) :
    (stepInstSlotC sim I₀ qBound qep slotE qE).cost ≤
      slotE.cost + qE.cost + sim.oracleStepCost qBound qep + 60 := by
  rw [← Nat.zero_add (Comp.cost _)]; unfold stepInstSlotC
  apply le_add_letV; intro args; apply le_add_letV; intro sl; apply le_add_letV; intro q0
  apply le_add_ite
  · simp only [Comp.cost, Expr.cost, cost_v, cost_emptySmRespE]; omega
  · apply le_add_bindV_of _ _ (sim.oracleStepC_cost _ _ _ _ _); intro res
    simp only [Comp.cost, Expr.cost, cost_v]; omega

theorem stepInstSlotC_eval (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (qBound qep : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (slotE : Expr Ops' Γ (instSlotTy ℓ)) (qE : Expr Ops' Γ smQT)
    (ρ : Env Γ) (d : BHModelInst S ℓ) (sq : SmDom')
    (hslot : slotE.eval ρ = instSlotOfModelInst d) (hq : qE.eval ρ = smQenc sq)
    (hreach : ∀ gs ∈ d.gs, SmReachBounded C K qBound gs) :
    (stepInstSlotC sim I₀ qBound qep slotE qE).eval ρ =
      match d.gs with
      | none => pure (packSmRespEnc (none, none, none), instSlotOfModelInst d)
      | some gs =>
        (stepAIface ℓ I₀).liftP
          ((fun out => (packSmRespEnc (bhPackSmResp sq out.1),
              instSlotOfModelInst { d with gs := some out.2 })) <$>
            ((CryptoGames.SM.oracleImplR
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins)
                (2 + 1) qep (configRefuseEarlyBobCorr decT encT) sq).run gs)) := by
  unfold stepInstSlotC
  simp only [letV, bindV, v, ext_refl_wk, ext_step_wk, Comp.eval, Expr.eval,
    env_get_zero, env_get_succ, eval_emptySmRespE, pure_bind, hslot, hq]
  cases hgs : d.gs with
  | none => simp [instSlotOfModelInst, hgs]
  | some gs =>
    have hr : SmReachBounded C K qBound gs := hreach gs hgs
    simp only [instSlotOfModelInst, hgs, Bool.false_eq_true, ↓reduceIte]
    rw [sim.oracleStepC_eval I₀ qBound qep _ _ _ d.idA d.idB d.spkCoins gs sq hr rfl rfl]
    rw [liftP_bind_pure, map_map_prob]
    congr 1; apply congrArg (· <$> _); funext out
    exact Prod.ext (smRenc_id_eq_packSmRespEnc sq out.1) rfl

attribute [local irreducible] stepInstSlotC

def stepInstTblSlotC (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (qBound qep : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (tblE : Expr Ops' Γ (.tbl (instSlotTy ℓ)))
    (idxE : Expr Ops' Γ .nat) (qE : Expr Ops' Γ smQT) :
    Comp Ops' (stepAIface ℓ I₀) Γ (.prod (smRT GhostStT) (.tbl (instSlotTy ℓ))) :=
  letV (.pair tblE (.pair idxE qE)) fun args =>
    letV (.fst (v args)) fun tb => letV (.fst (.snd (v args))) fun ix =>
    letV (.snd (.snd (v args))) fun q0 =>
      bindV (stepInstSlotC sim I₀ qBound qep (.tget (v tb) (v ix)) (v q0)) fun res =>
        letV (tblSetSlotE (v tb) (v ix) (.snd (v res))) fun tb' =>
          .ret (.pair (.fst (v res)) (v tb'))

@[simp] theorem stepInstTblSlotC_queries (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (qBound qep : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (tblE : Expr Ops' Γ (.tbl (instSlotTy ℓ)))
    (idxE : Expr Ops' Γ .nat) (qE : Expr Ops' Γ smQT) (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (stepInstTblSlotC sim I₀ qBound qep tblE idxE qE).queries w (fun _ => 0) = 0 := by
  simp [stepInstTblSlotC, letV, bindV, Comp.queries]

theorem stepInstTblSlotC_cost (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (qBound qep : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (tblE : Expr Ops' Γ (.tbl (instSlotTy ℓ)))
    (idxE : Expr Ops' Γ .nat) (qE : Expr Ops' Γ smQT) :
    (stepInstTblSlotC sim I₀ qBound qep tblE idxE qE).cost ≤
      tblE.cost + idxE.cost + qE.cost + sim.oracleStepCost qBound qep + 285 := by
  rw [← Nat.zero_add (Comp.cost _)]; unfold stepInstTblSlotC
  apply le_add_letV; intro args; apply le_add_letV; intro tb
  apply le_add_letV; intro ix; apply le_add_letV; intro q0
  apply le_add_bindV_of _ _ (stepInstSlotC_cost sim _ _ _ _ _); intro res
  apply le_add_letV_of _ _ (cost_tblSetSlotE _ _ _); intro tb'
  simp only [Comp.cost, Expr.cost, cost_v]; omega

theorem stepInstTblSlotC_eval (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (qBound qep : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (tblE : Expr Ops' Γ (.tbl (instSlotTy ℓ)))
    (idxE : Expr Ops' Γ .nat) (qE : Expr Ops' Γ smQT)
    (ρ : Env Γ) (insts : List (BHModelInst S ℓ)) (i : ℕ) (d : BHModelInst S ℓ) (sq : SmDom')
    (htbl : tblE.eval ρ = encodeInstTbl insts) (hidx : idxE.eval ρ = i) (hq : qE.eval ρ = smQenc sq)
    (hd : insts[i]? = some d) (hreach : ∀ gs ∈ d.gs, SmReachBounded C K qBound gs) :
    (stepInstTblSlotC sim I₀ qBound qep tblE idxE qE).eval ρ =
      match d.gs with
      | none => pure (packSmRespEnc (none, none, none), encodeInstTbl insts)
      | some gs =>
        (stepAIface ℓ I₀).liftP
          ((fun out => (packSmRespEnc (bhPackSmResp sq out.1),
              encodeInstTbl (insts.set i { d with gs := some out.2 }))) <$>
            ((CryptoGames.SM.oracleImplR
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins)
                (2 + 1) qep (configRefuseEarlyBobCorr decT encT) sq).run gs)) := by
  have hi : i < insts.length := (List.getElem?_eq_some_iff.mp hd).1
  unfold stepInstTblSlotC
  simp only [letV, bindV, v, ext_refl_wk, ext_step_wk, Comp.eval, Expr.eval,
    env_get_zero, env_get_succ, pure_bind, htbl, hidx, hq]
  rw [stepInstSlotC_eval sim I₀ qBound qep _ _ _ d sq
    (by simp [Expr.eval, env_get_zero, env_get_succ, encodeInstTbl, hd]) rfl hreach]
  cases d.gs with
  | none =>
    simp only [pure_bind]
    rw [eval_tblSetSlotE _ _ _ _ insts i d rfl rfl rfl hi, list_set_of_getElem? insts i d hd]
  | some gs =>
    rw [liftP_bind_pure, map_map_prob]
    congr 1; apply congrArg (· <$> _); funext out; dsimp only
    rw [eval_tblSetSlotE _ _ _ _ insts i { d with gs := some out.2 } rfl rfl rfl hi]

attribute [local irreducible] stepInstTblSlotC

/-- Single-instance model step factoring the inner `some d, some im` body of `bhE2EStepLocalSm`. -/
def bhStepSingleInst (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ikACorr : Bool) (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S) (sq : SmDom') :
    ProbComp (BHE2ESmResp ℓ × BHModelInst S ℓ × ModelDriverInstanceMeta S) :=
  if !im.bobAccepted && bhIsBobRecvSMQuery sq && ikACorr then
    pure ((none, none, none), d, { im with bobAccepted := true, ikACorrAtAccept := true })
  else
    match d.gs with
    | none => pure ((none, none, none), d, im)
    | some gs =>
      match bhFilterLocalSmQuery im.bobAccepted d.sid d.hdr sq with
      | none => pure ((none, none, none), d, im)
      | some q' => do
        let spqr := spqrV1SessionUniformCoins C.F K
        let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
        let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
        let (r, gs') ← (CryptoGames.SM.oracleImplR sch (2 + 1) qep cfg q').run gs
        let im' := if !im.bobAccepted && bhIsBobAcceptSMResp q' r then
            { im with bobAccepted := true, ikACorrAtAccept := ikACorr }
          else im
        pure (bhPackSmResp q' r, { d with gs := some gs' }, im')

theorem bhE2EStepLocalSm_eq_singleInst (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (σ : BHE2EDrvState S ℓ)
    (i : ℕ) (sq : SmDom') :
    bhE2EStepLocalSm C K qep decT encT σ i sq =
      if !bhE2EDrvInstClean σ i then pure ((none, none, none), σ)
      else
        match σ.insts[i]?, σ.instMeta[i]? with
        | some d, some im =>
          (fun out => (out.1, { σ with insts := σ.insts.set i out.2.1,
                                       instMeta := σ.instMeta.set i out.2.2 })) <$>
            bhStepSingleInst C K qep decT encT (bhE2EInstIkACorr σ d) d im sq
        | _, _ => pure ((none, none, none), σ) := by
  rw [bhE2EStepLocalSm_eq_filtered]
  by_cases hcl : !bhE2EDrvInstClean σ i
  · simp only [hcl, ↓reduceIte]
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte]
    cases hd : σ.insts[i]? with
    | none => rfl
    | some d =>
      cases him : σ.instMeta[i]? with
      | none => rfl
      | some im =>
        dsimp only [bhStepSingleInst]
        have hsetD := list_set_of_getElem? σ.insts i d hd
        have hsetIm := list_set_of_getElem? σ.instMeta i im him
        by_cases hcorr : !im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d
        · simp [hcorr, hsetD]
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte]
          cases d.gs with
          | none => simp [hsetD, hsetIm]
          | some gs =>
            cases bhFilterLocalSmQuery im.bobAccepted d.sid d.hdr sq with
            | none => simp [hsetD, hsetIm]
            | some q' => simp [map_eq_bind_pure_comp, LawfulMonad.bind_assoc]

/-- Single-instance `ReductionDsl` step handler implementing `bhStepSingleInst`. -/
def stepSingleInstC (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (qBound qep : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (hmE : Expr Ops' Γ (e2eInstHdrMetaTy S ℓ))
    (slotE : Expr Ops' Γ (instSlotTy ℓ)) (ikACorrE : Expr Ops' Γ .bool) (qE : Expr Ops' Γ smQT) :
    Comp Ops' (stepAIface ℓ I₀) Γ
      (.prod (smRT GhostStT) (.prod (e2eInstHdrMetaTy S ℓ) (instSlotTy ℓ))) :=
  letV (.pair hmE (.pair slotE (.pair ikACorrE qE))) fun args =>
    letV (.fst (v args)) fun hm => letV (.fst (.snd (v args))) fun sl =>
    letV (.fst (.snd (.snd (v args)))) fun ikc => letV (.snd (.snd (.snd (v args)))) fun q0 =>
    letV (.fst (v hm)) fun sid => letV (.fst (.snd (v hm))) fun hdr =>
    letV (.snd (.snd (v hm))) fun im => letV (.fst (v im)) fun bobAcc =>
    letV (isBobRecvSmQueryE (v q0)) fun isRecv =>
      .ite (.and (.not (v bobAcc)) (.and (v isRecv) (v ikc)))
        (letV (setInstMetaAcceptE (v im) (.bool true)) fun im1 =>
          .ret (.pair emptySmRespE (.pair (.pair (v sid) (.pair (v hdr) (v im1))) (v sl))))
        (.ite (.fst (.snd (.snd (.snd (v sl)))))
          (.ret (.pair emptySmRespE (.pair (v hm) (v sl))))
          (caseOptV (filterLocalSmQueryE (v bobAcc) (v sid) (v hdr) (v q0))
            (.ret (.pair emptySmRespE (.pair (v hm) (v sl))))
            (fun qf =>
              bindV (stepInstSlotC sim I₀ qBound qep (v sl) (v qf)) fun res =>
                letV (isBobAcceptSmRespE (v qf) (.fst (v res))) fun isAcc =>
                letV (setInstMetaAcceptE (v im) (v ikc)) fun imAcc =>
                letV (.ite (.and (.not (v bobAcc)) (v isAcc)) (v imAcc) (v im)) fun im' =>
                  .ret (.pair (.fst (v res))
                    (.pair (.pair (v sid) (.pair (v hdr) (v im'))) (.snd (v res)))))))

@[simp] theorem stepSingleInstC_queries (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (qBound qep : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (hmE : Expr Ops' Γ (e2eInstHdrMetaTy S ℓ))
    (slotE : Expr Ops' Γ (instSlotTy ℓ)) (ikACorrE : Expr Ops' Γ .bool) (qE : Expr Ops' Γ smQT)
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (stepSingleInstC sim I₀ qBound qep hmE slotE ikACorrE qE).queries w (fun _ => 0) = 0 := by
  simp [stepSingleInstC, letV, bindV, caseOptV, Comp.queries]

theorem stepSingleInstC_cost (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (qBound qep : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (hmE : Expr Ops' Γ (e2eInstHdrMetaTy S ℓ))
    (slotE : Expr Ops' Γ (instSlotTy ℓ)) (ikACorrE : Expr Ops' Γ .bool) (qE : Expr Ops' Γ smQT) :
    (stepSingleInstC sim I₀ qBound qep hmE slotE ikACorrE qE).cost ≤
      hmE.cost + slotE.cost + ikACorrE.cost + qE.cost + sim.oracleStepCost qBound qep + 8300 := by
  rw [← Nat.zero_add (Comp.cost _)]; unfold stepSingleInstC
  apply le_add_letV; intro args; apply le_add_letV; intro hm; apply le_add_letV; intro sl
  apply le_add_letV; intro ikc; apply le_add_letV; intro q0; apply le_add_letV; intro sid
  apply le_add_letV; intro hdr; apply le_add_letV; intro im; apply le_add_letV; intro bobAcc
  apply le_add_letV_of _ _ (cost_isBobRecvSmQueryE _); intro isRecv
  apply le_add_ite
  · apply le_add_letV_of _ _ (cost_setInstMetaAcceptE _ _); intro im1
    simp only [Comp.cost, Expr.cost, cost_v, cost_emptySmRespE]; omega
  · apply le_add_ite
    · simp only [Comp.cost, Expr.cost, cost_v, cost_emptySmRespE]; omega
    · apply le_add_caseOptV_of _ _ _ (cost_filterLocalSmQueryE _ _ _ _)
      · simp only [Comp.cost, Expr.cost, cost_v, cost_emptySmRespE]; omega
      · intro qf
        apply le_add_bindV_of _ _ (stepInstSlotC_cost sim _ _ _ _ _); intro res
        apply le_add_letV_of _ _ (cost_isBobAcceptSmRespE _ _); intro isAcc
        apply le_add_letV_of _ _ (cost_setInstMetaAcceptE _ _); intro imAcc
        apply le_add_letV; intro im'
        simp only [Comp.cost, Expr.cost, cost_v]; omega

theorem stepSingleInstC_eval (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (qBound qep : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (hmE : Expr Ops' Γ (e2eInstHdrMetaTy S ℓ))
    (slotE : Expr Ops' Γ (instSlotTy ℓ)) (ikACorrE : Expr Ops' Γ .bool) (qE : Expr Ops' Γ smQT)
    (ρ : Env Γ) (ikACorr : Bool) (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S) (sq : SmDom')
    (hhm : hmE.eval ρ = e2eInstHdrMetaEnc d im) (hslot : slotE.eval ρ = instSlotOfModelInst d)
    (hikc : ikACorrE.eval ρ = ikACorr) (hq : qE.eval ρ = smQenc sq)
    (hreach : ∀ gs ∈ d.gs, SmReachBounded C K qBound gs) :
    (stepSingleInstC sim I₀ qBound qep hmE slotE ikACorrE qE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun out => (packSmRespEnc out.1,
            (e2eInstHdrMetaEnc out.2.1 out.2.2, instSlotOfModelInst out.2.1))) <$>
          bhStepSingleInst C K qep decT encT ikACorr d im sq) := by
  unfold stepSingleInstC bhStepSingleInst
  simp only [letV, bindV, caseOptV, v, ext_refl_wk, ext_step_wk, Comp.eval, Expr.eval,
    env_get_zero, env_get_succ, eval_emptySmRespE, pure_bind, hhm, hslot, hikc, hq,
    e2eInstHdrMetaEnc, eval_isBobRecvSmQueryVal, smQdec_smQenc, Bool.and_assoc]
  have hb0 : (e2eInstMetaEnc (ℓ := ℓ) im).1 = im.bobAccepted := rfl
  simp only [hb0]
  by_cases hcorr : !im.bobAccepted && (bhIsBobRecvSMQuery sq && ikACorr)
  · simp [hcorr, liftP_pure, eval_setInstMetaAcceptVal, Expr.eval, env_get_zero, env_get_succ,
      e2eInstMetaDec_e2eInstMetaEnc]
  · simp only [hcorr, Bool.false_eq_true, ↓reduceIte]
    cases hgs : d.gs with
    | none => simp [instSlotOfModelInst, hgs, liftP_pure]
    | some gs =>
      simp only [instSlotOfModelInst, hgs, Bool.false_eq_true, ↓reduceIte,
        eval_filterLocalSmQueryVal, Expr.eval, env_get_zero, env_get_succ,
        sidOfV_sidV, hdrOfV_hdrV, smQdec_smQenc]
      cases hflt : bhFilterLocalSmQuery im.bobAccepted d.sid d.hdr sq with
      | none => simp [liftP_pure, hgs]
      | some q' =>
        dsimp only [Option.map]
        rw [stepInstSlotC_eval sim I₀ qBound qep _ _ _ d q'
          (by simp [Expr.eval, env_get_zero, env_get_succ, instSlotOfModelInst, hgs]) rfl hreach]
        simp only [hgs]
        rw [liftP_bind_pure]
        congr 1
        simp only [map_eq_bind_pure_comp, LawfulMonad.bind_assoc, pure_bind, Function.comp_def]
        congr 1; funext ⟨r, gs'⟩; congr 1
        rw [eval_isBobAcceptVal (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
          q' r rfl rfl]
        simp only [eval_setInstMetaAcceptVal, Expr.eval, env_get_zero, env_get_succ,
          e2eInstMetaDec_e2eInstMetaEnc]
        by_cases hacc : !im.bobAccepted && bhIsBobAcceptSMResp q' r <;>
          simp [hacc, instSlotOfModelInst]

attribute [local irreducible] stepSingleInstC

/-- Driver-level `bhE2EStepLocalSm` handler over `e2eDrvStateTy S ℓ`. -/
def stepLocalSmC {S : Setup} (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nCorr nPrins qBound qep : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr Ops' Γ (e2eDrvStateTy S ℓ)) (idxE : Expr Ops' Γ .nat) (qE : Expr Ops' Γ smQT) :
    Comp Ops' (stepAIface ℓ I₀) Γ (.prod (smRT GhostStT) (e2eDrvStateTy S ℓ)) :=
  letV (.pair σE (.pair idxE qE)) fun args =>
    letV (.fst (v args)) fun s => letV (.fst (.snd (v args))) fun ix =>
    letV (.snd (.snd (v args))) fun q0 => letV (.fst (v s)) fun base =>
    letV (.fst (.snd (v s))) fun cp => letV (.fst (.snd (.snd (v s)))) fun adv =>
    letV (.fst (.snd (.snd (.snd (v s))))) fun insts =>
    letV (.fst (.snd (.snd (.snd (.snd (v s)))))) fun metas =>
    letV (.snd (.snd (.snd (.snd (.snd (v s)))))) fun tail =>
    letV (drvInstCleanDrvStateE qStart nCorr (v adv) (v insts) (v metas) (v ix)) fun cl =>
      .ite (.not (v cl))
        (.ret (.pair emptySmRespE (v s)))
        (caseOptV (listGetOptE qStart (v insts) (v ix))
          (.ret (.pair emptySmRespE (v s)))
          (fun dEnc =>
            caseOptV (listGetOptE qStart (v metas) (v ix))
              (.ret (.pair emptySmRespE (v s)))
              (fun imEnc =>
                letV (modelInstToHmE (v dEnc) (v imEnc)) fun hm =>
                letV (modelInstToSlotE (v dEnc)) fun sl =>
                letV (instIkACorrListE nCorr nPrins
                    (.fst (v hm)) (.fst (.fst (.snd (v hm)))) (v cp) (.fst (v base))) fun ikc =>
                  bindV (stepSingleInstC sim I₀ qBound qep (v hm) (v sl) (v ikc) (v q0)) fun res =>
                    letV (slotHmToModelInstE (.fst (.snd (v res))) (.snd (.snd (v res)))) fun dEnc' =>
                    letV (.snd (.snd (.fst (.snd (v res))))) fun imEnc' =>
                    letV (listSetE qStart (v insts) (v ix) (v dEnc')) fun insts' =>
                    letV (listSetE qStart (v metas) (v ix) (v imEnc')) fun metas' =>
                      .ret (.pair (.fst (v res)) (.pair (v base) (.pair (v cp) (.pair (v adv)
                        (.pair (v insts') (.pair (v metas') (v tail))))))))))

def stepLocalSmCost (sim : DrSessionSimIface ℓ P C K decT encT)
    (qStart nCorr nPrins qBound qep : ℕ) : ℕ :=
  sim.oracleStepCost qBound qep + 190 * qStart + 160 * nCorr + 160 * nPrins + 9500

@[simp] theorem stepLocalSmC_queries {S : Setup} (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nCorr nPrins qBound qep : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr Ops' Γ (e2eDrvStateTy S ℓ)) (idxE : Expr Ops' Γ .nat) (qE : Expr Ops' Γ smQT)
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (stepLocalSmC sim I₀ qStart nCorr nPrins qBound qep σE idxE qE).queries w (fun _ => 0) = 0 := by
  simp [stepLocalSmC, letV, bindV, caseOptV, Comp.queries]

theorem stepLocalSmC_cost {S : Setup} (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nCorr nPrins qBound qep : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr Ops' Γ (e2eDrvStateTy S ℓ)) (idxE : Expr Ops' Γ .nat) (qE : Expr Ops' Γ smQT) :
    (stepLocalSmC sim I₀ qStart nCorr nPrins qBound qep σE idxE qE).cost ≤
      σE.cost + idxE.cost + qE.cost + stepLocalSmCost sim qStart nCorr nPrins qBound qep := by
  rw [← Nat.zero_add (Comp.cost _)]; unfold stepLocalSmC stepLocalSmCost
  apply le_add_letV; intro args; apply le_add_letV; intro s; apply le_add_letV; intro ix
  apply le_add_letV; intro q0; apply le_add_letV; intro base; apply le_add_letV; intro cp
  apply le_add_letV; intro adv; apply le_add_letV; intro insts; apply le_add_letV; intro metas
  apply le_add_letV; intro tail
  apply le_add_letV_of _ _ (cost_drvInstCleanDrvStateE _ _ _ _ _ _); intro cl
  apply le_add_ite
  · simp only [Comp.cost, Expr.cost, cost_v, cost_emptySmRespE]; omega
  · apply le_add_caseOptV_of _ _ _ (cost_listGetOptE _ _ _)
    · simp only [Comp.cost, Expr.cost, cost_v, cost_emptySmRespE]; omega
    · intro dEnc
      apply le_add_caseOptV_of _ _ _ (cost_listGetOptE _ _ _)
      · simp only [Comp.cost, Expr.cost, cost_v, cost_emptySmRespE]; omega
      · intro imEnc
        apply le_add_letV_of _ _ (cost_modelInstToHmE _ _); intro hm
        apply le_add_letV_of _ _ (cost_modelInstToSlotE _); intro sl
        apply le_add_letV_of _ _ (cost_instIkACorrListE _ _ _ _ _ _); intro ikc
        apply le_add_bindV_of _ _ (stepSingleInstC_cost sim _ _ _ _ _ _ _); intro res
        apply le_add_letV_of _ _ (cost_slotHmToModelInstE _ _); intro dEnc'
        apply le_add_letV; intro imEnc'
        apply le_add_letV_of _ _ (cost_listSetE _ _ _ _); intro insts'
        apply le_add_letV_of _ _ (cost_listSetE _ _ _ _); intro metas'
        simp only [Comp.cost, Expr.cost, cost_v]; omega

theorem stepLocalSmC_eval {S : Setup} (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nCorr nPrins qBound qep : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr Ops' Γ (e2eDrvStateTy S ℓ)) (idxE : Expr Ops' Γ .nat) (qE : Expr Ops' Γ smQT)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (i : ℕ) (sq : SmDom')
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hidx : idxE.eval ρ = i) (hq : qE.eval ρ = smQenc sq)
    (hInstLen : σ.insts.length ≤ qStart) (hMeta : DrvMetaAligned σ)
    (hCorrLen : σ.corrPrins.length ≤ nCorr) (hRevLen : σ.revealedSpks.length ≤ nCorr)
    (hPrinLen : σ.prins.length ≤ nPrins)
    (hSess : DrvSessionsBounded C K qBound σ) :
    (stepLocalSmC sim I₀ qStart nCorr nPrins qBound qep σE idxE qE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun out => (packSmRespEnc out.1, e2eDrvStateEnc out.2)) <$>
          bhE2EStepLocalSm C K qep decT encT σ i sq) := by
  have hMetaLen : σ.instMeta.length ≤ qStart := hMeta.trans_le hInstLen
  have hInstMapLen : (σ.insts.map (e2eModelInstEnc (ℓ := ℓ))).length ≤ qStart := by simp [hInstLen]
  have hMetaMapLen : (σ.instMeta.map (e2eInstMetaEnc (ℓ := ℓ))).length ≤ qStart := by simp [hMetaLen]
  rw [bhE2EStepLocalSm_eq_singleInst]; unfold stepLocalSmC
  simp only [eval_letV, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
    hσ, hidx, hq, e2eDrvStateEnc]
  rw [eval_ite_comp _ _ _ _ (!bhE2EDrvInstClean σ i)
    (by dsimp only [Expr.eval, env_get_zero]; congr 1
        exact eval_drvInstCleanDrvStateE qStart nCorr σ i hInstLen hMetaLen hRevLen
          rfl rfl rfl rfl)]
  by_cases hcl : !bhE2EDrvInstClean σ i
  · simp [hcl, Comp.eval, Expr.eval]
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte]
    rw [eval_caseOptV _ _ _ _ ((σ.insts.map (e2eModelInstEnc (ℓ := ℓ)))[i]?)
      (by exact eval_listGetOptE qStart _ _ _ hInstMapLen)]
    rw [List.getElem?_map]
    cases hd : σ.insts[i]? with
    | none => simp [Comp.eval, Expr.eval]
    | some d =>
      dsimp only [Option.map, Option.casesOn]
      rw [eval_caseOptV _ _ _ _ ((σ.instMeta.map (e2eInstMetaEnc (ℓ := ℓ)))[i]?)
        (by exact eval_listGetOptE qStart _ _ _ hMetaMapLen)]
      rw [List.getElem?_map]
      cases him : σ.instMeta[i]? with
      | none => simp [Comp.eval, Expr.eval]
      | some im =>
        dsimp only [Option.map, Option.casesOn]
        rw [eval_letV, eval_letV, eval_letV, eval_bindV]
        rw [eval_modelInstToHmE _ _ _ d im (by rfl) (by rfl)]
        rw [eval_modelInstToSlotE _ _ d (by rfl)]
        rw [eval_instIkACorrListE nCorr nPrins _ _ _ _ _ σ d
          (by rfl) (by rfl) (by rfl) (by rfl) hCorrLen hPrinLen]
        rw [stepSingleInstC_eval sim I₀ qBound qep _ _ _ _ _
          (bhE2EInstIkACorr σ d) d im sq (by rfl) (by rfl) (by rfl) (by rfl)
          (hSess d (List.mem_of_getElem? hd))]
        simp only [eval_letV, Comp.eval]
        rw [liftP_bind_pure, map_map_prob, map_map_prob]
        congr 1; apply congrArg (· <$> _); funext out
        dsimp only [Expr.eval, env_get_zero, env_get_succ]
        rw [eval_slotHmToModelInstE _ _ _ out.2.1 out.2.2 (by rfl) (by rfl)]
        dsimp only [e2eInstHdrMetaEnc]
        rw [eval_listSetE qStart _ _ _ _ (by exact hInstMapLen),
          eval_listSetE qStart _ _ _ _ (by exact hMetaMapLen)]
        dsimp only [Expr.eval, env_get_zero, env_get_succ]
        rw [map_set_eq (e2eModelInstEnc (ℓ := ℓ)) σ.insts i out.2.1,
            map_set_eq (e2eInstMetaEnc (ℓ := ℓ)) σ.instMeta i out.2.2]

attribute [local irreducible] stepLocalSmC

/-- Concrete `LocalSessionStepIface` bundle constructed from any `DrSessionSimIface`. -/
def localSessionStepIface (sim : DrSessionSimIface ℓ P C K decT encT) :
    LocalSessionStepIface ℓ S P C K decT encT where
  stepLocalSmC := stepLocalSmC (S := S) sim
  stepLocalSmCost := stepLocalSmCost sim
  stepLocalSmC_cost := stepLocalSmC_cost (S := S) sim
  stepLocalSmC_queries := stepLocalSmC_queries (S := S) sim
  stepLocalSmC_eval := stepLocalSmC_eval (S := S) sim

/-! ## Reachability preservation -/

theorem smReachBounded_mono {C : Crypto} {K : MlKem} {qBound qBound' : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : SmReachBounded C K qBound gs) (hle : qBound ≤ qBound') :
    SmReachBounded C K qBound' gs := h.mono hle

theorem smReachBounded_step_oracleImplR (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (qep qBound : ℕ) (spkCoins : BitVec 256) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qry : SmDom') {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : SmReachBounded C K qBound gs)
    {out : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range qry ×
      GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hout : out ∈ support ((CryptoGames.SM.oracleImplR
        (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
          ℓ spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT) qry).run gs)) :
    SmReachBounded C K (qBound + 1) out.2 :=
  smReachBounded_oracleImplR C K idA idB ℓ (2 + 1) qep qBound spkCoins
    (configRefuseEarlyBobCorr decT encT) qry h hout

theorem drvSmReachInv_stepLocalSm (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {σ : BHE2EDrvState S ℓ} (h : DrvSmReachInv C K σ) (i : ℕ) (sq : SmDom')
    {out : BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    DrvSmReachInv C K out.2 :=
  drvSmReachInv_bhE2EStepLocalSm C K qep decT encT h i sq hout

/-- Per-slot `SmReachBounded` preservation across `bhE2EStepLocalSm`. -/
theorem smReachBounded_bhE2EStepLocalSm (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {σ : BHE2EDrvState S ℓ} (i : ℕ) (sq : SmDom')
    {qBound : ℕ} (hi : ∀ d ∈ σ.insts[i]?, ∀ gs ∈ d.gs, SmReachBounded C K qBound gs)
    {out : BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    out.2.insts.length = σ.insts.length ∧
      (∀ d' ∈ out.2.insts[i]?, ∀ gs' ∈ d'.gs, SmReachBounded C K (qBound + 1) gs') ∧
      (∀ j : ℕ, j ≠ i → out.2.insts[j]? = σ.insts[j]?) := by
  have hpure : out.2 = σ →
      out.2.insts.length = σ.insts.length ∧
        (∀ d' ∈ out.2.insts[i]?, ∀ gs' ∈ d'.gs, SmReachBounded C K (qBound + 1) gs') ∧
        (∀ j : ℕ, j ≠ i → out.2.insts[j]? = σ.insts[j]?) := fun heq => by
    rw [heq]
    exact ⟨rfl, fun d' hd' gs' hgs' => (hi d' hd' gs' hgs').mono (Nat.le_succ qBound),
      fun _ _ => rfl⟩
  rw [bhE2EStepLocalSm_eq_filtered] at hout
  by_cases hcl : !bhE2EDrvInstClean σ i
  · simp only [hcl, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
    exact hpure (congrArg Prod.snd hout)
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[i]? with
    | none =>
      simp only [hd, support_pure, Set.mem_singleton_iff] at hout
      exact hpure (congrArg Prod.snd hout)
    | some d =>
      cases him : σ.instMeta[i]? with
      | none =>
        simp only [hd, him, support_pure, Set.mem_singleton_iff] at hout
        exact hpure (congrArg Prod.snd hout)
      | some im =>
        simp only [hd, him] at hout
        by_cases hcorr : !im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout; subst hout
          exact ⟨rfl, fun d' hd' gs' hgs' => (hi d' hd' gs' hgs').mono (Nat.le_succ qBound),
            fun _ _ => rfl⟩
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none =>
            simp only [hgs, support_pure, Set.mem_singleton_iff] at hout
            exact hpure (congrArg Prod.snd hout)
          | some gs =>
            simp only [hgs] at hout
            cases hflt : bhFilterLocalSmQuery im.bobAccepted d.sid d.hdr sq with
            | none =>
              simp only [hflt, support_pure, Set.mem_singleton_iff] at hout
              exact hpure (congrArg Prod.snd hout)
            | some q' =>
              simp only [hflt, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
              rcases hout with ⟨⟨r, gs'⟩, hstep, rfl⟩
              have hiLt : i < σ.insts.length := (List.getElem?_eq_some_iff.mp hd).1
              have hgs' := smReachBounded_step_oracleImplR C K d.idA d.idB qep qBound d.spkCoins
                decT encT q' (hi d hd gs hgs) hstep
              refine ⟨by simp, ?_, fun j hj => by simp [Ne.symm hj]⟩
              intro d' hd' gs0 hgs0
              simp only [List.getElem?_set_self hiLt, Option.mem_def, Option.some.injEq] at hd'
              subst hd'; simp only [Option.mem_def, Option.some.injEq] at hgs0; subst hgs0
              exact hgs'

/-- Uniform `DrvSessionsBounded C K (qBound + 1)` preservation across `bhE2EStepLocalSm`. -/
theorem smReachBounded_all_bhE2EStepLocalSm (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {σ : BHE2EDrvState S ℓ} {qBound : ℕ}
    (hall : DrvSessionsBounded C K qBound σ) (i : ℕ) (sq : SmDom')
    {out : BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    DrvSessionsBounded C K (qBound + 1) out.2 := by
  have ⟨_, hi', hother⟩ := smReachBounded_bhE2EStepLocalSm C K qep decT encT i sq
    (fun d hd => hall d (List.mem_of_getElem? hd)) hout
  intro d' hd' gs' hgs'
  obtain ⟨j, hjLt, rfl⟩ := List.getElem_of_mem hd'
  have hjOpt : out.2.insts[j]? = some out.2.insts[j] := List.getElem?_eq_getElem hjLt
  by_cases hji : j = i
  · subst hji; exact hi' _ hjOpt gs' hgs'
  · rw [hother j hji] at hjOpt
    exact (hall _ (List.mem_of_getElem? hjOpt) gs' hgs').mono (Nat.le_succ qBound)

end StepHandlers

end Computational.Proofs.E2E.Dsl.LocalSessionStep
