/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.StartAndExtSmAux
import Computational.Proofs.E2E.Dsl.ClampsLossless

/-!
# Session start and external promoted routing in `ReductionDsl`

Implements the session-start handlers, slot-promotion step, and promoted-session external
`SM.spec` query routing over `e2eOps`, together with `.eval`, `.cost`, `.queries`, and
driver-state invariant preservation theorems.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.StartAndExtSm

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Expr Comp Iface Env UniformSamplerTag)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (GameState initState)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes wirePrekey PreKeyMessageFields
  SampledSessionKey paramsIdsWithSpqr sessionSchemeFixedSpk
  BHPrefixCtx BHE2ESmResp ModelDriverBase ModelDriverInstanceMeta
  BHModelInst BHE2EDrvState bhIdKeyOf bhDrvSessionInitPrin? bhInitRegId
  bhE2EGuard bhE2EDrvInstClean bhE2EInstIkACorr bhE2EFinishStartSpk
  bhIsBobRecvSMQuery bhIsBobAcceptSMResp bhDecodePreKeyMsgE
  bhHdrOfPreKeyMsg bhExpectedPreKeyMsg bhPartneredInnerBytes shortCiphertext
  bhPackSmResp bhUnpackSmResp compositionLocalStart)
open CryptoVerification.E2E.Costed (e2eSig B PB PU32 U32 BV256 BV512 FinT IdKey
  PlainT GhostStT bundleT hdrT hdrV hdrOfV sidT sidV sidOfV
  keyIndQT keyIndQenc keyIndRT keyIndRenc keyIndRdec prefixCtxT
  recvResultT recvResultEnc recvResultDec
  partyToBool boolToParty smQT smQenc smRT smRdec
  E2EUnifBase e2eSamplers E2EPureOp e2ePureOps e2eOps
  E2ESessionTag e2eSessionTargetIface)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp eval_e2ePureOp cost_e2ePureOp
  hdrOfV_hdrV hdrV_hdrOfV sidOfV_sidV sidV_sidOfV
  keyIndQdec_keyIndQenc keyIndRdec_keyIndRenc
  boolToParty_partyToBool recvResultDec_recvResultEnc recvResultEnc_recvResultDec)
open Computational.Proofs.E2E.Dsl.ClampsLossless (e2ePureOps_eval_parsePreKeyWire_lossless)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v cost_v
  eLet eCaseOpt eCaseSum eAny
  letV bindV caseOptV caseSumV
  orE eval_orE isSomeE eval_isSomeE optMapE eval_optMapE
  hdrIkA stepAIface liftP_pure liftP_bind liftP_map
  e2eKeyIndStateTy e2eKeyIndStateToVal e2eValToKeyIndState
  KeyIndSetupBounded pqxdhKeyIndImpl1KeyReal_preserves_setupBounded)
open Computational.Proofs.E2E.Dsl.SmReachInv (SmReachBounded smReachBounded_initState)
open Computational.Proofs.E2E.Dsl.M2Interfaces (smQdec smQdec_smQenc smQenc_smQdec smRenc
  e2eGsTy e2eGsEnc e2eGsDec PqxdhSimIface)
open Computational.Proofs.E2E.Dsl.M3Interfaces (e2eMirrorPrinEntryTy
  e2eMirrorBaseTy e2eMirrorBaseEnc
  e2eInstMetaTy e2eInstMetaEnc
  e2eModelInstTy e2eModelInstEnc
  e2eDrvStateTy e2eDrvStateEnc
  drvSetStE eval_drvSetStE cost_drvSetStE
  prefixCtxEnc packSmRespEnc unpackSmRespDec
  smRenc_id_eq_packSmRespEnc smRdec_id_packSmRespEnc
  e2eGameRT mkTestSessionE mkRevealSpkSkE defaultPrefixCtxE
  eval_mkTestSessionE eval_mkRevealSpkSkE eval_defaultPrefixCtxE
  DrvMirrorBounded DrvMetaAligned drvMetaAligned_finishStartSpk
  DrvSessionsBounded KeyIndReachBounded
  bhPromoteSlotK promoteSlotKEnc bhFilterSmQuery bhExtSmStep
  StartAndExtSmIface respNotRevealedE eval_respNotRevealedE cost_respNotRevealedE)
open Computational.Proofs.E2E.Dsl.StartAndExtSmAux (
  e2eDecodePreKeyMsg_eq e2eHdrOfPreKeyMsg_eq e2ePartneredInnerBytes_false_eq
  mbPrins imBobAccepted imIkACorr miSid miHdr miIdA miIdB miSpkCoins miSetGsE
  drvBase drvCorrPrins drvRevSpks drvInsts drvInstMeta drvSt drvB
  drvSetInstMetaE drvSetInstsAndPausedE
  eval_miSetGsE eval_drvSetInstMetaE eval_drvSetInstsAndPausedE
  listGetOptE eval_listGetOptE cost_listGetOptE
  listSetE eval_listSetE cost_listSetE
  hdrEqE eval_hdrEqE cost_hdrEqE
  bhDrvSessionInitPrinE eval_bhDrvSessionInitPrinE
  bhInitRegIdE eval_bhInitRegIdE
  prepStartSpkE eval_prepStartSpkE cost_prepStartSpkE
  finishStartSpkGenE eval_finishStartSpkGenE cost_finishStartSpkGenE)

attribute [local irreducible]
  listGetOptE listSetE hdrEqE prepStartSpkE finishStartSpkGenE

/-! ## Helpers -/

section Helpers

theorem support_liftP_subset {S : Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S T) {α : Type} (p : ProbComp α) :
    support (I.liftP p) ⊆ support p := by
  induction p using OracleComp.inductionOn with
  | pure x =>
    simp [Iface.liftP]
  | query_bind t k ih =>
    intro y hy
    simp only [Iface.liftP, simulateQ_bind, simulateQ_query, mem_support_bind_iff] at hy ⊢
    rcases hy with ⟨u, -, hy⟩
    exact ⟨u, OracleComp.mem_support_query t u, ih u hy⟩

private theorem all_eq_not_any_not {α : Type} (p : α → Bool) :
    ∀ (l : List α), l.all p = !(l.any fun x => !p x)
  | [] => rfl
  | x :: xs => by
    simp only [List.all_cons, List.any_cons, Bool.not_or, Bool.not_not, all_eq_not_any_not p xs]

private theorem mapIdx_const_id {α : Type} :
    ∀ (xs : List α) (f : ℕ → α → α), (∀ i x, f i x = x) → xs.mapIdx f = xs := by
  intro xs
  induction xs with
  | nil => intro _ _; rfl
  | cons x xs ih =>
    intro f hf
    rw [List.mapIdx_cons, hf 0 x, ih (fun i y => f (i + 1) y) (fun i y => hf (i + 1) y)]

private theorem mapIdx_clearGs_eq_set {S : SignalPqxdh.Setup} {ℓ : ℕ} :
    ∀ (l : List (BHModelInst S ℓ)) (k : ℕ) (d : BHModelInst S ℓ),
      l[k]? = some d →
      l.mapIdx (fun i d0 => if i = k then { d0 with gs := none } else d0) =
        l.set k { d with gs := none }
  | [], _, _, hk => by simp at hk
  | d0 :: ds, 0, d, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    rw [List.mapIdx_cons]
    simp only [↓reduceIte, List.set_cons_zero]
    congr 1
    exact mapIdx_const_id ds _ (fun i x => by simp)
  | d0 :: ds, k + 1, d, hk => by
    simp only [List.getElem?_cons_succ] at hk
    rw [List.mapIdx_cons]
    simp only [Nat.zero_ne_add_one, ↓reduceIte, List.set_cons_succ]
    congr 1
    have heq : (fun i (x : BHModelInst S ℓ) => if i + 1 = k + 1 then { x with gs := none } else x) =
        (fun i (x : BHModelInst S ℓ) => if i = k then { x with gs := none } else x) := by
      funext i x; simp
    rw [heq]
    exact mapIdx_clearGs_eq_set ds k d hk

private theorem mem_set_iff_or {α : Type} :
    ∀ (l : List α) (i : ℕ) (x y : α), y ∈ l.set i x → y = x ∨ y ∈ l
  | [], _, _, _, hy => nomatch hy
  | _ :: as, 0, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ hmem)
  | a :: as, i + 1, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inr List.mem_cons_self
    · rcases mem_set_iff_or as i x y hmem with rfl | hmem'
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem a hmem')

private theorem foldr_corrTbl_apply {n : ℕ} :
    ∀ (cs : List (Fin n)) (u : Fin n),
      (cs.foldr (fun (c : Fin n) (m : ℕ → Bool) (j : ℕ) =>
        if j = c.val then true else m j) (fun _ => false)) u.val = cs.contains u
  | [], _ => rfl
  | c :: cs, u => by
    dsimp only [List.foldr]
    rw [List.contains_cons]
    by_cases h : u.val = c.val
    · have huc : u = c := Fin.ext h
      subst huc
      simp
    · have hne : (u == c) = false := beq_false_of_ne (fun huc => h (congrArg Fin.val huc))
      simp only [h, ↓reduceIte, hne, Bool.false_or]
      exact foldr_corrTbl_apply cs u

end Helpers

/-! ## Session-start combinators and slot promotion -/

section SessionStartAndPromotion

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "E2EExpr" => Expr (e2eOps ℓ P C K decT encT)

def finishStartSpkCost (qStart nPrins nBundles nOpks nSends : ℕ) : ℕ :=
  180 * qStart + 96 * nSends + 3300 * nBundles + 100 * nPrins + 144 * nOpks + 94890

/-- Pure `Comp` wrapper around `finishStartSpkGenE` matching `bhE2EFinishStartSpk`. -/
def finishStartSpkC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT)
    (acE : E2EExpr Γ BV256) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) :=
  .ret (finishStartSpkGenE qStart nPrins nBundles nOpks nSends
    bModeE σE (.pair sidE (.pair kr1E (.pair kr2E acE))))

theorem finishStartSpkC_cost {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT)
    (acE : E2EExpr Γ BV256) :
    (finishStartSpkC I₀ qStart nPrins nBundles nOpks nSends
      bModeE σE sidE kr1E kr2E acE).cost ≤
      bModeE.cost + σE.cost + sidE.cost + kr1E.cost + kr2E.cost + acE.cost +
        finishStartSpkCost qStart nPrins nBundles nOpks nSends := by
  have hg := cost_finishStartSpkGenE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends
    bModeE σE (.pair sidE (.pair kr1E (.pair kr2E acE)))
  unfold finishStartSpkC finishStartSpkCost
  simp only [Comp.cost, Expr.cost] at hg ⊢
  omega

theorem finishStartSpkC_queries {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT)
    (acE : E2EExpr Γ BV256)
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (finishStartSpkC I₀ qStart nPrins nBundles nOpks nSends
      bModeE σE sidE kr1E kr2E acE).queries w (fun _ => 0) = 0 := rfl

theorem finishStartSpkC_eval {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT)
    (acE : E2EExpr Γ BV256)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hsid : sidE.eval ρ = sidV sid)
    (hkr1 : kr1E.eval ρ = keyIndRenc kr1)
    (hkr2 : kr2E.eval ρ = keyIndRenc kr2)
    (hbnd : DrvMirrorBounded nPrins nBundles nOpks nSends nCorr qStart σ)
    (hCorrN : nCorr ≤ nPrins) :
    (finishStartSpkC I₀ qStart nPrins nBundles nOpks nSends
      bModeE σE sidE kr1E kr2E acE).eval ρ =
      let res := bhE2EFinishStartSpk C K (bModeE.eval ρ) σ sid kr1 kr2 (acE.eval ρ)
      pure (res.1, e2eDrvStateEnc res.2) := by
  have hbnd0 : DrvMirrorBounded nPrins nBundles nOpks nSends 0 qStart σ ∨
      (σ.insts.length ≤ qStart ∧ σ.instMeta.length ≤ qStart ∧ σ.prins.length ≤ nPrins ∧
       σ.bundles.length ≤ nBundles ∧ σ.opks.length ≤ nOpks ∧ σ.sends.length ≤ nSends ∧
       σ.corrPrins.length ≤ nPrins) :=
    Or.inr ⟨hbnd.insts_le, hbnd.instMeta_le, hbnd.prins_le, hbnd.bundles_le,
      hbnd.opks_le, hbnd.sends_le, hbnd.corrPrins_le.trans hCorrN⟩
  unfold finishStartSpkC
  simp only [Comp.eval]
  rw [eval_finishStartSpkGenE qStart nPrins nBundles nOpks nSends
    bModeE σE (.pair sidE (.pair kr1E (.pair kr2E acE))) ρ hσ hbnd0]
  simp only [hsid, hkr1, hkr2, sidOfV_sidV, keyIndRdec_keyIndRenc]

attribute [local irreducible] finishStartSpkC

def sampleBv256C {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    {Γ : List (Ty (e2eSig ℓ))} :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ BV256 :=
  .sample (I := stepAIface ℓ I₀) (UniformSamplerTag.base E2EUnifBase.bv256) .unit

@[simp] theorem sampleBv256C_cost {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    {Γ : List (Ty (e2eSig ℓ))} :
    (sampleBv256C (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀ (Γ := Γ)).cost = 2 := rfl

@[simp] theorem sampleBv256C_queries {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    {Γ : List (Ty (e2eSig ℓ))} (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (sampleBv256C (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀ (Γ := Γ)).queries w (fun _ => 0) = 0 := rfl

@[simp] theorem sampleBv256C_eval {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    {Γ : List (Ty (e2eSig ℓ))} (ρ : Env Γ) :
    (sampleBv256C (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀).eval ρ =
      (stepAIface ℓ I₀).liftP ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := rfl

def localStartGenC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) :=
  letV (.pair bModeE (.pair σE (.pair sidE (.pair kr1E kr2E)))) fun p =>
    bindV (sampleBv256C I₀) fun ac =>
      finishStartSpkC I₀ qStart nPrins nBundles nOpks nSends
        (.fst (v p))
        (.fst (.snd (v p)))
        (.fst (.snd (.snd (v p))))
        (.fst (.snd (.snd (.snd (v p)))))
        (.snd (.snd (.snd (.snd (v p)))))
        (v ac)

theorem localStartGenC_cost {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT) :
    (localStartGenC I₀ qStart nPrins nBundles nOpks nSends bModeE σE sidE kr1E kr2E).cost ≤
      bModeE.cost + σE.cost + sidE.cost + kr1E.cost + kr2E.cost +
        finishStartSpkCost qStart nPrins nBundles nOpks nSends + 40 := by
  let τp : Ty (e2eSig ℓ) :=
    .prod (.opt .bool) (.prod (e2eDrvStateTy S ℓ) (.prod (sidT S) (.prod keyIndRT keyIndRT)))
  have hf := finishStartSpkC_cost (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I₀ qStart nPrins nBundles nOpks nSends
    (Γ := BV256 :: τp :: Γ)
    (.fst (.var (.succ .zero)))
    (.fst (.snd (.var (.succ .zero))))
    (.fst (.snd (.snd (.var (.succ .zero)))))
    (.fst (.snd (.snd (.snd (.var (.succ .zero))))))
    (.snd (.snd (.snd (.snd (.var (.succ .zero))))))
    (.var .zero)
  dsimp only [τp] at hf
  unfold localStartGenC
  dsimp only [letV, bindV, v, Ext.wk]
  simp only [Comp.cost, Expr.cost, sampleBv256C_cost] at hf ⊢
  omega

theorem localStartGenC_queries {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT)
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (localStartGenC I₀ qStart nPrins nBundles nOpks nSends
      bModeE σE sidE kr1E kr2E).queries w (fun _ => 0) = 0 := by
  unfold localStartGenC
  simp only [letV, bindV, Comp.queries, sampleBv256C_queries, finishStartSpkC_queries, Nat.add_zero]

theorem localStartGenC_eval {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hsid : sidE.eval ρ = sidV sid)
    (hkr1 : kr1E.eval ρ = keyIndRenc kr1)
    (hkr2 : kr2E.eval ρ = keyIndRenc kr2)
    (hbnd : DrvMirrorBounded nPrins nBundles nOpks nSends nCorr qStart σ)
    (hCorrN : nCorr ≤ nPrins) :
    (localStartGenC I₀ qStart nPrins nBundles nOpks nSends
      bModeE σE sidE kr1E kr2E).eval ρ =
      (stepAIface ℓ I₀).liftP (do
        let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let res := bhE2EFinishStartSpk C K (bModeE.eval ρ) σ sid kr1 kr2 ac
        return (res.1, e2eDrvStateEnc res.2)) := by
  unfold localStartGenC
  simp only [letV, bindV, Comp.eval, Expr.eval, pure_bind, sampleBv256C_eval,
    liftP_bind, liftP_pure]
  congr 1
  funext ac
  exact finishStartSpkC_eval I₀ qStart nPrins nBundles nOpks nSends nCorr
    _ _ _ _ _ _ _ σ sid kr1 kr2
    (by simp only [v, Ext.wk, Expr.eval, Env.get, hσ])
    (by simp only [v, Ext.wk, Expr.eval, Env.get, hsid])
    (by simp only [v, Ext.wk, Expr.eval, Env.get, hkr1])
    (by simp only [v, Ext.wk, Expr.eval, Env.get, hkr2])
    hbnd hCorrN

attribute [local irreducible] localStartGenC

/-- Coin-sampling `bhE2EFinishStartSpk` specialized to `bMode? = some σ.b` (`kindRed` start path). -/
def localStartC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) :=
  letV (.pair σE (.pair sidE (.pair kr1E kr2E))) fun p =>
    localStartGenC I₀ qStart nPrins nBundles nOpks nSends
      (.some (drvB (.fst (v p))))
      (.fst (v p))
      (.fst (.snd (v p)))
      (.fst (.snd (.snd (v p))))
      (.snd (.snd (.snd (v p))))

theorem localStartC_cost {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT) :
    (localStartC I₀ qStart nPrins nBundles nOpks nSends σE sidE kr1E kr2E).cost ≤
      σE.cost + sidE.cost + kr1E.cost + kr2E.cost +
        finishStartSpkCost qStart nPrins nBundles nOpks nSends + 70 := by
  let τp : Ty (e2eSig ℓ) :=
    .prod (e2eDrvStateTy S ℓ) (.prod (sidT S) (.prod keyIndRT keyIndRT))
  have hg := localStartGenC_cost (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I₀ qStart nPrins nBundles nOpks nSends
    (Γ := τp :: Γ)
    (.some (drvB (.fst (.var .zero))))
    (.fst (.var .zero))
    (.fst (.snd (.var .zero)))
    (.fst (.snd (.snd (.var .zero))))
    (.snd (.snd (.snd (.var .zero))))
  dsimp only [τp] at hg
  unfold localStartC
  dsimp only [letV, v, Ext.wk]
  simp only [drvB, Comp.cost, Expr.cost] at hg ⊢
  omega

theorem localStartC_queries {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT)
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (localStartC I₀ qStart nPrins nBundles nOpks nSends
      σE sidE kr1E kr2E).queries w (fun _ => 0) = 0 := by
  unfold localStartC
  simp only [letV, Comp.queries, localStartGenC_queries, Nat.add_zero]

theorem localStartC_eval {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hsid : sidE.eval ρ = sidV sid)
    (hkr1 : kr1E.eval ρ = keyIndRenc kr1)
    (hkr2 : kr2E.eval ρ = keyIndRenc kr2)
    (hbnd : DrvMirrorBounded nPrins nBundles nOpks nSends nCorr qStart σ)
    (hCorrN : nCorr ≤ nPrins) :
    (localStartC I₀ qStart nPrins nBundles nOpks nSends
      σE sidE kr1E kr2E).eval ρ =
      (stepAIface ℓ I₀).liftP (do
        let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let res := bhE2EFinishStartSpk C K (some σ.b) σ sid kr1 kr2 ac
        return (res.1, e2eDrvStateEnc res.2)) := by
  unfold localStartC
  simp only [letV, Comp.eval, Expr.eval, pure_bind]
  rw [localStartGenC_eval I₀ qStart nPrins nBundles nOpks nSends nCorr
    _ _ _ _ _ _ σ sid kr1 kr2
    (by simp only [v, Ext.wk, Expr.eval, Env.get, hσ])
    (by simp only [v, Ext.wk, Expr.eval, Env.get, hsid])
    (by simp only [v, Ext.wk, Expr.eval, Env.get, hkr1])
    (by simp only [v, Ext.wk, Expr.eval, Env.get, hkr2])
    hbnd hCorrN]
  simp only [drvB, v, Ext.wk, Expr.eval, Env.get, hσ, e2eDrvStateEnc]

attribute [local irreducible] localStartC

theorem bhE2EFinishStartSpk_newInst_reach (bMode? : Option Bool)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256)
    {idx : ℕ} {σ' : BHE2EDrvState S ℓ}
    (hres : bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac = (some idx, σ'))
    {d : BHModelInst S ℓ} (hd : σ'.insts[idx]? = some d)
    {gs₀ : GameState (GhostState Bytes) (Plain ℓ) Bytes} (hgs : d.gs = some gs₀) :
    idx = σ.insts.length ∧ SmReachBounded C K 0 gs₀ := by
  unfold bhE2EFinishStartSpk at hres
  split at hres
  · split_ifs at hres
    · injection hres with hidx hσ'
      cases hidx
      subst hσ'
      simp only [List.getElem?_append_right (Nat.le_refl σ.insts.length),
        Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      rcases Option.mem_map.mp hgs with ⟨b, -, rfl⟩
      exact ⟨rfl, smReachBounded_initState C K _ _ ℓ _ _ b⟩
    · cases hres
  · cases hres

theorem localStartC_support_reach {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends nCorr qBound : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hsid : sidE.eval ρ = sidV sid)
    (hkr1 : kr1E.eval ρ = keyIndRenc kr1)
    (hkr2 : kr2E.eval ρ = keyIndRenc kr2)
    (hbnd : DrvMirrorBounded nPrins nBundles nOpks nSends nCorr qStart σ)
    (hCorrN : nCorr ≤ nPrins)
    (hSess : DrvSessionsBounded C K qBound σ)
    {vOut : (Ty.prod (.opt .nat) (e2eDrvStateTy S ℓ)).denote}
    (hmem : vOut ∈ support ((localStartC I₀ qStart nPrins nBundles nOpks nSends
      σE sidE kr1E kr2E).eval ρ)) :
    ∃ (ac : BitVec 256),
      let res := bhE2EFinishStartSpk C K (some σ.b) σ sid kr1 kr2 ac
      vOut = (res.1, e2eDrvStateEnc res.2) ∧
      DrvMirrorBounded nPrins nBundles nOpks nSends nCorr (qStart + 1) res.2 ∧
      DrvSessionsBounded C K qBound res.2 ∧
      (∀ idx d gs₀, res.1 = some idx → res.2.insts[idx]? = some d → d.gs = some gs₀ →
        SmReachBounded C K 0 gs₀) := by
  rw [localStartC_eval I₀ qStart nPrins nBundles nOpks nSends nCorr
    σE sidE kr1E kr2E ρ σ sid kr1 kr2 hσ hsid hkr1 hkr2 hbnd hCorrN] at hmem
  have hsub := support_liftP_subset (stepAIface ℓ I₀) _ hmem
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsub
  rcases hsub with ⟨ac, -, hvOut⟩
  refine ⟨ac, hvOut, hbnd.finishStartSpk C K (some σ.b) sid kr1 kr2 ac,
    hSess.finishStartSpk C K (some σ.b) sid kr1 kr2 ac, ?_⟩
  intro idx d gs₀ hidx hd hgs
  have hpair : bhE2EFinishStartSpk C K (some σ.b) σ sid kr1 kr2 ac =
      (some idx, (bhE2EFinishStartSpk C K (some σ.b) σ sid kr1 kr2 ac).2) :=
    Prod.ext hidx rfl
  exact (bhE2EFinishStartSpk_newInst_reach (some σ.b) σ sid kr1 kr2 ac hpair hd hgs).2

/-- Simulate `compositionLocalStart (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K bMode? σ sid`
inside `ReductionDsl` using `sim : PqxdhSimIface ℓ S P C K decT encT`. -/
def localStartSimC (sim : PqxdhSimIface ℓ S P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S)) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) :=
  letV (.pair bModeE (.pair σE sidE)) fun p =>
    caseOptV
      (prepStartSpkE qStart nPrins nBundles nOpks nSends
        (.fst (.snd (v p))) (.snd (.snd (v p))))
      (.ret (.pair .none (.fst (.snd (v p)))))
      (fun uj =>
        bindV
          (sim.stepC I₀ nAdv
            (drvSt (.fst (.snd (v p))))
            (mkTestSessionE (.snd (.snd (v p)))))
          fun r1 =>
            bindV
              (sim.stepC I₀ (nAdv + 1)
                (.snd (v r1))
                (mkRevealSpkSkE (v uj)))
              fun r2 =>
                localStartGenC I₀ qStart nPrins nBundles nOpks nSends
                  (.fst (v p))
                  (drvSetStE (.fst (.snd (v p))) (.snd (v r2)))
                  (.snd (.snd (v p)))
                  (.fst (v r1))
                  (.fst (v r2)))

theorem localStartSimC_cost (sim : PqxdhSimIface ℓ S P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S)) :
    (localStartSimC sim I₀ qStart nPrins nBundles nOpks nSends nAdv bModeE σE sidE).cost ≤
      bModeE.cost + σE.cost + sidE.cost +
        sim.stepCost nAdv + sim.stepCost (nAdv + 1) +
        2 * finishStartSpkCost qStart nPrins nBundles nOpks nSends + 300 := by
  let τp : Ty (e2eSig ℓ) := .prod (.opt .bool) (.prod (e2eDrvStateTy S ℓ) (sidT S))
  let τuj : Ty (e2eSig ℓ) := .prod (FinT S.N_id) (FinT S.N_recv)
  let τr : Ty (e2eSig ℓ) := .prod keyIndRT (e2eKeyIndStateTy ℓ S)
  have hp := cost_prepStartSpkE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends
    (Γ := τp :: Γ) (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero)))
  have hs1 := sim.stepC_cost I₀ nAdv (Γ := τuj :: τp :: Γ)
    (drvSt (.fst (.snd (.var (.succ .zero)))))
    (mkTestSessionE (.snd (.snd (.var (.succ .zero)))))
  have hs2 := sim.stepC_cost I₀ (nAdv + 1) (Γ := τr :: τuj :: τp :: Γ)
    (.snd (.var .zero))
    (mkRevealSpkSkE (.var (.succ .zero)))
  have hlg := localStartGenC_cost (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I₀ qStart nPrins nBundles nOpks nSends
    (Γ := τr :: τr :: τuj :: τp :: Γ)
    (.fst (.var (.succ (.succ (.succ .zero)))))
    (drvSetStE (.fst (.snd (.var (.succ (.succ (.succ .zero)))))) (.snd (.var .zero)))
    (.snd (.snd (.var (.succ (.succ (.succ .zero))))))
    (.fst (.var (.succ .zero)))
    (.fst (.var .zero))
  have hset := cost_drvSetStE (O := e2eOps ℓ P C K decT encT) (S := S) (ℓ := ℓ)
    (Γ := τr :: τr :: τuj :: τp :: Γ)
    (.fst (.snd (.var (.succ (.succ (.succ .zero))))))
    (.snd (.var .zero))
  dsimp only [τp, τuj, τr] at hp hs1 hs2 hlg hset
  unfold localStartSimC
  dsimp only [letV, caseOptV, bindV, v, Ext.wk]
  simp only [drvSt, mkTestSessionE, mkRevealSpkSkE, finishStartSpkCost,
    Comp.cost, Expr.cost] at hp hs1 hs2 hlg hset ⊢
  omega

theorem localStartSimC_queries (sim : PqxdhSimIface ℓ S P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (localStartSimC sim I₀ qStart nPrins nBundles nOpks nSends nAdv
      bModeE σE sidE).queries w (fun _ => 0) = 0 := by
  unfold localStartSimC
  simp only [letV, caseOptV, bindV, Comp.queries, sim.stepC_queries,
    localStartGenC_queries, Nat.add_zero, Nat.max_self]

theorem localStartSimC_eval (sim : PqxdhSimIface ℓ S P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends nCorr nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hsid : sidE.eval ρ = sidV sid)
    (hbnd : DrvMirrorBounded nPrins nBundles nOpks nSends nCorr qStart σ)
    (hCorrN : nCorr ≤ nPrins)
    (hst : KeyIndReachBounded S nAdv σ.st) :
    (localStartSimC sim I₀ qStart nPrins nBundles nOpks nSends nAdv
      bModeE σE sidE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun out => (out.1, e2eDrvStateEnc out.2)) <$>
          compositionLocalStart (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K
            (bModeE.eval ρ) σ sid) := by
  unfold localStartSimC
  simp only [letV, caseOptV, bindV, Comp.eval, Expr.eval, pure_bind]
  rw [eval_prepStartSpkE qStart nPrins nBundles nOpks nSends _ _ _
    (by simp only [v, Ext.wk, Expr.eval, Env.get, hσ])
    hbnd.insts_le hbnd.prins_le hbnd.bundles_le hbnd.opks_le hbnd.sends_le
    (hbnd.corrPrins_le.trans hCorrN)]
  simp only [v, Ext.wk, Expr.eval, Env.get, hsid, sidOfV_sidV, compositionLocalStart]
  rcases hg : bhE2EGuard σ sid with _ | ⟨hdr, bnd, ⟨u, j⟩⟩
  · dsimp only [Option.map, Comp.eval, Expr.eval, Env.get]
    simp only [hσ, map_pure, liftP_pure]
  · simp only [Option.map]
    rw [sim.stepC_eval I₀ nAdv _ _ _ σ.st (.testSession sid) hP
      (by simp only [drvSt, Expr.eval, Env.get, hσ, e2eDrvStateEnc])
      (by simp only [eval_mkTestSessionE, Expr.eval, Env.get, sidOfV_sidV])
      hst.setup hst.advKeys_le]
    simp only [map_eq_bind_pure_comp, Function.comp_def, LawfulMonad.bind_assoc,
      liftP_bind, liftP_pure, pure_bind]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro out1 hout1
    have hout1' : out1 ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
        (.testSession sid)).run σ.st) :=
      support_liftP_subset (stepAIface ℓ I₀) _ hout1
    have hst1 : KeyIndReachBounded S (nAdv + 1) out1.2 := hst.pqxdhStep (.testSession sid) hout1'
    rw [sim.stepC_eval I₀ (nAdv + 1) _ _ _ out1.2 (.revealSpkSk u j) hP
      (by simp only [Expr.eval, Env.get])
      (by simp only [eval_mkRevealSpkSkE, Expr.eval, Env.get])
      hst1.setup hst1.advKeys_le]
    simp only [map_eq_bind_pure_comp, Function.comp_def, LawfulMonad.bind_assoc,
      liftP_bind, liftP_pure, pure_bind]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro out2 _
    have hbnd2 : DrvMirrorBounded nPrins nBundles nOpks nSends nCorr qStart
        { σ with st := out2.2 } :=
      ⟨hbnd.prins_le, hbnd.bundles_le, hbnd.opks_le, hbnd.sends_le, hbnd.corrPrins_le,
       hbnd.insts_le, hbnd.instMeta_le, hbnd.revSpks_le⟩
    rw [localStartGenC_eval I₀ qStart nPrins nBundles nOpks nSends nCorr _ _ _ _ _ _
      { σ with st := out2.2 } sid out1.1 out2.1
      (by rw [eval_drvSetStE _ _ _ (σ := σ) (st' := out2.2)
            (by simp only [Expr.eval, Env.get, hσ])
            (by simp only [Expr.eval, Env.get])])
      (by simp only [Expr.eval, Env.get])
      (by simp only [Expr.eval, Env.get])
      (by simp only [Expr.eval, Env.get])
      hbnd2 hCorrN]
    simp only [Expr.eval, Env.get, liftP_bind, liftP_pure]

attribute [local irreducible] localStartSimC

theorem compositionLocalStart_preserves (bMode? : Option Bool)
    {nP nB nO nS nC qS nAdv qBound : ℕ} {σ : BHE2EDrvState S ℓ}
    (hMir : DrvMirrorBounded nP nB nO nS nC qS σ)
    (hMeta : DrvMetaAligned σ)
    (hSess : DrvSessionsBounded C K qBound σ)
    (hKi : KeyIndReachBounded S nAdv σ.st)
    (sid : SignalPqxdh.SessionId S)
    {out : Option ℕ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (compositionLocalStart
      (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K bMode? σ sid)) :
    DrvMirrorBounded nP nB nO nS nC (qS + 1) out.2 ∧
      DrvMetaAligned out.2 ∧
      DrvSessionsBounded C K qBound out.2 ∧
      KeyIndReachBounded S (nAdv + 2) out.2.st ∧
      (∀ idx d gs₀, out.1 = some idx → out.2.insts[idx]? = some d → d.gs = some gs₀ →
        SmReachBounded C K 0 gs₀) := by
  unfold compositionLocalStart at hout
  rcases hg : bhE2EGuard σ sid with _ | ⟨hdr, bnd, ⟨u, j⟩⟩
  · simp only [hg, support_pure, Set.mem_singleton_iff] at hout
    subst hout
    refine ⟨hMir.mono (le_refl _) (le_refl _) (le_refl _) (le_refl _) (le_refl _) (Nat.le_succ _),
      hMeta, hSess, hKi.mono (by omega), ?_⟩
    intro _ _ _ hnone; cases hnone
  · simp only [hg, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨kr1, st1⟩, h1, ⟨kr2, st2⟩, h2, ac, -, hout⟩
    have hKi1 : KeyIndReachBounded S (nAdv + 1) st1 := hKi.pqxdhStep (.testSession sid) h1
    have hKi2 : KeyIndReachBounded S (nAdv + 2) st2 := hKi1.pqxdhStep (.revealSpkSk u j) h2
    have hMir2 : DrvMirrorBounded nP nB nO nS nC qS { σ with st := st2 } :=
      ⟨hMir.prins_le, hMir.bundles_le, hMir.opks_le, hMir.sends_le, hMir.corrPrins_le,
       hMir.insts_le, hMir.instMeta_le, hMir.revSpks_le⟩
    have hMeta2 : DrvMetaAligned { σ with st := st2 } := hMeta
    have hSess2 : DrvSessionsBounded C K qBound { σ with st := st2 } := hSess
    have hstEq : (bhE2EFinishStartSpk C K bMode? { σ with st := st2 } sid kr1 kr2 ac).2.st = st2 := by
      unfold bhE2EFinishStartSpk
      split
      · split_ifs <;> rfl
      · rfl
    subst hout
    refine ⟨hMir2.finishStartSpk C K bMode? sid kr1 kr2 ac,
      drvMetaAligned_finishStartSpk C K bMode? hMeta2 sid kr1 kr2 ac,
      hSess2.finishStartSpk C K bMode? sid kr1 kr2 ac,
      by rw [hstEq]; exact hKi2, ?_⟩
    intro idx d gs₀ hidx hd hgs
    have hpair : bhE2EFinishStartSpk C K bMode? { σ with st := st2 } sid kr1 kr2 ac =
        (some idx, (bhE2EFinishStartSpk C K bMode? { σ with st := st2 } sid kr1 kr2 ac).2) :=
      Prod.ext hidx rfl
    exact (bhE2EFinishStartSpk_newInst_reach bMode? { σ with st := st2 } sid kr1 kr2 ac
      hpair hd hgs).2

/-- Pure expression implementing `bhPromoteSlotK k idx? σ'` when `σ'.insts.length ≤ nInsts`. -/
def promoteSlotKE (nInsts : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (idxOptE : E2EExpr Γ (.opt .nat))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) :
    E2EExpr Γ (.sum (.prod (.opt .nat) (e2eDrvStateTy S ℓ))
      (.prod prefixCtxT (.prod (.opt .nat) (e2eDrvStateTy S ℓ)))) :=
  eLet (.pair kE (.pair idxOptE σE)) fun p =>
    .ite (.lt (.fst (v p)) (.len (drvInsts (.snd (.snd (v p))))))
      (eCaseOpt (listGetOptE nInsts (drvInsts (.snd (.snd (v p)))) (.fst (v p)))
        (.inr (.pair
          (defaultPrefixCtxE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT))
          (.pair (.fst (.snd (v p)))
            (drvSetInstsAndPausedE (.snd (.snd (v p)))
              (drvInsts (.snd (.snd (v p)))) (.bool true)))))
        (fun d =>
          .inr (.pair
            (.pair (miIdA (v d)) (.pair (miIdB (v d)) (miSpkCoins (v d))))
            (.pair (.fst (.snd (v p)))
              (drvSetInstsAndPausedE (.snd (.snd (v p)))
                (listSetE nInsts (drvInsts (.snd (.snd (v p)))) (.fst (v p))
                  (miSetGsE (v d) .none))
                (.bool true))))))
      (.inl (.pair (.fst (.snd (v p))) (.snd (.snd (v p)))))

theorem eval_promoteSlotKE (nInsts : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (idxOptE : E2EExpr Γ (.opt .nat))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (ρ : Env Γ) (σ' : BHE2EDrvState S ℓ)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ')
    (hlen : σ'.insts.length ≤ nInsts) :
    (promoteSlotKE nInsts kE idxOptE σE).eval ρ =
      promoteSlotKEnc (bhPromoteSlotK (kE.eval ρ) (idxOptE.eval ρ) σ') := by
  unfold promoteSlotKE bhPromoteSlotK
  simp only [eLet, v, Ext.wk, Expr.eval, Env.get, drvInsts, hσ, e2eDrvStateEnc, List.length_map]
  by_cases hlt : kE.eval ρ < σ'.insts.length
  · have hlenEnc : (σ'.insts.map (e2eModelInstEnc (ℓ := ℓ))).length ≤ nInsts := by
      simpa using hlen
    simp only [hlt, decide_true, ↓reduceIte, eCaseOpt, Expr.eval]
    rw [eval_listGetOptE nInsts _ _ _ (by exact hlenEnc)]
    simp only [Expr.eval, Env.get, List.getElem?_map]
    have ⟨d, hd⟩ : ∃ d, σ'.insts[kE.eval ρ]? = some d :=
      ⟨σ'.insts[kE.eval ρ], List.getElem?_eq_getElem hlt⟩
    rw [hd]
    dsimp only [Option.map, Expr.eval, Env.get, miIdA, miIdB, miSpkCoins, e2eModelInstEnc]
    simp only [promoteSlotKEnc, prefixCtxEnc, mapIdx_clearGs_eq_set σ'.insts (kE.eval ρ) d hd]
    congr 1
    congr 1
    congr 1
    refine (eval_drvSetInstsAndPausedE _ _ _ _ (σ := σ')
      (ds := σ'.insts.set (kE.eval ρ) { d with gs := none }) rfl ?_).trans rfl
    rw [eval_listSetE nInsts _ _ _ _ (by exact hlenEnc),
        eval_miSetGsE _ _ _ (d := d) (gs? := none) rfl rfl]
    simp only [Expr.eval, Env.get, List.map_set]
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte, promoteSlotKEnc, e2eDrvStateEnc]

def promoteSlotKCost (nInsts : ℕ) : ℕ :=
  68 * nInsts + 700

def promoteSlotKC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (nInsts : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (idxOptE : E2EExpr Γ (.opt .nat))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.sum (.prod (.opt .nat) (e2eDrvStateTy S ℓ))
        (.prod prefixCtxT (.prod (.opt .nat) (e2eDrvStateTy S ℓ)))) :=
  .ret (promoteSlotKE nInsts kE idxOptE σE)

theorem promoteSlotKC_cost {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (nInsts : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (idxOptE : E2EExpr Γ (.opt .nat))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) :
    (promoteSlotKC I₀ nInsts kE idxOptE σE).cost ≤
      kE.cost + idxOptE.cost + σE.cost + promoteSlotKCost nInsts := by
  let τp : Ty (e2eSig ℓ) := .prod .nat (.prod (.opt .nat) (e2eDrvStateTy S ℓ))
  have hget := cost_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) nInsts
    (Γ := τp :: Γ) (drvInsts (.snd (.snd (.var .zero)))) (.fst (.var .zero))
  have hset := cost_listSetE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) nInsts
    (Γ := e2eModelInstTy S ℓ :: τp :: Γ)
    (drvInsts (.snd (.snd (.var (.succ .zero)))))
    (.fst (.var (.succ .zero)))
    (miSetGsE (.var .zero) .none)
  dsimp only [τp] at hget hset
  unfold promoteSlotKC promoteSlotKE promoteSlotKCost
  dsimp only [v, Ext.wk]
  simp only [drvInsts, drvSetInstsAndPausedE, drvBase, drvCorrPrins, drvRevSpks,
    drvInstMeta, drvSt, drvB, miIdA, miIdB, miSpkCoins, miSetGsE, miSid, miHdr,
    defaultPrefixCtxE, eLet, eCaseOpt, Comp.cost, Expr.cost, cost_v,
    cost_e2ePureOp, E2EPureOp.cost, PNat.val_ofNat, List.length_nil] at hget hset ⊢
  omega

theorem promoteSlotKC_queries {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (nInsts : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (idxOptE : E2EExpr Γ (.opt .nat))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (promoteSlotKC I₀ nInsts kE idxOptE σE).queries w (fun _ => 0) = 0 := rfl

theorem promoteSlotKC_eval {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (nInsts : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (idxOptE : E2EExpr Γ (.opt .nat))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (ρ : Env Γ) (σ' : BHE2EDrvState S ℓ)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ')
    (hlen : σ'.insts.length ≤ nInsts) :
    (promoteSlotKC I₀ nInsts kE idxOptE σE).eval ρ =
      pure (promoteSlotKEnc (bhPromoteSlotK (kE.eval ρ) (idxOptE.eval ρ) σ')) := by
  unfold promoteSlotKC
  simp only [Comp.eval, eval_promoteSlotKE nInsts kE idxOptE σE ρ σ' hσ hlen]

attribute [local irreducible] promoteSlotKE promoteSlotKC

theorem bhPromoteSlotK_preserves (k : ℕ) (idx? : Option ℕ)
    {nP nB nO nS nC qS qBound : ℕ} {σ' : BHE2EDrvState S ℓ}
    (hMir : DrvMirrorBounded nP nB nO nS nC qS σ')
    (hMeta : DrvMetaAligned σ')
    (hSess : DrvSessionsBounded C K qBound σ') :
    match bhPromoteSlotK k idx? σ' with
    | .inl (_, σ1) =>
      DrvMirrorBounded nP nB nO nS nC qS σ1 ∧
      DrvMetaAligned σ1 ∧
      DrvSessionsBounded C K qBound σ1 ∧
      σ1.st = σ'.st
    | .inr (_, (_, σ1)) =>
      DrvMirrorBounded nP nB nO nS nC qS σ1 ∧
      DrvMetaAligned σ1 ∧
      DrvSessionsBounded C K qBound σ1 ∧
      σ1.st = σ'.st ∧
      σ1.paused = true := by
  unfold bhPromoteSlotK
  by_cases hlt : k < σ'.insts.length
  · simp only [hlt, ↓reduceIte]
    have ⟨d, hd⟩ : ∃ d, σ'.insts[k]? = some d := ⟨σ'.insts[k], List.getElem?_eq_getElem hlt⟩
    rw [mapIdx_clearGs_eq_set σ'.insts k d hd]
    refine ⟨⟨hMir.prins_le, hMir.bundles_le, hMir.opks_le, hMir.sends_le, hMir.corrPrins_le,
             by simp [hMir.insts_le], hMir.instMeta_le, hMir.revSpks_le⟩,
            by simp [DrvMetaAligned] at hMeta ⊢; exact hMeta, ?_, trivial, trivial⟩
    intro d1 hd1 gs hgs
    rcases mem_set_iff_or σ'.insts k { d with gs := none } d1 hd1 with rfl | hmem
    · cases hgs
    · exact hSess d1 hmem gs hgs
  · simp only [hlt, ↓reduceIte]
    exact ⟨hMir, hMeta, hSess, trivial⟩

end SessionStartAndPromotion

/-! ## Cleanliness, wire filter, and external `SM.spec` routing -/

section ExtSmRouting

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "E2EExpr" => Expr (e2eOps ℓ P C K decT encT)

/-- Pure expression computing the per-instance cleanliness `bhE2EDrvInstClean σ k` (`DEV-C17`). -/
def bhE2EDrvInstCleanE (qStart nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (kE : E2EExpr Γ .nat) : E2EExpr Γ .bool :=
  eLet (.pair σE kE) fun p =>
    eCaseOpt (listGetOptE qStart (drvInsts (.fst (v p))) (.snd (v p))) (.bool true) fun d =>
      eCaseOpt (listGetOptE qStart (drvInstMeta (.fst (v p))) (.snd (v p))) (.bool true) fun im =>
        .and
          (.and (isSomeE (bhDrvSessionInitPrinE (miSid (v d)))) (.not (imIkACorr (v im))))
          (respNotRevealedE nCorr (v im) (drvRevSpks (.fst (v p))))

@[simp] theorem eval_bhE2EDrvInstCleanE (qStart nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (kE : E2EExpr Γ .nat) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} {k : ℕ} (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hk : kE.eval ρ = k)
    (hInsts : σ.insts.length ≤ qStart) (hMeta : σ.instMeta.length ≤ qStart)
    (hRev : σ.revealedSpks.length ≤ nCorr) :
    (bhE2EDrvInstCleanE qStart nCorr σE kE).eval ρ = bhE2EDrvInstClean σ k := by
  have hInstsEnc : (σ.insts.map (e2eModelInstEnc (ℓ := ℓ))).length ≤ qStart := by
    simpa using hInsts
  have hMetaEnc : (σ.instMeta.map (e2eInstMetaEnc (ℓ := ℓ))).length ≤ qStart := by
    simpa using hMeta
  unfold bhE2EDrvInstCleanE bhE2EDrvInstClean
  simp only [eLet, eCaseOpt, Expr.eval]
  rw [eval_listGetOptE qStart _ _ _ (by simpa [v, Ext.wk, Expr.eval, Env.get, drvInsts, hσ,
    e2eDrvStateEnc] using hInstsEnc)]
  simp only [drvInsts, v, Ext.wk, Expr.eval, Env.get, hσ, hk, e2eDrvStateEnc, List.getElem?_map]
  rcases hd : σ.insts[k]? with _ | d
  · rfl
  · simp only [Option.map]
    rw [eval_listGetOptE qStart _ _ _ (by simpa [v, Ext.wk, Expr.eval, Env.get, drvInstMeta, hσ,
      e2eDrvStateEnc] using hMetaEnc)]
    simp only [drvInstMeta, Expr.eval, Env.get,
      List.getElem?_map]
    rcases him : σ.instMeta[k]? with _ | im
    · rfl
    · simp only [Option.map, Expr.eval, eval_isSomeE, eval_bhDrvSessionInitPrinE, miSid,
        imIkACorr, Env.get, e2eModelInstEnc, e2eInstMetaEnc, sidOfV_sidV]
      rw [eval_respNotRevealedE nCorr _ _ _ (im := im) (revSpks := σ.revealedSpks)
        (by simp [Expr.eval, e2eInstMetaEnc])
        (by simp [drvRevSpks, Expr.eval]) hRev]
      rfl

theorem cost_bhE2EDrvInstCleanE (qStart nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (kE : E2EExpr Γ .nat) :
    (bhE2EDrvInstCleanE qStart nCorr σE kE).cost ≤
      σE.cost + kE.cost + 64 * qStart + 20 * nCorr + 140 := by
  let τp : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) .nat
  have hg1 := cost_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart (Γ := τp :: Γ)
    (drvInsts (.fst (.var .zero))) (.snd (.var .zero))
  have hg2 := cost_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := e2eModelInstTy S ℓ :: τp :: Γ)
    (drvInstMeta (.fst (.var (.succ .zero)))) (.snd (.var (.succ .zero)))
  have hrn := cost_respNotRevealedE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr
    (Γ := e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ :: τp :: Γ)
    (.var .zero) (drvRevSpks (.fst (.var (.succ (.succ .zero)))))
  dsimp only [τp] at hg1 hg2 hrn
  unfold bhE2EDrvInstCleanE
  dsimp only [v, Ext.wk]
  simp only [drvInsts, drvInstMeta, drvRevSpks, miSid, imIkACorr, isSomeE,
    bhDrvSessionInitPrinE, eLet, eCaseOpt, eCaseSum, Expr.cost, cost_v] at hg1 hg2 hrn ⊢
  omega

attribute [local irreducible] bhE2EDrvInstCleanE

def corrTblE (nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (corrPrinsE : E2EExpr Γ (.list (FinT S.N_id))) : E2EExpr Γ (.tbl .bool) :=
  .foldrB nCorr corrPrinsE (.tconst (.bool false))
    (.tset .v1 (e2ePureOp (.finVal S.N_id) .v0) (.bool true))

@[simp] theorem eval_corrTblE_apply (nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (corrPrinsE : E2EExpr Γ (.list (FinT S.N_id))) (ρ : Env Γ)
    (hlen : (corrPrinsE.eval ρ).length ≤ nCorr) (u : Fin S.N_id) :
    (corrTblE nCorr corrPrinsE).eval ρ u.val = (corrPrinsE.eval ρ).contains u := by
  simp only [corrTblE, Expr.eval, Expr.v0, Expr.v1, Env.get, eval_e2ePureOp, E2EPureOp.eval,
    List.take_of_length_le hlen]
  exact foldr_corrTbl_apply (corrPrinsE.eval ρ) u

theorem cost_corrTblE (nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (corrPrinsE : E2EExpr Γ (.list (FinT S.N_id))) :
    (corrTblE nCorr corrPrinsE).cost ≤ corrPrinsE.cost + 135 * nCorr + 4 := by
  simp only [corrTblE, Expr.cost, Expr.v0, Expr.v1, cost_e2ePureOp, E2EPureOp.cost]
  omega

/-- Linear `O(nCorr + nPrins)` expression computing `bhE2EInstIkACorr σ d`. -/
def bhE2EInstIkACorrE (nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (dE : E2EExpr Γ (e2eModelInstTy S ℓ)) : E2EExpr Γ .bool :=
  eLet (.pair σE dE) fun p =>
    eLet (corrTblE nCorr (drvCorrPrins (.fst (v p)))) fun tbl =>
      orE
        (eCaseOpt (bhDrvSessionInitPrinE (miSid (.snd (v p))))
          (.bool true)
          (fun u => .tget (v tbl) (e2ePureOp (.finVal S.N_id) (v u))))
        (eAny nPrins (mbPrins (drvBase (.fst (v p)))) fun pe =>
          .and
            (e2ePureOp (.pbytesEq 32 32) (.pair (.snd (v pe)) (hdrIkA (miHdr (.snd (v p))))))
            (.tget (v tbl) (e2ePureOp (.finVal S.N_id) (.fst (v pe)))))

@[simp] theorem eval_bhE2EInstIkACorrE (nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (dE : E2EExpr Γ (e2eModelInstTy S ℓ))
    (ρ : Env Γ) {σ : BHE2EDrvState S ℓ} {d : BHModelInst S ℓ}
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hd : dE.eval ρ = e2eModelInstEnc d)
    (hCorr : σ.corrPrins.length ≤ nCorr)
    (hPrins : σ.prins.length ≤ nPrins) :
    (bhE2EInstIkACorrE nCorr nPrins σE dE).eval ρ = bhE2EInstIkACorr σ d := by
  unfold bhE2EInstIkACorrE bhE2EInstIkACorr
  simp only [eLet, eval_orE, eCaseOpt, eAny, v, Ext.wk, Expr.eval, Env.get,
    drvCorrPrins, drvBase, mbPrins, miSid, miHdr, hdrIkA, eval_bhDrvSessionInitPrinE,
    eval_e2ePureOp, E2EPureOp.eval,
    hσ, hd, e2eDrvStateEnc, e2eMirrorBaseEnc, e2eModelInstEnc, sidOfV_sidV, hdrV,
    List.take_of_length_le hPrins]
  congr 1
  · rcases bhDrvSessionInitPrin? d.sid with _ | u
    · rfl
    · exact eval_corrTblE_apply nCorr _ _ (by exact hCorr) u
  · congr 1
    funext pe
    rw [eval_corrTblE_apply nCorr _ _ (by exact hCorr) pe.1]
    rfl

theorem cost_bhE2EInstIkACorrE (nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (dE : E2EExpr Γ (e2eModelInstTy S ℓ)) :
    (bhE2EInstIkACorrE nCorr nPrins σE dE).cost ≤
      σE.cost + dE.cost + 135 * nCorr + 150 * nPrins + 110 := by
  let τp : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) (e2eModelInstTy S ℓ)
  have htbl := cost_corrTblE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr (Γ := τp :: Γ) (drvCorrPrins (.fst (.var .zero)))
  dsimp only [τp] at htbl
  unfold bhE2EInstIkACorrE
  dsimp only [v, Ext.wk]
  simp only [drvCorrPrins, drvBase, mbPrins, miSid, miHdr, hdrIkA, bhDrvSessionInitPrinE,
    orE, eLet, eCaseOpt, eCaseSum, eAny, Expr.cost, cost_v,
    cost_e2ePureOp, E2EPureOp.cost, PNat.val_ofNat] at htbl ⊢
  omega

attribute [local irreducible] corrTblE bhE2EInstIkACorrE

def isBobRecvSmQE {Γ : List (Ty (e2eSig ℓ))} (sqE : E2EExpr Γ smQT) : E2EExpr Γ .bool :=
  eCaseSum sqE
    (fun _ => .bool false)
    (fun r1 => eCaseSum (v r1)
      (fun _ => .bool false)
      (fun r2 => eCaseSum (v r2)
        (fun dl => .fst (v dl))
        (fun r3 => eCaseSum (v r3)
          (fun ij => .fst (v ij))
          (fun _ => .bool false))))

@[simp] theorem eval_isBobRecvSmQE {Γ : List (Ty (e2eSig ℓ))}
    (sqE : E2EExpr Γ smQT) (ρ : Env Γ) :
    (isBobRecvSmQE sqE).eval ρ =
      bhIsBobRecvSMQuery (smQdec (ℓ := ℓ) (St := GhostState Bytes) (sqE.eval ρ)) := by
  rcases h : sqE.eval ρ with ⟨p, m, r⟩ | ⟨p, m0, m1, r⟩ | ⟨p, c⟩ | ⟨p, c⟩ | p
  · simp [isBobRecvSmQE, smQdec, bhIsBobRecvSMQuery, eCaseSum, v, Ext.wk, Expr.eval, h]
  · simp [isBobRecvSmQE, smQdec, bhIsBobRecvSMQuery, eCaseSum, v, Ext.wk, Expr.eval, h]
  · cases p <;>
      simp [isBobRecvSmQE, smQdec, boolToParty, bhIsBobRecvSMQuery, eCaseSum,
        v, Ext.wk, Expr.eval, h]
  · cases p <;>
      simp [isBobRecvSmQE, smQdec, boolToParty, bhIsBobRecvSMQuery, eCaseSum,
        v, Ext.wk, Expr.eval, h]
  · simp [isBobRecvSmQE, smQdec, bhIsBobRecvSMQuery, eCaseSum, v, Ext.wk, Expr.eval, h]

def isBobAcceptSmRE {Γ : List (Ty (e2eSig ℓ))}
    (sqE : E2EExpr Γ smQT) (srE : E2EExpr Γ (smRT GhostStT)) : E2EExpr Γ .bool :=
  .and (isBobRecvSmQE sqE)
    (eCaseOpt (.fst (.snd srE))
      (.bool false)
      (fun rr => eCaseSum (v rr) (fun _ => .bool false) (fun _ => .bool true)))

@[simp] theorem eval_isBobAcceptSmRE {Γ : List (Ty (e2eSig ℓ))}
    (sqE : E2EExpr Γ smQT) (srE : E2EExpr Γ (smRT GhostStT)) (ρ : Env Γ)
    {sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    {br : BHE2ESmResp ℓ}
    (hsq : sqE.eval ρ = smQenc sq) (hsr : srE.eval ρ = packSmRespEnc br) :
    (isBobAcceptSmRE sqE srE).eval ρ = bhIsBobAcceptSMResp sq (bhUnpackSmResp sq br) := by
  simp only [isBobAcceptSmRE, eCaseOpt, eCaseSum, v, Ext.wk, Expr.eval, Env.get,
    eval_isBobRecvSmQE, hsq, hsr, smQdec_smQenc, packSmRespEnc]
  rcases br with ⟨w, rr, st⟩
  rcases sq with (((_ | _) | ⟨p, c⟩) | ⟨p, c⟩) | _
  · rfl
  · rfl
  · cases p <;> cases rr with
    | none => rfl
    | some r => cases r <;> rfl
  · cases p <;> cases rr with
    | none => rfl
    | some r => cases r <;> rfl
  · rfl

def mkDeliverSmQE {Γ : List (Ty (e2eSig ℓ))}
    (pE : E2EExpr Γ .bool) (cE : E2EExpr Γ (B 32)) : E2EExpr Γ smQT :=
  .inr (.inr (.inl (.pair pE cE)))

def mkInjectSmQE {Γ : List (Ty (e2eSig ℓ))}
    (pE : E2EExpr Γ .bool) (cE : E2EExpr Γ (B 32)) : E2EExpr Γ smQT :=
  .inr (.inr (.inr (.inl (.pair pE cE))))

def filterDeliverE {Γ : List (Ty (e2eSig ℓ))}
    (dE : E2EExpr Γ (e2eModelInstTy S ℓ))
    (imE : E2EExpr Γ (e2eInstMetaTy S ℓ))
    (pcE : E2EExpr Γ (.prod .bool (B 32))) : E2EExpr Γ (.opt smQT) :=
  eLet (.pair dE (.pair imE pcE)) fun p =>
    .ite (.fst (.snd (.snd (v p))))
      (.ite (.not (imBobAccepted (.fst (.snd (v p)))))
        (optMapE
          (e2ePureOp .partneredInnerBytes
            (.pair (.bool false)
              (.pair (bhInitRegIdE (miSid (.fst (v p))))
                (.pair (miHdr (.fst (v p))) (.snd (.snd (.snd (v p))))))))
          (fun inner => mkDeliverSmQE (.bool true) (v inner)))
        (eCaseOpt (e2ePureOp .parsePreKeyWire (.snd (.snd (.snd (v p)))))
          (.some (mkDeliverSmQE (.bool true) (.snd (.snd (.snd (v p))))))
          (fun parsed =>
            .ite (hdrEqE (.fst (.snd (v parsed))) (miHdr (.fst (v p))))
              (.some (mkDeliverSmQE (.bool true) (.snd (.snd (v parsed)))))
              .none)))
      (.ite (isSomeE (e2ePureOp .parsePreKeyWire (.snd (.snd (.snd (v p))))))
        .none
        (.some (mkDeliverSmQE (.bool false) (.snd (.snd (.snd (v p)))))))

def filterInjectE {Γ : List (Ty (e2eSig ℓ))}
    (dE : E2EExpr Γ (e2eModelInstTy S ℓ))
    (imE : E2EExpr Γ (e2eInstMetaTy S ℓ))
    (pcE : E2EExpr Γ (.prod .bool (B 32))) : E2EExpr Γ (.opt smQT) :=
  eLet (.pair dE (.pair imE pcE)) fun p =>
    .ite (.fst (.snd (.snd (v p))))
      (.ite (.not (imBobAccepted (.fst (.snd (v p)))))
        .none
        (eCaseOpt (e2ePureOp .parsePreKeyWire (.snd (.snd (.snd (v p)))))
          (.some (mkInjectSmQE (.bool true) (.snd (.snd (.snd (v p))))))
          (fun parsed =>
            .ite
              (.and
                (hdrEqE (.fst (.snd (v parsed))) (miHdr (.fst (v p))))
                (e2ePureOp .checkShortCiphertext
                  (.pair (.snd (.snd (.snd (v p)))) (.some (.snd (.snd (v parsed)))))))
              (.some (mkInjectSmQE (.bool true) (.snd (.snd (v parsed)))))
              .none)))
      (.ite (isSomeE (e2ePureOp .parsePreKeyWire (.snd (.snd (.snd (v p))))))
        .none
        (.some (mkInjectSmQE (.bool false) (.snd (.snd (.snd (v p)))))))

/-- Pre-query wire filter expression implementing `bhFilterSmQuery d im sq`. -/
def filterSmQueryE {Γ : List (Ty (e2eSig ℓ))}
    (dE : E2EExpr Γ (e2eModelInstTy S ℓ))
    (imE : E2EExpr Γ (e2eInstMetaTy S ℓ))
    (sqE : E2EExpr Γ smQT) : E2EExpr Γ (.opt smQT) :=
  eLet (.pair dE (.pair imE sqE)) fun p =>
    eCaseSum (.snd (.snd (v p)))
      (fun _ => .some (.snd (.snd (v p))))
      (fun r1 => eCaseSum (v r1)
        (fun _ => .some (.snd (.snd (v p))))
        (fun r2 => eCaseSum (v r2)
          (fun dl => filterDeliverE (.fst (v p)) (.fst (.snd (v p))) (v dl))
          (fun r3 => eCaseSum (v r3)
            (fun ij => filterInjectE (.fst (v p)) (.fst (.snd (v p))) (v ij))
            (fun _ => .some (.snd (.snd (v p)))))))

theorem eval_filterSmQueryE {Γ : List (Ty (e2eSig ℓ))}
    (dE : E2EExpr Γ (e2eModelInstTy S ℓ))
    (imE : E2EExpr Γ (e2eInstMetaTy S ℓ))
    (sqE : E2EExpr Γ smQT)
    (ρ : Env Γ) {d : BHModelInst S ℓ} {im : ModelDriverInstanceMeta S}
    {sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (hd : dE.eval ρ = e2eModelInstEnc d)
    (him : imE.eval ρ = e2eInstMetaEnc im)
    (hsq : sqE.eval ρ = smQenc sq) :
    (filterSmQueryE dE imE sqE).eval ρ = (bhFilterSmQuery d im sq).map smQenc := by
  have hparse : ∀ c : Bytes,
      E2EPureOp.eval ℓ .parsePreKeyWire c =
        (bhDecodePreKeyMsgE c).map (fun m => (m.regId, (hdrV (bhHdrOfPreKeyMsg m), m.inner))) := by
    intro c
    rw [show E2EPureOp.eval ℓ .parsePreKeyWire c = (e2ePureOps ℓ).eval .parsePreKeyWire c from rfl,
        e2ePureOps_eval_parsePreKeyWire_lossless]
    simp [e2eDecodePreKeyMsg_eq, e2eHdrOfPreKeyMsg_eq]
  rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
  · simp [filterSmQueryE, bhFilterSmQuery, smQenc, eLet, eCaseSum, v, Ext.wk,
      Expr.eval, hsq]
  · simp [filterSmQueryE, bhFilterSmQuery, smQenc, eLet, eCaseSum, v, Ext.wk,
      Expr.eval, hsq]
  · cases pDl
    · simp [filterSmQueryE, filterDeliverE, mkDeliverSmQE, bhFilterSmQuery, smQenc,
        partyToBool, eLet, eCaseSum, v, Ext.wk, Expr.eval, hd, him, hsq,
        eval_isSomeE, eval_e2ePureOp, hparse]
      cases (bhDecodePreKeyMsgE cDl) <;> rfl
    · simp only [filterSmQueryE, filterDeliverE, mkDeliverSmQE, bhFilterSmQuery, smQenc,
        partyToBool, eLet, eCaseSum, eCaseOpt, eval_optMapE, v, Ext.wk, Expr.eval, Env.get,
        hd, him, hsq, imBobAccepted, miSid, miHdr, e2eModelInstEnc, e2eInstMetaEnc,
        eval_bhInitRegIdE, sidOfV_sidV, eval_e2ePureOp]
      by_cases hacc : !im.bobAccepted
      · simp only [hacc, ↓reduceIte, E2EPureOp.eval, hdrOfV_hdrV, e2ePartneredInnerBytes_false_eq]
        unfold bhPartneredInnerBytes
        simp only [Bool.not_false, ↓reduceIte]
        rcases bhDecodePreKeyMsgE cDl with _ | m
        · rfl
        · dsimp only
          split_ifs <;> rfl
      · simp only [hacc, Bool.false_eq_true, ↓reduceIte, hparse]
        rcases bhDecodePreKeyMsgE cDl with _ | m
        · rfl
        · simp only [Option.map, eval_hdrEqE, Expr.eval, Env.get, hdrOfV_hdrV]
          split_ifs <;> rfl
  · cases pIj
    · simp [filterSmQueryE, filterInjectE, mkInjectSmQE, bhFilterSmQuery, smQenc,
        partyToBool, eLet, eCaseSum, v, Ext.wk, Expr.eval, hd, him, hsq,
        eval_isSomeE, eval_e2ePureOp, hparse]
      cases (bhDecodePreKeyMsgE cIj) <;> rfl
    · simp only [filterSmQueryE, filterInjectE, mkInjectSmQE, bhFilterSmQuery, smQenc,
        partyToBool, eLet, eCaseSum, eCaseOpt, v, Ext.wk, Expr.eval, Env.get,
        hd, him, hsq, imBobAccepted, miHdr, e2eModelInstEnc, e2eInstMetaEnc,
        eval_e2ePureOp]
      by_cases hacc : !im.bobAccepted
      · simp only [hacc, ↓reduceIte, Option.map]
      · simp only [hacc, Bool.false_eq_true, ↓reduceIte, hparse]
        rcases bhDecodePreKeyMsgE cIj with _ | m
        · rfl
        · simp only [Option.map, eval_hdrEqE, Expr.eval, Env.get, hdrOfV_hdrV,
            E2EPureOp.eval, Bool.and_assoc]
          split_ifs <;> rfl
  · simp [filterSmQueryE, bhFilterSmQuery, smQenc, eLet, eCaseSum, v, Ext.wk,
      Expr.eval, hsq]

theorem cost_filterSmQueryE {Γ : List (Ty (e2eSig ℓ))}
    (dE : E2EExpr Γ (e2eModelInstTy S ℓ))
    (imE : E2EExpr Γ (e2eInstMetaTy S ℓ))
    (sqE : E2EExpr Γ smQT) :
    (filterSmQueryE dE imE sqE).cost ≤ dE.cost + imE.cost + sqE.cost + 3800 := by
  let τp : Ty (e2eSig ℓ) := .prod (e2eModelInstTy S ℓ) (.prod (e2eInstMetaTy S ℓ) smQT)
  let τpc : Ty (e2eSig ℓ) := .prod .bool (B 32)
  let τSub : Ty (e2eSig ℓ) :=
    .prod (e2eModelInstTy S ℓ) (.prod (e2eInstMetaTy S ℓ) τpc)
  let τParsed : Ty (e2eSig ℓ) := .prod U32 (.prod hdrT (B 32))
  have hhd1 := cost_hdrEqE (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := τParsed :: τSub :: τpc :: (.sum τpc (.sum τpc .bool)) ::
          (.sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
            (.sum τpc (.sum τpc .bool))) :: τp :: Γ)
    (.fst (.snd (.var .zero))) (miHdr (.fst (.var (.succ .zero))))
  have hhd2 := cost_hdrEqE (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := τParsed :: τSub :: τpc :: (.sum τpc .bool) ::
          (.sum τpc (.sum τpc .bool)) ::
          (.sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
            (.sum τpc (.sum τpc .bool))) :: τp :: Γ)
    (.fst (.snd (.var .zero))) (miHdr (.fst (.var (.succ .zero))))
  dsimp only [τp, τpc, τSub, τParsed] at hhd1 hhd2
  unfold filterSmQueryE filterDeliverE filterInjectE
  dsimp only [v, Ext.wk]
  simp only [mkDeliverSmQE, mkInjectSmQE, imBobAccepted, miSid, miHdr, bhInitRegIdE,
    bhDrvSessionInitPrinE, optMapE, isSomeE, eLet, eCaseSum, eCaseOpt,
    Expr.cost, cost_v, cost_e2ePureOp, E2EPureOp.cost] at hhd1 hhd2 ⊢
  omega

attribute [local irreducible] filterSmQueryE

def defaultExtGameSmRespE {Γ : List (Ty (e2eSig ℓ))} : E2EExpr Γ (e2eGameRT ℓ) :=
  .inr (.pair .none (.pair .none .none))

def checkExtSmE (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (iE : E2EExpr Γ .nat)
    (sqE : E2EExpr Γ smQT) :
    E2EExpr Γ (.sum (e2eGameRT ℓ) smQT) :=
  eLet (.pair kE (.pair σE (.pair iE sqE))) fun p =>
    .ite
      (orE
        (.not (.eqN (.fst (.snd (.snd (v p)))) (.fst (v p))))
        (.not (bhE2EDrvInstCleanE qStart nCorr (.fst (.snd (v p))) (.fst (v p)))))
      (.inl defaultExtGameSmRespE)
      (eCaseOpt (listGetOptE qStart (drvInsts (.fst (.snd (v p)))) (.fst (v p)))
        (.inl defaultExtGameSmRespE)
        (fun d =>
          eCaseOpt (listGetOptE qStart (drvInstMeta (.fst (.snd (v p)))) (.fst (v p)))
            (.inl defaultExtGameSmRespE)
            (fun im =>
              .ite
                (.and
                  (.and (.not (imBobAccepted (v im))) (isBobRecvSmQE (.snd (.snd (.snd (v p))))))
                  (bhE2EInstIkACorrE nCorr nPrins (.fst (.snd (v p))) (v d)))
                (.inl defaultExtGameSmRespE)
                (eCaseOpt (filterSmQueryE (v d) (v im) (.snd (.snd (.snd (v p)))))
                  (.inl defaultExtGameSmRespE)
                  (fun sq' => .inr (v sq'))))))

theorem eval_checkExtSmE (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (iE : E2EExpr Γ .nat)
    (sqE : E2EExpr Γ smQT)
    (ρ : Env Γ) {k i : ℕ} {σ : BHE2EDrvState S ℓ}
    {sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (hk : kE.eval ρ = k) (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hi : iE.eval ρ = i) (hsq : sqE.eval ρ = smQenc sq)
    (hInsts : σ.insts.length ≤ qStart) (hMeta : DrvMetaAligned σ)
    (hCorr : σ.corrPrins.length ≤ nCorr) (hRev : σ.revealedSpks.length ≤ nCorr)
    (hPrins : σ.prins.length ≤ nPrins) :
    (checkExtSmE qStart nCorr nPrins kE σE iE sqE).eval ρ =
      if i != k || !bhE2EDrvInstClean σ k then
        .inl (.inr (packSmRespEnc (none, none, none)))
      else
        match σ.insts[k]?, σ.instMeta[k]? with
        | some d, some im =>
          if !im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d then
            .inl (.inr (packSmRespEnc (none, none, none)))
          else
            match bhFilterSmQuery d im sq with
            | some sq' => .inr (smQenc sq')
            | none => .inl (.inr (packSmRespEnc (none, none, none)))
        | _, _ => .inl (.inr (packSmRespEnc (none, none, none))) := by
  have hMetaLe : σ.instMeta.length ≤ qStart := hMeta.symm ▸ hInsts
  have hInstsEnc : (σ.insts.map (e2eModelInstEnc (ℓ := ℓ))).length ≤ qStart := by
    simpa using hInsts
  have hMetaEnc : (σ.instMeta.map (e2eInstMetaEnc (ℓ := ℓ))).length ≤ qStart := by
    simpa using hMetaLe
  unfold checkExtSmE
  simp only [eLet, eval_orE, v, Ext.wk, Expr.eval, Env.get, hk, hσ, hi, hsq]
  rw [eval_bhE2EDrvInstCleanE qStart nCorr _ _ _ (σ := σ) (k := k) rfl rfl hInsts hMetaLe hRev]
  have hneq : (!decide (i = k)) = (i != k) := by
    by_cases hik : i = k <;> simp [hik]
  rw [hneq]
  by_cases hbad : (i != k || !bhE2EDrvInstClean σ k) = true
  · simp [hbad, defaultExtGameSmRespE, packSmRespEnc, Expr.eval]
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte, eCaseOpt, Expr.eval]
    rw [eval_listGetOptE qStart _ _ _ (by exact hInstsEnc)]
    simp only [drvInsts, Expr.eval, Env.get, e2eDrvStateEnc, List.getElem?_map]
    rcases hd : σ.insts[k]? with _ | d
    · simp [defaultExtGameSmRespE, packSmRespEnc, Expr.eval]
    · simp only [Option.map]
      rw [eval_listGetOptE qStart _ _ _ (by exact hMetaEnc)]
      simp only [drvInstMeta, Expr.eval, Env.get, List.getElem?_map]
      rcases him : σ.instMeta[k]? with _ | im
      · simp [defaultExtGameSmRespE, packSmRespEnc, Expr.eval]
      · simp only [Option.map, Expr.eval, Env.get, imBobAccepted, e2eInstMetaEnc,
          eval_isBobRecvSmQE, smQdec_smQenc]
        rw [eval_bhE2EInstIkACorrE nCorr nPrins _ _ _ (σ := σ) (d := d) rfl rfl hCorr hPrins]
        by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · simp [hcorr, defaultExtGameSmRespE, packSmRespEnc, Expr.eval]
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte]
          rw [eval_filterSmQueryE _ _ _ _ (d := d) (im := im) (sq := sq) rfl rfl rfl]
          rcases bhFilterSmQuery d im sq with _ | sq' <;>
            simp [defaultExtGameSmRespE, packSmRespEnc, Expr.eval]

theorem cost_checkExtSmE (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (iE : E2EExpr Γ .nat)
    (sqE : E2EExpr Γ smQT) :
    (checkExtSmE qStart nCorr nPrins kE σE iE sqE).cost ≤
      kE.cost + σE.cost + iE.cost + sqE.cost +
        180 * qStart + 160 * nCorr + 150 * nPrins + 4400 := by
  let τp : Ty (e2eSig ℓ) := .prod .nat (.prod (e2eDrvStateTy S ℓ) (.prod .nat smQT))
  have hcl := cost_bhE2EDrvInstCleanE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nCorr (Γ := τp :: Γ) (.fst (.snd (.var .zero)))
    (.fst (.var .zero))
  have hg1 := cost_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart (Γ := τp :: Γ)
    (drvInsts (.fst (.snd (.var .zero)))) (.fst (.var .zero))
  have hg2 := cost_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := e2eModelInstTy S ℓ :: τp :: Γ)
    (drvInstMeta (.fst (.snd (.var (.succ .zero))))) (.fst (.var (.succ .zero)))
  have hcr := cost_bhE2EInstIkACorrE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr nPrins
    (Γ := e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ :: τp :: Γ)
    (.fst (.snd (.var (.succ (.succ .zero))))) (.var (.succ .zero))
  have hfl := cost_filterSmQueryE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ :: τp :: Γ)
    (.var (.succ .zero)) (.var .zero) (.snd (.snd (.snd (.var (.succ (.succ .zero))))))
  dsimp only [τp] at hcl hg1 hg2 hcr hfl
  unfold checkExtSmE
  dsimp only [v, Ext.wk]
  simp only [defaultExtGameSmRespE, drvInsts, drvInstMeta, imBobAccepted, isBobRecvSmQE,
    orE, eLet, eCaseOpt, eCaseSum, Expr.cost, cost_v] at hcl hg1 hg2 hcr hfl ⊢
  omega

attribute [local irreducible] checkExtSmE

def commitExtSmE (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sqE : E2EExpr Γ smQT)
    (srE : E2EExpr Γ (smRT GhostStT)) :
    E2EExpr Γ (.prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ)) :=
  eLet (.pair kE (.pair σE (.pair sqE srE))) fun p =>
    .pair (.inr (.snd (.snd (.snd (v p)))))
      (.ite (.not (bhE2EDrvInstCleanE qStart nCorr (.fst (.snd (v p))) (.fst (v p))))
        (.fst (.snd (v p)))
        (eCaseOpt (listGetOptE qStart (drvInsts (.fst (.snd (v p)))) (.fst (v p)))
          (.fst (.snd (v p)))
          (fun d =>
            eCaseOpt (listGetOptE qStart (drvInstMeta (.fst (.snd (v p)))) (.fst (v p)))
              (.fst (.snd (v p)))
              (fun im =>
                .ite
                  (.and
                    (.and (.not (imBobAccepted (v im))) (isBobRecvSmQE (.fst (.snd (.snd (v p))))))
                    (bhE2EInstIkACorrE nCorr nPrins (.fst (.snd (v p))) (v d)))
                  (drvSetInstMetaE (.fst (.snd (v p)))
                    (listSetE qStart (drvInstMeta (.fst (.snd (v p)))) (.fst (v p))
                      (.pair (.bool true) (.pair (.bool true) (.snd (.snd (v im)))))))
                  (drvSetInstMetaE (.fst (.snd (v p)))
                    (listSetE qStart (drvInstMeta (.fst (.snd (v p)))) (.fst (v p))
                      (.ite
                        (.and (.not (imBobAccepted (v im)))
                          (isBobAcceptSmRE (.fst (.snd (.snd (v p)))) (.snd (.snd (.snd (v p))))))
                        (.pair (.bool true)
                          (.pair (bhE2EInstIkACorrE nCorr nPrins (.fst (.snd (v p))) (v d))
                            (.snd (.snd (v im)))))
                        (v im))))))))

theorem eval_commitExtSmE (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sqE : E2EExpr Γ smQT)
    (srE : E2EExpr Γ (smRT GhostStT))
    (ρ : Env Γ) {k : ℕ} {σ : BHE2EDrvState S ℓ}
    {sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    {sr : BHE2ESmResp ℓ}
    (hk : kE.eval ρ = k) (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hsq : sqE.eval ρ = smQenc sq) (hsr : srE.eval ρ = packSmRespEnc sr)
    (hInsts : σ.insts.length ≤ qStart) (hMeta : DrvMetaAligned σ)
    (hCorr : σ.corrPrins.length ≤ nCorr) (hRev : σ.revealedSpks.length ≤ nCorr)
    (hPrins : σ.prins.length ≤ nPrins) :
    (commitExtSmE qStart nCorr nPrins kE σE sqE srE).eval ρ =
      let σ1 :=
        if !bhE2EDrvInstClean σ k then σ
        else match σ.insts[k]?, σ.instMeta[k]? with
          | some d, some im =>
            if !im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d then
              { σ with instMeta :=
                  σ.instMeta.set k { im with bobAccepted := true, ikACorrAtAccept := true } }
            else
              let r := bhUnpackSmResp sq sr
              let im' := if !im.bobAccepted && bhIsBobAcceptSMResp sq r then
                  { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                else im
              { σ with instMeta := σ.instMeta.set k im' }
          | _, _ => σ
      (.inr (packSmRespEnc sr), e2eDrvStateEnc σ1) := by
  have hMetaLe : σ.instMeta.length ≤ qStart := hMeta.symm ▸ hInsts
  have hInstsEnc : (σ.insts.map (e2eModelInstEnc (ℓ := ℓ))).length ≤ qStart := by
    simpa using hInsts
  have hMetaEnc : (σ.instMeta.map (e2eInstMetaEnc (ℓ := ℓ))).length ≤ qStart := by
    simpa using hMetaLe
  unfold commitExtSmE
  simp only [eLet, v, Ext.wk, Expr.eval, Env.get, hk, hσ, hsq, hsr]
  congr 1
  rw [eval_bhE2EDrvInstCleanE qStart nCorr _ _ _ (σ := σ) (k := k) rfl rfl hInsts hMetaLe hRev]
  by_cases hcl : !bhE2EDrvInstClean σ k
  · simp [hcl]
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte, eCaseOpt, Expr.eval]
    rw [eval_listGetOptE qStart _ _ _ (by exact hInstsEnc)]
    simp only [drvInsts, Expr.eval, Env.get, e2eDrvStateEnc, List.getElem?_map]
    rcases hd : σ.insts[k]? with _ | d
    · rfl
    · simp only [Option.map]
      rw [eval_listGetOptE qStart _ _ _ (by exact hMetaEnc)]
      simp only [drvInstMeta, Expr.eval, Env.get, List.getElem?_map]
      rcases him : σ.instMeta[k]? with _ | im
      · rfl
      · simp only [Option.map, Expr.eval, Env.get, imBobAccepted, e2eInstMetaEnc,
          eval_isBobRecvSmQE, smQdec_smQenc]
        rw [eval_bhE2EInstIkACorrE nCorr nPrins _ _ _ (σ := σ) (d := d) rfl rfl hCorr hPrins]
        by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · simp only [hcorr, ↓reduceIte]
          refine (eval_drvSetInstMetaE _ _ _ (σ := σ)
            (ms := σ.instMeta.set k { im with bobAccepted := true, ikACorrAtAccept := true })
            rfl ?_).trans rfl
          rw [eval_listSetE qStart _ _ _ _ (by exact hMetaEnc)]
          simp [Expr.eval, e2eInstMetaEnc, List.map_set]
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte]
          let im' : ModelDriverInstanceMeta S :=
            if !im.bobAccepted && bhIsBobAcceptSMResp sq (bhUnpackSmResp sq sr) then
              { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
            else im
          refine (eval_drvSetInstMetaE _ _ _ (σ := σ)
            (ms := σ.instMeta.set k im') rfl ?_).trans rfl
          rw [eval_listSetE qStart _ _ _ _ (by exact hMetaEnc), List.map_set]
          simp only [Expr.eval, Env.get]
          congr 1
          split
          · next h =>
            rw [eval_isBobAcceptSmRE _ _ _ (sq := sq) (br := sr) rfl rfl] at h
            rw [eval_bhE2EInstIkACorrE nCorr nPrins _ _ _ (σ := σ) (d := d) rfl rfl hCorr hPrins]
            dsimp only [im']
            simp [h, e2eInstMetaEnc]
          · next h =>
            rw [eval_isBobAcceptSmRE _ _ _ (sq := sq) (br := sr) rfl rfl] at h
            dsimp only [im']
            simp [h, e2eInstMetaEnc]

theorem cost_commitExtSmE (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sqE : E2EExpr Γ smQT)
    (srE : E2EExpr Γ (smRT GhostStT)) :
    (commitExtSmE qStart nCorr nPrins kE σE sqE srE).cost ≤
      kE.cost + σE.cost + sqE.cost + srE.cost +
        210 * qStart + 300 * nCorr + 310 * nPrins + 900 := by
  let τp : Ty (e2eSig ℓ) := .prod .nat (.prod (e2eDrvStateTy S ℓ) (.prod smQT (smRT GhostStT)))
  have hcl := cost_bhE2EDrvInstCleanE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nCorr (Γ := τp :: Γ) (.fst (.snd (.var .zero)))
    (.fst (.var .zero))
  have hg1 := cost_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart (Γ := τp :: Γ)
    (drvInsts (.fst (.snd (.var .zero)))) (.fst (.var .zero))
  have hg2 := cost_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := e2eModelInstTy S ℓ :: τp :: Γ)
    (drvInstMeta (.fst (.snd (.var (.succ .zero))))) (.fst (.var (.succ .zero)))
  have hcr := cost_bhE2EInstIkACorrE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr nPrins
    (Γ := e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ :: τp :: Γ)
    (.fst (.snd (.var (.succ (.succ .zero))))) (.var (.succ .zero))
  have hs1 := cost_listSetE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ :: τp :: Γ)
    (drvInstMeta (.fst (.snd (.var (.succ (.succ .zero))))))
    (.fst (.var (.succ (.succ .zero))))
    (.pair (.bool true) (.pair (.bool true) (.snd (.snd (.var .zero)))))
  have hs2 := cost_listSetE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ :: τp :: Γ)
    (drvInstMeta (.fst (.snd (.var (.succ (.succ .zero))))))
    (.fst (.var (.succ (.succ .zero))))
    (.ite
      (.and (.not (imBobAccepted (.var .zero)))
        (isBobAcceptSmRE (.fst (.snd (.snd (.var (.succ (.succ .zero))))))
          (.snd (.snd (.snd (.var (.succ (.succ .zero))))))))
      (.pair (.bool true)
        (.pair
          (bhE2EInstIkACorrE nCorr nPrins
            (.fst (.snd (.var (.succ (.succ .zero))))) (.var (.succ .zero)))
          (.snd (.snd (.var .zero)))))
      (.var .zero))
  dsimp only [τp] at hcl hg1 hg2 hcr hs1 hs2
  unfold commitExtSmE
  dsimp only [v, Ext.wk]
  simp only [drvInsts, drvInstMeta, drvSetInstMetaE, drvBase, drvCorrPrins, drvRevSpks,
    imBobAccepted, isBobRecvSmQE, isBobAcceptSmRE,
    eLet, eCaseOpt, eCaseSum, Expr.cost, cost_v] at hcl hg1 hg2 hcr hs1 hs2 ⊢
  omega

attribute [local irreducible] commitExtSmE

def forwardExtSmC {Γ : List (Ty (e2eSig ℓ))}
    (sqE : E2EExpr Γ smQT) :
    Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ) Γ (smRT GhostStT) :=
  caseSumV sqE
    (fun tr =>
      bindV (.query (I := e2eSessionTargetIface ℓ) .tr (v tr)) fun r =>
        .ret (.pair (v r) (.pair .none .none)))
    (fun s1 =>
      caseSumV (v s1)
        (fun ch =>
          bindV (.query (I := e2eSessionTargetIface ℓ) .ch (v ch)) fun r =>
            .ret (.pair (v r) (.pair .none .none)))
        (fun s2 =>
          caseSumV (v s2)
            (fun dl =>
              bindV (.query (I := e2eSessionTargetIface ℓ) .dl (v dl)) fun r =>
                .ret (.pair .none (.pair (v r) .none)))
            (fun s3 =>
              caseSumV (v s3)
                (fun ij =>
                  bindV (.query (I := e2eSessionTargetIface ℓ) .ij (v ij)) fun r =>
                    .ret (.pair .none (.pair (v r) .none)))
                (fun cr =>
                  bindV (.query (I := e2eSessionTargetIface ℓ) .cr (v cr)) fun r =>
                    .ret (.pair .none (.pair .none (v r)))))))

theorem forwardExtSmC_cost {Γ : List (Ty (e2eSig ℓ))}
    (sqE : E2EExpr Γ smQT) :
    (forwardExtSmC sqE).cost ≤ sqE.cost + 2 * (ℓ / 32) + 32060 := by
  unfold forwardExtSmC
  dsimp only [caseSumV, bindV, v, Ext.wk]
  simp only [Comp.cost, Expr.cost]
  omega

theorem forwardExtSmC_queries {Γ : List (Ty (e2eSig ℓ))}
    (sqE : E2EExpr Γ smQT)
    (w : E2ESessionTag → ℕ) (wmax : ℕ) (hw : ∀ g, w g ≤ wmax) :
    (forwardExtSmC sqE).queries w (fun _ => 0) ≤ wmax := by
  have htr := hw .tr
  have hch := hw .ch
  have hdl := hw .dl
  have hij := hw .ij
  have hcr := hw .cr
  unfold forwardExtSmC
  dsimp only [caseSumV, bindV]
  simp only [Comp.queries, Nat.add_zero]
  omega

theorem forwardExtSmC_eval {Γ : List (Ty (e2eSig ℓ))}
    (sqE : E2EExpr Γ smQT) (ρ : Env Γ)
    {sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (hsq : sqE.eval ρ = smQenc sq) :
    (forwardExtSmC sqE).eval ρ =
      (fun r => packSmRespEnc (bhPackSmResp sq r)) <$>
        (liftM ((unifSpec +
          CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).query (.inr sq)) :
          OracleComp (unifSpec +
            CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) _) := by
  rcases sq with (((⟨_ | _, m, r⟩ | ⟨_ | _, m0, m1, r⟩) | ⟨_ | _, c⟩) | ⟨_ | _, c⟩) | (_ | _) <;>
    simp [forwardExtSmC, caseSumV, bindV, v, Ext.wk, Comp.eval, Expr.eval, hsq,
      smQenc, e2eSessionTargetIface, partyToBool, boolToParty,
      map_eq_bind_pure_comp, packSmRespEnc, bhPackSmResp]

attribute [local irreducible] forwardExtSmC

def extSmStepCost (ℓ qStart nCorr nPrins : ℕ) : ℕ :=
  220 * qStart + 300 * nCorr + 310 * nPrins + 2 * (ℓ / 32) + 37100

/-- External promoted-session `SM.spec` query handler on slot `k` (`bhExtSmStep k σ sq`). -/
def extSmStepC (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sqE : E2EExpr Γ smQT) :
    Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ) Γ
      (.prod (smRT GhostStT) (e2eDrvStateTy S ℓ)) :=
  letV (.pair kE (.pair σE sqE)) fun p =>
    .ite (.not (bhE2EDrvInstCleanE qStart nCorr (.fst (.snd (v p))) (.fst (v p))))
      (.ret (.pair (.pair .none (.pair .none .none)) (.fst (.snd (v p)))))
      (caseOptV (listGetOptE qStart (drvInsts (.fst (.snd (v p)))) (.fst (v p)))
        (.ret (.pair (.pair .none (.pair .none .none)) (.fst (.snd (v p)))))
        (fun d =>
          caseOptV (listGetOptE qStart (drvInstMeta (.fst (.snd (v p)))) (.fst (v p)))
            (.ret (.pair (.pair .none (.pair .none .none)) (.fst (.snd (v p)))))
            (fun im =>
              .ite
                (.and
                  (.and (.not (imBobAccepted (v im))) (isBobRecvSmQE (.snd (.snd (v p)))))
                  (bhE2EInstIkACorrE nCorr nPrins (.fst (.snd (v p))) (v d)))
                (.ret (.pair (.pair .none (.pair .none .none))
                  (drvSetInstMetaE (.fst (.snd (v p)))
                    (listSetE qStart (drvInstMeta (.fst (.snd (v p)))) (.fst (v p))
                      (.pair (.bool true) (.pair (.bool true) (.snd (.snd (v im)))))))))
                (caseOptV (filterSmQueryE (v d) (v im) (.snd (.snd (v p))))
                  (.ret (.pair (.pair .none (.pair .none .none)) (.fst (.snd (v p)))))
                  (fun sq' =>
                    bindV (forwardExtSmC (v sq')) fun sr =>
                      .ret (.pair (v sr)
                        (drvSetInstMetaE (.fst (.snd (v p)))
                          (listSetE qStart (drvInstMeta (.fst (.snd (v p)))) (.fst (v p))
                            (.ite
                              (.and (.not (imBobAccepted (v im)))
                                (isBobAcceptSmRE (v sq') (v sr)))
                              (.pair (.bool true)
                                (.pair (bhE2EInstIkACorrE nCorr nPrins (.fst (.snd (v p))) (v d))
                                  (.snd (.snd (v im)))))
                              (v im))))))))))

theorem extSmStepC_cost (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sqE : E2EExpr Γ smQT) :
    (extSmStepC qStart nCorr nPrins kE σE sqE).cost ≤
      kE.cost + σE.cost + sqE.cost + extSmStepCost ℓ qStart nCorr nPrins := by
  let τp : Ty (e2eSig ℓ) := .prod .nat (.prod (e2eDrvStateTy S ℓ) smQT)
  have hcl := cost_bhE2EDrvInstCleanE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nCorr (Γ := τp :: Γ) (.fst (.snd (.var .zero)))
    (.fst (.var .zero))
  have hg1 := cost_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart (Γ := τp :: Γ)
    (drvInsts (.fst (.snd (.var .zero)))) (.fst (.var .zero))
  have hg2 := cost_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := e2eModelInstTy S ℓ :: τp :: Γ)
    (drvInstMeta (.fst (.snd (.var (.succ .zero))))) (.fst (.var (.succ .zero)))
  have hcr1 := cost_bhE2EInstIkACorrE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr nPrins
    (Γ := e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ :: τp :: Γ)
    (.fst (.snd (.var (.succ (.succ .zero))))) (.var (.succ .zero))
  have hs1 := cost_listSetE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ :: τp :: Γ)
    (drvInstMeta (.fst (.snd (.var (.succ (.succ .zero))))))
    (.fst (.var (.succ (.succ .zero))))
    (.pair (.bool true) (.pair (.bool true) (.snd (.snd (.var .zero)))))
  have hfl := cost_filterSmQueryE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ :: τp :: Γ)
    (.var (.succ .zero)) (.var .zero) (.snd (.snd (.var (.succ (.succ .zero)))))
  have hfw := forwardExtSmC_cost (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := smQT :: e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ :: τp :: Γ) (.var .zero)
  have hcr2 := cost_bhE2EInstIkACorrE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr nPrins
    (Γ := smRT GhostStT :: smQT :: e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ :: τp :: Γ)
    (.fst (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))
    (.var (.succ (.succ (.succ .zero))))
  have hs2 := cost_listSetE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := smRT GhostStT :: smQT :: e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ :: τp :: Γ)
    (drvInstMeta (.fst (.snd (.var (.succ (.succ (.succ (.succ .zero))))))))
    (.fst (.var (.succ (.succ (.succ (.succ .zero))))))
    (.ite
      (.and (.not (imBobAccepted (.var (.succ (.succ .zero)))))
        (isBobAcceptSmRE (.var (.succ .zero)) (.var .zero)))
      (.pair (.bool true)
        (.pair
          (bhE2EInstIkACorrE nCorr nPrins
            (.fst (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))
            (.var (.succ (.succ (.succ .zero)))))
          (.snd (.snd (.var (.succ (.succ .zero)))))))
      (.var (.succ (.succ .zero))))
  dsimp only [τp] at hcl hg1 hg2 hcr1 hs1 hfl hfw hcr2 hs2
  unfold extSmStepC extSmStepCost
  dsimp only [letV, caseOptV, bindV, v, Ext.wk]
  simp only [drvInsts, drvInstMeta, drvSetInstMetaE, drvBase, drvCorrPrins, drvRevSpks,
    imBobAccepted, isBobRecvSmQE, isBobAcceptSmRE,
    eLet, eCaseOpt, eCaseSum, Comp.cost, Expr.cost, cost_v]
    at hcl hg1 hg2 hcr1 hs1 hfl hfw hcr2 hs2 ⊢
  omega

theorem extSmStepC_queries (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sqE : E2EExpr Γ smQT)
    (w : E2ESessionTag → ℕ) (wmax : ℕ) (hw : ∀ g, w g ≤ wmax) :
    (extSmStepC qStart nCorr nPrins kE σE sqE).queries w (fun _ => 0) ≤ wmax := by
  have hfw := forwardExtSmC_queries (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := smQT :: e2eInstMetaTy S ℓ :: e2eModelInstTy S ℓ ::
          .prod .nat (.prod (e2eDrvStateTy S ℓ) smQT) :: Γ)
    (.var .zero) w wmax hw
  unfold extSmStepC
  dsimp only [letV, caseOptV, bindV, v, Ext.wk]
  simp only [Comp.queries, Nat.add_zero, Nat.zero_add] at hfw ⊢
  omega

theorem extSmStepC_eval (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sqE : E2EExpr Γ smQT)
    (ρ : Env Γ) (k : ℕ) (σ : BHE2EDrvState S ℓ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hk : kE.eval ρ = k)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hsq : sqE.eval ρ = smQenc sq)
    (hInsts : σ.insts.length ≤ qStart)
    (hMeta : DrvMetaAligned σ)
    (hCorr : σ.corrPrins.length ≤ nCorr)
    (hRev : σ.revealedSpks.length ≤ nCorr)
    (hPrins : σ.prins.length ≤ nPrins) :
    (extSmStepC qStart nCorr nPrins kE σE sqE).eval ρ =
      ((fun out => (packSmRespEnc out.1, e2eDrvStateEnc out.2)) <$> bhExtSmStep k σ sq) := by
  have hMetaLe : σ.instMeta.length ≤ qStart := hMeta.symm ▸ hInsts
  have hInstsEnc : (σ.insts.map (e2eModelInstEnc (ℓ := ℓ))).length ≤ qStart := by
    simpa using hInsts
  have hMetaEnc : (σ.instMeta.map (e2eInstMetaEnc (ℓ := ℓ))).length ≤ qStart := by
    simpa using hMetaLe
  unfold extSmStepC bhExtSmStep
  simp only [letV, caseOptV, bindV, Comp.eval, Expr.eval, pure_bind, v, Ext.wk, Env.get,
    hk, hσ, hsq]
  rw [eval_bhE2EDrvInstCleanE qStart nCorr _ _ _ (σ := σ) (k := k) rfl rfl hInsts hMetaLe hRev]
  by_cases hcl : !bhE2EDrvInstClean σ k
  · simp [hcl, packSmRespEnc]
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte]
    rw [eval_listGetOptE qStart _ _ _ (by exact hInstsEnc)]
    simp only [drvInsts, Expr.eval, Env.get, e2eDrvStateEnc, List.getElem?_map]
    rcases hd : σ.insts[k]? with _ | d
    · simp [packSmRespEnc]
    · simp only [Option.map]
      rw [eval_listGetOptE qStart _ _ _ (by exact hMetaEnc)]
      simp only [drvInstMeta, Expr.eval, Env.get, List.getElem?_map]
      rcases him : σ.instMeta[k]? with _ | im
      · simp [packSmRespEnc]
      · simp only [Option.map, Expr.eval, Env.get, imBobAccepted, e2eInstMetaEnc,
          eval_isBobRecvSmQE, smQdec_smQenc]
        rw [eval_bhE2EInstIkACorrE nCorr nPrins _ _ _ (σ := σ) (d := d) rfl rfl hCorr hPrins]
        by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · simp only [hcorr, ↓reduceIte, map_pure]
          congr 1
          congr 1
          refine (eval_drvSetInstMetaE _ _ _ (σ := σ)
            (ms := σ.instMeta.set k { im with bobAccepted := true, ikACorrAtAccept := true })
            rfl ?_).trans rfl
          rw [eval_listSetE qStart _ _ _ _ (by exact hMetaEnc)]
          simp [Expr.eval, e2eInstMetaEnc, List.map_set]
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte]
          rw [eval_filterSmQueryE _ _ _ _ (d := d) (im := im) (sq := sq) rfl rfl rfl]
          rcases bhFilterSmQuery d im sq with _ | sq'
          · simp [packSmRespEnc]
          · simp only [Option.map]
            rw [forwardExtSmC_eval _ _ (sq := sq') rfl]
            simp only [map_eq_bind_pure_comp, Function.comp_def, LawfulMonad.bind_assoc, pure_bind]
            congr 1
            funext r
            have hUnpack : bhUnpackSmResp sq' (bhPackSmResp sq' r) = r := by
              rcases sq' with (((_ | _) | _) | _) | _ <;> simp [bhPackSmResp, bhUnpackSmResp]
            congr 1
            congr 1
            let im' : ModelDriverInstanceMeta S :=
              if !im.bobAccepted && bhIsBobAcceptSMResp sq' r then
                { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
              else im
            refine (eval_drvSetInstMetaE _ _ _ (σ := σ)
              (ms := σ.instMeta.set k im') rfl ?_).trans rfl
            rw [eval_listSetE qStart _ _ _ _ (by exact hMetaEnc), List.map_set]
            simp only [Expr.eval, Env.get]
            congr 1
            split
            · next h =>
              rw [eval_isBobAcceptSmRE _ _ _ (sq := sq') (br := bhPackSmResp sq' r) rfl rfl,
                hUnpack] at h
              rw [eval_bhE2EInstIkACorrE nCorr nPrins _ _ _ (σ := σ) (d := d) rfl rfl hCorr hPrins]
              dsimp only [im']
              simp [h, e2eInstMetaEnc]
            · next h =>
              rw [eval_isBobAcceptSmRE _ _ _ (sq := sq') (br := bhPackSmResp sq' r) rfl rfl,
                hUnpack] at h
              dsimp only [im']
              simp [h, e2eInstMetaEnc]

attribute [local irreducible] extSmStepC

theorem bhExtSmStep_preserves (k : ℕ)
    {nP nB nO nS nC qS qBound : ℕ} {σ : BHE2EDrvState S ℓ}
    (hMir : DrvMirrorBounded nP nB nO nS nC qS σ)
    (hMeta : DrvMetaAligned σ)
    (hSess : DrvSessionsBounded C K qBound σ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (bhExtSmStep k σ sq)) :
    DrvMirrorBounded nP nB nO nS nC qS out.2 ∧
      DrvMetaAligned out.2 ∧
      DrvSessionsBounded C K qBound out.2 ∧
      out.2.st = σ.st := by
  have hpure : out ∈ support (pure ((none, none, none), σ) :
      OracleComp (unifSpec +
        CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (BHE2ESmResp ℓ × BHE2EDrvState S ℓ)) →
      DrvMirrorBounded nP nB nO nS nC qS out.2 ∧
        DrvMetaAligned out.2 ∧
        DrvSessionsBounded C K qBound out.2 ∧
        out.2.st = σ.st := by
    simp only [support_pure, Set.mem_singleton_iff]
    intro heq; subst heq
    exact ⟨hMir, hMeta, hSess, rfl⟩
  unfold bhExtSmStep at hout
  by_cases hcl : !bhE2EDrvInstClean σ k
  · simp only [hcl, ↓reduceIte] at hout; exact hpure hout
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    rcases hd : σ.insts[k]? with _ | d
    · simp only [hd] at hout; exact hpure hout
    · rcases him : σ.instMeta[k]? with _ | im
      · simp only [hd, him] at hout; exact hpure hout
      · simp only [hd, him] at hout
        by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact ⟨⟨hMir.prins_le, hMir.bundles_le, hMir.opks_le, hMir.sends_le,
                  hMir.corrPrins_le, hMir.insts_le, by simp [hMir.instMeta_le], hMir.revSpks_le⟩,
                 by simp [DrvMetaAligned] at hMeta ⊢; exact hMeta, hSess, rfl⟩
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          rcases hfl : bhFilterSmQuery d im sq with _ | sq'
          · simp only [hfl] at hout; exact hpure hout
          · simp only [hfl, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
            rcases hout with ⟨r, -, rfl⟩
            exact ⟨⟨hMir.prins_le, hMir.bundles_le, hMir.opks_le, hMir.sends_le,
                    hMir.corrPrins_le, hMir.insts_le, by simp [hMir.instMeta_le], hMir.revSpks_le⟩,
                   by simp [DrvMetaAligned] at hMeta ⊢; exact hMeta, hSess, rfl⟩

end ExtSmRouting

/-! ## `StartAndExtSmIface` bundle -/

section Bundle

/-- Concrete implementation of `StartAndExtSmIface ℓ S P C K decT encT`. -/
def startAndExtSmIface (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    StartAndExtSmIface ℓ S P C K decT encT where
  finishStartSpkC := finishStartSpkC (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
  finishStartSpkCost := finishStartSpkCost
  finishStartSpkC_cost := finishStartSpkC_cost (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C)
    (K := K) (decT := decT) (encT := encT)
  finishStartSpkC_queries := finishStartSpkC_queries (ℓ := ℓ) (S := S) (Pt := Pt) (P := P)
    (C := C) (K := K) (decT := decT) (encT := encT)
  finishStartSpkC_eval := finishStartSpkC_eval (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C)
    (K := K) (decT := decT) (encT := encT)
  promoteSlotKC := promoteSlotKC (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
  promoteSlotKCost := promoteSlotKCost
  promoteSlotKC_cost := promoteSlotKC_cost (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
  promoteSlotKC_queries := promoteSlotKC_queries (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C)
    (K := K) (decT := decT) (encT := encT)
  promoteSlotKC_eval := promoteSlotKC_eval (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
  extSmStepC := extSmStepC (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
  extSmStepCost := extSmStepCost ℓ
  extSmStepC_cost := extSmStepC_cost (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
  extSmStepC_queries := extSmStepC_queries (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
  extSmStepC_eval := extSmStepC_eval (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)

end Bundle

end Computational.Proofs.E2E.Dsl.StartAndExtSm
