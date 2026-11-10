/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec

/-!
# AVL RO Shadow Arms and Post-Step Head Sync Simulation

Proves simulation and `RoBothShadowRel` preservation for `emptyRoBothAvlE`, `syncRoBothC`
(`syncBaseShadowRespC`, `syncFixedShadowRespC`), and the AVL random-oracle handler arms
(`roBaseShadowArmC`, `roRootBaseShadowArmC`, `roFixedShadowArmC`, `roRootFixedShadowArmC`).
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Env Expr Comp Iface pqAtomicSig pqAtomicOps PB)
open Computational.Proofs.SignalPqxdh.AtomicLift
  (AtomicIface embedTy embedVar exprRename exprRename_eval mapOpExpr mapExpr
   mapSamp mapSampH mapSampCast castLegacySamp mapComp
   aiAuthPrim aiPrfMk aiPrfHmac
   tlAuthPrim tlPrfMk tlPrfHmac)
open _root_.SignalPqxdh (Setup QueryBudget)
open _root_.SignalPqxdh.LegacyCosted (B msgKeyPrfOracle hmacPrfOracle)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
  (roB roRootB hkdfOrRoC rs
   stSecb stHasWon stPrin stSpks stOpks stSess stUsedS stUsedO stUsedN stKyb
   stSOE stSNE stROE stRNE stRo stRoot stAdv)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (authHybridStateFixedTy liftPrimComp roFixedB roRootFixedB hkdfRoC samplePrim
   fhstSetBase ahsfUpd ahsfUpdSlots ahsfMkSlots ahsfHybrid ahsfRecvCount ahsfMkSaltCache ahsfSlots
   ahsUpd ahsMk ahsBase ahsInitKemRecs ahsRecvKemRecs ahsIdealSessions
   asSecb asHasWonAuth asPrincipals asSpkBundles asOpkEntries asSessions
   asUsedSendSessions asUsedRecvOPK asUsedRecvNoOPK asUsedKyberTriples
   asSentOPKEvents asSentNoOPKEvents asRecvdOPKEvents asRecvdNoOPKEvents
   asRoCache asRootRoCache asAdvKeys)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec
  (AvlB192Valid AvlPair32Valid
   avlSearchInsertB192_spec avlSearchInsertPair32_spec avlInsertAtPathC_eval_congr)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
  (pair32_find?_beq_eq)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels roAvlTy roRootAvlTy roBothAvlTy roListAtomicTy roRootListAtomicTy
   authBaseAtomicTy authFixedAtomicTy authBaseShadowStTy authFixedShadowStTy
   forgetAuthBaseShadow forgetAuthFixedShadow
   emptyRoBothAvlE emptyRoBothAvlE_valid
   liftExpr1 liftExpr2
   baseRoCacheE baseRootRoCacheE fixedRoCacheE fixedRootRoCacheE
   aNoneAtomicE aDrKeyAtomicE aRootKdfAtomicE
   baseSetRoCacheE baseSetRootRoCacheE fixedHasWonE fixedSetRoCacheE fixedSetRootRoCacheE
   roShadowStepC roRootShadowStepC
   roBaseShadowArmC roRootBaseShadowArmC roFixedShadowArmC roRootFixedShadowArmC
   listHeadOptE listHeadOptE_eval syncRoHeadB192C syncRoHeadPair32C
   syncRoBothC syncBaseShadowRespC syncFixedShadowRespC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (atomRoCache atomRootRoCache RoBothShadowRel CacheStepAtMostOne
   AuthBaseShadowAt AuthFixedShadowAt)

/-- Empty RO caches satisfy `RoBothShadowRel` against `emptyRoBothAvlE`. -/
theorem emptyRoBothAvlE_roBothShadowRel {Γ : List (Ty pqAtomicSig)}
    (cap : ℕ) (st : authBaseAtomicTy.denote) (ρ : Env Γ)
    (hRo : atomRoCache st = [])
    (hRoot : atomRootRoCache st = []) :
    RoBothShadowRel cap st (emptyRoBothAvlE.eval ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hRo, hRoot]
    exact emptyRoBothAvlE_valid cap ρ
  · simp [hRo]
  · simp [hRoot]

/-! ## Post-Step Head Sync -/

private theorem liftExpr1_eval {a b : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    {Γ : List (Ty pqAtomicSig)}
    (e : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps [a] b)
    (argE : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (liftExpr1 e argE).eval ρ =
      (mapExpr e : Expr pqAtomicOps [embedTy a] (embedTy b)).eval (.cons (argE.eval ρ) .nil) := by
  dsimp only [liftExpr1, Expr.eval]
  exact exprRename_eval _ _ _ _ (fun | .zero => rfl | .succ v' => nomatch v')

private theorem liftExpr2_eval {a b c : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    {Γ : List (Ty pqAtomicSig)}
    (e : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps [a, b] c)
    (arg0 : Expr pqAtomicOps Γ (embedTy a))
    (arg1 : Expr pqAtomicOps Γ (embedTy b)) (ρ : Env Γ) :
    (liftExpr2 e arg0 arg1).eval ρ =
      (mapExpr e : Expr pqAtomicOps [embedTy a, embedTy b] (embedTy c)).eval
        (.cons (arg0.eval ρ) (.cons (arg1.eval ρ) .nil)) := by
  dsimp only [liftExpr2, Expr.eval]
  rw [show (exprRename Var.succ arg0).eval (.cons (arg1.eval ρ) ρ) = arg0.eval ρ from
    exprRename_eval _ _ _ _ (fun _ => rfl)]
  exact exprRename_eval _ _ _ _
    (fun | .zero => rfl | .succ .zero => rfl | .succ (.succ v') => nomatch v')

private theorem baseRoCacheE_eval {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ authBaseAtomicTy) (ρ : Env Γ) :
    (baseRoCacheE stE).eval ρ = atomRoCache (stE.eval ρ) := by rw [baseRoCacheE, liftExpr1_eval]; rfl

private theorem baseRootRoCacheE_eval {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ authBaseAtomicTy) (ρ : Env Γ) :
    (baseRootRoCacheE stE).eval ρ = atomRootRoCache (stE.eval ρ) := by
  rw [baseRootRoCacheE, liftExpr1_eval]; rfl

private theorem fixedRoCacheE_eval {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) (ρ : Env Γ) :
    (fixedRoCacheE fhstE).eval ρ = atomRoCache (fhstE.eval ρ).1.1 := by
  rw [fixedRoCacheE, liftExpr1_eval]; rfl

private theorem fixedRootRoCacheE_eval {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) (ρ : Env Γ) :
    (fixedRootRoCacheE fhstE).eval ρ = atomRootRoCache (fhstE.eval ρ).1.1 := by
  rw [fixedRootRoCacheE, liftExpr1_eval]; rfl

private theorem not_mem_fst_of_find?_isNone {K V : Type} [BEq K] [LawfulBEq K]
    {l : List (K × V)} {k : K}
    (hNone : (l.find? (fun p => p.1 == k)).isNone = true) :
    k ∉ l.map Prod.fst := by
  intro hMem
  rw [List.mem_map] at hMem
  rcases hMem with ⟨⟨k', v⟩, hIn, hEq⟩
  dsimp only at hEq; subst hEq
  have hFind : l.find? (fun p => p.1 == k') = none := Option.isNone_iff_eq_none.mp hNone
  have hFalse := List.find?_eq_none.mp hFind (k', v) hIn
  simp at hFalse

private theorem syncRoHeadB192C_sim {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} (cap : ℕ)
    (l l' : roListAtomicTy.denote) (tbl : roAvlTy.denote)
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (tblE : Expr pqAtomicOps Γ roAvlTy) (ρ : Env Γ)
    (hValid : AvlB192Valid cap tbl l)
    (hNodup : (l.map Prod.fst).Nodup)
    (hStep : CacheStepAtMostOne l l')
    (hCap : l'.length ≤ cap)
    (hRoE : roListE.eval ρ = l')
    (hTblE : tblE.eval ρ = tbl) :
    ∃ tbl' : roAvlTy.denote,
      (syncRoHeadB192C (I := I) cap roListE tblE).eval ρ = pure tbl' ∧
      AvlB192Valid cap tbl' l' ∧
      (l'.map Prod.fst).Nodup := by
  rcases hStep with hEq | ⟨sec, dk, hMiss, hEq⟩
  · rw [hEq] at hRoE hCap ⊢
    simp only [syncRoHeadB192C, Comp.eval, Expr.eval, hRoE, hTblE, pure_bind, listHeadOptE_eval,
      Env.get, Expr.v0]
    cases l with
    | nil => exact ⟨tbl, rfl, hValid, hNodup⟩
    | cons hd tl =>
      rcases hd with ⟨sec, dk⟩
      simp only [List.head?, _root_.ReductionDsl.AtomicPureOp.eval, Expr.eval, Env.get,
        Expr.v1]
      obtain ⟨path, hSearch, _⟩ :=
        avlSearchInsertB192_spec (I := I) cap (.fst (.var .zero)) (.fst (.snd (.var .zero)))
          (.cons (tbl, (CryptoVerification.E2E.ofU8 sec, dk))
            (.cons (sec, dk) (.cons ((sec, dk) :: tl, tbl) ρ)) :
            Env (.prod roAvlTy (.prod (_root_.ReductionDsl.B 192)
                (_root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty))) ::
              .prod (PB (ℓ := 0) (Pt := Empty) 192)
                (_root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty)) ::
              .prod roListAtomicTy roAvlTy :: Γ))
          sec ((sec, dk) :: tl) rfl hValid
      rw [hSearch, pure_bind]
      simp only [List.find?, beq_self_eq_true, Option.map, Expr.eval, Env.get, Expr.v2]
      exact ⟨tbl, rfl, hValid, hNodup⟩
  · rw [hEq] at hRoE hCap ⊢
    simp only [syncRoHeadB192C, Comp.eval, Expr.eval, hRoE, hTblE, pure_bind, listHeadOptE_eval,
      Env.get, Expr.v0, List.head?, _root_.ReductionDsl.AtomicPureOp.eval, Expr.v1]
    obtain ⟨path, hSearch, hIns⟩ :=
      avlSearchInsertB192_spec (I := I) cap (.fst (.var .zero)) (.fst (.snd (.var .zero)))
        (.cons (tbl, (CryptoVerification.E2E.ofU8 sec, dk))
          (.cons (sec, dk) (.cons ((sec, dk) :: l, tbl) ρ)) :
          Env (.prod roAvlTy (.prod (_root_.ReductionDsl.B 192)
              (_root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty))) ::
            .prod (PB (ℓ := 0) (Pt := Empty) 192)
              (_root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty)) ::
            .prod roListAtomicTy roAvlTy :: Γ))
        sec l rfl hValid
    simp only [Expr.eval, Env.get] at hIns
    have hFindNone : l.find? (fun p => p.1 == sec) = none := Option.isNone_iff_eq_none.mp hMiss
    rw [hSearch, hFindNone, Option.map, pure_bind]
    rw [avlInsertAtPathC_eval_congr]
    simp only [Expr.eval, Env.get]
    obtain ⟨tbl', hInsEval, hValid'⟩ := hIns hMiss (by simpa using hCap) dk
    exact ⟨tbl', hInsEval, hValid',
      List.Nodup.cons (not_mem_fst_of_find?_isNone hMiss) hNodup⟩

private theorem syncRoHeadPair32C_sim {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} (cap : ℕ)
    (l l' : roRootListAtomicTy.denote) (tbl : roRootAvlTy.denote)
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy)
    (tblE : Expr pqAtomicOps Γ roRootAvlTy) (ρ : Env Γ)
    (hValid : AvlPair32Valid cap tbl l)
    (hNodup : (l.map Prod.fst).Nodup)
    (hStep : CacheStepAtMostOne l l')
    (hCap : l'.length ≤ cap)
    (hRootE : rootListE.eval ρ = l')
    (hTblE : tblE.eval ρ = tbl) :
    ∃ tbl' : roRootAvlTy.denote,
      (syncRoHeadPair32C (I := I) cap rootListE tblE).eval ρ = pure tbl' ∧
      AvlPair32Valid cap tbl' l' ∧
      (l'.map Prod.fst).Nodup := by
  rcases hStep with hEq | ⟨⟨rk, dh⟩, rkCk, hMiss, hEq⟩
  · rw [hEq] at hRootE hCap ⊢
    simp only [syncRoHeadPair32C, Comp.eval, Expr.eval, hRootE, hTblE, pure_bind, listHeadOptE_eval,
      Env.get, Expr.v0]
    cases l with
    | nil => exact ⟨tbl, rfl, hValid, hNodup⟩
    | cons hd tl =>
      rcases hd with ⟨⟨rk, dh⟩, rkCk⟩
      simp only [List.head?, _root_.ReductionDsl.AtomicPureOp.eval, Expr.eval, Env.get,
        Expr.v1]
      obtain ⟨path, hSearch, _⟩ :=
        avlSearchInsertPair32_spec (I := I) cap (.fst (.var .zero)) (.fst (.snd (.var .zero)))
          (.cons (tbl, ((CryptoVerification.E2E.ofU8 rk, CryptoVerification.E2E.ofU8 dh), rkCk))
            (.cons ((rk, dh), rkCk) (.cons (((rk, dh), rkCk) :: tl, tbl) ρ)) :
            Env (.prod roRootAvlTy
                (.prod (.prod (_root_.ReductionDsl.B 32) (_root_.ReductionDsl.B 32))
                  (.prod (PB (ℓ := 0) (Pt := Empty) 32) (PB (ℓ := 0) (Pt := Empty) 32))) ::
              .prod (.prod (PB (ℓ := 0) (Pt := Empty) 32) (PB (ℓ := 0) (Pt := Empty) 32))
                (.prod (PB (ℓ := 0) (Pt := Empty) 32) (PB (ℓ := 0) (Pt := Empty) 32)) ::
              .prod roRootListAtomicTy roRootAvlTy :: Γ))
          rk dh (((rk, dh), rkCk) :: tl) rfl hValid
      rw [pair32_find?_beq_eq] at hSearch
      rw [hSearch, pure_bind]
      simp only [List.find?, beq_self_eq_true, Option.map, Expr.eval, Env.get, Expr.v2]
      exact ⟨tbl, rfl, hValid, hNodup⟩
  · rw [hEq] at hRootE hCap ⊢
    simp only [syncRoHeadPair32C, Comp.eval, Expr.eval, hRootE, hTblE, pure_bind, listHeadOptE_eval,
      Env.get, Expr.v0, List.head?, _root_.ReductionDsl.AtomicPureOp.eval, Expr.v1]
    obtain ⟨path, hSearch, hIns⟩ :=
      avlSearchInsertPair32_spec (I := I) cap (.fst (.var .zero)) (.fst (.snd (.var .zero)))
        (.cons (tbl, ((CryptoVerification.E2E.ofU8 rk, CryptoVerification.E2E.ofU8 dh), rkCk))
          (.cons ((rk, dh), rkCk) (.cons (((rk, dh), rkCk) :: l, tbl) ρ)) :
          Env (.prod roRootAvlTy
              (.prod (.prod (_root_.ReductionDsl.B 32) (_root_.ReductionDsl.B 32))
                (.prod (PB (ℓ := 0) (Pt := Empty) 32) (PB (ℓ := 0) (Pt := Empty) 32))) ::
            .prod (.prod (PB (ℓ := 0) (Pt := Empty) 32) (PB (ℓ := 0) (Pt := Empty) 32))
              (.prod (PB (ℓ := 0) (Pt := Empty) 32) (PB (ℓ := 0) (Pt := Empty) 32)) ::
            .prod roRootListAtomicTy roRootAvlTy :: Γ))
        rk dh l rfl hValid
    simp only [Expr.eval, Env.get] at hIns
    rw [pair32_find?_beq_eq] at hSearch hIns
    have hFindNone : l.find? (fun p => p.1 == (rk, dh)) = none :=
      Option.isNone_iff_eq_none.mp hMiss
    rw [hSearch, hFindNone, Option.map, pure_bind]
    rw [avlInsertAtPathC_eval_congr]
    simp only [Expr.eval, Env.get]
    obtain ⟨tbl', hInsEval, hValid'⟩ := hIns hMiss (by simpa using hCap) rkCk
    exact ⟨tbl', hInsEval, hValid',
      List.Nodup.cons (not_mem_fst_of_find?_isNone hMiss) hNodup⟩

/-- Under `RoBothShadowRel` and at-most-one cache insertion within capacity `cap`, `syncRoBothC`
    evaluates to a pure updated AVL pair preserving `RoBothShadowRel`. -/
theorem syncRoBothC_sim {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} (cap : ℕ)
    (st_pre st_post : authBaseAtomicTy.denote)
    (avls : roBothAvlTy.denote)
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy)
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy)
    (ρ : Env Γ)
    (hRel : RoBothShadowRel cap st_pre avls)
    (hRoStep : CacheStepAtMostOne (atomRoCache st_pre) (atomRoCache st_post))
    (hRootStep : CacheStepAtMostOne (atomRootRoCache st_pre) (atomRootRoCache st_post))
    (hRoCap : (atomRoCache st_post).length ≤ cap)
    (hRootCap : (atomRootRoCache st_post).length ≤ cap)
    (hRoE : roListE.eval ρ = atomRoCache st_post)
    (hRootE : rootListE.eval ρ = atomRootRoCache st_post)
    (hBothE : roBothE.eval ρ = avls) :
    ∃ avls' : roBothAvlTy.denote,
      (syncRoBothC (I := I) cap roListE rootListE roBothE).eval ρ = pure avls' ∧
      RoBothShadowRel cap st_post avls' := by
  dsimp only [syncRoBothC, Comp.eval, Expr.eval]
  rw [hRoE, hRootE, hBothE, pure_bind]
  obtain ⟨roAvl', hRoEval, hRoValid', hRoNodup'⟩ :=
    syncRoHeadB192C_sim (I := I) cap (atomRoCache st_pre) (atomRoCache st_post) avls.1
      (.fst .v0) (.fst (.snd (.snd .v0)))
      (.cons (atomRoCache st_post, (atomRootRoCache st_post, avls)) ρ)
      hRel.both_valid.ro_valid hRel.ro_nodup hRoStep hRoCap rfl rfl
  rw [hRoEval, pure_bind]
  obtain ⟨rootAvl', hRootEval, hRootValid', hRootNodup'⟩ :=
    syncRoHeadPair32C_sim (I := I) cap (atomRootRoCache st_pre) (atomRootRoCache st_post) avls.2
      (.fst (.snd .v1)) (.snd (.snd (.snd .v1)))
      (.cons roAvl' (.cons (atomRoCache st_post, (atomRootRoCache st_post, avls)) ρ))
      hRel.both_valid.root_valid hRel.root_nodup hRootStep hRootCap rfl rfl
  rw [hRootEval, pure_bind]
  exact ⟨(roAvl', rootAvl'), rfl, ⟨⟨hRoValid', hRootValid'⟩, hRoNodup', hRootNodup'⟩⟩

set_option linter.constructorNameAsVariable false in
/-- Composing an online base step with `syncBaseShadowRespC` preserves its projection under
    `forgetAuthBaseShadow` and re-establishes `RoBothShadowRel`. -/
theorem syncBaseShadowRespC_bind_sim {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} (cap : ℕ)
    (bs : authBaseShadowStTy.denote)
    (c_leg : Comp pqAtomicOps I Γ
      (.prod Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authRespAtomicTy
             authBaseAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy)
    (ρ : Env Γ)
    (hRel : RoBothShadowRel cap bs.1 bs.2)
    (hBothE : roBothE.eval ρ = bs.2)
    (hStep : ∀ rs ∈ support (c_leg.eval ρ),
      CacheStepAtMostOne (atomRoCache bs.1) (atomRoCache rs.2) ∧
      CacheStepAtMostOne (atomRootRoCache bs.1) (atomRootRoCache rs.2) ∧
      (atomRoCache rs.2).length ≤ cap ∧
      (atomRootRoCache rs.2).length ≤ cap) :
    let synced := Comp.bind c_leg
      (syncBaseShadowRespC (I := I) cap (.var .zero) (exprRename Var.succ roBothE))
    Prod.map id forgetAuthBaseShadow <$> synced.eval ρ = c_leg.eval ρ ∧
    ∀ p ∈ support (synced.eval ρ), RoBothShadowRel cap p.2.1 p.2.2 := by
  have hEach : ∀ rs ∈ support (c_leg.eval ρ),
      ∃ avls' : roBothAvlTy.denote,
        (syncBaseShadowRespC (I := I) cap (.var .zero) (exprRename Var.succ roBothE)).eval
          (.cons rs ρ) = pure (rs.1, (rs.2, avls')) ∧
        RoBothShadowRel cap rs.2 avls' := by
    intro rs hrs
    rcases hStep rs hrs with ⟨hRoS, hRtS, hRoC, hRtC⟩
    have hBothSub : (exprRename Var.succ roBothE).eval (.cons rs ρ) = bs.2 :=
      (exprRename_eval roBothE Var.succ ρ (.cons rs ρ) (fun _ => rfl)).trans hBothE
    simp only [syncBaseShadowRespC, Comp.eval, Expr.eval, Env.get, hBothSub, pure_bind]
    obtain ⟨avls', hSyncEval, hRel'⟩ :=
      syncRoBothC_sim (I := I) cap bs.1 rs.2 bs.2
        (baseRoCacheE (.snd (.fst .v0)))
        (baseRootRoCacheE (.snd (.fst .v0)))
        (.snd .v0)
        (.cons (rs, bs.2) (.cons rs ρ))
        hRel hRoS hRtS hRoC hRtC
        (baseRoCacheE_eval _ _) (baseRootRoCacheE_eval _ _) rfl
    rw [hSyncEval, pure_bind]
    exact ⟨avls', rfl, hRel'⟩
  constructor
  · dsimp only [Comp.eval]
    rw [map_bind]
    conv_rhs => rw [← bind_pure (c_leg.eval ρ)]
    refine OracleComp.bind_congr_of_forall_mem_support (c_leg.eval ρ) fun rs hrs => ?_
    obtain ⟨avls', hEval, _⟩ := hEach rs hrs
    rw [hEval]
    rfl
  · intro p hp
    dsimp only [Comp.eval] at hp
    rw [mem_support_bind_iff] at hp
    rcases hp with ⟨rs, hrs, hp'⟩
    obtain ⟨avls', hEval, hRel'⟩ := hEach rs hrs
    rw [hEval, support_pure, Set.mem_singleton_iff] at hp'
    subst hp'
    exact hRel'

set_option linter.constructorNameAsVariable false in
/-- Composing an online fixed-hybrid step with `syncFixedShadowRespC` preserves its projection
    under `forgetAuthFixedShadow` and re-establishes `RoBothShadowRel`. -/
theorem syncFixedShadowRespC_bind_sim {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} (cap : ℕ)
    (fs : authFixedShadowStTy.denote)
    (c_leg : Comp pqAtomicOps I Γ
      (.prod Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authRespAtomicTy
             authFixedAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy)
    (ρ : Env Γ)
    (hRel : RoBothShadowRel cap fs.1.1.1 fs.2)
    (hBothE : roBothE.eval ρ = fs.2)
    (hStep : ∀ rsf ∈ support (c_leg.eval ρ),
      CacheStepAtMostOne (atomRoCache fs.1.1.1) (atomRoCache rsf.2.1.1) ∧
      CacheStepAtMostOne (atomRootRoCache fs.1.1.1) (atomRootRoCache rsf.2.1.1) ∧
      (atomRoCache rsf.2.1.1).length ≤ cap ∧
      (atomRootRoCache rsf.2.1.1).length ≤ cap) :
    let synced := Comp.bind c_leg
      (syncFixedShadowRespC (I := I) cap (.var .zero) (exprRename Var.succ roBothE))
    Prod.map id forgetAuthFixedShadow <$> synced.eval ρ = c_leg.eval ρ ∧
    ∀ p ∈ support (synced.eval ρ), RoBothShadowRel cap p.2.1.1.1 p.2.2 := by
  have hEach : ∀ rsf ∈ support (c_leg.eval ρ),
      ∃ avls' : roBothAvlTy.denote,
        (syncFixedShadowRespC (I := I) cap (.var .zero) (exprRename Var.succ roBothE)).eval
          (.cons rsf ρ) = pure (rsf.1, (rsf.2, avls')) ∧
        RoBothShadowRel cap rsf.2.1.1 avls' := by
    intro rsf hrsf
    rcases hStep rsf hrsf with ⟨hRoS, hRtS, hRoC, hRtC⟩
    have hBothSub : (exprRename Var.succ roBothE).eval (.cons rsf ρ) = fs.2 :=
      (exprRename_eval roBothE Var.succ ρ (.cons rsf ρ) (fun _ => rfl)).trans hBothE
    simp only [syncFixedShadowRespC, Comp.eval, Expr.eval, Env.get, hBothSub, pure_bind]
    obtain ⟨avls', hSyncEval, hRel'⟩ :=
      syncRoBothC_sim (I := I) cap fs.1.1.1 rsf.2.1.1 fs.2
        (fixedRoCacheE (.snd (.fst .v0)))
        (fixedRootRoCacheE (.snd (.fst .v0)))
        (.snd .v0)
        (.cons (rsf, fs.2) (.cons rsf ρ))
        hRel hRoS hRtS hRoC hRtC
        (fixedRoCacheE_eval _ _) (fixedRootRoCacheE_eval _ _) rfl
    rw [hSyncEval, pure_bind]
    exact ⟨avls', rfl, hRel'⟩
  constructor
  · dsimp only [Comp.eval]
    rw [map_bind]
    conv_rhs => rw [← bind_pure (c_leg.eval ρ)]
    refine OracleComp.bind_congr_of_forall_mem_support (c_leg.eval ρ) fun rsf hrsf => ?_
    obtain ⟨avls', hEval, _⟩ := hEach rsf hrsf
    rw [hEval]
    rfl
  · intro p hp
    dsimp only [Comp.eval] at hp
    rw [mem_support_bind_iff] at hp
    rcases hp with ⟨rsf, hrsf, hp'⟩
    obtain ⟨avls', hEval, hRel'⟩ := hEach rsf hrsf
    rw [hEval, support_pure, Set.mem_singleton_iff] at hp'
    subst hp'
    exact hRel'

/-! ## Shadow RO Arm Simulation -/

private theorem mapSamp_eval_irrel {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (s : _root_.SignalPqxdh.LegacyCosted.PSamp)
    {Γ₁ Γ₂ : List (Ty pqAtomicSig)} (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂) :
    (mapSamp A s).eval ρ₁ = (mapSamp A s).eval ρ₂ := by
  cases s <;> rfl

private theorem roShadowStepC_sim {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ Γs : List (Ty pqAtomicSig)}
    (roList : roListAtomicTy.denote) (tbl : roAvlTy.denote) (sec : (PB 192).denote)
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (tblE : Expr pqAtomicOps Γ roAvlTy)
    (secE : Expr pqAtomicOps Γ (PB 192))
    (ρ : Env Γ) (ρs : Env Γs)
    (hValid : AvlB192Valid cap tbl roList)
    (hNodup : (roList.map Prod.fst).Nodup)
    (hCap : roList.length + 1 ≤ cap)
    (hRoE : roListE.eval ρ = roList)
    (hTblE : tblE.eval ρ = tbl)
    (hSecE : secE.eval ρ = sec) :
    let step := (roShadowStepC A cap roListE tblE secE).eval ρ
    Prod.map id Prod.fst <$> step =
      (match roList.find? (fun p => p.1 == sec) with
       | none => (mapSamp A .drKey96).eval ρs >>= fun dk => pure (dk, (sec, dk) :: roList)
       | some p => pure (p.2, roList)) ∧
    ∀ q ∈ support step,
      q.2.1.length ≤ roList.length + 1 ∧
      AvlB192Valid cap q.2.2 q.2.1 ∧
      (q.2.1.map Prod.fst).Nodup := by
  simp only [roShadowStepC, _root_.ReductionDsl.AtomicPureOp.eval, Comp.eval, Expr.eval,
    hRoE, hTblE, hSecE, pure_bind]
  obtain ⟨path, hSearch, hIns⟩ :=
    avlSearchInsertB192_spec (I := A.toIface) cap
      (.fst (.snd .v0)) (.snd (.snd (.snd .v0)))
      (.cons (roList, (tbl, (sec, CryptoVerification.E2E.ofU8 sec))) ρ :
        Env (.prod roListAtomicTy (.prod roAvlTy
          (.prod (PB (ℓ := 0) (Pt := Empty) 192) (_root_.ReductionDsl.B 192))) :: Γ))
      sec roList rfl hValid
  simp only [Expr.eval, Env.get, Expr.v0] at hIns
  rw [hSearch, pure_bind]
  cases hFind : roList.find? (fun p => p.1 == sec) with
  | some p =>
    simp only [Option.map, Expr.eval, Env.get, Expr.v0, Expr.v2, map_pure,
      Prod.map, id_eq, support_pure, Set.mem_singleton_iff, forall_eq]
    exact ⟨trivial, Nat.le_succ _, hValid, hNodup⟩
  | none =>
    have hMiss : (roList.find? (fun p => p.1 == sec)).isNone = true := by simp [hFind]
    simp only [Option.map, Expr.eval, Env.get, Expr.v0]
    constructor
    · rw [map_bind, mapSamp_eval_irrel A .drKey96 _ ρs]
      refine congrArg (_ >>= ·) (funext fun dk => ?_)
      simp only [Expr.eval, Env.get, Expr.v1, Expr.v2]
      rw [avlInsertAtPathC_eval_congr]
      simp only [Expr.eval, Env.get]
      obtain ⟨tbl', hInsEval, _⟩ := hIns hMiss hCap dk
      rw [hInsEval, pure_bind, map_pure]
      rfl
    · intro q hq
      rw [mem_support_bind_iff] at hq
      rcases hq with ⟨dk, _, hq'⟩
      simp only [Expr.eval, Env.get, Expr.v1, Expr.v2] at hq'
      rw [avlInsertAtPathC_eval_congr] at hq'
      simp only [Expr.eval, Env.get] at hq'
      obtain ⟨tbl', hInsEval, hValid'⟩ := hIns hMiss hCap dk
      rw [hInsEval, pure_bind, support_pure, Set.mem_singleton_iff] at hq'
      subst hq'
      exact ⟨le_refl _, hValid', List.Nodup.cons (not_mem_fst_of_find?_isNone hMiss) hNodup⟩

private theorem roRootShadowStepC_sim {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ Γs₁ : List (Ty pqAtomicSig)} {Γs₂ : (PB 32).denote → List (Ty pqAtomicSig)}
    (rootList : roRootListAtomicTy.denote) (tbl : roRootAvlTy.denote)
    (inp : ((PB 32).prod (PB 32)).denote)
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy)
    (tblE : Expr pqAtomicOps Γ roRootAvlTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32)))
    (ρ : Env Γ) (ρs₁ : Env Γs₁) (ρs₂ : ∀ rk1, Env (Γs₂ rk1))
    (hValid : AvlPair32Valid cap tbl rootList)
    (hNodup : (rootList.map Prod.fst).Nodup)
    (hCap : rootList.length + 1 ≤ cap)
    (hRootE : rootListE.eval ρ = rootList)
    (hTblE : tblE.eval ρ = tbl)
    (hInpE : inpE.eval ρ = inp) :
    let step := (roRootShadowStepC A cap rootListE tblE inpE).eval ρ
    Prod.map id Prod.fst <$> step =
      (match rootList.find? (fun p => p.1.1 == inp.1 && p.1.2 == inp.2) with
       | none =>
         (mapSamp A .bytes32).eval ρs₁ >>= fun rk1 =>
           (mapSamp A .bytes32).eval (ρs₂ rk1) >>= fun ck1 =>
             pure ((rk1, ck1), (inp, (rk1, ck1)) :: rootList)
       | some p => pure (p.2, rootList)) ∧
    ∀ q ∈ support step,
      q.2.1.length ≤ rootList.length + 1 ∧
      AvlPair32Valid cap q.2.2 q.2.1 ∧
      (q.2.1.map Prod.fst).Nodup := by
  rcases inp with ⟨rk, dh⟩
  simp only [roRootShadowStepC, _root_.ReductionDsl.AtomicPureOp.eval, Comp.eval, Expr.eval,
    Env.get, Expr.v0, hRootE, hTblE, hInpE, pure_bind]
  obtain ⟨path, hSearch, hIns⟩ :=
    avlSearchInsertPair32_spec (I := A.toIface) cap
      (.fst (.snd (.var .zero))) (.snd (.snd (.snd (.var .zero))))
      (.cons (rootList, (tbl, ((rk, dh),
        (CryptoVerification.E2E.ofU8 rk, CryptoVerification.E2E.ofU8 dh)))) ρ :
        Env (.prod roRootListAtomicTy (.prod roRootAvlTy
          (.prod (.prod (PB (ℓ := 0) (Pt := Empty) 32) (PB (ℓ := 0) (Pt := Empty) 32))
            (.prod (_root_.ReductionDsl.B 32) (_root_.ReductionDsl.B 32)))) :: Γ))
      rk dh rootList rfl hValid
  simp only [Expr.eval, Env.get] at hIns
  rw [hSearch, pure_bind]
  cases hFind : rootList.find? (fun p => p.1.1 == rk && p.1.2 == dh) with
  | some p =>
    simp only [Option.map, Expr.eval, Env.get, Expr.v2, map_pure,
      Prod.map, id_eq, support_pure, Set.mem_singleton_iff, forall_eq]
    exact ⟨trivial, Nat.le_succ _, hValid, hNodup⟩
  | none =>
    have hMiss : (rootList.find? (fun p => p.1.1 == rk && p.1.2 == dh)).isNone = true := by
      simp [hFind]
    have hMissEq : (rootList.find? (fun p => p.1 == (rk, dh))).isNone = true := by
      rwa [← pair32_find?_beq_eq]
    simp only [Option.map, bind_assoc, pure_bind]
    constructor
    · rw [map_bind, mapSamp_eval_irrel A .bytes32 _ ρs₁]
      refine congrArg (_ >>= ·) (funext fun rk1 => ?_)
      rw [map_bind, mapSamp_eval_irrel A .bytes32 _ (ρs₂ rk1)]
      refine congrArg (_ >>= ·) (funext fun ck1 => ?_)
      simp only [Expr.eval, Env.get, Expr.v1, Expr.v2]
      rw [avlInsertAtPathC_eval_congr]
      simp only [Expr.eval, Env.get]
      obtain ⟨tbl', hInsEval, _⟩ := hIns hMiss hCap (rk1, ck1)
      rw [hInsEval, pure_bind, map_pure]
      rfl
    · intro q hq
      rw [mem_support_bind_iff] at hq
      rcases hq with ⟨rk1, _, hq1⟩
      rw [mem_support_bind_iff] at hq1
      rcases hq1 with ⟨ck1, _, hq2⟩
      simp only [Expr.eval, Env.get, Expr.v1, Expr.v2] at hq2
      rw [avlInsertAtPathC_eval_congr] at hq2
      simp only [Expr.eval, Env.get] at hq2
      obtain ⟨tbl', hInsEval, hValid'⟩ := hIns hMiss hCap (rk1, ck1)
      rw [hInsEval, pure_bind, support_pure, Set.mem_singleton_iff] at hq2
      subst hq2
      exact ⟨le_refl _, hValid', List.Nodup.cons (not_mem_fst_of_find?_isNone hMissEq) hNodup⟩

private theorem baseSetRoCacheE_props {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ authBaseAtomicTy)
    (roE : Expr pqAtomicOps Γ roListAtomicTy) (ρ : Env Γ) {nOn : ℕ}
    (hOn : AuthCoreKSimBase.AuthBaseAtomOnlineBounded nOn (stE.eval ρ)) :
    AuthCoreKSimBase.AuthBaseAtomOnlineBounded nOn ((baseSetRoCacheE stE roE).eval ρ) ∧
    atomRoCache ((baseSetRoCacheE stE roE).eval ρ) = roE.eval ρ ∧
    atomRootRoCache ((baseSetRoCacheE stE roE).eval ρ) = atomRootRoCache (stE.eval ρ) := by
  simp only [baseSetRoCacheE, liftExpr2_eval,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stUpd,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stMk,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRoot, stAdv,
    embedVar, mapExpr, Expr.eval, Env.get]
  exact ⟨⟨hOn.1, hOn.2, hOn.3, hOn.4, hOn.5, hOn.6, hOn.7, hOn.8, hOn.9,
    hOn.10, hOn.11, hOn.12, hOn.13⟩, rfl, rfl⟩

private theorem baseSetRootRoCacheE_props {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ authBaseAtomicTy)
    (rootE : Expr pqAtomicOps Γ roRootListAtomicTy) (ρ : Env Γ) {nOn : ℕ}
    (hOn : AuthCoreKSimBase.AuthBaseAtomOnlineBounded nOn (stE.eval ρ)) :
    AuthCoreKSimBase.AuthBaseAtomOnlineBounded nOn ((baseSetRootRoCacheE stE rootE).eval ρ) ∧
    atomRoCache ((baseSetRootRoCacheE stE rootE).eval ρ) = atomRoCache (stE.eval ρ) ∧
    atomRootRoCache ((baseSetRootRoCacheE stE rootE).eval ρ) = rootE.eval ρ := by
  simp only [baseSetRootRoCacheE, liftExpr2_eval,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stUpd,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stMk,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stAdv,
    embedVar, mapExpr, Expr.eval, Env.get]
  exact ⟨⟨hOn.1, hOn.2, hOn.3, hOn.4, hOn.5, hOn.6, hOn.7, hOn.8, hOn.9,
    hOn.10, hOn.11, hOn.12, hOn.13⟩, rfl, rfl⟩

/-- Step simulation for `.roQuery` on `authBaseShadowStTy` against `roB`. -/
theorem roBaseShadowArmC_sim (S : Setup) (b : QueryBudget)
    {nOn nRo nRoot : ℕ}
    {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy)
    (secE : Expr pqAtomicOps Γ (PB 192))
    (ρ : Env Γ)
    (bs : authBaseShadowStTy.denote)
    (sec : (PB 192).denote)
    (hsE : sE.eval ρ = bs)
    (hsecE : secE.eval ρ = sec)
    (hSh : AuthBaseShadowAt S b nOn nRo nRoot bs)
    (hOld : nRo + 1 ≤ b.q_total)
    (hCap : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap) :
    let arm := roBaseShadowArmC aiAuthPrim (AuthKindFuels.ofBudget S b).K_cap sE secE
    let leg := mapComp tlAuthPrim
      (roB b.q_total (Γ₁ := [authStateTy, B 192]) (Γ₂ := [B 192]) (Δ := [authStateTy, B 192]) .zero .zero)
    Prod.map id forgetAuthBaseShadow <$> arm.eval ρ = leg.eval (.cons bs.1 (.cons sec .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthBaseShadowAt S b nOn (nRo + 1) nRoot p.2 := by
  intro arm leg
  have hCapStep : (atomRoCache bs.1).length + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap :=
    Nat.le_trans (Nat.add_le_add_right hSh.ro_len_le 1) hCap
  have hTake : (atomRoCache bs.1).take b.q_total = atomRoCache bs.1 :=
    List.take_of_length_le (Nat.le_trans hSh.ro_len_le (Nat.le_of_succ_le hOld))
  have ⟨hStepMap, hStepSup⟩ :=
    roShadowStepC_sim aiAuthPrim (AuthKindFuels.ofBudget S b).K_cap
      (atomRoCache bs.1) bs.2.1 sec
      (baseRoCacheE (.fst (.fst .v0))) (.fst (.snd (.fst .v0))) (.snd .v0)
      (.cons (bs, sec) ρ) (.cons sec (.cons bs.1 (.cons sec .nil)))
      hSh.ro_shadow.both_valid.ro_valid hSh.ro_shadow.ro_nodup hCapStep (baseRoCacheE_eval _ _) rfl rfl
  constructor
  · have hLeg : leg.eval (.cons bs.1 (.cons sec .nil)) =
        (match (atomRoCache bs.1).find? (fun p => p.1 == sec) with
         | none =>
           (mapSamp aiAuthPrim .drKey96).eval (.cons sec (.cons bs.1 (.cons sec .nil))) >>=
             fun dk => pure (dk, (sec, dk) :: atomRoCache bs.1)
         | some p => pure (p.2, atomRoCache bs.1)) >>= fun r =>
          pure ((aDrKeyAtomicE (Γ := [_root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty)]) .v0).eval
              (.cons r.1 .nil),
            (baseSetRoCacheE (Γ := [roListAtomicTy, authBaseAtomicTy]) (.var (.succ .zero)) .v0).eval
              (.cons r.2 (.cons bs.1 .nil))) := by
      simp only [atomRoCache] at hTake
      simp only [leg, roB, hkdfOrRoC, rs, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.aDrKey,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stUpd, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stMk,
        stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
        stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eFind,
        _root_.ReductionDsl.Comp.letC, _root_.ReductionDsl.Expr.findBounded,
        _root_.ReductionDsl.Expr.bytesBeq, _root_.ReductionDsl.Expr.listCons,
        _root_.ReductionDsl.Comp.sampleDrKey96, _root_.ReductionDsl.AtomicPureOp.eval,
        embedVar, mapComp, mapExpr, mapOpExpr, mapSampCast, mapSampH, castLegacySamp,
        Comp.eval, Expr.eval, Env.get, Expr.v0, atomRoCache, ↓reduceIte, pure_bind,
        hTake, aDrKeyAtomicE, baseSetRoCacheE, liftExpr1_eval, liftExpr2_eval]
      split <;> (next h => simp only [h]; try rfl)
    rw [hLeg]
    dsimp only [arm, roBaseShadowArmC, Comp.eval, Expr.eval]
    rw [hsE, hsecE, pure_bind, map_bind, ← hStepMap, bind_map_left]
    refine congrArg (_ >>= ·) (funext fun q => ?_)
    simp only [Expr.eval, Env.get, Expr.v0, Expr.v1, forgetAuthBaseShadow, map_pure, Prod.map,
      id_eq, aDrKeyAtomicE, baseSetRoCacheE, liftExpr1_eval, liftExpr2_eval]
  · intro p hp
    dsimp only [arm, roBaseShadowArmC, Comp.eval, Expr.eval] at hp
    rw [hsE, hsecE, pure_bind, mem_support_bind_iff] at hp
    rcases hp with ⟨q, hq, hp'⟩
    rw [support_pure, Set.mem_singleton_iff] at hp'
    subst hp'
    rcases hStepSup q hq with ⟨hLen, hValid', hNodup'⟩
    rcases baseSetRoCacheE_props (.fst (.fst .v1)) (.fst (.snd .v0))
      (.cons q (.cons (bs, sec) ρ)) hSh.online_le with ⟨hOn', hRo', hRoot'⟩
    simp only [Expr.eval, Env.get, Expr.v0, Expr.v1] at hOn' hRo' hRoot' ⊢
    refine ⟨hOn', ?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
    · rw [hRo']; exact Nat.le_trans hLen (Nat.add_le_add_right hSh.ro_len_le 1)
    · rw [hRoot']; exact hSh.root_len_le
    · rw [hRo']; exact hValid'
    · rw [hRoot']; exact hSh.ro_shadow.both_valid.root_valid
    · rw [hRo']; exact hNodup'
    · rw [hRoot']; exact hSh.ro_shadow.root_nodup

/-- Step simulation for `.roRootQuery` on `authBaseShadowStTy` against `roRootB`. -/
theorem roRootBaseShadowArmC_sim (S : Setup) (b : QueryBudget)
    {nOn nRo nRoot : ℕ}
    {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32)))
    (ρ : Env Γ)
    (bs : authBaseShadowStTy.denote)
    (inp : ((PB 32).prod (PB 32)).denote)
    (hsE : sE.eval ρ = bs)
    (hinpE : inpE.eval ρ = inp)
    (hSh : AuthBaseShadowAt S b nOn nRo nRoot bs)
    (hOld : nRoot + 1 ≤ b.q_total)
    (hCap : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap) :
    let B32 := B 32
    let arm := roRootBaseShadowArmC aiAuthPrim (AuthKindFuels.ofBudget S b).K_cap sE inpE
    let leg := mapComp tlAuthPrim
      (roRootB b.q_total (Γ₁ := [authStateTy, .prod B32 B32]) (Γ₂ := [.prod B32 B32])
        (Δ := [authStateTy, .prod B32 B32]) .zero .zero)
    Prod.map id forgetAuthBaseShadow <$> arm.eval ρ = leg.eval (.cons bs.1 (.cons inp .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthBaseShadowAt S b nOn nRo (nRoot + 1) p.2 := by
  intro B32 arm leg
  have hCapStep : (atomRootRoCache bs.1).length + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap :=
    Nat.le_trans (Nat.add_le_add_right hSh.root_len_le 1) hCap
  have hTake : (atomRootRoCache bs.1).take b.q_total = atomRootRoCache bs.1 :=
    List.take_of_length_le (Nat.le_trans hSh.root_len_le (Nat.le_of_succ_le hOld))
  have ⟨hStepMap, hStepSup⟩ :=
    roRootShadowStepC_sim aiAuthPrim (AuthKindFuels.ofBudget S b).K_cap
      (atomRootRoCache bs.1) bs.2.2 inp
      (baseRootRoCacheE (.fst (.fst .v0))) (.snd (.snd (.fst .v0))) (.snd .v0)
      (.cons (bs, inp) ρ) (.cons inp (.cons bs.1 (.cons inp .nil)))
      (fun rk1 => .cons rk1 (.cons inp (.cons bs.1 (.cons inp .nil))))
      hSh.ro_shadow.both_valid.root_valid hSh.ro_shadow.root_nodup hCapStep (baseRootRoCacheE_eval _ _) rfl rfl
  constructor
  · have hLeg : leg.eval (.cons bs.1 (.cons inp .nil)) =
        (match (atomRootRoCache bs.1).find? (fun p => p.1.1 == inp.1 && p.1.2 == inp.2) with
         | none =>
           (mapSamp aiAuthPrim .bytes32).eval (.cons inp (.cons bs.1 (.cons inp .nil))) >>=
             fun rk1 =>
               (mapSamp aiAuthPrim .bytes32).eval
                 (.cons rk1 (.cons inp (.cons bs.1 (.cons inp .nil)))) >>=
                 fun ck1 => pure ((rk1, ck1), (inp, (rk1, ck1)) :: atomRootRoCache bs.1)
         | some p => pure (p.2, atomRootRoCache bs.1)) >>= fun r =>
          pure ((aRootKdfAtomicE (Γ := [.prod (PB 32) (PB 32)]) .v0).eval (.cons r.1 .nil),
            (baseSetRootRoCacheE (Γ := [roRootListAtomicTy, authBaseAtomicTy])
              (.var (.succ .zero)) .v0).eval (.cons r.2 (.cons bs.1 .nil))) := by
      rcases inp with ⟨rk, dh⟩
      simp only [atomRootRoCache] at hTake
      simp only [leg, roRootB, rs, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.rootRoC,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.aRootKdf,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stUpd, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stMk,
        stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
        stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bytes2Eq,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eFind,
        _root_.ReductionDsl.Comp.letC, _root_.ReductionDsl.Expr.findBounded,
        _root_.ReductionDsl.Expr.bytesBeq, _root_.ReductionDsl.Expr.boolAnd,
        _root_.ReductionDsl.Expr.listCons, _root_.ReductionDsl.Comp.sampleBytes32,
        _root_.ReductionDsl.AtomicPureOp.eval, embedVar, mapComp, mapExpr, mapOpExpr,
        mapSampCast, mapSampH, castLegacySamp, Comp.eval, Expr.eval, Env.get, Expr.v0, atomRootRoCache,
        pure_bind, hTake, aRootKdfAtomicE, baseSetRootRoCacheE, liftExpr1_eval, liftExpr2_eval]
      split <;> (next h => simp only [h]; try rfl)
    rw [hLeg]
    dsimp only [arm, roRootBaseShadowArmC, Comp.eval, Expr.eval]
    rw [hsE, hinpE, pure_bind, map_bind, ← hStepMap, bind_map_left]
    refine congrArg (_ >>= ·) (funext fun q => ?_)
    simp only [Expr.eval, Env.get, Expr.v0, Expr.v1, forgetAuthBaseShadow, map_pure, Prod.map,
      id_eq, aRootKdfAtomicE, baseSetRootRoCacheE, liftExpr1_eval, liftExpr2_eval]
  · intro p hp
    dsimp only [arm, roRootBaseShadowArmC, Comp.eval, Expr.eval] at hp
    rw [hsE, hinpE, pure_bind, mem_support_bind_iff] at hp
    rcases hp with ⟨q, hq, hp'⟩
    rw [support_pure, Set.mem_singleton_iff] at hp'
    subst hp'
    rcases hStepSup q hq with ⟨hLen, hValid', hNodup'⟩
    rcases baseSetRootRoCacheE_props (.fst (.fst .v1)) (.fst (.snd .v0))
      (.cons q (.cons (bs, inp) ρ)) hSh.online_le with ⟨hOn', hRo', hRoot'⟩
    simp only [Expr.eval, Env.get, Expr.v0, Expr.v1] at hOn' hRo' hRoot' ⊢
    refine ⟨hOn', ?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
    · rw [hRo']; exact hSh.ro_len_le
    · rw [hRoot']; exact Nat.le_trans hLen (Nat.add_le_add_right hSh.root_len_le 1)
    · rw [hRo']; exact hSh.ro_shadow.both_valid.ro_valid
    · rw [hRoot']; exact hValid'
    · rw [hRo']; exact hSh.ro_shadow.ro_nodup
    · rw [hRoot']; exact hNodup'

private theorem fixedHasWonE_eval {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) (ρ : Env Γ) :
    (fixedHasWonE fhstE).eval ρ = (fhstE.eval ρ).1.1.2.1 := by
  simp only [fixedHasWonE, liftExpr1_eval, asHasWonAuth, ahsBase, ahsfHybrid,
    embedVar, mapExpr, Expr.eval, Env.get]

private theorem fixedSetRoCacheE_props {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy)
    (roE : Expr pqAtomicOps Γ roListAtomicTy) (ρ : Env Γ) {nOn : ℕ}
    (hOn : AuthCoreKSimBase.AuthFixedAtomOnlineBounded nOn (fhstE.eval ρ)) :
    AuthCoreKSimBase.AuthFixedAtomOnlineBounded nOn ((fixedSetRoCacheE fhstE roE).eval ρ) ∧
    atomRoCache ((fixedSetRoCacheE fhstE roE).eval ρ).1.1 = roE.eval ρ ∧
    atomRootRoCache ((fixedSetRoCacheE fhstE roE).eval ρ).1.1 =
      atomRootRoCache (fhstE.eval ρ).1.1 := by
  simp only [fixedSetRoCacheE, liftExpr2_eval, fhstSetBase,
    ahsfUpd, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsUpd, ahsMk, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stUpd,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stMk,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRootRoCache, asAdvKeys, embedVar, mapExpr, Expr.eval, Env.get]
  exact ⟨⟨⟨hOn.1.1, hOn.1.2, hOn.1.3, hOn.1.4, hOn.1.5, hOn.1.6, hOn.1.7, hOn.1.8, hOn.1.9,
    hOn.1.10, hOn.1.11, hOn.1.12, hOn.1.13⟩,
    hOn.2, hOn.3, hOn.4, hOn.5⟩, rfl, rfl⟩

private theorem fixedSetRootRoCacheE_props {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy)
    (rootE : Expr pqAtomicOps Γ roRootListAtomicTy) (ρ : Env Γ) {nOn : ℕ}
    (hOn : AuthCoreKSimBase.AuthFixedAtomOnlineBounded nOn (fhstE.eval ρ)) :
    AuthCoreKSimBase.AuthFixedAtomOnlineBounded nOn ((fixedSetRootRoCacheE fhstE rootE).eval ρ) ∧
    atomRoCache ((fixedSetRootRoCacheE fhstE rootE).eval ρ).1.1 =
      atomRoCache (fhstE.eval ρ).1.1 ∧
    atomRootRoCache ((fixedSetRootRoCacheE fhstE rootE).eval ρ).1.1 = rootE.eval ρ := by
  simp only [fixedSetRootRoCacheE, liftExpr2_eval, fhstSetBase,
    ahsfUpd, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsUpd, ahsMk, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stUpd,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stMk,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asAdvKeys, embedVar, mapExpr, Expr.eval, Env.get]
  exact ⟨⟨⟨hOn.1.1, hOn.1.2, hOn.1.3, hOn.1.4, hOn.1.5, hOn.1.6, hOn.1.7, hOn.1.8, hOn.1.9,
    hOn.1.10, hOn.1.11, hOn.1.12, hOn.1.13⟩,
    hOn.2, hOn.3, hOn.4, hOn.5⟩, rfl, rfl⟩

private theorem roFixedShadowArmC_sim_gen {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (secE : Expr pqAtomicOps Γ (PB 192))
    (ρ : Env Γ)
    (fs : authFixedShadowStTy.denote)
    (sec : (PB 192).denote)
    (leg : Comp pqAtomicOps A.toIface [authFixedAtomicTy, PB 192]
      (.prod AuthCoreK.authRespAtomicTy authFixedAtomicTy))
    (hfsE : fsE.eval ρ = fs)
    (hsecE : secE.eval ρ = sec)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hOld : nRo + 1 ≤ b.q_total)
    (hCap : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap)
    (hLeg : leg.eval (.cons fs.1 (.cons sec .nil)) =
      if fs.1.1.1.2.1 = true then pure (.inl (), fs.1)
      else
        (match ((atomRoCache fs.1.1.1).take b.q_total).find? (fun p => p.1 == sec) with
         | none =>
           (mapSamp A .drKey96).eval (.cons sec (.cons fs.1.1.1 (.cons fs.1 (.cons sec .nil)))) >>=
             fun dk => pure (dk, (sec, dk) :: atomRoCache fs.1.1.1)
         | some p => pure (p.2, atomRoCache fs.1.1.1)) >>= fun r =>
          pure ((aDrKeyAtomicE (Γ := [_root_.ReductionDsl.drKeyT (ℓ := 0) (Pt := Empty)]) .v0).eval
              (.cons r.1 .nil),
            (fixedSetRoCacheE (Γ := [roListAtomicTy, authFixedAtomicTy])
              (.var (.succ .zero)) .v0).eval (.cons r.2 (.cons fs.1 .nil)))) :
    let arm := roFixedShadowArmC A (AuthKindFuels.ofBudget S b).K_cap fsE secE
    Prod.map id forgetAuthFixedShadow <$> arm.eval ρ =
      leg.eval (.cons fs.1 (.cons sec .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthFixedShadowAt S b nOn (nRo + 1) nRoot p.2 := by
  have hCapStep : (atomRoCache fs.1.1.1).length + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap :=
    Nat.le_trans (Nat.add_le_add_right hSh.ro_len_le 1) hCap
  have hTake : (atomRoCache fs.1.1.1).take b.q_total = atomRoCache fs.1.1.1 :=
    List.take_of_length_le (Nat.le_trans hSh.ro_len_le (Nat.le_of_succ_le hOld))
  have ⟨hStepMap, hStepSup⟩ :=
    roShadowStepC_sim A (AuthKindFuels.ofBudget S b).K_cap
      (atomRoCache fs.1.1.1) fs.2.1 sec
      (fixedRoCacheE (.fst (.fst .v0))) (.fst (.snd (.fst .v0))) (.snd .v0)
      (.cons (fs, sec) ρ) (.cons sec (.cons fs.1.1.1 (.cons fs.1 (.cons sec .nil))))
      hSh.ro_shadow.both_valid.ro_valid hSh.ro_shadow.ro_nodup hCapStep
      (fixedRoCacheE_eval _ _) rfl rfl
  intro arm
  constructor
  · rw [hLeg, hTake]
    dsimp only [arm, roFixedShadowArmC, Comp.eval, Expr.eval]
    rw [hfsE, hsecE, pure_bind]
    simp only [fixedHasWonE_eval, Expr.eval, Env.get, Expr.v0]
    cases hWon : fs.1.1.1.2.1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [map_bind, ← hStepMap, bind_map_left]
      refine congrArg (_ >>= ·) (funext fun q => ?_)
      simp only [Expr.eval, Env.get, Expr.v1, forgetAuthFixedShadow, map_pure, Prod.map,
        id_eq, aDrKeyAtomicE, fixedSetRoCacheE, liftExpr1_eval, liftExpr2_eval]
    · simp only [↓reduceIte, Expr.eval, aNoneAtomicE,
        forgetAuthFixedShadow, map_pure, Prod.map, id_eq]
  · intro p hp
    dsimp only [arm, roFixedShadowArmC, Comp.eval, Expr.eval] at hp
    rw [hfsE, hsecE, pure_bind] at hp
    simp only [fixedHasWonE_eval, Expr.eval, Env.get, Expr.v0] at hp
    cases hWon : fs.1.1.1.2.1 <;> simp only [hWon, Bool.false_eq_true, ↓reduceIte] at hp
    · rw [mem_support_bind_iff] at hp
      rcases hp with ⟨q, hq, hp'⟩
      rw [support_pure, Set.mem_singleton_iff] at hp'
      subst hp'
      rcases hStepSup q hq with ⟨hLen, hValid', hNodup'⟩
      rcases fixedSetRoCacheE_props (.fst (.fst .v1)) (.fst (.snd .v0))
        (.cons q (.cons (fs, sec) ρ)) hSh.online_le with ⟨hOn', hRo', hRoot'⟩
      simp only [Expr.eval, Env.get, Expr.v0, Expr.v1] at hOn' hRo' hRoot' ⊢
      refine ⟨hOn', ?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
      · rw [hRo']; exact Nat.le_trans hLen (Nat.add_le_add_right hSh.ro_len_le 1)
      · rw [hRoot']; exact hSh.root_len_le
      · rw [hRo']; exact hValid'
      · rw [hRoot']; exact hSh.ro_shadow.both_valid.root_valid
      · rw [hRo']; exact hNodup'
      · rw [hRoot']; exact hSh.ro_shadow.root_nodup
    · simp only [support_pure, Set.mem_singleton_iff, Expr.eval, aNoneAtomicE] at hp
      subst hp
      exact hSh.mono (le_refl _) (Nat.le_succ _) (le_refl _)

private theorem roRootFixedShadowArmC_sim_gen {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32)))
    (ρ : Env Γ)
    (fs : authFixedShadowStTy.denote)
    (inp : ((PB 32).prod (PB 32)).denote)
    (leg : Comp pqAtomicOps A.toIface [authFixedAtomicTy, .prod (PB 32) (PB 32)]
      (.prod AuthCoreK.authRespAtomicTy authFixedAtomicTy))
    (hfsE : fsE.eval ρ = fs)
    (hinpE : inpE.eval ρ = inp)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hOld : nRoot + 1 ≤ b.q_total)
    (hCap : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap)
    (hLeg : leg.eval (.cons fs.1 (.cons inp .nil)) =
      if fs.1.1.1.2.1 = true then pure (.inl (), fs.1)
      else
        (match ((atomRootRoCache fs.1.1.1).take b.q_total).find?
            (fun p => p.1.1 == inp.1 && p.1.2 == inp.2) with
         | none =>
           (mapSamp A .bytes32).eval (.cons inp (.cons fs.1.1.1 (.cons fs.1 (.cons inp .nil)))) >>=
             fun rk1 =>
               (mapSamp A .bytes32).eval
                 (.cons rk1 (.cons inp (.cons fs.1.1.1 (.cons fs.1 (.cons inp .nil))))) >>=
                 fun ck1 => pure ((rk1, ck1), (inp, (rk1, ck1)) :: atomRootRoCache fs.1.1.1)
         | some p => pure (p.2, atomRootRoCache fs.1.1.1)) >>= fun r =>
          pure ((aRootKdfAtomicE (Γ := [.prod (PB 32) (PB 32)]) .v0).eval (.cons r.1 .nil),
            (fixedSetRootRoCacheE (Γ := [roRootListAtomicTy, authFixedAtomicTy])
              (.var (.succ .zero)) .v0).eval (.cons r.2 (.cons fs.1 .nil)))) :
    let arm := roRootFixedShadowArmC A (AuthKindFuels.ofBudget S b).K_cap fsE inpE
    Prod.map id forgetAuthFixedShadow <$> arm.eval ρ =
      leg.eval (.cons fs.1 (.cons inp .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthFixedShadowAt S b nOn nRo (nRoot + 1) p.2 := by
  have hCapStep : (atomRootRoCache fs.1.1.1).length + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap :=
    Nat.le_trans (Nat.add_le_add_right hSh.root_len_le 1) hCap
  have hTake : (atomRootRoCache fs.1.1.1).take b.q_total = atomRootRoCache fs.1.1.1 :=
    List.take_of_length_le (Nat.le_trans hSh.root_len_le (Nat.le_of_succ_le hOld))
  have ⟨hStepMap, hStepSup⟩ :=
    roRootShadowStepC_sim A (AuthKindFuels.ofBudget S b).K_cap
      (atomRootRoCache fs.1.1.1) fs.2.2 inp
      (fixedRootRoCacheE (.fst (.fst .v0))) (.snd (.snd (.fst .v0))) (.snd .v0)
      (.cons (fs, inp) ρ)
      (.cons inp (.cons fs.1.1.1 (.cons fs.1 (.cons inp .nil))))
      (fun rk1 => .cons rk1 (.cons inp (.cons fs.1.1.1 (.cons fs.1 (.cons inp .nil)))))
      hSh.ro_shadow.both_valid.root_valid hSh.ro_shadow.root_nodup hCapStep
      (fixedRootRoCacheE_eval _ _) rfl rfl
  intro arm
  constructor
  · rw [hLeg, hTake]
    dsimp only [arm, roRootFixedShadowArmC, Comp.eval, Expr.eval]
    rw [hfsE, hinpE, pure_bind]
    simp only [fixedHasWonE_eval, Expr.eval, Env.get, Expr.v0]
    cases hWon : fs.1.1.1.2.1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [map_bind, ← hStepMap, bind_map_left]
      refine congrArg (_ >>= ·) (funext fun q => ?_)
      simp only [Expr.eval, Env.get, Expr.v1, forgetAuthFixedShadow, map_pure, Prod.map,
        id_eq, aRootKdfAtomicE, fixedSetRootRoCacheE, liftExpr1_eval, liftExpr2_eval]
    · simp only [↓reduceIte, Expr.eval, aNoneAtomicE,
        forgetAuthFixedShadow, map_pure, Prod.map, id_eq]
  · intro p hp
    dsimp only [arm, roRootFixedShadowArmC, Comp.eval, Expr.eval] at hp
    rw [hfsE, hinpE, pure_bind] at hp
    simp only [fixedHasWonE_eval, Expr.eval, Env.get, Expr.v0] at hp
    cases hWon : fs.1.1.1.2.1 <;> simp only [hWon, Bool.false_eq_true, ↓reduceIte] at hp
    · rw [mem_support_bind_iff] at hp
      rcases hp with ⟨q, hq, hp'⟩
      rw [support_pure, Set.mem_singleton_iff] at hp'
      subst hp'
      rcases hStepSup q hq with ⟨hLen, hValid', hNodup'⟩
      rcases fixedSetRootRoCacheE_props (.fst (.fst .v1)) (.fst (.snd .v0))
        (.cons q (.cons (fs, inp) ρ)) hSh.online_le with ⟨hOn', hRo', hRoot'⟩
      simp only [Expr.eval, Env.get, Expr.v0, Expr.v1] at hOn' hRo' hRoot' ⊢
      refine ⟨hOn', ?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
      · rw [hRo']; exact hSh.ro_len_le
      · rw [hRoot']; exact Nat.le_trans hLen (Nat.add_le_add_right hSh.root_len_le 1)
      · rw [hRo']; exact hSh.ro_shadow.both_valid.ro_valid
      · rw [hRoot']; exact hValid'
      · rw [hRo']; exact hSh.ro_shadow.ro_nodup
      · rw [hRoot']; exact hNodup'
    · simp only [support_pure, Set.mem_singleton_iff, Expr.eval, aNoneAtomicE] at hp
      subst hp
      exact hSh.mono (le_refl _) (le_refl _) (Nat.le_succ _)

/-- Step simulation for `.roQuery` on `authFixedShadowStTy` over `aiAuthPrim`. -/
theorem roFixedShadowArmC_sim_prim (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    {Γ : List (Ty pqAtomicSig)} (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) (ρ : Env Γ)
    (fs : authFixedShadowStTy.denote) (sec : (PB 192).denote)
    (hfsE : fsE.eval ρ = fs) (hsecE : secE.eval ρ = sec)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hOld : nRo + 1 ≤ b.q_total) (hCap : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap) :
    let arm := roFixedShadowArmC aiAuthPrim (AuthKindFuels.ofBudget S b).K_cap fsE secE
    let leg := mapComp tlAuthPrim (roFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, B 192])
      (Γ₂ := [B 192]) (Δ := [authHybridStateFixedTy, B 192]) .zero .zero)
    Prod.map id forgetAuthFixedShadow <$> arm.eval ρ = leg.eval (.cons fs.1 (.cons sec .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthFixedShadowAt S b nOn (nRo + 1) nRoot p.2 := by
  refine roFixedShadowArmC_sim_gen aiAuthPrim S b fsE secE ρ fs sec _ hfsE hsecE hSh hOld hCap ?_
  simp only [roFixedB, hkdfRoC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseOptV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eFind, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext.wk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bytesBeq, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aNone,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aDrKey, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.aDrKey,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stUpd, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stMk,
    fhstSetBase, ahsfUpd, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsUpd, ahsMk, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, samplePrim, _root_.ReductionDsl.AtomicPureOp.eval,
    embedVar, mapComp, mapExpr, mapOpExpr, mapSampCast, mapSampH, castLegacySamp, Comp.eval, Expr.eval, Env.get,
    Expr.v0, atomRoCache, pure_bind, aDrKeyAtomicE, fixedSetRoCacheE, liftExpr1_eval, liftExpr2_eval]
  cases fs.1.1.1.2.1
  · simp only [Bool.false_eq_true, ↓reduceIte]; split <;> (next h => simp only [h]; try rfl)
  · rfl

/-- Step simulation for `.roRootQuery` on `authFixedShadowStTy` over `aiAuthPrim`. -/
theorem roRootFixedShadowArmC_sim_prim (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    {Γ : List (Ty pqAtomicSig)} (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) (ρ : Env Γ)
    (fs : authFixedShadowStTy.denote) (inp : ((PB 32).prod (PB 32)).denote)
    (hfsE : fsE.eval ρ = fs) (hinpE : inpE.eval ρ = inp)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hOld : nRoot + 1 ≤ b.q_total) (hCap : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap) :
    let B32 := B 32
    let arm := roRootFixedShadowArmC aiAuthPrim (AuthKindFuels.ofBudget S b).K_cap fsE inpE
    let leg := mapComp tlAuthPrim (roRootFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .prod B32 B32])
      (Γ₂ := [.prod B32 B32]) (Δ := [authHybridStateFixedTy, .prod B32 B32]) .zero .zero)
    Prod.map id forgetAuthFixedShadow <$> arm.eval ρ = leg.eval (.cons fs.1 (.cons inp .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthFixedShadowAt S b nOn nRo (nRoot + 1) p.2 := by
  refine roRootFixedShadowArmC_sim_gen aiAuthPrim S b fsE inpE ρ fs inp _ hfsE hinpE hSh hOld hCap ?_
  rcases inp with ⟨rk, dh⟩
  simp only [roRootFixedB, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.rootRoC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseOptV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eFind,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext.wk, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bytesBeq,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bytes2Eq, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aNone,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aRootKdf, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.aRootKdf,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stUpd, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stMk,
    fhstSetBase, ahsfUpd, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsUpd, ahsMk, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, samplePrim, _root_.ReductionDsl.AtomicPureOp.eval,
    embedVar, mapComp, mapExpr, mapOpExpr, mapSampCast, mapSampH, castLegacySamp, Comp.eval, Expr.eval, Env.get,
    Expr.v0, atomRootRoCache, pure_bind, aRootKdfAtomicE, fixedSetRootRoCacheE, liftExpr1_eval, liftExpr2_eval]
  cases fs.1.1.1.2.1
  · simp only [Bool.false_eq_true, ↓reduceIte]; split <;> (next h => simp only [h]; try rfl)
  · rfl

/-- Step simulation for `.roQuery` on `authFixedShadowStTy` over `aiPrfMk`. -/
theorem roFixedShadowArmC_sim_mk (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    {Γ : List (Ty pqAtomicSig)} (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) (ρ : Env Γ)
    (fs : authFixedShadowStTy.denote) (sec : (PB 192).denote)
    (hfsE : fsE.eval ρ = fs) (hsecE : secE.eval ρ = sec)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hOld : nRo + 1 ≤ b.q_total) (hCap : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap) :
    let arm := roFixedShadowArmC aiPrfMk (AuthKindFuels.ofBudget S b).K_cap fsE secE
    let leg := mapComp tlPrfMk (liftPrimComp (C := msgKeyPrfOracle)
      (roFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, B 192]) (Γ₂ := [B 192])
        (Δ := [authHybridStateFixedTy, B 192]) .zero .zero))
    Prod.map id forgetAuthFixedShadow <$> arm.eval ρ = leg.eval (.cons fs.1 (.cons sec .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthFixedShadowAt S b nOn (nRo + 1) nRoot p.2 := by
  refine roFixedShadowArmC_sim_gen aiPrfMk S b fsE secE ρ fs sec _ hfsE hsecE hSh hOld hCap ?_
  simp only [roFixedB, hkdfRoC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseOptV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eFind, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext.wk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bytesBeq, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aNone,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aDrKey, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.aDrKey,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stUpd, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stMk,
    fhstSetBase, ahsfUpd, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsUpd, ahsMk, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, samplePrim, liftPrimComp, _root_.ReductionDsl.AtomicPureOp.eval,
    embedVar, mapComp, mapExpr, mapOpExpr, mapSampCast, mapSampH, castLegacySamp, Comp.eval, Expr.eval, Env.get,
    Expr.v0, atomRoCache, pure_bind, aDrKeyAtomicE, fixedSetRoCacheE, liftExpr1_eval, liftExpr2_eval]
  cases fs.1.1.1.2.1
  · simp only [Bool.false_eq_true, ↓reduceIte]; split <;> (next h => simp only [h]; try rfl)
  · rfl

/-- Step simulation for `.roRootQuery` on `authFixedShadowStTy` over `aiPrfMk`. -/
theorem roRootFixedShadowArmC_sim_mk (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    {Γ : List (Ty pqAtomicSig)} (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) (ρ : Env Γ)
    (fs : authFixedShadowStTy.denote) (inp : ((PB 32).prod (PB 32)).denote)
    (hfsE : fsE.eval ρ = fs) (hinpE : inpE.eval ρ = inp)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hOld : nRoot + 1 ≤ b.q_total) (hCap : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap) :
    let B32 := B 32
    let arm := roRootFixedShadowArmC aiPrfMk (AuthKindFuels.ofBudget S b).K_cap fsE inpE
    let leg := mapComp tlPrfMk (liftPrimComp (C := msgKeyPrfOracle)
      (roRootFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .prod B32 B32]) (Γ₂ := [.prod B32 B32])
        (Δ := [authHybridStateFixedTy, .prod B32 B32]) .zero .zero))
    Prod.map id forgetAuthFixedShadow <$> arm.eval ρ = leg.eval (.cons fs.1 (.cons inp .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthFixedShadowAt S b nOn nRo (nRoot + 1) p.2 := by
  refine roRootFixedShadowArmC_sim_gen aiPrfMk S b fsE inpE ρ fs inp _ hfsE hinpE hSh hOld hCap ?_
  rcases inp with ⟨rk, dh⟩
  simp only [roRootFixedB, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.rootRoC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseOptV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eFind,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext.wk, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bytesBeq,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bytes2Eq, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aNone,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aRootKdf, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.aRootKdf,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stUpd, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stMk,
    fhstSetBase, ahsfUpd, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsUpd, ahsMk, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, samplePrim, liftPrimComp, _root_.ReductionDsl.AtomicPureOp.eval,
    embedVar, mapComp, mapExpr, mapOpExpr, mapSampCast, mapSampH, castLegacySamp, Comp.eval, Expr.eval, Env.get,
    Expr.v0, atomRootRoCache, pure_bind, aRootKdfAtomicE, fixedSetRootRoCacheE, liftExpr1_eval, liftExpr2_eval]
  cases fs.1.1.1.2.1
  · simp only [Bool.false_eq_true, ↓reduceIte]; split <;> (next h => simp only [h]; try rfl)
  · rfl

/-- Step simulation for `.roQuery` on `authFixedShadowStTy` over `aiPrfHmac`. -/
theorem roFixedShadowArmC_sim_hmac (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    {Γ : List (Ty pqAtomicSig)} (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) (ρ : Env Γ)
    (fs : authFixedShadowStTy.denote) (sec : (PB 192).denote)
    (hfsE : fsE.eval ρ = fs) (hsecE : secE.eval ρ = sec)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hOld : nRo + 1 ≤ b.q_total) (hCap : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap) :
    let arm := roFixedShadowArmC aiPrfHmac (AuthKindFuels.ofBudget S b).K_cap fsE secE
    let leg := mapComp tlPrfHmac (liftPrimComp (C := hmacPrfOracle)
      (roFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, B 192]) (Γ₂ := [B 192])
        (Δ := [authHybridStateFixedTy, B 192]) .zero .zero))
    Prod.map id forgetAuthFixedShadow <$> arm.eval ρ = leg.eval (.cons fs.1 (.cons sec .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthFixedShadowAt S b nOn (nRo + 1) nRoot p.2 := by
  refine roFixedShadowArmC_sim_gen aiPrfHmac S b fsE secE ρ fs sec _ hfsE hsecE hSh hOld hCap ?_
  simp only [roFixedB, hkdfRoC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseOptV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eFind, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext.wk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bytesBeq, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aNone,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aDrKey, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.aDrKey,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stUpd, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stMk,
    fhstSetBase, ahsfUpd, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsUpd, ahsMk, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, samplePrim, liftPrimComp, _root_.ReductionDsl.AtomicPureOp.eval,
    embedVar, mapComp, mapExpr, mapOpExpr, mapSampCast, mapSampH, castLegacySamp, Comp.eval, Expr.eval, Env.get,
    Expr.v0, atomRoCache, pure_bind, aDrKeyAtomicE, fixedSetRoCacheE, liftExpr1_eval, liftExpr2_eval]
  cases fs.1.1.1.2.1
  · simp only [Bool.false_eq_true, ↓reduceIte]; split <;> (next h => simp only [h]; try rfl)
  · rfl

/-- Step simulation for `.roRootQuery` on `authFixedShadowStTy` over `aiPrfHmac`. -/
theorem roRootFixedShadowArmC_sim_hmac (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    {Γ : List (Ty pqAtomicSig)} (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) (ρ : Env Γ)
    (fs : authFixedShadowStTy.denote) (inp : ((PB 32).prod (PB 32)).denote)
    (hfsE : fsE.eval ρ = fs) (hinpE : inpE.eval ρ = inp)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hOld : nRoot + 1 ≤ b.q_total) (hCap : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap) :
    let B32 := B 32
    let arm := roRootFixedShadowArmC aiPrfHmac (AuthKindFuels.ofBudget S b).K_cap fsE inpE
    let leg := mapComp tlPrfHmac (liftPrimComp (C := hmacPrfOracle)
      (roRootFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .prod B32 B32]) (Γ₂ := [.prod B32 B32])
        (Δ := [authHybridStateFixedTy, .prod B32 B32]) .zero .zero))
    Prod.map id forgetAuthFixedShadow <$> arm.eval ρ = leg.eval (.cons fs.1 (.cons inp .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthFixedShadowAt S b nOn nRo (nRoot + 1) p.2 := by
  refine roRootFixedShadowArmC_sim_gen aiPrfHmac S b fsE inpE ρ fs inp _ hfsE hinpE hSh hOld hCap ?_
  rcases inp with ⟨rk, dh⟩
  simp only [roRootFixedB, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.rootRoC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseOptV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eFind,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext.wk, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bytesBeq,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bytes2Eq, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aNone,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aRootKdf, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.aRootKdf,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stUpd, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stMk,
    fhstSetBase, ahsfUpd, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsUpd, ahsMk, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, samplePrim, liftPrimComp, _root_.ReductionDsl.AtomicPureOp.eval,
    embedVar, mapComp, mapExpr, mapOpExpr, mapSampCast, mapSampH, castLegacySamp, Comp.eval, Expr.eval, Env.get,
    Expr.v0, atomRootRoCache, pure_bind, aRootKdfAtomicE, fixedSetRootRoCacheE, liftExpr1_eval, liftExpr2_eval]
  cases fs.1.1.1.2.1
  · simp only [Bool.false_eq_true, ↓reduceIte]; split <;> (next h => simp only [h]; try rfl)
  · rfl

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo
