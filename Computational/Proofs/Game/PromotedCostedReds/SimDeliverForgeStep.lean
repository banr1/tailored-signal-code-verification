/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorr
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwd
public import Computational.Proofs.ReductionDsl.Ratchet.LibsignalSimDF

/-!
# Atomic Step Program for `SimDeliverForge`

Packages the single-query atomic step computation matching `simDeliverForgeOracleSanQ`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStep

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ops Iface Ty Expr Comp Env Var liftRen handlerImpl bits atomicSig
  atomicSessionOps fig8SmIfaceDF e2eSessionCodec GhostStT PlainT BV512 B smQT smRT smQenc smRdec
  recvResultT recvResultDec smRrDec partyToBool fig8CtT fig8CtOfV)
open _root_.CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (partyEnc)
open CryptoGames.Ratchet.LibsignalSim (Fig8C SimCStateBounded deliverForgeSemHook)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (semHandleHookDedupS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SanSnapExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost (simFullT simFullDec)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSortDescBits atomicTyDescBits varIdx atomicSessionOpDescBits
   atomicExprDescBits atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepSendCorr
  (simDeliverForgeSendCorrSpec)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdCost (dfRecvOutDec)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwd
  (dfRecvHookC dfRecvHookC_queries dfRecvHookC_cost dfRecvHookC_descBits_le dfRecvHookC_eval)

noncomputable section

@[reducible] def dfStepT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt) (.list (fig8CtT (ℓ := ℓ) (Pt := Pt)))

@[reducible] def dfStepDec {ℓ : ℕ} {Pt : Type} (v : (dfStepT ℓ Pt).denote) :
    LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt) :=
  (simFullDec v.1, v.2.map fig8CtOfV)

/-- Specification record for the single-query `SimDeliverForge` step computation matching
`simDeliverForgeOracleSanQ`. -/
structure SimDeliverForgeRawStepSpec (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) where
  step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
    [dfStepT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
    (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfStepT ℓ Pt))
  hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1
  hstep_c : ℓ < 10 ^ 6 →
    step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1)
  hstep_d : ℓ < 10 ^ 6 →
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
      2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))
  hstep : ℓ < 10 ^ 6 → ∀ t (s_raw : (dfStepT ℓ Pt).denote),
    SimCStateBounded q (dfStepDec s_raw).1 →
    (dfStepDec s_raw).2.length ≤ q →
    SanSnapExtra C K (dfStepDec s_raw).1 →
    (Prod.map id dfStepDec <$>
      ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
    semHandleHookDedupS (paramsV1 C K idA idB) Dh encPt encT decT lam
      (50000 * q) (25001 * q + 25000) (25000 * q)
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
      qep (2 ^ 32) t (dfStepDec s_raw).1 (dfStepDec s_raw).2

private theorem varIdx_liftRen {S : Sig} {Γ Δ : List (Ty S)} {a : Ty S}
    (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u)
    (hξ : ∀ ⦃u⦄ (v : Var Γ u), varIdx (ξ v) = varIdx v) :
    ∀ ⦃u⦄ (v : Var (a :: Γ) u), varIdx (liftRen ξ v) = varIdx v
  | _, .zero => rfl
  | _, .succ v => congrArg (· + 1) (hξ v)

private theorem atomicExprDescBits_renameM {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}
    (opBits : O.Op → ℕ) {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (e : Expr O Γ t) :
    ∀ {Δ : List (Ty (atomicSig ℓ Pt))} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u),
      (∀ ⦃u⦄ (v : Var Γ u), varIdx (ξ v) = varIdx v) →
      atomicExprDescBits opBits (Expr.renameM ξ e) = atomicExprDescBits opBits e := by
  induction e with
  | var v => intro Δ ξ hξ; simp [Expr.renameM, atomicExprDescBits, hξ v]
  | unit | bool _ | nat _ | none | nil => intro _ _ _; rfl
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2
  | and _ _ ih1 ih2 | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2
  | tget _ _ ih1 ih2 | appendL _ _ _ ih1 ih2 =>
    intro Δ ξ hξ; simp [Expr.renameM, atomicExprDescBits, ih1 ξ hξ, ih2 ξ hξ]
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | some _ ih | len _ ih | tconst _ ih | inl _ ih | inr _ ih | op _ _ ih =>
    intro Δ ξ hξ; simp [Expr.renameM, atomicExprDescBits, ih ξ hξ]
  | ite _ _ _ ih1 ih2 ih3 | tset _ _ _ ih1 ih2 ih3 =>
    intro Δ ξ hξ; simp [Expr.renameM, atomicExprDescBits, ih1 ξ hξ, ih2 ξ hξ, ih3 ξ hξ]
  | caseOpt _ _ _ ih1 ih2 ih3 =>
    intro Δ ξ hξ
    simp [Expr.renameM, atomicExprDescBits, ih1 ξ hξ, ih2 ξ hξ,
      ih3 (liftRen ξ) (varIdx_liftRen ξ hξ)]
  | caseSum _ _ _ ih1 ih2 ih3 =>
    intro Δ ξ hξ
    simp [Expr.renameM, atomicExprDescBits, ih1 ξ hξ,
      ih2 (liftRen ξ) (varIdx_liftRen ξ hξ), ih3 (liftRen ξ) (varIdx_liftRen ξ hξ)]
  | letE _ _ ih1 ih2 | findB _ _ _ ih1 ih2 | anyB _ _ _ ih1 ih2 | mapB _ _ _ ih1 ih2 =>
    intro Δ ξ hξ
    simp [Expr.renameM, atomicExprDescBits, ih1 ξ hξ, ih2 (liftRen ξ) (varIdx_liftRen ξ hξ)]
  | foldrB _ _ _ _ ih1 ih2 ih3 =>
    intro Δ ξ hξ
    simp [Expr.renameM, atomicExprDescBits, ih1 ξ hξ, ih2 ξ hξ,
      ih3 (liftRen (liftRen ξ)) (varIdx_liftRen _ (varIdx_liftRen ξ hξ))]

private theorem atomicCompDescBits_renameM {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}
    {ι : Type} {T : OracleSpec ι} {I : Iface (atomicSig ℓ Pt) T}
    (opBits : O.Op → ℕ) (sBits : I.smp.Samp → ℕ) (qBits : I.Tag → ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)} (c : Comp O I Γ t) :
    ∀ {Δ : List (Ty (atomicSig ℓ Pt))} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u),
      (∀ ⦃u⦄ (v : Var Γ u), varIdx (ξ v) = varIdx v) →
      atomicCompDescBits opBits sBits qBits (Comp.renameM ξ c) =
        atomicCompDescBits opBits sBits qBits c := by
  induction c with
  | ret e =>
    intro Δ ξ hξ; simp [Comp.renameM, atomicCompDescBits, atomicExprDescBits_renameM opBits e ξ hξ]
  | bind _ _ ih1 ih2 =>
    intro Δ ξ hξ
    simp [Comp.renameM, atomicCompDescBits, ih1 ξ hξ, ih2 (liftRen ξ) (varIdx_liftRen ξ hξ)]
  | ite b _ _ ih1 ih2 =>
    intro Δ ξ hξ
    simp [Comp.renameM, atomicCompDescBits, atomicExprDescBits_renameM opBits b ξ hξ,
      ih1 ξ hξ, ih2 ξ hξ]
  | caseOpt e _ _ ih1 ih2 =>
    intro Δ ξ hξ
    simp [Comp.renameM, atomicCompDescBits, atomicExprDescBits_renameM opBits e ξ hξ,
      ih1 ξ hξ, ih2 (liftRen ξ) (varIdx_liftRen ξ hξ)]
  | caseSum e _ _ ih1 ih2 =>
    intro Δ ξ hξ
    simp [Comp.renameM, atomicCompDescBits, atomicExprDescBits_renameM opBits e ξ hξ,
      ih1 (liftRen ξ) (varIdx_liftRen ξ hξ), ih2 (liftRen ξ) (varIdx_liftRen ξ hξ)]
  | sample _ e | query _ e =>
    intro Δ ξ hξ
    simp [Comp.renameM, atomicCompDescBits, atomicExprDescBits_renameM opBits e ξ hξ]
  | iter _ e _ ih | findM _ e _ ih | anyM _ e _ ih | mapM _ e _ ih =>
    intro Δ ξ hξ
    simp [Comp.renameM, atomicCompDescBits, atomicExprDescBits_renameM opBits e ξ hξ,
      ih (liftRen ξ) (varIdx_liftRen ξ hξ)]
  | consumeFirstM _ l _ mk ih =>
    intro Δ ξ hξ
    simp [Comp.renameM, atomicCompDescBits, atomicExprDescBits_renameM opBits l ξ hξ,
      ih (liftRen ξ) (varIdx_liftRen ξ hξ),
      atomicExprDescBits_renameM opBits mk (liftRen ξ) (varIdx_liftRen ξ hξ)]
  | foldM _ l z _ ih =>
    intro Δ ξ hξ
    simp [Comp.renameM, atomicCompDescBits, atomicExprDescBits_renameM opBits l ξ hξ,
      atomicExprDescBits_renameM opBits z ξ hξ,
      ih (liftRen (liftRen ξ)) (varIdx_liftRen _ (varIdx_liftRen ξ hξ))]

@[reducible] private def wkTop1Comp {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {a t : Ty S} (c : Comp O I [a] t) : Comp O I (a :: Γ) t :=
  Comp.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ w => nomatch w) c

private theorem atomicCompDescBits_wkTop1 {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}
    {ι : Type} {T : OracleSpec ι} {I : Iface (atomicSig ℓ Pt) T}
    (opBits : O.Op → ℕ) (sBits : I.smp.Samp → ℕ) (qBits : I.Tag → ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))} {a t : Ty (atomicSig ℓ Pt)} (c : Comp O I [a] t) :
    atomicCompDescBits opBits sBits qBits (wkTop1Comp (Γ := Γ) c) =
      atomicCompDescBits opBits sBits qBits c :=
  atomicCompDescBits_renameM opBits sBits qBits c _ fun ⦃_⦄ v => by
    cases v with
    | zero => rfl
    | succ w => nomatch w

private def smRRecvPackE {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (rrE : Expr O Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt)))) :
    Expr O Γ (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) :=
  .pair .none (.pair rrE .none)

private theorem bits_c0 : bits 0 = 1 := by decide
private theorem bits_c1 : bits 1 = 1 := by decide
private theorem bits_c2 : bits 2 = 2 := by decide

private abbrev dfSendArgT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512)))

private abbrev dfRecvArgT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .bool (.prod (B 32) .bool)

private abbrev dfClassT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .sum (dfSendArgT ℓ Pt) (.sum (dfRecvArgT ℓ Pt) .bool)

private def classifySmQE {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (qE : Expr O Γ (smQT (ℓ := ℓ) (Pt := Pt))) :
    Expr O Γ (dfClassT ℓ Pt) :=
  .caseSum qE
    (.inl (.pair (.fst (.var .zero))
      (.pair (.fst (.snd (.var .zero)))
        (.pair .none (.snd (.snd (.var .zero)))))))
    (.caseSum (.var .zero)
      (.inl (.pair (.fst (.var .zero))
        (.pair (.fst (.snd (.var .zero)))
          (.pair (.some (.fst (.snd (.snd (.var .zero)))))
            (.snd (.snd (.snd (.var .zero))))))))
      (.caseSum (.var .zero)
        (.inr (.inl (.pair (.fst (.var .zero)) (.pair (.snd (.var .zero)) (.bool true)))))
        (.caseSum (.var .zero)
          (.inr (.inl (.pair (.fst (.var .zero)) (.pair (.snd (.var .zero)) (.bool false)))))
          (.inr (.inr (.var .zero))))))

private def dfStepC {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfStepT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfStepT ℓ Pt)) :=
  let sc := simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q
  .caseSum (classifySmQE (.var (.succ .zero)))
    (sc.sendC (.var (.succ .zero))
      (.fst (.var .zero))
      (.fst (.snd (.var .zero)))
      (.fst (.snd (.snd (.var .zero))))
      (.snd (.snd (.snd (.var .zero)))))
    (.caseSum (.var .zero)
      (.bind (.bind (.ret (.pair (.var (.succ (.succ .zero))) (.var .zero)))
          (wkTop1Comp (dfRecvHookC C K idA idB Dh encPt encT decT lam qep q)))
        (.ret (.pair (smRRecvPackE (.fst (.var .zero))) (.snd (.var .zero)))))
      (sc.corrC (.var (.succ (.succ .zero))) (.var .zero)))

private theorem dfStepC_queries {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    (dfStepC ℓ C K idA idB Dh encPt encT decT lam qep q).queries (fun _ => 1) (fun _ => 0) ≤ 1 := by
  let Γs : List (Ty (atomicSig ℓ Pt)) := [dfSendArgT ℓ Pt, dfStepT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γc : List (Ty (atomicSig ℓ Pt)) :=
    [.bool, .sum (dfRecvArgT ℓ Pt) .bool, dfStepT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  have hs := (simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q).hsend_q
    (Γ := Γs) (.var (.succ .zero)) (.fst (.var .zero))
    (.fst (.snd (.var .zero))) (.fst (.snd (.snd (.var .zero)))) (.snd (.snd (.snd (.var .zero))))
  have hr :
      Comp.queries (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (I := fig8SmIfaceDF ℓ Pt)
        (fun _ => 1) (fun _ => 0)
        (dfRecvHookC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q) ≤ 1 :=
    dfRecvHookC_queries (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q
  have hc := (simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q).hcorr_q
    (Γ := Γc) (.var (.succ (.succ .zero))) (.var .zero)
  simp only [dfStepC, wkTop1Comp, Comp.queries, Comp.renameM_queries] at hs hr hc ⊢
  omega

private theorem dfStepC_cost {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) :
    (dfStepC ℓ C K idA idB Dh encPt encT decT lam qep q).cost ≤
      199000000 + 100000000 * q + 4096 * bits (qep + 1) := by
  let Γs : List (Ty (atomicSig ℓ Pt)) := [dfSendArgT ℓ Pt, dfStepT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γc : List (Ty (atomicSig ℓ Pt)) :=
    [.bool, .sum (dfRecvArgT ℓ Pt) .bool, dfStepT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  have hs := (simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q).hsend_c hℓ
    (Γ := Γs) (.var (.succ .zero)) (.fst (.var .zero))
    (.fst (.snd (.var .zero))) (.fst (.snd (.snd (.var .zero)))) (.snd (.snd (.snd (.var .zero))))
  have hr :
      Comp.cost (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (I := fig8SmIfaceDF ℓ Pt)
        (dfRecvHookC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q) ≤
        185000000 + 40000000 * q + 512 * bits (qep + 1) :=
    dfRecvHookC_cost (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q hℓ
  have hc := (simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q).hcorr_c hℓ
    (Γ := Γc) (.var (.succ (.succ .zero))) (.var .zero)
  simp only [dfStepC, classifySmQE, smRRecvPackE, wkTop1Comp, Comp.cost, Expr.cost,
    Comp.renameM_cost] at hs hc ⊢
  omega

private theorem dfStepC_descBits_le {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (dfStepC ℓ C K idA idB Dh encPt encT decT lam qep q) ≤
      2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  let Γs : List (Ty (atomicSig ℓ Pt)) := [dfSendArgT ℓ Pt, dfStepT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γc : List (Ty (atomicSig ℓ Pt)) :=
    [.bool, .sum (dfRecvArgT ℓ Pt) .bool, dfStepT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  have hs := (simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q).hsend_d hℓ
    (Γ := Γs) (.var (.succ .zero)) (.fst (.var .zero))
    (.fst (.snd (.var .zero))) (.fst (.snd (.snd (.var .zero)))) (.snd (.snd (.snd (.var .zero))))
  have hr :
      atomicCompDescBits (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (I := fig8SmIfaceDF ℓ Pt) atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (dfRecvHookC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q) ≤
        (2 ^ 20 + 2 ^ 18) + (2 ^ 12 + 2 ^ 10) * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) :=
    dfRecvHookC_descBits_le (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q hℓ
  have hc := (simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q).hcorr_d hℓ
    (Γ := Γc) (.var (.succ (.succ .zero))) (.var .zero)
  simp only [dfStepC, classifySmQE, dfClassT, dfSendArgT, dfRecvArgT, smRRecvPackE,
    PlainT, BV512, B, GhostStT, recvResultT,
    atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    varIdx, Nat.reduceAdd, bits_c0, bits_c1, bits_c2,
    atomicCompDescBits_wkTop1] at hs hr hc ⊢
  have hp32 : bits (32 : ℕ+) = 6 := by decide
  omega

private theorem partyToBool_eq_partyEnc_local (Q : Party) :
    partyToBool Q = partyEnc Q := by
  cases Q <;> rfl

private theorem recvResultDec_eq_smRrDec_id {ℓ : ℕ} {Pt : Type}
    (v : (recvResultT (ℓ := ℓ) (Pt := Pt)).denote) :
    recvResultDec v = smRrDec id v := by
  rcases v with ⟨⟩ | ⟨t, i, _ | m⟩ <;> rfl

private theorem wkTop1Comp_eval {S : Sig} {O : Ops S}
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a t : Ty S} (c : Comp O I [a] t) (x : a.denote) (ρ : Env Γ) :
    (wkTop1Comp c).eval (.cons x ρ) = c.eval (.cons x .nil) :=
  Comp.renameM_eval c fun ⦃_⦄ v => by cases v with | zero => rfl | succ w => nomatch w

private theorem dfStepC_eval {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (t : (CryptoGames.SM.spec (CryptoGames.LibsignalSession.GhostState Bytes)
      (Plain ℓ) (BitVec 512) Bytes).Domain)
    (s_raw : (dfStepT ℓ Pt).denote)
    (hbnd : SimCStateBounded q (dfStepDec s_raw).1)
    (hex : (dfStepDec s_raw).2.length ≤ q)
    (hextra : SanSnapExtra C K (dfStepDec s_raw).1) :
    (Prod.map id dfStepDec <$>
      ((handlerImpl (C := e2eSessionCodec ℓ Pt)
        (dfStepC ℓ C K idA idB Dh encPt encT decT lam qep q) (.inr t)).run s_raw)) =
    semHandleHookDedupS (paramsV1 C K idA idB) Dh encPt encT decT lam
      (50000 * q) (25001 * q + 25000) (25000 * q)
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
      qep (2 ^ 32) t (dfStepDec s_raw).1 (dfStepDec s_raw).2 := by
  let Γs : List (Ty (atomicSig ℓ Pt)) := [dfSendArgT ℓ Pt, dfStepT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γc : List (Ty (atomicSig ℓ Pt)) :=
    [.bool, .sum (dfRecvArgT ℓ Pt) .bool, dfStepT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  have hfunRecv :
      (fun (out : (SimDeliverForgeStepRecvFwdCost.dfRecvOutT ℓ Pt).denote) =>
        (Option.map recvResultDec out.1, dfStepDec out.2)) = dfRecvOutDec := by
    funext out
    rcases out with ⟨_ | v, st⟩
    · rfl
    · exact Prod.ext (congrArg some (recvResultDec_eq_smRrDec_id v)) rfl
  rcases t with (((⟨Q, m, r⟩ | ⟨Q, m0, m1, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
  · simp only [StateT.run, StateT.mk, handlerImpl, e2eSessionCodec, smQenc, dfStepC, classifySmQE,
      Comp.eval, Expr.eval, Env.get, bind_pure_comp, Functor.map_map, smRdec,
      semHandleHookDedupS]
    let ρs : Env Γs :=
      .cons (partyToBool Q, (m, (none, r)))
        (.cons s_raw (.cons (t := smQT (ℓ := ℓ) (Pt := Pt)) (.inl (partyToBool Q, (m, r))) .nil))
    exact (simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q).hsend_eval hℓ
      (Γ := Γs) (.var (.succ .zero)) (.fst (.var .zero))
      (.fst (.snd (.var .zero))) (.fst (.snd (.snd (.var .zero)))) (.snd (.snd (.snd (.var .zero))))
      ρs Q (partyToBool_eq_partyEnc_local Q) hbnd hextra
  · simp only [StateT.run, StateT.mk, handlerImpl, e2eSessionCodec, smQenc, dfStepC, classifySmQE,
      Comp.eval, Expr.eval, Env.get, bind_pure_comp, Functor.map_map, smRdec,
      semHandleHookDedupS]
    let ρs : Env Γs :=
      .cons (partyToBool Q, (m0, (some m1, r)))
        (.cons s_raw
          (.cons (t := smQT (ℓ := ℓ) (Pt := Pt)) (.inr (.inl (partyToBool Q, (m0, (m1, r))))) .nil))
    exact (simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q).hsend_eval hℓ
      (Γ := Γs) (.var (.succ .zero)) (.fst (.var .zero))
      (.fst (.snd (.var .zero))) (.fst (.snd (.snd (.var .zero)))) (.snd (.snd (.snd (.var .zero))))
      ρs Q (partyToBool_eq_partyEnc_local Q) hbnd hextra
  · simp only [StateT.run, StateT.mk, handlerImpl, e2eSessionCodec, smQenc, dfStepC, classifySmQE,
      smRRecvPackE, Comp.eval, Expr.eval, Env.get, pure_bind, wkTop1Comp_eval, bind_pure_comp,
      Functor.map_map, smRdec, partyToBool_eq_partyEnc_local]
    change (fun (out : (SimDeliverForgeStepRecvFwdCost.dfRecvOutT ℓ Pt).denote) =>
      (Option.map recvResultDec out.1, dfStepDec out.2)) <$> _ = _
    rw [hfunRecv, dfRecvHookC_eval C K idA idB Dh encPt encT decT lam qep q hℓ
      s_raw Q w true hbnd hex hextra]
    simp [semHandleHookDedupS, deliverForgeSemHook]
  · simp only [StateT.run, StateT.mk, handlerImpl, e2eSessionCodec, smQenc, dfStepC, classifySmQE,
      smRRecvPackE, Comp.eval, Expr.eval, Env.get, pure_bind, wkTop1Comp_eval, bind_pure_comp,
      Functor.map_map, smRdec, partyToBool_eq_partyEnc_local, semHandleHookDedupS]
    change (fun (out : (SimDeliverForgeStepRecvFwdCost.dfRecvOutT ℓ Pt).denote) =>
      (Option.map recvResultDec out.1, dfStepDec out.2)) <$> _ = _
    exact (congrArg (· <$> _) hfunRecv).trans
      (dfRecvHookC_eval C K idA idB Dh encPt encT decT lam qep q hℓ
        s_raw Q w false hbnd hex hextra)
  · have hfunCorr :
        (fun (r : ((smRT (ℓ := ℓ) (Pt := Pt) GhostStT).prod (dfStepT ℓ Pt)).denote) =>
          (Option.map id r.1.2.2, dfStepDec r.2)) =
        Prod.map (fun r => r.2.2) dfStepDec := by
      funext r; simp [Prod.map]
    simp only [StateT.run, StateT.mk, handlerImpl, e2eSessionCodec, smQenc, dfStepC, classifySmQE,
      Comp.eval, Expr.eval, Env.get, bind_pure_comp, Functor.map_map, smRdec,
      semHandleHookDedupS]
    let ρc : Env Γc :=
      .cons (partyToBool Q)
        (.cons (t := .sum (dfRecvArgT ℓ Pt) .bool) (.inr (partyToBool Q))
          (.cons s_raw
            (.cons (t := smQT (ℓ := ℓ) (Pt := Pt)) (.inr (.inr (.inr (.inr (partyToBool Q))))) .nil)))
    change (fun (r : ((smRT (ℓ := ℓ) (Pt := Pt) GhostStT).prod (dfStepT ℓ Pt)).denote) =>
      (Option.map id r.1.2.2, dfStepDec r.2)) <$> _ = _
    rw [hfunCorr]
    exact (simDeliverForgeSendCorrSpec ℓ C K idA idB Dh encPt encT decT lam qep q).hcorr_eval hℓ
      (Γ := Γc) (.var (.succ (.succ .zero))) (.var .zero)
      ρc Q (partyToBool_eq_partyEnc_local Q) hbnd hextra

theorem simDeliverForgeRawStepSpec_nonempty
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    Nonempty (SimDeliverForgeRawStepSpec Pt ℓ C K idA idB Dh encPt encT decT lam qep q) :=
  ⟨{ step := dfStepC ℓ C K idA idB Dh encPt encT decT lam qep q
     hstep_q := dfStepC_queries ℓ C K idA idB Dh encPt encT decT lam qep q
     hstep_c := dfStepC_cost ℓ C K idA idB Dh encPt encT decT lam qep q
     hstep_d := dfStepC_descBits_le ℓ C K idA idB Dh encPt encT decT lam qep q
     hstep := dfStepC_eval ℓ C K idA idB Dh encPt encT decT lam qep q }⟩

def simDeliverForgeRawStepSpec
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    SimDeliverForgeRawStepSpec Pt ℓ C K idA idB Dh encPt encT decT lam qep q :=
  Classical.choice (simDeliverForgeRawStepSpec_nonempty ℓ C K idA idB Dh encPt encT decT lam qep q)

end

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStep
