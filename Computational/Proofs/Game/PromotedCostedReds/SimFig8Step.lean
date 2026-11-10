/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepSend
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepCorr
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSame
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewCost
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNew

/-!
# Concrete Atomic Step Program for `simFig8`

Packages the single-query atomic step computation matching `simFig8OracleSan`
at `(L, B, T, Kc, Bsk) = (q, 2 ^ 32 + q + 2, 50000 * q, 25001 * q + 25000, 25000 * q)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8Step

open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp liftRen handlerImpl bits
  atomicSig atomicSessionOps fig8SmIface e2eSessionCodec GhostStT smQT smRT smQenc smRdec
  PlainT B partyToBool boolToParty recvResultT recvResultDec
  fig8CtT fig8CtV fig8CtOfV fig8StT fig8StV fig8StOfV fsSendStV fsSendStOfV)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (partyEnc partyDec posTy posEnc posDec)
open CryptoGames.Ratchet.LibsignalSim (SimCStateBounded)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.ReductionDsl.Fig8Atomic (salt32V_salt32OfV)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (semRecvHookS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle (simFig8OracleSan)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SanSnapExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State (rename_descBits_eq bits_eq_of_bounds)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simRecT simRecEnc simRecDec simMirT simMirEnc simMirDec
   honestPairEnc honestPairDec ghostChainEnc ghostChainDec
   simBaseT simBaseEnc simBaseDec keptT keptEnc keptDec
   sentEntryEnc sentEntryDec snapEnc snapDec simFullT simFullEnc simFullDec fig8IdSemHook)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (varIdx atomicSessionOpDescBits atomicSortDescBits atomicTyDescBits
   atomicExprDescBits atomicCompDescBits
   bits_two_mul_add_two_le_ratchetCostBudget)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepSend (simFig8SendStepSpec)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepCorr
  (simFig8StepCorrC simFig8StepCorrC_queries simFig8StepCorrC_cost
   simFig8StepCorrC_descBits_le simFig8StepCorrC_run)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSame
  (semRecvSameBranch simFig8FwdHookSpec simFig8RecvSameSpec)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewCost
  (recvOutT recvHookInpT wkTop1Comp callSub1C recvHookOfBranchesC
   recvHookOfBranchesC_queries recvHookOfBranchesC_cost recvHookOfBranchesC_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewSkip (callSub1C_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNew
  (simFig8RecvNewSpec_of_fwd recvHookOfBranchesC_eval
   simFig8OracleSan_deliver_eq simFig8OracleSan_inject_eq)

noncomputable section

section Helpers

variable {ℓ : ℕ} {Pt : Type}

private theorem fig8CtV_fig8CtOfV (v : (fig8CtT (ℓ := ℓ) (Pt := Pt)).denote) :
    fig8CtV (ℓ := ℓ) (Pt := Pt) (fig8CtOfV v) = v := by
  rcases v with ⟨h, n, ws, sv⟩
  simp [fig8CtV, fig8CtOfV, _root_.ReductionDsl.lctV, _root_.ReductionDsl.lctOfV,
    _root_.ReductionDsl.wireSaltCtV, _root_.ReductionDsl.wireSaltCtOfV, salt32V_salt32OfV]

private theorem fig8StV_fig8StOfV (v : (fig8StT (ℓ := ℓ) (Pt := Pt)).denote) :
    fig8StV (ℓ := ℓ) (Pt := Pt) (fig8StOfV v) = v := by
  rcases v with ⟨p, rk, vs?, vrTbl, γv, cur?, tc⟩
  simp only [fig8StV, fig8StOfV]
  have hp : partyToBool (boolToParty p) = p := by cases p <;> rfl
  have hvs : (vs?.map (_root_.ReductionDsl.fsSendStOfV (ℓ := ℓ) (Pt := Pt))).map
      _root_.ReductionDsl.fsSendStV = vs? := by
    rcases vs? with _ | ⟨ck, li⟩ <;> rfl
  have hvr : (fun t => ((vrTbl t).map (_root_.ReductionDsl.fsRecvStOfV (ℓ := ℓ) (Pt := Pt))).map
      _root_.ReductionDsl.fsRecvStV) = vrTbl := by
    funext t; rcases vrTbl t with _ | ⟨ck, li, sk⟩ <;> rfl
  have hγ : _root_.ReductionDsl.ckaStV (ℓ := ℓ) (Pt := Pt) (_root_.ReductionDsl.ckaStOfV γv) = γv := by
    rcases γv with h | x <;> rfl
  rw [hp, hvs, hvr, hγ]

private theorem simMirEnc_simMirDec (v : (simMirT ℓ Pt).denote) :
    simMirEnc (Pt := Pt) (simMirDec v) = v := by
  rcases v with ⟨b, win, ⟨epA, epB⟩, ⟨idA, idB⟩, tL, trs, chall, comp, ⟨maA, maB⟩, leaks, corrs⟩
  simp only [simMirEnc, simMirDec, List.map_map]
  have htr : (simRecEnc (Pt := Pt) ∘ simRecDec :
      (simRecT ℓ Pt).denote → (simRecT ℓ Pt).denote) = id := by funext ⟨⟨p, _, _⟩, _, _⟩; cases p <;> rfl
  have hpos : (posEnc ∘ posDec : (posTy (S' := atomicSig ℓ Pt)).denote → _) = id := by
    funext ⟨p, _, _⟩; cases p <;> rfl
  have hcor : ((fun pe : Party × ℕ => (partyEnc pe.1, pe.2)) ∘
      (fun pe : Bool × ℕ => (partyDec pe.1, pe.2))) = id := by funext ⟨p, _⟩; cases p <;> rfl
  simp only [htr, hpos, hcor, List.map_id]

private theorem simBaseEnc_simBaseDec (v : (simBaseT ℓ Pt).denote) :
    simBaseEnc (simBaseDec v) = v := by
  rcases v with ⟨mir, ⟨pqA, pqB⟩, ⟨pnA, pnB⟩, unackA, honest, ⟨chA, chB⟩, amb, stopped⟩
  simp only [simBaseEnc, simBaseDec, simMirEnc_simMirDec, List.map_map]
  have hhon : (honestPairEnc (ℓ := ℓ) (Pt := Pt) ∘ honestPairDec) = id := by
    funext ⟨w, cv⟩; simp [honestPairEnc, honestPairDec, fig8CtV_fig8CtOfV]
  have hgc : (ghostChainEnc (ℓ := ℓ) (Pt := Pt) ∘ ghostChainDec) = id := by
    funext ⟨k, ep, la, sk⟩; rfl
  simp only [hhon, hgc, List.map_id]

private theorem keptEnc_keptDec (v : (keptT ℓ Pt).denote) :
    keptEnc (ℓ := ℓ) (Pt := Pt) (keptDec v) = v := by
  rcases v with ⟨full?, rsTbl⟩
  simp only [keptEnc, keptDec]
  congr 1
  · rcases full? with _ | stv
    · rfl
    · exact congrArg some (fig8StV_fig8StOfV stv)
  · funext t; rcases rsTbl t with _ | ⟨ck, li, sk⟩ <;> rfl

private theorem simFullEnc_simFullDec (v : (simFullT ℓ Pt).denote) :
    simFullEnc (simFullDec v) = v := by
  rcases v with ⟨base, ⟨kA, kB⟩, sent, snaps⟩
  simp only [simFullEnc, simFullDec, simBaseEnc_simBaseDec, keptEnc_keptDec, List.map_map]
  have hse : (sentEntryEnc (ℓ := ℓ) (Pt := Pt) ∘ sentEntryDec) = id := by
    funext ⟨cv, ⟨ck, li⟩⟩
    simp [sentEntryEnc, sentEntryDec, fig8CtV_fig8CtOfV, fsSendStV, fsSendStOfV]
  have hsn : (snapEnc (ℓ := ℓ) (Pt := Pt) ∘ snapDec) = id := by
    funext ⟨p, ep, g⟩; cases p <;> rfl
  simp only [hse, hsn, List.map_id]

private theorem sb_c0 : bits 0 = 1 := rfl
private theorem sb_c1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem sb_c32 : bits 32 = 6 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem sb_p32 : bits ((32 : ℕ+) : ℕ) = 6 := sb_c32

private theorem bits_mono_le {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem liftRen_varIdx {S : Sig} {Γ₁ Γ₂ : List (Ty S)} {a : Ty S}
    {ξ : ∀ ⦃u⦄, Var Γ₁ u → Var Γ₂ u}
    (hξ : ∀ u (v : Var Γ₁ u), varIdx (ξ v) = varIdx v) :
    ∀ u (v : Var (a :: Γ₁) u), varIdx (liftRen ξ v) = varIdx v
  | _, .zero => rfl
  | _, .succ w => by simp only [liftRen, varIdx, hξ _ w]

private theorem comp_renameM_descBits_eq {ℓ : ℕ} {Pt : Type} {O' : Ops (atomicSig ℓ Pt)}
    {ι : Type} {T : OracleSpec ι} {I' : Iface (atomicSig ℓ Pt) T}
    (opB : O'.Op → ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ₁ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)} (c : Comp O' I' Γ₁ t) :
    ∀ {Γ₂ : List (Ty (atomicSig ℓ Pt))} (ξ : ∀ ⦃u⦄, Var Γ₁ u → Var Γ₂ u),
      (∀ u (v : Var Γ₁ u), varIdx (ξ v) = varIdx v) →
      atomicCompDescBits opB sB qB (Comp.renameM ξ c) =
        atomicCompDescBits opB sB qB c := by
  induction c with
  | ret e =>
    intro Γ₂ ξ hξ; simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ]
  | bind c k ihc ihk =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, ihc ξ hξ, ihk (liftRen ξ) (liftRen_varIdx hξ)]
  | ite b c d ihc ihd =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ, ihc ξ hξ, ihd ξ hξ]
  | caseOpt e n s ihn ihs =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ,
      ihn ξ hξ, ihs (liftRen ξ) (liftRen_varIdx hξ)]
  | caseSum e l r ihl ihr =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ,
      ihl (liftRen ξ) (liftRen_varIdx hξ), ihr (liftRen ξ) (liftRen_varIdx hξ)]
  | sample s e | query s e =>
    intro Γ₂ ξ hξ; simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ]
  | iter n e body ihb =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ,
      ihb (liftRen ξ) (liftRen_varIdx hξ)]
  | findM K l p ihp | anyM K l p ihp | mapM K l p ihp =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ,
      ihp (liftRen ξ) (liftRen_varIdx hξ)]
  | consumeFirstM K l p mk ihp =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ,
      rename_descBits_eq opB _ _ (liftRen_varIdx hξ), ihp (liftRen ξ) (liftRen_varIdx hξ)]
  | foldM K l z f ihf =>
    intro Γ₂ ξ hξ
    simp only [Comp.renameM, atomicCompDescBits, rename_descBits_eq opB _ _ hξ,
      ihf (liftRen (liftRen ξ)) (liftRen_varIdx (liftRen_varIdx hξ))]

private theorem wkTop1Comp_descBits_eq {ℓ : ℕ} {Pt : Type} {O' : Ops (atomicSig ℓ Pt)}
    {ι : Type} {T : OracleSpec ι} {I' : Iface (atomicSig ℓ Pt) T}
    (opB : O'.Op → ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))} {a t : Ty (atomicSig ℓ Pt)} (c : Comp O' I' [a] t) :
    atomicCompDescBits opB sB qB (wkTop1Comp (Γ := Γ) c) =
      atomicCompDescBits opB sB qB c :=
  comp_renameM_descBits_eq opB sB qB c _ fun _ v => by
    cases v with
    | zero => rfl
    | succ w => nomatch w

private theorem callSub1C_descBits_eq {ℓ : ℕ} {Pt : Type} {O' : Ops (atomicSig ℓ Pt)}
    {ι : Type} {T : OracleSpec ι} {I' : Iface (atomicSig ℓ Pt) T}
    (opB : O'.Op → ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))} {a t : Ty (atomicSig ℓ Pt)}
    (c : Comp O' I' [a] t) (argE : Expr O' Γ a) :
    atomicCompDescBits opB sB qB (callSub1C c argE) =
      (atomicExprDescBits opB argE + 6) + atomicCompDescBits opB sB qB c + 6 := by
  simp only [callSub1C, atomicCompDescBits, wkTop1Comp_descBits_eq]

def extractRecvOptE {ℓ : ℕ} {Pt : Type} {O' : Ops (atomicSig ℓ Pt)} :
    Expr O' [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.opt (.prod .bool (.prod (B 32) .bool))) :=
  .caseSum (.var (.succ .zero))
    .none
    (.caseSum .v0
      .none
      (.caseSum .v0
        (.some (.pair (.fst .v0) (.pair (.snd .v0) (.bool true))))
        (.caseSum .v0
          (.some (.pair (.fst .v0) (.pair (.snd .v0) (.bool false))))
          .none)))

def isSendOrChallE {ℓ : ℕ} {Pt : Type} {O' : Ops (atomicSig ℓ Pt)} :
    Expr O' [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)] .bool :=
  .caseSum (.var (.succ .zero))
    (.bool true)
    (.caseSum .v0 (.bool true) (.bool false))

def stepDispatchC {ℓ : ℕ} {Pt : Type}
    {O' : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι} {I' : Iface (atomicSig ℓ Pt) T}
    (cSend cCorr : Comp O' I' [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (cRecv : Comp O' I' [recvHookInpT ℓ Pt] (recvOutT ℓ Pt)) :
    Comp O' I' [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)) :=
  .caseOpt (extractRecvOptE (ℓ := ℓ) (Pt := Pt))
    (.ite (isSendOrChallE (ℓ := ℓ) (Pt := Pt)) cSend cCorr)
    (.bind (callSub1C cRecv (.pair .v1 .v0))
      (.ret (.pair (.pair .none (.pair (.fst .v0) .none)) (.snd .v0))))

private theorem stepDispatchC_queries {ℓ : ℕ} {Pt : Type}
    {O' : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι} {I' : Iface (atomicSig ℓ Pt) T}
    (cSend cCorr : Comp O' I' [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (cRecv : Comp O' I' [recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (stepDispatchC cSend cCorr cRecv).queries w ws ≤
      max (max (cSend.queries w ws) (cCorr.queries w ws)) (cRecv.queries w ws) := by
  simp only [stepDispatchC, callSub1C, wkTop1Comp, Comp.queries, Comp.renameM_queries]
  omega

private theorem stepDispatchC_cost {ℓ : ℕ} {Pt : Type}
    {O' : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι} {I' : Iface (atomicSig ℓ Pt) T}
    (cSend cCorr : Comp O' I' [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (cRecv : Comp O' I' [recvHookInpT ℓ Pt] (recvOutT ℓ Pt)) :
    (stepDispatchC cSend cCorr cRecv).cost ≤
      max (max cSend.cost cCorr.cost) cRecv.cost + 50 := by
  simp only [stepDispatchC, extractRecvOptE, isSendOrChallE, callSub1C, wkTop1Comp,
    Comp.cost, Comp.renameM_cost, Expr.cost, Expr.v0, Expr.v1]
  omega

private theorem stepDispatchC_descBits_le {ℓ : ℕ} {Pt : Type}
    {O' : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι} {I' : Iface (atomicSig ℓ Pt) T}
    (opB : O'.Op → ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    (cSend cCorr : Comp O' I' [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (cRecv : Comp O' I' [recvHookInpT ℓ Pt] (recvOutT ℓ Pt)) :
    atomicCompDescBits opB sB qB (stepDispatchC cSend cCorr cRecv) ≤
      atomicCompDescBits opB sB qB cSend +
      atomicCompDescBits opB sB qB cCorr +
      atomicCompDescBits opB sB qB cRecv + 500 := by
  dsimp only [stepDispatchC]
  rw [atomicCompDescBits, atomicCompDescBits, atomicCompDescBits, callSub1C_descBits_eq]
  dsimp only [extractRecvOptE, isSendOrChallE, GhostStT, B,
    Expr.v0, Expr.v1, varIdx, atomicCompDescBits, atomicExprDescBits,
    atomicTyDescBits, atomicSortDescBits]
  simp only [Nat.reduceAdd, sb_c0, sb_c1, sb_p32]
  omega

private theorem stepDispatchC_run_tr {ℓ : ℕ} {Pt : Type} [SampleableType Pt]
    {O' : Ops (atomicSig ℓ Pt)}
    (cSend cCorr : Comp O' (fig8SmIface ℓ Pt) [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (cRecv : Comp O' (fig8SmIface ℓ Pt) [recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (P : Party) (m : Plain ℓ) (r : Option (BitVec 512)) (s_raw : (simFullT ℓ Pt).denote) :
    ((handlerImpl (C := e2eSessionCodec ℓ Pt) (stepDispatchC cSend cCorr cRecv)
      (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run s_raw) =
    ((handlerImpl (C := e2eSessionCodec ℓ Pt) cSend
      (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run s_raw) := rfl

private theorem stepDispatchC_run_ch {ℓ : ℕ} {Pt : Type} [SampleableType Pt]
    {O' : Ops (atomicSig ℓ Pt)}
    (cSend cCorr : Comp O' (fig8SmIface ℓ Pt) [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (cRecv : Comp O' (fig8SmIface ℓ Pt) [recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (P : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512)) (s_raw : (simFullT ℓ Pt).denote) :
    ((handlerImpl (C := e2eSessionCodec ℓ Pt) (stepDispatchC cSend cCorr cRecv)
      (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run s_raw) =
    ((handlerImpl (C := e2eSessionCodec ℓ Pt) cSend
      (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run s_raw) := rfl

private theorem stepDispatchC_run_cr {ℓ : ℕ} {Pt : Type} [SampleableType Pt]
    {O' : Ops (atomicSig ℓ Pt)}
    (cSend cCorr : Comp O' (fig8SmIface ℓ Pt) [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (cRecv : Comp O' (fig8SmIface ℓ Pt) [recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (P : Party) (s_raw : (simFullT ℓ Pt).denote) :
    ((handlerImpl (C := e2eSessionCodec ℓ Pt) (stepDispatchC cSend cCorr cRecv)
      (.inr (.inr P))).run s_raw) =
    ((handlerImpl (C := e2eSessionCodec ℓ Pt) cCorr
      (.inr (.inr P))).run s_raw) := rfl

private theorem stepDispatchC_run_dl {ℓ : ℕ} {Pt : Type} [SampleableType Pt]
    {O' : Ops (atomicSig ℓ Pt)}
    (cSend cCorr : Comp O' (fig8SmIface ℓ Pt) [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (cRecv : Comp O' (fig8SmIface ℓ Pt) [recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (P : Party) (w : Bytes) (s_raw : (simFullT ℓ Pt).denote) :
    (Prod.map id simFullDec <$>
      ((handlerImpl (C := e2eSessionCodec ℓ Pt) (stepDispatchC cSend cCorr cRecv)
        (.inr (.inl (.inl (.inr (P, w)))))).run s_raw)) =
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      cRecv.eval (.cons (s_raw, (partyToBool P, (w, true))) .nil)) := by
  dsimp only [handlerImpl, e2eSessionCodec, smQenc, smRdec, StateT.run, StateT.mk]
  let qEnc : (smQT (ℓ := ℓ) (Pt := Pt)).denote := Sum.inr (Sum.inr (Sum.inl (partyToBool P, w)))
  change (Prod.map id simFullDec <$>
    (((callSub1C cRecv (.pair .v1 .v0)).bind
      (.ret (.pair (.pair .none (.pair (.fst .v0) .none)) (.snd .v0)))).eval
        (.cons (partyToBool P, (w, true)) (.cons s_raw (.cons qEnc .nil))) >>=
      fun p => pure (p.1.2.1.map recvResultDec, p.2))) = _
  rw [Comp.eval, callSub1C_eval]
  simp only [Comp.eval, Expr.eval, Expr.v0, Expr.v1, Env.get,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map, id_eq]

private theorem stepDispatchC_run_ij {ℓ : ℕ} {Pt : Type} [SampleableType Pt]
    {O' : Ops (atomicSig ℓ Pt)}
    (cSend cCorr : Comp O' (fig8SmIface ℓ Pt) [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (cRecv : Comp O' (fig8SmIface ℓ Pt) [recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (P : Party) (w : Bytes) (s_raw : (simFullT ℓ Pt).denote) :
    (Prod.map id simFullDec <$>
      ((handlerImpl (C := e2eSessionCodec ℓ Pt) (stepDispatchC cSend cCorr cRecv)
        (.inr (.inl (.inr (P, w))))).run s_raw)) =
    (Prod.map (Option.map recvResultDec) simFullDec <$>
      cRecv.eval (.cons (s_raw, (partyToBool P, (w, false))) .nil)) := by
  dsimp only [handlerImpl, e2eSessionCodec, smQenc, smRdec, StateT.run, StateT.mk]
  let qEnc : (smQT (ℓ := ℓ) (Pt := Pt)).denote :=
    Sum.inr (Sum.inr (Sum.inr (Sum.inl (partyToBool P, w))))
  change (Prod.map id simFullDec <$>
    (((callSub1C cRecv (.pair .v1 .v0)).bind
      (.ret (.pair (.pair .none (.pair (.fst .v0) .none)) (.snd .v0)))).eval
        (.cons (partyToBool P, (w, false)) (.cons s_raw (.cons qEnc .nil))) >>=
      fun p => pure (p.1.2.1.map recvResultDec, p.2))) = _
  rw [Comp.eval, callSub1C_eval]
  simp only [Comp.eval, Expr.eval, Expr.v0, Expr.v1, Env.get,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map, id_eq]

/-- Single-invocation concrete atomic `SimFig8` step `Comp`. -/
def simFig8RawStepC {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)) :=
  let sendSpec := simFig8SendStepSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let corrC := simFig8StepCorrC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q
  let fwdSpec := simFig8FwdHookSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let sameSpec := simFig8RecvSameSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let newSpec := simFig8RecvNewSpec_of_fwd C K Dh encPt encT decT lam
    idA idB qep q fwdSpec.comp fwdSpec.hq fwdSpec.hcost fwdSpec.hdesc fwdSpec.heval
  let recvHookC := recvHookOfBranchesC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB q sameSpec.comp newSpec.comp
  stepDispatchC sendSpec.step corrC recvHookC

end Helpers

/-- Specification record for the concrete single-query `SimFig8` step `Comp` matching
`simFig8OracleSan` at `(L, B, T, Kc, Bsk) = (q, 2 ^ 32 + q + 2, 50000 * q, 25001 * q + 25000, 25000 * q)`. -/
structure SimFig8RawStepSpec (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) where
  step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
    [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
    (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt))
  hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1
  hstep_c : ℓ < 10 ^ 6 →
    step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1)
  hstep_d : ℓ < 10 ^ 6 →
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
      2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))
  hstep : ℓ < 10 ^ 6 → ∀ t (s_raw : (simFullT ℓ Pt).denote),
    SimCStateBounded q (simFullDec s_raw) →
    SanSnapExtra C K (simFullDec s_raw) →
    (Prod.map id simFullDec <$>
      ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
    ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep
      (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q)
      (.inr t)).run (simFullDec s_raw))

private theorem step_queries_arith {qTot qS qC qR qN qSm : ℕ}
    (h0 : qTot ≤ max (max qS qC) qR) (hS : qS ≤ 1) (hC : qC ≤ 1)
    (hR : qR = max qN qSm) (hN : qN ≤ 1) (hSm : qSm ≤ 1) :
    qTot ≤ 1 := by
  omega

private theorem step_cost_arith {ℓ q qep cTot cS cC cR cN cSm : ℕ}
    (hℓ : ℓ < 10 ^ 6)
    (h0 : cTot ≤ max (max cS cC) cR + 50)
    (hS : cS ≤ 60000000 + 30000000 * q + 1024 * bits (qep + 1))
    (hC : cC ≤ 2000100 + 25100000 * q)
    (hR : cR ≤ max cN cSm + 2 * (ℓ / 32) + 500 * q + 131220000)
    (hN : cN ≤ 24010005 + 20000000 * q + 128 * bits (qep + 1))
    (hSm : cSm ≤ 25000005 + 20000000 * q + 128 * bits (qep + 1)) :
    cTot ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1) := by
  omega

private theorem step_descBits_arith {q qep dTot dS dC dR dN dSm : ℕ}
    (h0 : dTot ≤ dS + dC + dR + 500)
    (hS : dS ≤ 2 ^ 20 + 2 ^ 11 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hC : dC ≤ 132000 + 128 * bits (q + 1))
    (hR : dR ≤ dN + dSm + 8 * bits q + 130000)
    (hN : dN ≤ 275010 + 256 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hSm : dSm ≤ 260010 + 256 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))) :
    dTot ≤ 2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  have hb2 := bits_two_mul_add_two_le_ratchetCostBudget q (qep + 1)
  have hbq : bits q ≤ bits (2 * q + 2) := bits_mono_le (by omega)
  have hbq1 : bits (q + 1) ≤ bits (2 * q + 2) := bits_mono_le (by omega)
  omega

theorem simFig8RawStepSpec_nonempty {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    Nonempty (SimFig8RawStepSpec Pt ℓ C K idA idB Dh encPt encT decT lam qep q) := by
  let sendSpec := simFig8SendStepSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let fwdSpec := simFig8FwdHookSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let sameSpec := simFig8RecvSameSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let newSpec := simFig8RecvNewSpec_of_fwd C K Dh encPt encT decT lam
    idA idB qep q fwdSpec.comp fwdSpec.hq fwdSpec.hcost fwdSpec.hdesc fwdSpec.heval
  let cSend := sendSpec.step
  let cCorr := simFig8StepCorrC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q
  let cRecv := recvHookOfBranchesC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB q sameSpec.comp newSpec.comp
  refine ⟨{
    step := stepDispatchC cSend cCorr cRecv
    hstep_q := step_queries_arith
      (stepDispatchC_queries cSend cCorr cRecv (fun _ => 1) (fun _ => 0))
      sendSpec.hstep_q
      (simFig8StepCorrC_queries (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q)
      (recvHookOfBranchesC_queries C K Dh encPt encT decT lam idA idB q
        sameSpec.comp newSpec.comp (fun _ => 1) (fun _ => 0))
      newSpec.hq sameSpec.hq
    hstep_c := fun hℓ => step_cost_arith hℓ
      (stepDispatchC_cost cSend cCorr cRecv)
      (sendSpec.hstep_c hℓ)
      (simFig8StepCorrC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q hℓ)
      (recvHookOfBranchesC_cost C K Dh encPt encT decT lam idA idB q sameSpec.comp newSpec.comp)
      (newSpec.hcost hℓ) (sameSpec.hcost hℓ)
    hstep_d := fun hℓ => step_descBits_arith
      (stepDispatchC_descBits_le atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        cSend cCorr cRecv)
      (sendSpec.hstep_d hℓ)
      (simFig8StepCorrC_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q hℓ)
      (recvHookOfBranchesC_descBits_le C K Dh encPt encT decT lam idA idB q
        sameSpec.comp newSpec.comp (fun _ => 8) (fun _ => 8))
      (newSpec.hdesc hℓ) (sameSpec.hdesc hℓ)
    hstep := ?_
  }⟩
  intro hℓ t s_raw hbnd hextra
  have hrecv : ∀ (Q : Party) (w : Bytes) (isDel : Bool),
      (Prod.map (Option.map recvResultDec) simFullDec <$>
        cRecv.eval (.cons (s_raw, (partyToBool Q, (w, isDel))) .nil)) =
      (Prod.map id Prod.fst <$>
        semRecvHookS (paramsV1 C K idA idB) Dh encPt encT decT lam (50000 * q) (25001 * q + 25000)
          (fig8IdSemHook (PQC := BitVec 512) none)
          qep (2 ^ 32 + q + 2) (simFullDec s_raw) () Q w isDel) := by
    intro Q w isDel
    have hs : s_raw = simFullEnc (simFullDec s_raw) := (simFullEnc_simFullDec s_raw).symm
    conv_lhs => rw [hs]
    exact recvHookOfBranchesC_eval C K Dh encPt encT decT lam idA idB
      q qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000)
      sameSpec.comp newSpec.comp
      (fun sC₀ Q₀ w₀ isDel₀ pq'₀ i₀ pk₀ T?₀ lct₀ honestC₀ ci₀ hb₀ hs₀ => by
        rw [sameSpec.heval hℓ sC₀ Q₀ w₀ isDel₀ pq'₀ i₀ pk₀ T?₀ lct₀ honestC₀ ci₀ hb₀ hs₀]
        dsimp only [semRecvSameBranch]
        split_ifs
        · simp only [map_pure, Prod.map, id_eq]
        · rfl)
      (newSpec.heval hℓ)
      (simFullDec s_raw) Q w isDel hbnd hextra
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, w⟩) | ⟨P, w⟩) | P
  · rw [stepDispatchC_run_tr]
    exact sendSpec.hstep_tr hℓ P m r s_raw hbnd hextra
  · rw [stepDispatchC_run_ch]
    exact sendSpec.hstep_ch hℓ P m₀ m₁ r s_raw hbnd hextra
  · rw [stepDispatchC_run_dl, hrecv P w true, ← simFig8OracleSan_deliver_eq]
  · rw [stepDispatchC_run_ij, hrecv P w false, ← simFig8OracleSan_inject_eq]
  · rw [stepDispatchC_run_cr]
    exact simFig8StepCorrC_run idA idB qep q hℓ P s_raw hbnd hextra

def simFig8RawStepSpec {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    SimFig8RawStepSpec Pt ℓ C K idA idB Dh encPt encT decT lam qep q :=
  Classical.choice (simFig8RawStepSpec_nonempty ℓ C K idA idB Dh encPt encT decT lam qep q)

end

end Computational.Proofs.Game.PromotedCostedReds.SimFig8Step
