/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound -- shake: keep
public import Computational.Proofs.SessionCostedBase -- shake: keep
public import Computational.Proofs.ReductionDsl.Ratchet.LibsignalSim -- shake: keep
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain -- shake: keep
import VCVio.EvalDist.EvalDistEq -- shake: keep
import Computational.Proofs.ReductionDsl.Bridge -- shake: keep
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire -- shake: keep
import Computational.Proofs.ReductionDsl.PubRed -- shake: keep
import Computational.Proofs.ReductionDsl.SM.RedFS -- shake: keep
import Computational.Proofs.GameHop.StateSim -- shake: keep
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv -- shake: keep
public import Computational.Proofs.GameHop.CompDedup -- shake: keep

/-!
# Soundness and Resource Bounds for `simDeliverForgeProg` and `kemFailRedProg`

Proves static query bounds, `GRedBounded` cost bounds, evaluation agreement, and `2 ^ 32`-clamp
equivalence bridges for `simDeliverForgeProg` and `kemFailRedProg`.
-/

@[expose] public section

namespace CryptoGames.Ratchet.LibsignalSim

set_option exponentiation.threshold 1024

open ReductionDsl OracleSpec OracleComp
open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA LibsignalSession LibsignalInst
open CryptoGames.Ratchet.LibsignalSimC CryptoVerification.LibsignalSession
open Computational.Proofs.GameHop.CompDedup

@[simp] private theorem v0_eval_cons {S' : Sig} {O' : Ops S'} {Γ' : List (Ty S')} {a : Ty S'}
    (x : a.denote) (ρ : Env Γ') :
    (Expr.v0 (O := O')).eval (Env.cons x ρ) = x := rfl

/-! ## Query bounds -/

section QueryBounds

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt) (K : CryptoVerification.LibsignalSpqrV1.MlKem) (toKemCoins : PQC → BitVec 512)

local notation "S" => simSig PQ PQC Pt ℓ
local notation "OFig" => simOpsUnitCost (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins
local notation "SIfaceDF" => simIfaceDF PQ PQC Pt ℓ
local notation "KIface" => kemFailIface PQ PQC Pt ℓ

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem makesAtMostQueriesDF_iff_isGameQuery {St Msg Coins C : Type}
    (oa : SM.Construction.DeliverForge.AdversaryDF St Msg Coins C) (q : ℕ) :
    SM.Construction.DeliverForge.MakesAtMostQueriesDF oa q ↔
      oa.IsQueryBoundP
        (isGameQuery (G := SM.specDF St Msg Coins C)) q :=
  ⟨Computational.Proofs.GameHop.StateSim.isQueryBoundP_congr_pred
      (by rintro (x | x) <;> simp [isGameQuery]),
    Computational.Proofs.GameHop.StateSim.isQueryBoundP_congr_pred
      (by rintro (x | x) <;> simp [isGameQuery])⟩

@[simp] theorem simSendHookC_df_queries (L qep B : ℕ) {Γ}
    (st : Expr OFig Γ (.prod simStateCTy (.list (fig8CTy PQ PQC Pt ℓ))))
    (qParty : Expr OFig Γ .bool) (m₀ : Expr OFig Γ (.base .plain))
    (chal : Expr OFig Γ (.opt (.base .plain))) (r : Expr OFig Γ (.opt (.base .pqc))) :
    (simSendHookC P Dh encPt encT decT lam K toKemCoins
      (deliverForgeHookC P Dh encPt encT decT lam K toKemCoins L)
      qep B st qParty m₀ chal r).queries (fun _ => 1) (fun _ => 0) = 1 := by
  simp [simSendHookC, simDrawSendCoinsHookC, deliverForgeHookC, Comp.queries]

@[simp] theorem fwdHookC_df_queries (L qep B : ℕ) {Γ}
    (sC : Expr OFig Γ simStateCTy) (ex : Expr OFig Γ (.list (fig8CTy PQ PQC Pt ℓ)))
    (qParty : Expr OFig Γ .bool) (wire : Expr OFig Γ (.base .wire))
    (isDel : Expr OFig Γ .bool) (ci? : Expr OFig Γ (.opt .nat))
    (Tpk : Expr OFig Γ (.base .pk)) (pq' : Expr OFig Γ (.base .pq))
    (honestC : Expr OFig Γ (.opt (fig8CTy PQ PQC Pt ℓ)))
    (c' : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) :
    (fwdHookC P Dh encPt encT decT lam K toKemCoins
      (deliverForgeHookC P Dh encPt encT decT lam K toKemCoins L) L qep B
      sC ex qParty wire isDel ci? Tpk pq' honestC c').queries (fun _ => 1) (fun _ => 0) = 1 := by
  simp [fwdHookC, fwdAnswerHookC, resyncHookC, deliverForgeHookC, Comp.queries]

@[simp] theorem fwdEvictHookC_df_queries (L qep B : ℕ) {Γ}
    (sC : Expr OFig Γ simStateCTy) (ex : Expr OFig Γ (.list (fig8CTy PQ PQC Pt ℓ)))
    (qParty : Expr OFig Γ .bool) (wire : Expr OFig Γ (.base .wire))
    (isDel : Expr OFig Γ .bool) (Tpk : Expr OFig Γ (.base .pk))
    (pq' : Expr OFig Γ (.base .pq)) (c' : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) :
    (fwdEvictHookC P Dh encPt encT decT lam K toKemCoins
      (deliverForgeHookC P Dh encPt encT decT lam K toKemCoins L) L qep B
      sC ex qParty wire isDel Tpk pq' c').queries (fun _ => 1) (fun _ => 0) = 1 := by
  simp [fwdEvictHookC, fwdAnswerHookC, deliverForgeHookC, Comp.queries]

@[simp] theorem simRecvHookC_df_queries (L qep B : ℕ) {Γ}
    (st : Expr OFig Γ (.prod simStateCTy (.list (fig8CTy PQ PQC Pt ℓ))))
    (qParty : Expr OFig Γ .bool) (wire : Expr OFig Γ (.base .wire))
    (isDel : Expr OFig Γ .bool) :
    (simRecvHookC P Dh encPt encT decT lam K toKemCoins
      (deliverForgeHookC P Dh encPt encT decT lam K toKemCoins L) L qep B
      st qParty wire isDel).queries (fun _ => 1) (fun _ => 0) = 1 := by
  simp [simRecvHookC, Comp.queries]

@[simp] theorem simCorrHookC_df_queries (L : ℕ) {Γ}
    (st : Expr OFig Γ (.prod simStateCTy (.list (fig8CTy PQ PQC Pt ℓ))))
    (qParty : Expr OFig Γ .bool) :
    (simCorrHookC P Dh encPt encT decT lam K toKemCoins
      (deliverForgeHookC P Dh encPt encT decT lam K toKemCoins L) L st qParty).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [simCorrHookC, deliverForgeHookC, Comp.queries]

@[simp] private lemma deliverForgeHookC_onDeliverPost_queries (L : ℕ) {Γ}
    (qB : Expr OFig Γ .bool) (j? : Expr OFig Γ (.opt .nat))
    (res : Expr OFig Γ (.opt (simRrTy PQ PQC Pt ℓ)))
    (ex : Expr OFig Γ (.list (fig8CTy PQ PQC Pt ℓ))) :
    ((deliverForgeHookC P Dh encPt encT decT lam K toKemCoins L).onDeliverPost
      qB j? res ex).queries (fun _ => 1) (fun _ => 0) = 0 := rfl

@[simp] theorem simHandleHookC_df_queries (L qep B : ℕ) :
    (simHandleHookC (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins
      (deliverForgeHookC (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L) L qep B).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [simHandleHookC, Comp.queries]

@[simp] theorem simDeliverForgeProg_totalQueries (L qep B q : ℕ) :
    (simDeliverForgeProg (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins
      L qep B).totalQueries (fun _ => 1) (fun _ => 0) q = q := by
  simp [CostedReduction.totalQueries, simDeliverForgeProg, Comp.queries]

/-- Query-forwarding bound for `simDeliverForgeProg` from `SM.MakesAtMostQueries` to `MakesAtMostQueriesDF`. -/
theorem simDeliverForgeProg_queries (L qep B : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (q : ℕ) (hA : SM.MakesAtMostQueries A q) :
    SM.Construction.DeliverForge.MakesAtMostQueriesDF
      ((simDeliverForgeProg (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins
        L qep B).eval (fun _ => A) ()) q := by
  rw [makesAtMostQueriesDF_iff_isGameQuery]
  have hA' := (makesAtMostQueries_iff_isGameQuery A q).mp hA
  have h := CostedReduction.queryBound_eval
    (simDeliverForgeProg (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
    (isGameQuery (G := SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)))
    (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => le_rfl)
    (fun n => by simp [isGameQuery, isQueryBoundP_query_iff])
    (fun _ => A) q (fun _ => hA') ()
  exact h.mono (le_of_eq
    (simDeliverForgeProg_totalQueries P Dh encPt encT decT lam K toKemCoins L qep B q))

end QueryBounds

/-! ## Cost bounds -/

section CostBounds

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}

local notation "S" => simSig PQ PQC Pt ℓ

variable (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt) (K : CryptoVerification.LibsignalSpqrV1.MlKem) (toKemCoins : PQC → BitVec 512)

local notation "OFig" => simOpsUnitCost (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins
local notation "SIfaceDF" => simIfaceDF PQ PQC Pt ℓ
local notation "KIface" => kemFailIface PQ PQC Pt ℓ

end CostBounds

/-! ## Evaluation agreement -/

section EvalAgreement

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt) (K : CryptoVerification.LibsignalSpqrV1.MlKem) (toKemCoins : PQC → BitVec 512)

local notation "S" => simSig PQ PQC Pt ℓ
local notation "OFig" => simOpsUnitCost (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins
local notation "SIfaceDF" => simIfaceDF PQ PQC Pt ℓ
local notation "KIface" => kemFailIface PQ PQC Pt ℓ

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp] theorem expr_fst_eval {O' : Ops S} {Γ} {t₁ t₂ : Ty S}
    (e : Expr O' Γ (.prod t₁ t₂)) (ρ : Env Γ) :
    (Expr.fst e).eval ρ = (e.eval ρ).1 := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp] theorem expr_snd_eval {O' : Ops S} {Γ} {t₁ t₂ : Ty S}
    (e : Expr O' Γ (.prod t₁ t₂)) (ρ : Env Γ) :
    (Expr.snd e).eval ρ = (e.eval ρ).2 := rfl

def keptDec (k : (@keptTy PQ PQC Pt ℓ).denote) : Kept Pt :=
  ⟨k.1, fun t => match k.2.2 t with
    | some v? => v?
    | none => match k.2.1 with | some st => st.vR t | none => none⟩

def snapDec (e : (@snapEntryTy PQ PQC Pt ℓ).denote) : Party × ℕ × GhostState PQ :=
  (partyDec e.1, e.2.1, e.2.2)

def snapEnc (e : Party × ℕ × GhostState PQ) : (@snapEntryTy PQ PQC Pt ℓ).denote :=
  (partyEnc e.1, e.2.1, e.2.2)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp]
theorem snapDec_snapEnc (e : Party × ℕ × GhostState PQ) :
    snapDec (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) (snapEnc e) = e := by
  rcases e with ⟨Q, ep, g⟩
  simp [snapDec, snapEnc]

def simStateCDec (s : (@simStateCTy PQ PQC Pt ℓ).denote) : LibsignalToModularSchemeSimState PQ Pt ℓ :=
  ⟨simStateDec s.1,
   fun Q => match Q with | .A => keptDec s.2.1.1 | .B => keptDec s.2.1.2,
   s.2.2.1,
   s.2.2.2.map snapDec⟩

omit [SampleableType PQC] in
@[simp] theorem mInTransitFigE_eval {Γ} (L : ℕ) (s : Expr OFig Γ simMirTy)
    (qParty : Expr OFig Γ .bool) (w : Expr OFig Γ (.base .wire)) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (hL : st.trans.length ≤ L)
    (hs : s.eval ρ = simMirEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (mInTransitFigE P Dh encPt encT decT lam K toKemCoins L s qParty w).eval ρ =
      (st.inTransit Q (w.eval ρ)).map simRecEnc := by
  have htake : (st.trans.map simRecEnc).take L = st.trans.map simRecEnc :=
    List.take_of_length_le (by simpa using hL)
  simp only [mInTransitFigE, GameState.inTransit, mTrans, srecPos, posSender, srecCt,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    boolEq_eval, simOpsUnitCost, hs, hq, simMirEnc, htake]
  rw [find?_map_eq]
  congr 2
  funext ⟨⟨sender, ep, idx⟩, msg, ct⟩
  cases sender <;> cases Q <;> by_cases h : ct = w.eval ρ <;>
    simp [simRecEnc, posEnc, partyEnc, h]

omit [SampleableType PQC] in
@[simp] theorem initChainAFigE_eval {Γ} (ρ : Env Γ) :
    (initChainAFigE (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins).eval ρ =
      ghostChainEnc ⟨none, 0, 0, []⟩ :=
  rfl

omit [SampleableType PQC] in
theorem hasUnknownKeyFigE_eval {Γ}
    (cs : Expr OFig Γ (.list (ghostChainTy PQ PQC Pt ℓ))) (ρ : Env Γ)
    (xs : List GhostChain) (hxs : xs.length ≤ 5)
    (hcs : cs.eval ρ = xs.map ghostChainEnc) :
    (hasUnknownKeyFigE P Dh encPt encT decT lam K toKemCoins cs).eval ρ =
      xs.any (·.key.isNone) := by
  unfold hasUnknownKeyFigE
  have htake : (xs.map ghostChainEnc).take 5 = xs.map ghostChainEnc :=
    List.take_of_length_le (by simp [hxs])
  simp only [Expr.eval, hcs, htake, List.any_map, Function.comp_def]
  congr 1; funext g
  rcases g with ⟨_ | k, ep, ls, sk⟩ <;> rfl

private theorem foldr_findChainFig (cs : List (Option PublicKey × (ℕ × (ℕ × List ℕ))))
    (pk : PublicKey) :
    cs.foldr
      (fun x acc =>
        if (match x.1 with | none => false | some k => decide (k = pk)) then
          some (0, x)
        else
          match acc with
          | none => none
          | some p => some (p.1 + 1, p.2))
      none =
    simFindChain cs pk := by
  induction cs with
  | nil => rfl
  | cons x xs ih =>
    have hcond : (match x.1 with | none => false | some k => decide (k = pk)) =
        (x.1 == some pk) := by
      rcases x.1 with _ | k <;> rfl
    simp only [List.foldr_cons, hcond, ih]
    unfold simFindChain
    rw [List.findIdx?_cons]
    by_cases hx : (x.1 == some pk) = true
    · simp [hx]
    · simp only [hx, Bool.false_eq_true, ↓reduceIte]
      rcases hfind : xs.findIdx? (fun g => g.1 == some pk) with _ | ci <;> simp [hfind]

omit [SampleableType PQC] in
theorem findChainFigE_eval {Γ}
    (arg : Expr OFig Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.base .pk))) (ρ : Env Γ)
    (cs : List (Option PublicKey × (ℕ × (ℕ × List ℕ)))) (pk : PublicKey)
    (hcs : cs.length ≤ 5) (harg : arg.eval ρ = (cs, pk)) :
    (findChainFigE P Dh encPt encT decT lam K toKemCoins arg).eval ρ =
      simFindChain cs pk := by
  unfold findChainFigE
  rw [letE_eval, harg]
  have htake : cs.take 5 = cs := List.take_of_length_le hcs
  simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v3, Env.get, htake, simOpsUnitCost]
  rw [← foldr_findChainFig cs pk]
  congr 1; funext x acc
  rcases x with ⟨_ | k, rest⟩ <;> rcases acc with _ | ⟨ci, g⟩ <;> rfl

private theorem foldr_modify_noopFig {α : Type} (f : α → α) (xs : List α) (c L : ℕ)
    (hle : xs.length + c ≤ L) :
    xs.foldr
      (fun x acc => (if decide (acc.length + c = L) then f x else x) :: acc)
      [] = xs := by
  induction xs with
  | nil => rfl
  | cons a ys ih =>
    simp only [List.length_cons] at hle
    have htail := ih (by omega)
    simp only [List.foldr_cons, htail]
    have hne : ¬ (ys.length + c = L) := by omega
    simp [hne]

private theorem foldr_modifyFig {α : Type} (f : α → α) (xs : List α) (ci : ℕ) :
    xs.foldr
      (fun x acc => (if decide (acc.length + (ci + 1) = xs.length) then f x else x) :: acc)
      [] =
    xs.modify ci f := by
  induction xs generalizing ci with
  | nil => simp
  | cons a ys ih =>
    cases ci with
    | zero =>
      simp only [List.foldr_cons, List.length_cons, Nat.zero_add, List.modify_cons]
      have htail := foldr_modify_noopFig f ys 1 (ys.length + 1) (by omega)
      rw [htail]
      simp
    | succ ci' =>
      simp only [List.foldr_cons, List.length_cons]
      have hstep :
          (fun x (acc : List α) =>
            (if decide (acc.length + (ci' + 1 + 1) = ys.length + 1) then f x else x) :: acc) =
          (fun x (acc : List α) =>
            (if decide (acc.length + (ci' + 1) = ys.length) then f x else x) :: acc) := by
        funext x acc
        have heq : decide (acc.length + (ci' + 1 + 1) = ys.length + 1) =
            decide (acc.length + (ci' + 1) = ys.length) := by
          simp only [decide_eq_decide]; omega
        rw [heq]
      rw [hstep, ih ci']
      have hne : ¬ ((ys.modify ci' f).length + (ci' + 1 + 1) = ys.length + 1) := by
        rw [List.length_modify]; omega
      simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte]
      rfl

omit [SampleableType PQC] in
theorem modifyChainAcceptFigE_eval {Γ}
    (arg : Expr OFig Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.prod .nat .nat)))
    (ρ : Env Γ)
    (cs : List (Option PublicKey × (ℕ × (ℕ × List ℕ)))) (ci i : ℕ)
    (hcs : cs.length ≤ 5) (harg : arg.eval ρ = (cs, (ci, i))) :
    (modifyChainAcceptFigE P Dh encPt encT decT lam K toKemCoins arg).eval ρ =
      simModifyChainAccept cs ci i := by
  unfold modifyChainAcceptFigE simModifyChainAccept
  rw [letE_eval, harg]
  have htake : cs.take 5 = cs := List.take_of_length_le hcs
  simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, htake, simOpsUnitCost]
  exact foldr_modifyFig (fun g => (g.1, (g.2.1, simChainAccept g.2.2 i))) cs ci

private theorem foldr_pushChainFig {α : Type} (cs : List α) (g : α) (hcs : cs.length ≤ 5) :
    cs.foldr (fun x acc => if decide (acc.length < 5) then x :: acc else acc) [g] =
      (cs ++ [g]).drop ((cs ++ [g]).length - 5) := by
  rcases cs with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, _ | ⟨x₄, _ | ⟨x₅, _ | ⟨x₆, rest⟩⟩⟩⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [List.length_cons] at hcs; omega

omit [SampleableType PQC] in
theorem pushChainFigE_eval {Γ}
    (arg : Expr OFig Γ
      (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.prod (.base .pk) (.prod .nat .nat))))
    (ρ : Env Γ)
    (cs : List (Option PublicKey × (ℕ × (ℕ × List ℕ)))) (T : PublicKey) (t i : ℕ)
    (hcs : cs.length ≤ 5) (harg : arg.eval ρ = (cs, (T, (t, i)))) :
    (pushChainFigE P Dh encPt encT decT lam K toKemCoins arg).eval ρ =
      simPushChain cs T t i := by
  unfold pushChainFigE simPushChain
  rw [letE_eval, harg]
  have htake : cs.take 5 = cs := List.take_of_length_le hcs
  simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, htake, simOpsUnitCost]
  exact foldr_pushChainFig cs (some T, (t, simChainAccept (0, []) i)) hcs

omit [SampleableType PQC] in
theorem revealSpkChainsFigE_eval {Γ}
    (arg : Expr OFig Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.base .fig8st))) (ρ : Env Γ)
    (csA : List (Option PublicKey × (ℕ × (ℕ × List ℕ)))) (st : SimFig8St Pt)
    (hcsA : csA.length ≤ 5) (harg : arg.eval ρ = (csA, st)) :
    (revealSpkChainsFigE P Dh encPt encT decT lam K toKemCoins arg).eval ρ =
      simRevealSpkChains Dh encT csA st := by
  unfold revealSpkChainsFigE simRevealSpkChains
  rw [letE_eval, harg]
  have htake : csA.take 5 = csA := List.take_of_length_le hcsA
  simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, simOpsUnitCost]
  rcases st.γ with _ | x
  · rfl
  · simp only [htake]
    congr 1; funext g
    rcases g with ⟨_ | k, rest⟩ <;> rfl

omit [SampleableType PQC] in
theorem spqrSendPubFigE_eval {Γ}
    (arg : Expr OFig Γ
      (.prod .bool (.prod .bool (.prod (.base .pq) (.prod (.base .pqc) (.base .u32))))))
    (ρ : Env Γ)
    (qB unackA : Bool) (pq : PQ) (rq : PQC) (pn : BitVec 32)
    (harg : arg.eval ρ = (qB, (unackA, (pq, (rq, pn))))) :
    (spqrSendPubFigE P Dh encPt encT decT lam K toKemCoins arg).eval ρ =
      simSpqrSendPub P qB unackA pq rq pn := by
  unfold spqrSendPubFigE simSpqrSendPub
  rw [letE_eval, harg]
  simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, simOpsUnitCost]
  rcases P.spqr.send pq rq with _ | ⟨pq', salt?, pqm⟩
  · rfl
  · cases qB <;> cases unackA <;> rfl

/-- Parse an incoming wire for `Q`, run `P.spqr.recv`, and extract the `B`-clamped 1-based counter, ratchet key, decoded point, and ciphertext body. -/
def simParseRecvC (B : ℕ) (qB : Bool) (pq : PQ) (w : List (BitVec 8)) :
    Option (PQ × (ℕ × (PublicKey × (Option Pt × (ℕ × LibsignalCiphertextWithSalt32))))) :=
  let Q := partyDec qB
  if w.length < 9 then none
  else
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    match (signalWireCodec P.codec).parse ser with
    | none => none
    | some (h, _) =>
      if !(addressCheckPasses h.addresses (P.expectedAddrs Q)) || P.spqr.recvPanics pq h.pqRatchet then none
      else
        match P.spqr.recv pq h.pqRatchet with
        | .error _ => none
        | .ok (pq', salt) =>
          some (pq', (min (h.counter.toNat + 1) B,
            (h.senderRatchetKey, (decT h.senderRatchetKey,
              (h.counter.toNat + 1, ((ser, tag), effectiveHkdfSalt32 salt))))))

omit [SampleableType PQC] in
theorem parseRecvFigCE_eval (B : ℕ) {Γ}
    (arg : Expr OFig Γ (.prod .bool (.prod (.base .pq) (.base .wire)))) (ρ : Env Γ)
    (qB : Bool) (pq : PQ) (w : List (BitVec 8))
    (harg : arg.eval ρ = (qB, (pq, w))) :
    (parseRecvFigCE P Dh encPt encT decT lam K toKemCoins B arg).eval ρ =
      simParseRecvC P decT B qB pq w := by
  unfold parseRecvFigCE simParseRecvC
  rw [letE_eval, harg]
  simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, simOpsUnitCost,
    simSplitWireTag, simParseWire]
  by_cases hlen : w.length < 9
  · simp [hlen]
  · simp only [hlen, ↓reduceIte]
    rcases hwire : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, rest⟩
    · rfl
    · dsimp only [Option.map]
      cases qB
      · simp only [partyDec, Bool.false_eq_true, ↓reduceIte]
        by_cases ha : addressCheckPasses h.addresses (P.expectedAddrs .A) = true <;>
          by_cases hp : P.spqr.recvPanics pq h.pqRatchet = true <;>
          rcases P.spqr.recv pq h.pqRatchet with err | ⟨pq', salt⟩ <;>
          simp [ha, hp, Except.toOption]
      · simp only [partyDec, ↓reduceIte]
        by_cases hb : addressCheckPasses h.addresses (P.expectedAddrs .B) = true <;>
          by_cases hp : P.spqr.recvPanics pq h.pqRatchet = true <;>
          rcases P.spqr.recv pq h.pqRatchet with err | ⟨pq', salt⟩ <;>
          simp [hb, hp, Except.toOption]

omit [SampleableType PQC] in
theorem toGhostFigE_eval {Γ}
    (arg : Expr OFig Γ
      (.prod .bool
        (.prod (.base .fig8st)
          (.prod (.base .u32)
            (.prod (.list (ghostChainTy PQ PQC Pt ℓ))
              (.prod .bool (.prod (.base .pq) .nat)))))))
    (ρ : Env Γ)
    (qB : Bool) (st : SimFig8St Pt) (pn : BitVec 32)
    (cs : List (Option PublicKey × (ℕ × (ℕ × List ℕ))))
    (unackA : Bool) (pq : PQ) (ep : ℕ)
    (hcs : cs.length ≤ 5)
    (harg : arg.eval ρ = (qB, (st, (pn, (cs, (unackA, (pq, ep))))))) :
    (toGhostFigE P Dh encPt encT decT lam K toKemCoins arg).eval ρ =
      simToGhost P qB st pn cs unackA pq ep := by
  unfold toGhostFigE simToGhost
  rw [letE_eval, harg]
  have htake : cs.take 5 = cs := List.take_of_length_le hcs
  simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, htake, simOpsUnitCost,
    simMkGhostState, simMkSenderChain]
  rcases st.γ with _ | x <;> rcases st.vS with _ | v <;> cases qB <;> rfl

omit [SampleableType PQC] in
theorem inTFigE_eval (L : ℕ) {Γ} (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party) (c₀ : Fig8C Pt)
    (hTrans : st.mir.trans.length ≤ L) (hHonest : st.honest.length ≤ L)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q)
    (hc : c.eval ρ = c₀) :
    (inTFigE P Dh encPt encT decT lam K toKemCoins L s qParty c).eval ρ =
      (st.honest.any fun wc =>
        decide (wc.2 = c₀) && (st.mir.inTransit Q.other wc.1).isSome) := by
  unfold inTFigE
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair qParty c)).eval ρ = (simStateEnc st, partyEnc Q, c₀) := by
    simp [Expr.eval, hs, hq, hc]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod simStateTy (.prod .bool (fig8CTy PQ PQC Pt ℓ)))
    (simStateEnc st, partyEnc Q, c₀) ρ
  have ht : st.honest.take L = st.honest := List.take_of_length_le hHonest
  have hHon : (ssHonest (.fst (Expr.v0 (O := OFig)))).eval ρ₁ = st.honest := rfl
  simp only [Expr.eval, hHon, ht]
  congr 1; funext wc
  have htr := mInTransitFigE_eval P Dh encPt encT decT lam K toKemCoins L
    (ssMir (.fst .v1)) (otherE (.fst (.snd .v1))) (.fst .v0)
    (Env.cons (t := .prod (.base SimSort.wire) (fig8CTy PQ PQC Pt ℓ)) wc ρ₁)
    st.mir Q.other hTrans rfl
    (by simp [ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ])
  have his := isSomeE_eval
    (mInTransitFigE P Dh encPt encT decT lam K toKemCoins L
      (ssMir (.fst .v1)) (otherE (.fst (.snd .v1))) (.fst .v0))
    (Env.cons (t := .prod (.base SimSort.wire) (fig8CTy PQ PQC Pt ℓ)) wc ρ₁)
  rw [his, htr]
  simp [ρ₁, simOpsUnitCost, Expr.eval, Expr.v0, Expr.v1]

omit [SampleableType PQC] in
theorem onAcceptPreFigE_eval {Γ}
    (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (t i : Expr OFig Γ .nat) (ciOpt : Expr OFig Γ (.opt .nat))
    (T : Expr OFig Γ (.base .pk)) (pq' : Expr OFig Γ (.base .pq)) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hChains : (st.chains Q).length ≤ 5)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (onAcceptPreFigE P Dh encPt encT decT lam K toKemCoins
      s qParty t i ciOpt T pq').eval ρ =
    simStateEnc
      (let cs := match ciOpt.eval ρ with
         | some ci => (st.chains Q).modify ci (·.accept (i.eval ρ))
         | none => pushChain (st.chains Q)
             (GhostChain.accept ⟨some (T.eval ρ), t.eval ρ, 0, []⟩ (i.eval ρ))
       { st with
         chains := Function.update st.chains Q cs,
         pq := Function.update st.pq Q (pq'.eval ρ),
         unackA := st.unackA && Q != Party.A }) := by
  unfold onAcceptPreFigE
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair qParty (.pair t (.pair i (.pair ciOpt (.pair T pq')))))).eval ρ =
      (simStateEnc st, partyEnc Q, t.eval ρ, i.eval ρ, ciOpt.eval ρ, T.eval ρ, pq'.eval ρ) := by
    simp [Expr.eval, hs, hq]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod simStateTy (.prod .bool (.prod .nat (.prod .nat
      (.prod (.opt .nat) (.prod (.base SimSort.pk) (.base SimSort.pq)))))))
    (simStateEnc st, partyEnc Q, t.eval ρ, i.eval ρ, ciOpt.eval ρ, T.eval ρ, pq'.eval ρ) ρ
  have hcs :
      (Expr.caseOpt (.fst (.snd (.snd (.snd (.snd (Expr.v0 (O := OFig)))))))
        (pushChainFigE P Dh encPt encT decT lam K toKemCoins
          (.pair (pGet (ssChains (.fst .v0)) (.fst (.snd .v0)))
            (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
              (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))))))
        (modifyChainAcceptFigE P Dh encPt encT decT lam K toKemCoins
          (.pair (pGet (ssChains (.fst .v1)) (.fst (.snd .v1)))
            (.pair .v0 (.fst (.snd (.snd (.snd .v1)))))))).eval ρ₁ =
      (match ciOpt.eval ρ with
       | some ci => (st.chains Q).modify ci (·.accept (i.eval ρ))
       | none => pushChain (st.chains Q)
           (GhostChain.accept ⟨some (T.eval ρ), t.eval ρ, 0, []⟩
             (i.eval ρ))).map ghostChainEnc := by
    rw [expr_caseOpt_eval]
    have hci : (Expr.fst (.snd (.snd (.snd (.snd (Expr.v0 (O := OFig))))))).eval ρ₁ =
        ciOpt.eval ρ := rfl
    rw [hci]
    rcases ciOpt.eval ρ with _ | ci
    · rw [← simPushChain_map_ghostChainEnc]
      refine pushChainFigE_eval P Dh encPt encT decT lam K toKemCoins _ ρ₁
        ((st.chains Q).map ghostChainEnc) (T.eval ρ) (t.eval ρ) (i.eval ρ) (by simp [hChains]) ?_
      cases Q <;>
        simp [ρ₁, ssChains, pGet_eval, simStateEnc, partyEnc, Expr.eval, Expr.v0]
    · rw [← simModifyChainAccept_map_ghostChainEnc]
      refine modifyChainAcceptFigE_eval P Dh encPt encT decT lam K toKemCoins _ _
        ((st.chains Q).map ghostChainEnc) ci (i.eval ρ) (by simp [hChains]) ?_
      cases Q <;>
        simp [ρ₁, ssChains, pGet_eval, simStateEnc, partyEnc, Expr.eval, Expr.v0, Expr.v1]
  simp only [ssMk, expr_pair_eval, pSet_eval, hcs]
  cases Q <;>
    simp [ρ₁, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped,
      simStateEnc, partyEnc, Function.update, bne, Expr.eval, Expr.v0]

omit [SampleableType PQC] in
theorem onAcceptFigE_eval (L qep : ℕ) {Γ}
    (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (w : Expr OFig Γ (.base .wire)) (isDel : Expr OFig Γ .bool)
    (t i : Expr OFig Γ .nat) (m : Expr OFig Γ (.base .plain))
    (ciOpt : Expr OFig Γ (.opt .nat)) (T : Expr OFig Γ (.base .pk))
    (pq' : Expr OFig Γ (.base .pq)) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hBound : SimStateBounded L st)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (pure ((onAcceptFigE P Dh encPt encT decT lam K toKemCoins L qep
      s qParty w isDel t i m ciOpt T pq').eval ρ) :
        Fig8Comp Pt ℓ (Option (@simRrTy PQ PQC Pt ℓ).denote × (@simStateTy PQ PQC Pt ℓ).denote)) =
    Prod.map (Option.map SM.smRrEnc) simStateEnc <$>
      ((onAccept qep Q (w.eval ρ) (isDel.eval ρ) (t.eval ρ) (i.eval ρ) (m.eval ρ)
        (ciOpt.eval ρ) (T.eval ρ) (pq'.eval ρ)).run st) := by
  unfold onAcceptFigE onAccept
  rw [letE_eval]
  set s' :=
    let cs := match ciOpt.eval ρ with
      | some ci => (st.chains Q).modify ci (·.accept (i.eval ρ))
      | none => pushChain (st.chains Q)
          (GhostChain.accept ⟨some (T.eval ρ), t.eval ρ, 0, []⟩ (i.eval ρ))
    { st with
      chains := Function.update st.chains Q cs,
      pq := Function.update st.pq Q (pq'.eval ρ),
      unackA := st.unackA && Q != Party.A }
  have hpre := onAcceptPreFigE_eval P Dh encPt encT decT lam K toKemCoins
    s qParty t i ciOpt T pq' ρ st Q (hBound.chains_le Q) hs hq
  have h0 :
      (Expr.pair s (.pair (onAcceptPreFigE P Dh encPt encT decT lam K toKemCoins
        s qParty t i ciOpt T pq')
        (.pair qParty (.pair w (.pair isDel (.pair t (.pair i m))))))).eval ρ =
      (simStateEnc st, simStateEnc s', partyEnc Q, w.eval ρ, isDel.eval ρ,
        t.eval ρ, i.eval ρ, m.eval ρ) := by
    simp [Expr.eval, hs, hq, hpre, s']
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod simStateTy (.prod simStateTy (.prod .bool (.prod (.base SimSort.wire)
      (.prod .bool (.prod .nat (.prod .nat (.base SimSort.plain))))))))
    (simStateEnc st, simStateEnc s', partyEnc Q, w.eval ρ, isDel.eval ρ,
      t.eval ρ, i.eval ρ, m.eval ρ) ρ
  rw [ite_eval]
  have hdel0 : (Expr.fst (.snd (.snd (.snd (.snd (Expr.v0 (O := OFig))))))).eval ρ₁ =
      isDel.eval ρ := rfl
  rw [hdel0]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hdel : isDel.eval ρ = true
  · simp only [hdel, ↓reduceIte]
    rw [expr_caseOpt_eval]
    have hinTr := mInTransitFigE_eval P Dh encPt encT decT lam K toKemCoins L
      (ssMir (.fst .v0)) (otherE (.fst (.snd (.snd .v0)))) (.fst (.snd (.snd (.snd .v0))))
      ρ₁ st.mir Q.other hBound.trans_le rfl
      (by simp [ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v0])
    have hw0 : (Expr.fst (.snd (.snd (.snd (Expr.v0 (O := OFig)))))).eval ρ₁ = w.eval ρ := rfl
    rw [hw0] at hinTr
    rw [hinTr]
    rcases st.mir.inTransit Q.other (w.eval ρ) with _ | r
    · simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · dsimp only [Option.map_some]
      set ρ₂ := Env.cons (t := simRecTy) (simRecEnc r) ρ₁
      have hch := mChallContainsE_eval (O' := OFig) L (ssMir (.fst .v1)) (srecPos .v0)
        ρ₂ st.mir r.pos hBound.chall_le rfl rfl
      have hacc := mAcceptE_eval (O' := OFig) L (ssMir (.fst .v1)) (.fst (.snd (.snd .v1)))
        (srecPos .v0) ρ₂ st.mir Q r.pos
        hBound.trans_le hBound.chall_le hBound.comp_le rfl rfl rfl
      have hset := ssSetMir_eval (O' := OFig) (.fst (.snd .v1))
        (mAcceptE (O' := OFig) L (ssMir (.fst .v1)) (.fst (.snd (.snd .v1))) (srecPos .v0))
        ρ₂ s' (st.mir.accept Q () r.pos) rfl hacc
      have hfst :
          (Expr.some (.inr (t := .unit)
            (.pair (.fst (.snd (.snd (.snd (.snd (.snd (Expr.v1 (O := OFig))))))))
              (.pair (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
                (.ite (mChallContainsE L (ssMir (.fst .v1)) (srecPos .v0))
                  .none (.some (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))))))).eval ρ₂ =
          some (SM.smRrEnc (.accepted (t.eval ρ) (i.eval ρ)
            (if st.mir.chall.contains r.pos then none else some (m.eval ρ)))) := by
        change some (Sum.inr (t.eval ρ, i.eval ρ,
          (Expr.ite (mChallContainsE L (ssMir (.fst (Expr.v1 (O := OFig)))) (srecPos .v0))
            .none (.some (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))).eval ρ₂)) = _
        rw [ite_eval, hch]
        cases st.mir.chall.contains r.pos <;> rfl
      rw [expr_pair_eval, hfst, hset]
      simp only [putS, StateT.run_bind, StateT.run_set, StateT.run_pure,
        pure_bind, map_pure, Prod.map, Option.map, s']
      cases ciOpt.eval ρ <;> rfl
  · simp only [hdel, Bool.false_eq_true, ↓reduceIte]
    rw [ite_eval]
    have hlt : (Expr.lt (.nat (qep + 1))
        (.fst (.snd (.snd (.snd (.snd (.snd (Expr.v0 (O := OFig))))))))).eval ρ₁ =
        decide (qep + 1 < t.eval ρ) := rfl
    rw [hlt]
    by_cases h1 : qep + 1 < t.eval ρ
    · simp [ρ₁, h1, SM.smRrEnc, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [ite_eval]
      have hpos : (Expr.pair (otherE (.fst (.snd (.snd (Expr.v0 (O := OFig))))))
          (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
            (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))).eval ρ₁ =
          posEnc ⟨Q.other, t.eval ρ, i.eval ρ⟩ := by
        simp [ρ₁, otherE, posEnc, partyEnc_other, Expr.eval, Expr.v0]
      have htriv := mTrivialE_eval (O' := OFig) L (ssMir (.fst .v0))
        (.pair (otherE (.fst (.snd (.snd .v0))))
          (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
            (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))))
        ρ₁ st.mir ⟨Q.other, t.eval ρ, i.eval ρ⟩ hBound.trans_le hBound.comp_le rfl hpos
      rw [htriv]
      by_cases h2 : (st.mir.trivial 3 ⟨Q.other, t.eval ρ, i.eval ρ⟩) = true
      · simp only [h2, ↓reduceIte]
        have hacc := mAcceptE_eval (O' := OFig) L (ssMir (.fst .v0)) (.fst (.snd (.snd .v0)))
          (.pair (otherE (.fst (.snd (.snd .v0))))
            (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
              (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))))
          ρ₁ st.mir Q ⟨Q.other, t.eval ρ, i.eval ρ⟩
          hBound.trans_le hBound.chall_le hBound.comp_le rfl rfl hpos
        have hset := ssSetMir_eval (O' := OFig) (.fst (.snd .v0))
          (mAcceptE (O' := OFig) L (ssMir (.fst .v0)) (.fst (.snd (.snd .v0)))
            (.pair (otherE (.fst (.snd (.snd .v0))))
              (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))))
          ρ₁ s' (st.mir.accept Q () ⟨Q.other, t.eval ρ, i.eval ρ⟩) rfl hacc
        rw [expr_pair_eval, hset]
        simp only [putS, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, map_pure, Prod.map, Option.map, s']
        cases ciOpt.eval ρ <;> rfl
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        have hwin := ssSetMirWin_eval (O' := OFig) (.fst .v0) ρ₁ st rfl
        rw [expr_pair_eval, hwin]
        simp only [putS, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, map_pure, Prod.map, Option.map]
        rfl

omit [SampleableType PQC] in
theorem onAnswerFigE_eval (L qep : ℕ) {Γ}
    (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (w : Expr OFig Γ (.base .wire)) (isDel : Expr OFig Γ .bool)
    (ciOpt : Expr OFig Γ (.opt .nat)) (T : Expr OFig Γ (.base .pk))
    (pq' : Expr OFig Γ (.base .pq))
    (resE : Expr OFig Γ (.opt (fig8RrTy PQ PQC Pt ℓ))) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hBound : SimStateBounded L st)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q)
    (hres : resE.eval ρ = res.map SM.smRrEnc) :
    (pure ((onAnswerFigE P Dh encPt encT decT lam K toKemCoins L qep
        s qParty w isDel ciOpt T pq' resE).eval ρ) :
      Fig8Comp Pt ℓ (Option (@simRrTy PQ PQC Pt ℓ).denote × (@simStateTy PQ PQC Pt ℓ).denote)) =
    Prod.map (Option.map SM.smRrEnc) simStateEnc <$>
      ((onAnswer qep Q (w.eval ρ) (isDel.eval ρ) (ciOpt.eval ρ) (T.eval ρ) (pq'.eval ρ)
        res).run st) := by
  unfold onAnswerFigE onAnswer
  rw [letE_eval]
  have h0 :
      (Expr.pair s (.pair qParty (.pair w (.pair isDel
        (.pair ciOpt (.pair T (.pair pq' resE))))))).eval ρ =
      (simStateEnc st, partyEnc Q, w.eval ρ, isDel.eval ρ,
        ciOpt.eval ρ, T.eval ρ, pq'.eval ρ, res.map SM.smRrEnc) := by
    simp [Expr.eval, hs, hq, hres]
  rw [h0]; clear h0
  rcases res with _ | (_ | ⟨t₀, i₀, pm⟩)
  · simp [SM.smRrEnc, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · simp [SM.smRrEnc, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v2]
  · dsimp only [Option.map_some, SM.smRrEnc]
    let ρ₁ := Env.cons
      (t := .prod simStateTy (.prod .bool (.prod (.base SimSort.wire) (.prod .bool
        (.prod (.opt .nat) (.prod (.base SimSort.pk)
          (.prod (.base SimSort.pq) (.opt (fig8RrTy PQ PQC Pt ℓ)))))))))
      (simStateEnc st, partyEnc Q, w.eval ρ, isDel.eval ρ,
        ciOpt.eval ρ, T.eval ρ, pq'.eval ρ, some (.inr (t₀, i₀, pm))) ρ
    let ρ₂ := Env.cons (t := .prod .nat (.prod .nat (.opt (lpubPlainTy PQ PQC Pt ℓ))))
      (t₀, i₀, pm)
      (Env.cons (t := fig8RrTy PQ PQC Pt ℓ) (.inr (t₀, i₀, pm)) ρ₁)
    change pure ((onAcceptFigE P Dh encPt encT decT lam K toKemCoins L qep
        (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2))) (.fst (.snd (.snd (.snd .v2))))
        (.fst .v0) (.fst (.snd .v0))
        (.caseOpt (.snd (.snd .v0)) (Expr.op (O := OFig) SimOp.defaultPlain .unit) (.snd .v0))
        (.fst (.snd (.snd (.snd (.snd .v2)))))
        (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v2)))))))).eval ρ₂) = _
    have hm : (Expr.caseOpt (.snd (.snd (Expr.v0 (O := OFig))))
        (Expr.op (O := OFig) SimOp.defaultPlain .unit) (.snd .v0)).eval ρ₂ =
        (pm.map (·.2)).getD default := by
      rcases pm with _ | ⟨pub, plain⟩ <;>
        simp [ρ₂, simOpsUnitCost, Expr.eval, Expr.v0]
    have hacc := onAcceptFigE_eval P Dh encPt encT decT lam K toKemCoins L qep
        (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2))) (.fst (.snd (.snd (.snd .v2))))
        (.fst .v0) (.fst (.snd .v0))
        (.caseOpt (.snd (.snd .v0)) (Expr.op (O := OFig) SimOp.defaultPlain .unit) (.snd .v0))
        (.fst (.snd (.snd (.snd (.snd .v2)))))
        (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v2)))))))
        ρ₂ st Q hBound rfl rfl
    rw [hacc, hm]
    rfl

omit [SampleableType PQC] in
theorem honestCFigE_eval (L : ℕ) {Γ} (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (w : Expr OFig Γ (.base .wire)) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party) (w₀ : List (BitVec 8))
    (hHonest : st.honest.length ≤ L)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q)
    (hw : w.eval ρ = w₀) :
    (honestCFigE P Dh encPt encT decT lam K toKemCoins L s qParty w).eval ρ =
      (st.honest.find? fun wc =>
        wc.1 == w₀ && Party.senderOf wc.2.1.1 == Q.other).map (·.2) := by
  unfold honestCFigE
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair qParty w)).eval ρ = (simStateEnc st, partyEnc Q, w₀) := by
    simp [Expr.eval, hs, hq, hw]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod simStateTy (.prod .bool (.base SimSort.wire)))
    (simStateEnc st, partyEnc Q, w₀) ρ
  have ht : st.honest.take L = st.honest := List.take_of_length_le hHonest
  have hfind :
      (Expr.findB L (ssHonest (.fst (Expr.v0 (O := OFig))))
        (.and
          (Expr.op (O := OFig) SimOp.eqWire (.pair (.fst .v0) (.snd (.snd .v1))))
          (boolEq (senderOfE (.fst (.fst (.snd .v0)))) (otherE (.fst (.snd .v1)))))).eval ρ₁ =
      st.honest.find? fun wc => wc.1 == w₀ && Party.senderOf wc.2.1.1 == Q.other := by
    have hHon : (ssHonest (.fst (Expr.v0 (O := OFig)))).eval ρ₁ = st.honest := rfl
    simp only [Expr.eval, hHon, ht]
    congr 1; funext wc
    let ρ₂ := Env.cons (t := .prod (.base SimSort.wire) (fig8CTy PQ PQC Pt ℓ)) wc ρ₁
    have hsnd : (senderOfE (O' := OFig) (.fst (.fst (.snd .v0)))).eval ρ₂ =
        partyEnc (Party.senderOf wc.2.1.1) :=
      senderOfE_eval (O' := OFig) (.fst (.fst (.snd .v0))) ρ₂
    have hoth : (otherE (O' := OFig) (.fst (.snd .v1))).eval ρ₂ = partyEnc Q.other := by
      simp [ρ₂, ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v1]
    have hbeq := boolEq_eval (O' := OFig)
      (senderOfE (.fst (.fst (.snd .v0)))) (otherE (.fst (.snd .v1))) ρ₂
    rw [hbeq, hsnd, hoth, partyEnc_beq]
    rfl
  rw [expr_caseOpt_eval, hfind]
  rcases h : st.honest.find? (fun wc => wc.1 == w₀ && Party.senderOf wc.2.1.1 == Q.other) with
    _ | wc <;> simp [h, Expr.eval, Expr.v0]

omit [SampleableType PQC] in
theorem mkCFigE_eval {Γ} (honestC : Expr OFig Γ (.opt (fig8CTy PQ PQC Pt ℓ)))
    (lct : Expr OFig Γ (.base .lct)) (t : Expr OFig Γ .nat) (T? : Expr OFig Γ (.opt (.base .pt)))
    (ρ : Env Γ) :
    (mkCFigE P Dh encPt encT decT lam K toKemCoins honestC lct t T?).eval ρ =
      match honestC.eval ρ with
      | some c => if c.2.2.2 = (lct.eval ρ).2.2 then c else ((t.eval ρ, T?.eval ρ), lct.eval ρ)
      | none => ((t.eval ρ, T?.eval ρ), lct.eval ρ) := by
  unfold mkCFigE
  rw [letE_eval]
  rcases h : honestC.eval ρ with _ | c
  · simp [h, Expr.eval, Expr.v0]
  · simp [h, simOpsUnitCost, Expr.eval, Expr.v0, Expr.v1]

omit [SampleableType PQC] in
theorem ambCondFigE_eval {Γ} (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hChains : (st.chains Q).length ≤ 5)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (ambCondFigE P Dh encPt encT decT lam K toKemCoins s qParty).eval ρ =
      (inReceiveOnlyEpoch st.mir Q || (Q == Party.A && (st.chains Q).any (·.key.isNone))) := by
  unfold ambCondFigE
  have hp : (pGet (ssChains s) qParty).eval ρ = (st.chains Q).map ghostChainEnc := by
    rw [pGet_eval]
    cases Q <;> simp [ssChains, hs, hq, simStateEnc, partyEnc, Expr.eval]
  have hhas := hasUnknownKeyFigE_eval P Dh encPt encT decT lam K toKemCoins
    (pGet (ssChains s) qParty) ρ (st.chains Q) hChains hp
  rw [orE_eval,
    mInWinE_eval (O' := OFig) (ssMir s) qParty ρ st.mir Q
      (by simp [ssMir, hs, simStateEnc]) hq]
  congr 1
  dsimp only [Expr.eval]
  rw [hhas, hq]
  cases Q <;> rfl

omit [SampleableType PQC] in
theorem sAmbFigE_eval {Γ} (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hChains : (st.chains Q).length ≤ 5)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (sAmbFigE P Dh encPt encT decT lam K toKemCoins s qParty).eval ρ =
      simStateEnc
        (if inReceiveOnlyEpoch st.mir Q || (Q == Party.A && (st.chains Q).any (·.key.isNone))
         then { st with amb := st.amb + 1 }
         else st) := by
  unfold sAmbFigE
  rw [ite_eval, ambCondFigE_eval P Dh encPt encT decT lam K toKemCoins s qParty ρ st Q
    hChains hs hq]
  split_ifs
  · rw [ssSetAmb_eval s (.add (ssAmb s) (.nat 1)) ρ st hs]
    simp [ssAmb, hs, simStateEnc, Expr.eval]
  · exact hs

omit [SampleableType PQC] in
theorem evictedHonestFigE_eval {Γ} (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (honestC : Expr OFig Γ (.opt (fig8CTy PQ PQC Pt ℓ))) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (evictedHonestFigE P Dh encPt encT decT lam K toKemCoins s qParty honestC).eval ρ =
      ((honestC.eval ρ).map (fun c => decide (c.1.1 ≠ st.mir.epoch Q + 1)) == some true) := by
  unfold evictedHonestFigE
  rw [letE_eval, expr_caseOpt_eval]
  rcases h : honestC.eval ρ with _ | c
  · simp [h, Expr.eval]
  · cases Q <;>
      simp [h, hs, hq, mEpoch, ssMir, pGet_eval, simStateEnc, simMirEnc, partyEnc,
        Option.some_beq_some, decide_not, Expr.eval, Expr.v0, Expr.v1]

omit [SampleableType PQC] in
theorem honestSaltEqFigE_eval {Γ} (honestC : Expr OFig Γ (.opt (fig8CTy PQ PQC Pt ℓ)))
    (lct : Expr OFig Γ (.base .lct)) (ρ : Env Γ) :
    (honestSaltEqFigE P Dh encPt encT decT lam K toKemCoins honestC lct).eval ρ =
      ((honestC.eval ρ).map (fun c => decide (c.2.2.2 = (lct.eval ρ).2.2)) == some true) := by
  unfold honestSaltEqFigE
  rw [letE_eval, expr_caseOpt_eval]
  rcases h : honestC.eval ρ with _ | c
  · simp [h, Expr.eval]
  · simp [h, simOpsUnitCost, Option.some_beq_some, Expr.eval, Expr.v0, Expr.v1]

omit [SampleableType PQC] in
@[simp] theorem keptUnknownE_eval {Γ} (ρ : Env Γ) :
    keptDec ((keptUnknownE (O' := OFig) (Γ := Γ)).eval ρ) =
      (Kept.unknown : Kept Pt) := by
  rfl

omit [SampleableType PQC] in
@[simp] theorem keptOfStE_eval {Γ} (st : Expr OFig Γ (.base .fig8st)) (ρ : Env Γ) :
    keptDec ((keptOfStE st).eval ρ) = Kept.ofSt (st.eval ρ) := by
  rfl

omit [SampleableType PQC] in
@[simp] theorem keptRsAtE_eval {Γ} (k : Expr OFig Γ keptTy) (t : Expr OFig Γ .nat) (ρ : Env Γ) :
    (keptRsAtE P Dh encPt encT decT lam K toKemCoins k t).eval ρ =
      (keptDec (k.eval ρ)).rs (t.eval ρ) := by
  unfold keptRsAtE keptDec
  rw [letE_eval]
  rcases hk : k.eval ρ with ⟨full, baseSt, ov⟩
  simp only [hk, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, simOpsUnitCost]
  cases ov (t.eval ρ) <;> cases baseSt <;> rfl

omit [SampleableType PQC] in
@[simp] theorem keptSendE_eval {Γ} (B : ℕ) (k : Expr OFig Γ keptTy) (ρ : Env Γ) :
    keptDec ((keptSendE P Dh encPt encT decT lam K toKemCoins B k).eval ρ) =
      Kept.send
        (fig := lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
        (keptDec (k.eval ρ)) := by
  unfold keptSendE Kept.send keptDec
  rw [letE_eval, expr_caseOpt_eval]
  rcases hk : k.eval ρ with ⟨full, baseSt, ov⟩
  rcases full with _ | st
  · simp [Expr.eval, Expr.v0]
  · simp only [Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, simOpsUnitCost]
    cases st.id.sendsIn (st.tcur + 1) <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem keptDec_tset_none (baseSt : Option (SimFig8St Pt))
    (ov : ℕ → Option (Option (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))))
    (t₀ : ℕ) (v' : Option (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))) :
    keptDec (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)
      (none, baseSt, fun j => if j = t₀ then some v' else ov j) =
    { (keptDec (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) (none, baseSt, ov)) with
      rs := Function.update
        (keptDec (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) (none, baseSt, ov)).rs t₀ v' } := by
  unfold keptDec
  dsimp only
  congr 1
  funext j
  by_cases hj : j = t₀
  · subst hj; simp [Function.update_self]
  · simp [hj]

omit [SampleableType PQC] in
@[simp] theorem keptRecvE_eval {Γ} (B : ℕ) (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ))
    (k : Expr OFig Γ keptTy) (ρ : Env Γ) :
    keptDec ((keptRecvE P Dh encPt encT decT lam K toKemCoins B c k).eval ρ) =
      Kept.recv
        (fig := lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
        (fs := lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000)
        (c.eval ρ) (keptDec (k.eval ρ)) := by
  unfold keptRecvE Kept.recv
  rw [letE_eval, expr_caseOpt_eval]
  rcases hk : k.eval ρ with ⟨full, baseSt, ov⟩
  rcases full with _ | st
  · simp only [hk, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
      keptRsAtE_eval, simOpsUnitCost]
    rw [keptDec_tset_none]
    change ({ full := none, rs := Function.update _ (c.eval ρ).1.1 _ } : Kept Pt) =
      ({ full := none, rs := Function.update _ (c.eval ρ).1.1 _ } : Kept Pt)
    congr 2
    cases hrs : (keptDec (none, baseSt, ov)).rs (c.eval ρ).1.1 with
    | none => rfl
    | some v =>
      simp only [Option.bind]
      cases hfs : (lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000).receive
          v (c.eval ρ).1 (c.eval ρ).2 with
      | none => rfl
      | some vip => rfl
  · simp only [hk, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
      simOpsUnitCost]
    rcases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam).receive
        st (c.eval ρ) with _ | ⟨st', t, i, pm⟩ <;>
      simp only [hfig, Option.map, keptDec, Expr.eval, Expr.v2,
        Env.get_cons_zero, Env.get_cons_succ]

/-- `B`-clamped `SMScheme` wrapper matching `SimOp.fig8SendStep B` and `SimOp.fig8Receive B`. -/
def fig8Clamp (B : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (SimFig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) :
    SMScheme (BitVec 256 × BitVec 256) (SimFig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) :=
  { fig with
    send := fun st m r =>
      let (st', c) := fig.send st m r
      (st', ((min c.1.1 B, c.1.2), c.2))
    receive := fun st c =>
      (fig.receive st c).map fun (st', t, i, pm) => (st', min t B, min i B, pm) }

/-- `B`-clamped `FSAEADScheme` wrapper matching `SimOp.fsReceive B`. -/
def fsClampSim (B : ℕ)
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) :
    FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) :=
  { fs with
    receive := fun v hdr ct =>
      (fs.receive v hdr ct).map fun (v', i, pm) => (v', min i B, pm) }

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp]
theorem snapEnc_snapDec (e : (@snapEntryTy PQ PQC Pt ℓ).denote) :
    snapEnc (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) (snapDec e) = e := by
  rcases e with ⟨b, ep, g⟩
  cases b <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp]
theorem scBase_eval {O' : Ops S} {Γ} (sC : Expr O' Γ simStateCTy) (ρ : Env Γ) :
    (scBase sC).eval ρ = simStateEnc (simStateCDec (sC.eval ρ)).base := by
  simp [scBase, simStateCDec, simStateEnc_simStateDec]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp]
theorem scSent_eval {O' : Ops S} {Γ} (sC : Expr O' Γ simStateCTy) (ρ : Env Γ) :
    (scSent sC).eval ρ = (simStateCDec (sC.eval ρ)).sent := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp]
theorem scSnaps_eval {O' : Ops S} {Γ} (sC : Expr O' Γ simStateCTy) (ρ : Env Γ) :
    (scSnaps sC).eval ρ =
      (simStateCDec (sC.eval ρ)).snaps.map
        (snapEnc (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) := by
  simp [scSnaps, simStateCDec, Expr.eval, List.map_map, Function.comp_def]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem scKept_pGet_eval {O' : Ops S} {Γ}
    (sC : Expr O' Γ simStateCTy) (q : Expr O' Γ .bool) (ρ : Env Γ) :
    keptDec ((pGet (scKept sC) q).eval ρ) =
      (simStateCDec (sC.eval ρ)).kept (partyDec (q.eval ρ)) := by
  cases hq : q.eval ρ <;>
    simp [scKept, pGet_eval, hq, partyDec, simStateCDec, Expr.eval]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem scKept_pGet_fst_eval {O' : Ops S} {Γ}
    (sC : Expr O' Γ simStateCTy) (q : Expr O' Γ .bool) (ρ : Env Γ) :
    ((pGet (scKept sC) q).eval ρ).1 =
      ((simStateCDec (sC.eval ρ)).kept (partyDec (q.eval ρ))).full := by
  rw [← scKept_pGet_eval]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp]
theorem scSetBase_eval {O' : Ops S} {Γ}
    (sC : Expr O' Γ simStateCTy) (b : Expr O' Γ simStateTy) (ρ : Env Γ)
    (base' : SimState PQ Pt ℓ) (hb : b.eval ρ = simStateEnc base') :
    simStateCDec ((scSetBase sC b).eval ρ) =
      { simStateCDec (sC.eval ρ) with base := base' } := by
  simp [scSetBase, scMk, scKept, scSent, scSnaps, simStateCDec, hb, Expr.eval, Expr.v0]

omit [SampleableType PQC] in
theorem keptEvalE_eval {Γ} (B : ℕ)
    (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ))
    (k : Expr OFig Γ keptTy) (ρ : Env Γ) :
    (keptEvalE P Dh encPt encT decT lam K toKemCoins B c k).eval ρ =
      Kept.eval
        (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam))
        (fs := fsClampSim B (lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000))
        (c.eval ρ) (keptDec (k.eval ρ)) := by
  unfold keptEvalE Kept.eval
  rw [letE_eval, expr_caseOpt_eval]
  rcases hk : k.eval ρ with ⟨full, baseSt, ov⟩
  rcases full with _ | st
  · simp only [hk, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
      keptRsAtE_eval, simOpsUnitCost, fsClampSim]
    have hfull : (keptDec (none, baseSt, ov)).full = none := rfl
    rw [hfull]
    rcases hrs : (keptDec (none, baseSt, ov)).rs (c.eval ρ).1.1 with _ | v
    · rfl
    · dsimp only [Option.map, Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]
      rcases (lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000).receive
          v (c.eval ρ).1 (c.eval ρ).2 with _ | ⟨v', i, pm⟩ <;> rfl
  · simp only [hk, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
      simOpsUnitCost, fig8Clamp]
    have hfull : (keptDec (some st, baseSt, ov)).full = some st := rfl
    rw [hfull]
    dsimp only [Option.map, Expr.eval, Expr.v0, Env.get_cons_zero, Env.get_cons_succ]
    rcases (lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam).receive
        st (c.eval ρ) with _ | ⟨st', t, i, pm⟩ <;> rfl

omit [SampleableType PQC] in
theorem sentEvalE_eval {Γ} (L B : ℕ)
    (sent : Expr OFig Γ (.list (.prod (fig8CTy PQ PQC Pt ℓ) (.base .vsSt))))
    (c c' : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) (ρ : Env Γ)
    (hL : (sent.eval ρ).length ≤ L) :
    (sentEvalE P Dh encPt encT decT lam K toKemCoins L B sent c c').eval ρ =
      sentEval
        (fs := fsClampSim B (lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000))
        (sent.eval ρ) (c.eval ρ) (c'.eval ρ) := by
  unfold sentEvalE sentEval
  rw [letE_eval, expr_caseOpt_eval]
  have htake : (sent.eval ρ).take L = sent.eval ρ := List.take_of_length_le hL
  have hfind :
      (Expr.findB L (.fst (Expr.v0 (O := OFig)))
        (Expr.op (O := OFig) SimOp.eqFig8C (.pair (.fst .v0) (.fst (.snd .v1))))).eval
        (Env.cons (sent.eval ρ, c.eval ρ, c'.eval ρ) ρ) =
      List.find? (fun (e : Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256)) =>
        decide (e.1 = c.eval ρ)) (sent.eval ρ) := by
    simp only [Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
      htake, simOpsUnitCost]
  rw [expr_pair_eval, expr_pair_eval, hfind]
  rcases List.find? (fun (e : Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256)) =>
      decide (e.1 = c.eval ρ)) (sent.eval ρ) with _ | ⟨c0, u⟩
  · rfl
  · dsimp only [Option.map, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
      Env.get_cons_zero, Env.get_cons_succ, simOpsUnitCost, fsClampSim]
    rcases (lFS P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000).receive
        ⟨u.chainKey, u.lastIndex, []⟩ (c'.eval ρ).1 (c'.eval ρ).2 with _ | ⟨v', i, pm⟩ <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem orElseOptE_eval {O' : Ops S} {Γ α} (x y : Expr O' Γ (.opt α)) (ρ : Env Γ) :
    (orElseOptE x y).eval ρ = (x.eval ρ <|> y.eval ρ) := by
  unfold orElseOptE
  rw [expr_caseOpt_eval]
  cases x.eval ρ <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem foldrB_caseOpt_eval {O' : Ops S} {Γ} {α β : Ty S} (L : ℕ)
    (xs : Expr O' Γ (.list α))
    (body : Expr O' (α :: .opt β :: Γ) (.opt β))
    (ρ : Env Γ) (ls : List α.denote)
    (hxs : (xs.eval ρ).take L = ls)
    (f : α.denote → Option β.denote)
    (hbody : ∀ x acc, body.eval (Env.cons x (Env.cons acc ρ)) = f x) :
    (Expr.foldrB L xs .none
      (.caseOpt body .v1 (.some .v0))).eval ρ =
      ls.findSome? f := by
  simp only [Expr.eval, hxs, hbody, Env.get_cons_zero, Env.get_cons_succ, Expr.v0, Expr.v1]
  clear hxs
  induction ls with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.foldr_cons, List.findSome?_cons]
    cases f x with
    | none => exact ih
    | some v => rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem foldrB_caseOpt_keep_eval {O' : Ops S} {Γ} {α β : Ty S} (L : ℕ)
    (xs : Expr O' Γ (.list α))
    (body : Expr O' (α :: .opt α :: Γ) (.opt β))
    (ρ : Env Γ) (ls : List α.denote)
    (hxs : (xs.eval ρ).take L = ls)
    (f : α.denote → Option β.denote)
    (hbody : ∀ x acc, body.eval (Env.cons x (Env.cons acc ρ)) = f x) :
    (Expr.foldrB L xs .none
      (.caseOpt body .v1 (.some .v1))).eval ρ =
      ls.findSome? (fun x => (f x).map fun _ => x) := by
  simp only [Expr.eval, hxs, hbody, Env.get_cons_zero, Env.get_cons_succ, Expr.v1]
  clear hxs
  induction ls with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.foldr_cons, List.findSome?_cons]
    cases f x with
    | none => exact ih
    | some v => rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem findSome_map {α β γ : Type} (xs : List α) (g : α → β) (f : β → Option γ) :
    (xs.map g).findSome? f = xs.findSome? (fun x => f (g x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.findSome?_cons, ih]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem simChainKeyAfter_eq (F : ShaCompress) (n : ℕ) (k : BitVec 256) :
    simChainKeyAfter F n k = chainKeyAfter F n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => exact ih _

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem simChainSeedAt_eq (F : ShaCompress) (ck : LibsignalSession.ChainKey)
    (counter : BitVec 32) :
    simChainSeedAt F ck counter = chainSeedAt F ck counter := by
  simp [simChainSeedAt, chainSeedAt, simChainKeyAfter_eq]

omit [SampleableType PQC] in
theorem knownSeedRE_eval {Γ} (L : ℕ)
    (snaps : Expr OFig Γ (.list snapEntryTy))
    (qB : Expr OFig Γ .bool) (t : Expr OFig Γ .nat) (w : Expr OFig Γ (.base .wire))
    (ρ : Env Γ) (s_snaps : List (Party × ℕ × GhostState PQ))
    (hsnaps : snaps.eval ρ =
      s_snaps.map (snapEnc (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)))
    (hL : s_snaps.length ≤ L) :
    (knownSeedRE P Dh encPt encT decT lam K toKemCoins L snaps qB t w).eval ρ =
      snapshotMessageKeySeed P s_snaps (partyDec (qB.eval ρ)) (t.eval ρ) (w.eval ρ) := by
  let sEnc := snapEnc (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)
  have hlen : (snaps.eval ρ).length ≤ L := by rw [hsnaps, List.length_map]; exact hL
  have htake : (snaps.eval ρ).take L = s_snaps.map sEnc := by
    rw [List.take_of_length_le hlen, hsnaps]
  unfold knownSeedRE
  rw [letE_eval, orElseOptE_eval, orElseOptE_eval, orElseOptE_eval]
  dsimp only [expr_pair_eval]
  set ρ₁ := Env.cons
    (t := .prod (.list snapEntryTy) (.prod .bool (.prod .nat (.base .wire))))
    (snaps.eval ρ, qB.eval ρ, t.eval ρ, w.eval ρ) ρ
  have htake0 : ((Expr.fst (Expr.v0 (O := OFig))).eval ρ₁).take L = s_snaps.map sEnc := htake
  have hbr : ∀ br : ℕ,
      (Expr.foldrB L (.fst (Expr.v0 (O := OFig))) .none
        (.caseOpt
          (Expr.op (O := OFig) SimOp.snapSeed
            (.pair (.nat br)
              (.pair (.fst (.snd .v2))
                (.pair (.snd (.snd (.snd .v2)))
                  (.pair (.fst (.snd (.snd .v2))) (.pair .v0 .none))))))
          .v1
          (.some .v0))).eval ρ₁ =
      s_snaps.findSome? (fun e =>
        simSnapSeed P br (qB.eval ρ) (w.eval ρ) (t.eval ρ) (sEnc e) none) := by
    intro br
    rw [foldrB_caseOpt_eval L (.fst .v0) _ ρ₁ (s_snaps.map sEnc) htake0
      (fun x => simSnapSeed P br (qB.eval ρ) (w.eval ρ) (t.eval ρ) x none)
      (fun x acc => by simp [ρ₁, Expr.eval, Expr.v0, Expr.v2, simOpsUnitCost]),
      findSome_map]
  have hcur :
      (Expr.foldrB L (.fst (Expr.v0 (O := OFig))) .none
        (.caseOpt
          (Expr.op (O := OFig) SimOp.snapSeed
            (.pair (.nat 4)
              (.pair (.fst (.snd .v2))
                (.pair (.snd (.snd (.snd .v2)))
                  (.pair (.fst (.snd (.snd .v2))) (.pair .v0 .none))))))
          .v1
          (.some .v1))).eval ρ₁ =
      s_snaps.findSome? (fun e =>
        (simSnapSeed P 4 (qB.eval ρ) (w.eval ρ) (t.eval ρ) (sEnc e) none).map
          fun _ => sEnc e) := by
    rw [foldrB_caseOpt_keep_eval L (.fst .v0) _ ρ₁ (s_snaps.map sEnc) htake0
      (fun x => simSnapSeed P 4 (qB.eval ρ) (w.eval ρ) (t.eval ρ) x none)
      (fun x acc => by simp [ρ₁, Expr.eval, Expr.v0, Expr.v2, simOpsUnitCost]),
      findSome_map]
  have hk4 :
      (Expr.caseOpt
        (.foldrB L (.fst (Expr.v0 (O := OFig))) .none
          (.caseOpt
            (Expr.op (O := OFig) SimOp.snapSeed
              (.pair (.nat 4)
                (.pair (.fst (.snd .v2))
                  (.pair (.snd (.snd (.snd .v2)))
                    (.pair (.fst (.snd (.snd .v2))) (.pair .v0 .none))))))
            .v1
            (.some .v1)))
        .none
        (.foldrB L (.fst .v1) .none
          (.caseOpt
            (Expr.op (O := OFig) SimOp.snapSeed
              (.pair (.nat 3)
                (.pair (.fst (.snd .v3))
                  (.pair (.snd (.snd (.snd .v3)))
                    (.pair (.fst (.snd (.snd .v3)))
                      (.pair .v2 (.some .v0)))))))
            .v1
            (.some .v0)))).eval ρ₁ =
      (s_snaps.findSome? (fun e =>
        (simSnapSeed P 4 (qB.eval ρ) (w.eval ρ) (t.eval ρ) (sEnc e) none).map
          fun _ => sEnc e)).bind (fun x =>
        s_snaps.findSome? (fun e2 =>
          simSnapSeed P 3 (qB.eval ρ) (w.eval ρ) (t.eval ρ) x (some (sEnc e2)))) := by
    rw [expr_caseOpt_eval, hcur]
    cases s_snaps.findSome? (fun e =>
        (simSnapSeed P 4 (qB.eval ρ) (w.eval ρ) (t.eval ρ) (sEnc e) none).map
          fun _ => sEnc e) with
    | none => rfl
    | some x =>
      dsimp only [Option.bind]
      have htake1 : ((Expr.fst (Expr.v1 (O := OFig))).eval (Env.cons x ρ₁)).take L =
          s_snaps.map sEnc := htake
      rw [foldrB_caseOpt_eval L (.fst .v1) _ (Env.cons x ρ₁) (s_snaps.map sEnc) htake1
        (fun y => simSnapSeed P 3 (qB.eval ρ) (w.eval ρ) (t.eval ρ) x (some y))
        (fun y acc2 => by simp [ρ₁, Expr.eval, Expr.v0, Expr.v2, Expr.v3, simOpsUnitCost]),
        findSome_map]
  rw [hbr 0, hbr 1, hbr 2, hk4]
  unfold snapshotMessageKeySeed simSnapSeed
  cases SignalMessage.tryFrom P.codec (w.eval ρ) with
  | error err => simp
  | ok msg =>
    simp only [sEnc, snapEnc, partyDec_partyEnc, simChainSeedAt_eq,
      Nat.reduceEqDiff, ↓reduceIte]
    congr 1; funext ⟨⟩
    congr 1; funext ⟨⟩
    congr 1; funext ⟨⟩
    suffices h4 : ∀ xs : List (Party × ℕ × GhostState PQ),
        (List.findSome? (fun (e : Party × ℕ × GhostState PQ) =>
          Option.map (fun _ => (partyEnc e.1, e.2.1, e.2.2))
            (if e.1 = (partyDec (qB.eval ρ)).other ∧ e.2.1 = t.eval ρ then
              e.2.2.session.senderChain.bind fun sc_cur =>
                if sc_cur.ratchetKey.publicKey = msg.senderRatchetKey then
                  e.2.2.session.receiverChains.getLast?.map fun _ => []
                else none
            else none)) xs).bind (fun x =>
          List.findSome? (fun (e2 : Party × ℕ × GhostState PQ) =>
            if partyDec x.1 = (partyDec (qB.eval ρ)).other ∧ x.2.1 = t.eval ρ then
              x.2.2.session.senderChain.bind fun sc_cur =>
                if sc_cur.ratchetKey.publicKey = msg.senderRatchetKey then
                  x.2.2.session.receiverChains.getLast?.bind fun rc_last =>
                    if e2.1 = (partyDec (qB.eval ρ)).other ∧
                        (partyDec (qB.eval ρ)).other.sendsIn e2.2.1 = true ∧
                        t.eval ρ = e2.2.1 + 2 then
                      e2.2.2.session.senderChain.bind fun sc_prev =>
                        match rootCreateChain P.C e2.2.2.session.rootKey
                            rc_last.senderRatchetKey sc_prev.ratchetKey.privateKey with
                        | .ok (rk1, _) =>
                          match rootCreateChain P.C rk1 rc_last.senderRatchetKey
                              sc_cur.ratchetKey.privateKey with
                          | .ok (_, ck0) => chainSeedAt P.C.F ck0 msg.counter
                          | .error _ => none
                        | .error _ => none
                    else none
                else none
            else none) s_snaps) =
        (List.findSome? (fun (e_cur : Party × ℕ × GhostState PQ) =>
          if e_cur.1 = (partyDec (qB.eval ρ)).other ∧ e_cur.2.1 = t.eval ρ then
            e_cur.2.2.session.senderChain.bind fun sc_cur =>
              if sc_cur.ratchetKey.publicKey = msg.senderRatchetKey then
                e_cur.2.2.session.receiverChains.getLast?.map fun rc_last =>
                  (rc_last.senderRatchetKey, sc_cur.ratchetKey.privateKey)
              else none
          else none) xs).bind (fun p =>
          List.findSome? (fun (e_prev : Party × ℕ × GhostState PQ) =>
            if e_prev.1 = (partyDec (qB.eval ρ)).other ∧
                (partyDec (qB.eval ρ)).other.sendsIn e_prev.2.1 = true ∧
                t.eval ρ = e_prev.2.1 + 2 then
              e_prev.2.2.session.senderChain.bind fun sc_prev =>
                match rootCreateChain P.C e_prev.2.2.session.rootKey
                    p.1 sc_prev.ratchetKey.privateKey with
                | .ok (rk1, _) =>
                  match rootCreateChain P.C rk1 p.1 p.2 with
                  | .ok (_, ck0) => chainSeedAt P.C.F ck0 msg.counter
                  | .error _ => none
                | .error _ => none
            else none) s_snaps) from h4 s_snaps
    intro xs
    induction xs with
    | nil => rfl
    | cons e tl ih =>
      rcases e with ⟨eP, eEp, eG⟩
      simp only [List.findSome?_cons]
      by_cases h1 : eP = (partyDec (qB.eval ρ)).other ∧ eEp = t.eval ρ
      · simp only [h1, and_self, ↓reduceIte]
        cases hsc : eG.session.senderChain with
        | none => simp [Option.bind]; exact ih
        | some sc =>
          dsimp only [Option.bind]
          by_cases hpk : sc.ratchetKey.publicKey = msg.senderRatchetKey
          · simp only [hpk, ↓reduceIte]
            cases hrc : eG.session.receiverChains.getLast? with
            | none => simp; exact ih
            | some rc =>
              dsimp only [Option.map, Option.bind]
              simp only [partyDec_partyEnc, and_self, ↓reduceIte, hsc, hpk, hrc]
          · simp [hpk]; exact ih
      · simp [h1]; exact ih

def evalCKClamp (B : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party)
    (w : List (BitVec 8)) (c c' : SimFig8C Pt) :
    Option (Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :=
  let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
  let fs := fsClampSim B (lFS P.C P.codec ℓ encT idOf 25000)
  (predictReceive (fig := fig) (fs := fs) sC Q c c').orElse fun _ =>
    (snapshotMessageKeySeed P sC.snaps Q c.1.1 w).map (simKDecryptFig8 P ℓ B (partyEnc Q) w c')

omit [SampleableType PQC] in
theorem evalCKE_eval {Γ} (L B : ℕ)
    (sC : Expr OFig Γ simStateCTy) (qB : Expr OFig Γ .bool)
    (w : Expr OFig Γ (.base .wire)) (c c' : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ))
    (ρ : Env Γ)
    (hSent : (simStateCDec (sC.eval ρ)).sent.length ≤ L)
    (hSnaps : (simStateCDec (sC.eval ρ)).snaps.length ≤ L) :
    (evalCKE P Dh encPt encT decT lam K toKemCoins L B sC qB w c c').eval ρ =
      evalCKClamp P Dh encPt encT lam B
        (simStateCDec (sC.eval ρ)) (partyDec (qB.eval ρ))
        (w.eval ρ) (c.eval ρ) (c'.eval ρ) := by
  unfold evalCKE evalCKClamp predictReceive
  rw [letE_eval, orElseOptE_eval, orElseOptE_eval]
  dsimp only [expr_pair_eval]
  set ρ₁ := Env.cons
    (t := .prod simStateCTy (.prod .bool (.prod (.base .wire)
      (.prod (fig8CTy PQ PQC Pt ℓ) (fig8CTy PQ PQC Pt ℓ)))))
    (sC.eval ρ, qB.eval ρ, w.eval ρ, c.eval ρ, c'.eval ρ) ρ
  have hk := keptEvalE_eval P Dh encPt encT decT lam K toKemCoins B
    (.snd (.snd (.snd (.snd .v0)))) (pGet (scKept (.fst .v0)) (.fst (.snd .v0))) ρ₁
  have hkp : keptDec ((pGet (scKept (.fst (Expr.v0 (O := OFig)))) (.fst (.snd .v0))).eval ρ₁) =
      (simStateCDec (sC.eval ρ)).kept (partyDec (qB.eval ρ)) :=
    scKept_pGet_eval (.fst .v0) (.fst (.snd .v0)) ρ₁
  rw [hkp] at hk
  have hs := sentEvalE_eval P Dh encPt encT decT lam K toKemCoins L B
    (scSent (.fst .v0)) (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
    ρ₁ hSent
  have hks := knownSeedRE_eval P Dh encPt encT decT lam K toKemCoins L
    (scSnaps (.fst .v0)) (.fst (.snd .v0))
    (.fst (.fst (.fst (.snd (.snd (.snd .v0)))))) (.fst (.snd (.snd .v0)))
    ρ₁ (simStateCDec (sC.eval ρ)).snaps (scSnaps_eval (.fst .v0) ρ₁) hSnaps
  rw [expr_caseOpt_eval, hk, hs, hks]
  dsimp only [ρ₁, scSent_eval, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    simOpsUnitCost]
  rw [partyEnc_partyDec]
  cases Kept.eval
    (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam))
    (fs := fsClampSim B (lFS P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000))
    (c'.eval ρ) ((simStateCDec (sC.eval ρ)).kept (partyDec (qB.eval ρ))) <;>
  cases sentEval
    (fs := fsClampSim B (lFS P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000))
    (simStateCDec (sC.eval ρ)).sent (c.eval ρ) (c'.eval ρ) <;>
  cases snapshotMessageKeySeed P (simStateCDec (sC.eval ρ)).snaps (partyDec (qB.eval ρ))
    (c.eval ρ).1.1 (w.eval ρ) <;>
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem scMk_pSet_kept_eval {O' : Ops S} {Γ}
    (b : Expr O' Γ simStateTy) (sC : Expr O' Γ simStateCTy)
    (q : Expr O' Γ .bool) (k' : Expr O' Γ keptTy)
    (sent : Expr O' Γ (.list (.prod (fig8CTy PQ PQC Pt ℓ) (.base .vsSt))))
    (snaps : Expr O' Γ (.list snapEntryTy)) (ρ : Env Γ)
    (base' : SimState PQ Pt ℓ) (hb : b.eval ρ = simStateEnc base') :
    simStateCDec ((scMk b (pSet (scKept sC) q k') sent snaps).eval ρ) =
      { base := base'
        kept := Function.update (simStateCDec (sC.eval ρ)).kept (partyDec (q.eval ρ))
          (keptDec (k'.eval ρ))
        sent := sent.eval ρ
        snaps := (snaps.eval ρ).map snapDec } := by
  simp only [scMk, simStateCDec, hb, simStateDec_simStateEnc, Expr.eval]
  congr 1
  funext R
  cases hq : q.eval ρ <;> cases R <;>
    simp [pSet, scKept, partyDec, hq, Function.update, Expr.eval, Expr.v0]

def scPostSendPure (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s₁ : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (Q : Party) (m₀ : Plain ℓ) (isChall : Bool) (pq' : PQ)
    (pn5 : BitVec 32) (c : SimFig8C Pt) : LibsignalToModularSchemeSimState PQ Pt ℓ :=
  let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let w := toWire c
  let rec' : Record (Plain ℓ) (List (BitVec 8)) :=
    ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
  let mir' := s₁.record 3 Q () rec' isChall
  let base' : SimState PQ Pt ℓ :=
    { sC.base with
      mir := mir'
      pq := Function.update sC.base.pq Q pq'
      pn := Function.update sC.base.pn Q pn5
      honest := (w, c) :: sC.base.honest }
  let sent' := match (sC.kept Q).full with
    | some st =>
      if st.id.sendsIn (st.tcur + 1) then sC.sent
      else match st.vS with
        | some v => (c, v) :: sC.sent
        | none => sC.sent
    | none => sC.sent
  { sC with
    base := base'
    kept := Function.update sC.kept Q (Kept.send (fig := fig) (sC.kept Q))
    sent := sent' }

omit [SampleableType PQC] in
theorem scPostSendE_eval {Γ} (B : ℕ)
    (sC : Expr OFig Γ simStateCTy) (s1 : Expr OFig Γ simMirTy)
    (q0 : Expr OFig Γ .bool) (m0 : Expr OFig Γ (.base .plain))
    (isChall : Expr OFig Γ .bool) (pq' : Expr OFig Γ (.base .pq))
    (pn5 : Expr OFig Γ (.base .u32)) (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ))
    (ρ : Env Γ)
    (s₁ : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (hs₁ : s1.eval ρ = simMirEnc s₁) :
    ((scPostSendE P Dh encPt encT decT lam K toKemCoins B
      sC s1 q0 m0 isChall pq' pn5 c).eval ρ).1 = toWire (c.eval ρ) ∧
    simStateCDec (((scPostSendE P Dh encPt encT decT lam K toKemCoins B
      sC s1 q0 m0 isChall pq' pn5 c).eval ρ).2) =
      scPostSendPure P Dh encPt encT lam (simStateCDec (sC.eval ρ)) s₁
        (partyDec (q0.eval ρ)) (m0.eval ρ) (isChall.eval ρ) (pq'.eval ρ)
        (pn5.eval ρ) (c.eval ρ) := by
  unfold scPostSendE scPostSendPure
  rw [letE_eval]
  set ρ₁ := Env.cons
    (t := .prod simStateCTy (.prod simMirTy (.prod .bool (.prod (.base .plain)
      (.prod .bool (.prod (.base .pq) (.prod (.base .u32) (fig8CTy PQ PQC Pt ℓ))))))))
    (sC.eval ρ, s1.eval ρ, q0.eval ρ, m0.eval ρ, isChall.eval ρ, pq'.eval ρ,
      pn5.eval ρ, c.eval ρ) ρ
  refine ⟨rfl, ?_⟩
  dsimp only [expr_pair_eval]
  have hrec :
      (mRecordE (.fst (.snd (Expr.v0 (O := OFig)))) (.fst (.snd (.snd .v0)))
        (.pair (.pair (.fst (.snd (.snd .v0)))
          (.pair (pGet (mEpoch (.fst (.snd .v0))) (.fst (.snd (.snd .v0))))
            (.add (pGet (mIdx (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))) (.nat 1))))
          (.pair (.fst (.snd (.snd (.snd .v0))))
            (Expr.op (O := OFig) SimOp.toWire
              (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))))
        (.fst (.snd (.snd (.snd (.snd .v0)))))).eval ρ₁ =
      simMirEnc (s₁.record 3 (partyDec (q0.eval ρ)) ()
        ⟨⟨partyDec (q0.eval ρ), s₁.epoch (partyDec (q0.eval ρ)),
          s₁.idx (partyDec (q0.eval ρ)) + 1⟩, m0.eval ρ, toWire (c.eval ρ)⟩
        (isChall.eval ρ)) := by
    apply mRecordE_eval
    · exact hs₁
    · exact (partyEnc_partyDec (q0.eval ρ)).symm
    · cases hq0 : q0.eval ρ <;>
        simp [ρ₁, hs₁, hq0, mEpoch, mIdx, pGet_eval, simMirEnc, simRecEnc, posEnc,
          partyDec, partyEnc, simOpsUnitCost, simToWire, toWire, simTagBytes, tagBytes,
          Expr.eval, Expr.v0, Env.get_cons_zero]
  have hbase :
      (ssMk
        (mRecordE (.fst (.snd (Expr.v0 (O := OFig)))) (.fst (.snd (.snd .v0)))
          (.pair (.pair (.fst (.snd (.snd .v0)))
            (.pair (pGet (mEpoch (.fst (.snd .v0))) (.fst (.snd (.snd .v0))))
              (.add (pGet (mIdx (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))) (.nat 1))))
            (.pair (.fst (.snd (.snd (.snd .v0))))
              (Expr.op (O := OFig) SimOp.toWire
                (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))))
          (.fst (.snd (.snd (.snd (.snd .v0))))))
        (pSet (ssPq (scBase (.fst .v0))) (.fst (.snd (.snd .v0)))
          (.fst (.snd (.snd (.snd (.snd (.snd .v0)))))))
        (pSet (ssPn (scBase (.fst .v0))) (.fst (.snd (.snd .v0)))
          (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
        (ssUnackA (scBase (.fst .v0)))
        (.cons (.pair
          (Expr.op (O := OFig) SimOp.toWire
            (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
          (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
          (ssHonest (scBase (.fst .v0))))
        (ssChains (scBase (.fst .v0)))
        (ssAmb (scBase (.fst .v0)))
        (ssStopped (scBase (.fst .v0)))).eval ρ₁ =
      simStateEnc
        { (simStateCDec (sC.eval ρ)).base with
          mir := s₁.record 3 (partyDec (q0.eval ρ)) ()
            ⟨⟨partyDec (q0.eval ρ), s₁.epoch (partyDec (q0.eval ρ)),
              s₁.idx (partyDec (q0.eval ρ)) + 1⟩, m0.eval ρ, toWire (c.eval ρ)⟩
            (isChall.eval ρ)
          pq := Function.update (simStateCDec (sC.eval ρ)).base.pq
            (partyDec (q0.eval ρ)) (pq'.eval ρ)
          pn := Function.update (simStateCDec (sC.eval ρ)).base.pn
            (partyDec (q0.eval ρ)) (pn5.eval ρ)
          honest := (toWire (c.eval ρ), c.eval ρ) ::
            (simStateCDec (sC.eval ρ)).base.honest } := by
    simp only [ssMk, expr_pair_eval, hrec, pSet_eval]
    cases hq0 : q0.eval ρ <;>
      simp [ρ₁, hq0, scBase_eval, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped,
        partyDec, Function.update, simOpsUnitCost, simToWire, toWire, simTagBytes, tagBytes,
        simStateEnc, Expr.eval, Expr.v0, Env.get_cons_zero]
  rw [scMk_pSet_kept_eval _ _ _ _ _ _ ρ₁ _ hbase]
  have hkept :
      keptDec ((keptSendE P Dh encPt encT decT lam K toKemCoins B
        (pGet (scKept (.fst .v0)) (.fst (.snd (.snd .v0))))).eval ρ₁) =
      Kept.send
        (fig := lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
        ((simStateCDec (sC.eval ρ)).kept (partyDec (q0.eval ρ))) := by
    rw [keptSendE_eval, scKept_pGet_eval]
    rfl
  rw [hkept]
  have hsnaps :
      List.map snapDec ((scSnaps (.fst (Expr.v0 (O := OFig)))).eval ρ₁) =
        (simStateCDec (sC.eval ρ)).snaps := by
    simp [ρ₁, scSnaps_eval, List.map_map, Function.comp_def, snapDec_snapEnc, Expr.eval, Expr.v0]
  rw [hsnaps]
  congr 1
  · rw [expr_caseOpt_eval]
    have hfull :
        ((Expr.fst (pGet (scKept (.fst (Expr.v0 (O := OFig))))
          (.fst (.snd (.snd .v0))))).eval ρ₁) =
        ((simStateCDec (sC.eval ρ)).kept (partyDec (q0.eval ρ))).full :=
      scKept_pGet_fst_eval (.fst .v0) (.fst (.snd (.snd .v0))) ρ₁
    rw [hfull]
    rcases ((simStateCDec (sC.eval ρ)).kept (partyDec (q0.eval ρ))).full with _ | st
    · rfl
    · simp only [ρ₁, scSent_eval, simOpsUnitCost, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
        Env.get_cons_zero, Env.get_cons_succ]
      split_ifs
      · rfl
      · rcases st.vS with _ | v <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem expr_caseOpt_some_eval {S' : Sig} {O' : Ops S'} {Γ} {t u : Ty S'}
    (e : Expr O' Γ (.opt t)) (noneB : Expr O' Γ u) (someB : Expr O' (t :: Γ) u)
    (ρ : Env Γ) (x : t.denote) (he : e.eval ρ = some x) :
    (Expr.caseOpt e noneB someB).eval ρ = someB.eval (Env.cons x ρ) := by
  rw [expr_caseOpt_eval, he]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem expr_caseSum_inr_eval {S' : Sig} {O' : Ops S'} {Γ} {a b u : Ty S'}
    (e : Expr O' Γ (.sum a b)) (inlB : Expr O' (a :: Γ) u) (inrB : Expr O' (b :: Γ) u)
    (ρ : Env Γ) (y : b.denote) (he : e.eval ρ = Sum.inr y) :
    (Expr.caseSum e inlB inrB).eval ρ = inrB.eval (Env.cons y ρ) := by
  simp [Expr.eval, he]

omit [SampleableType PQC] in
theorem scPostFwdKeptE_eval {Γ} (B : ℕ)
    (sC : Expr OFig Γ simStateCTy) (q : Expr OFig Γ .bool)
    (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ))
    (res : Expr OFig Γ (.opt (fig8RrTy PQ PQC Pt ℓ))) (ρ : Env Γ)
    (res₀ : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hres : res.eval ρ = res₀.map SM.smRrEnc) :
    simStateCDec
      ((scPostFwdKeptE P Dh encPt encT decT lam K toKemCoins B sC q c res).eval ρ) =
    match res₀ with
    | some (.accepted _ _ _) =>
      { simStateCDec (sC.eval ρ) with
        kept := Function.update (simStateCDec (sC.eval ρ)).kept (partyDec (q.eval ρ))
          (Kept.recv
            (fig := lFig8 Dh encPt P.C P.codec ℓ encT
              (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
            (fs := lFS P.C P.codec ℓ encT
              (fun R => if R == Party.A then P.idA else P.idB) 25000)
            (c.eval ρ) ((simStateCDec (sC.eval ρ)).kept (partyDec (q.eval ρ)))) }
    | _ => simStateCDec (sC.eval ρ) := by
  unfold scPostFwdKeptE
  rw [letE_eval]
  dsimp only [expr_pair_eval]
  set ρ₁ := Env.cons
    (t := .prod simStateCTy (.prod .bool (.prod (fig8CTy PQ PQC Pt ℓ)
      (.opt (fig8RrTy PQ PQC Pt ℓ)))))
    (sC.eval ρ, q.eval ρ, c.eval ρ, res.eval ρ) ρ
  rcases res₀ with _ | (_ | ⟨t, i, m⟩)
  · rw [expr_caseOpt_eval,
      show (Expr.snd (.snd (.snd (Expr.v0 (O := OFig))))).eval ρ₁ = none from hres]
    rfl
  · rw [expr_caseOpt_some_eval _ _ _ ρ₁ (Sum.inl ()) hres]
    rfl
  · rw [expr_caseOpt_some_eval _ _ _ ρ₁ (Sum.inr (t, i, m)) hres,
      expr_caseSum_inr_eval _ _ _ _ (t, i, m) rfl]
    set ρ₂ := Env.cons (t := .prod .nat (.prod .nat (.opt (lpubPlainTy PQ PQC Pt ℓ))))
      (t, i, m) (Env.cons (t := fig8RrTy PQ PQC Pt ℓ) (Sum.inr (t, i, m)) ρ₁)
    rw [scMk_pSet_kept_eval _ _ _ _ _ _ ρ₂ _ (scBase_eval (.fst .v2) ρ₂)]
    simp only [ρ₂, ρ₁, keptRecvE_eval, scKept_pGet_eval, scSent_eval, scSnaps_eval,
      List.map_map, Function.comp_def, snapDec_snapEnc, List.map_id',
      Expr.eval, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem findIdx_go_eq_map {α : Type} (p : α → Bool) (xs : List α) (k : ℕ) :
    List.findIdx?.go p xs k = (xs.findIdx? p).map (· + k) := by
  induction xs generalizing k with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.findIdx?, List.findIdx?.go]
    split_ifs with h
    · simp
    · rw [ih (k + 1), ih 1, Option.map_map]
      congr 1; funext j; dsimp; omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem findIdx_cons_eq {α : Type} (p : α → Bool) (a : α) (tl : List α) :
    (a :: tl).findIdx? p = if p a then some 0 else (tl.findIdx? p).map (· + 1) := by
  simp only [List.findIdx?, List.findIdx?.go]
  split_ifs with h
  · rfl
  · exact findIdx_go_eq_map p tl 1

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem findIdx_append_singleton {α : Type} (p : α → Bool) (ys : List α) (x : α) :
    (ys ++ [x]).findIdx? p =
      match ys.findIdx? p with
      | none => if p x then some ys.length else none
      | some i => some i := by
  induction ys with
  | nil =>
    simp only [List.nil_append, List.length_nil, findIdx_cons_eq, List.findIdx?_nil]
    split_ifs <;> rfl
  | cons y ys ih =>
    simp only [List.cons_append, findIdx_cons_eq, List.length_cons, ih]
    cases hy : p y <;> cases ys.findIdx? p <;> cases hx : p x <;> simp

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem foldr_findIdx_rev {α : Type} (p : α → Bool) (xs : List α) :
    xs.foldr (fun x (acc : ℕ × Option ℕ) =>
      (acc.1 + 1, match acc.2 with
        | none => if p x then some acc.1 else none
        | some i => some i)) (0, none) =
    (xs.length, xs.reverse.findIdx? p) := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.foldr_cons, ih, List.length_cons, List.reverse_cons,
      findIdx_append_singleton, List.length_reverse]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem expr_foldrB_eval {O' : Ops S} {Γ} {α β : Ty S} (L : ℕ)
    (xs : Expr O' Γ (.list α)) (init : Expr O' Γ β)
    (step : Expr O' (α :: β :: Γ) β) (ρ : Env Γ) :
    (Expr.foldrB L xs init step).eval ρ =
      ((xs.eval ρ).take L).foldr
        (fun x acc => step.eval (Env.cons x (Env.cons acc ρ)))
        (init.eval ρ) := rfl

omit [SampleableType PQC] in
theorem findRevHonestIdxE_eval {Γ} (L : ℕ)
    (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (w : Expr OFig Γ (.base .wire)) (ρ : Env Γ)
    (hHon : (simStateDec (s.eval ρ)).honest.length ≤ L) :
    (findRevHonestIdxE P Dh encPt encT decT lam K toKemCoins L s qParty w).eval ρ =
      (simStateDec (s.eval ρ)).honest.reverse.findIdx? (fun wc =>
        wc.1 == w.eval ρ && Party.senderOf wc.2.1.1 == (partyDec (qParty.eval ρ)).other) := by
  unfold findRevHonestIdxE
  rw [letE_eval]
  dsimp only [expr_pair_eval]
  set ρ₁ := Env.cons (t := .prod simStateTy (.prod .bool (.base .wire)))
    (s.eval ρ, qParty.eval ρ, w.eval ρ) ρ
  have hs : (ssHonest (.fst (Expr.v0 (O := OFig)))).eval ρ₁ =
      (simStateDec (s.eval ρ)).honest := by
    simp [ρ₁, ssHonest, simStateDec, Expr.eval, Expr.v0]
  have htake : ((ssHonest (.fst (Expr.v0 (O := OFig)))).eval ρ₁).take L =
      (simStateDec (s.eval ρ)).honest := by
    rw [hs]; exact List.take_of_length_le hHon
  have hfold :
      (Expr.foldrB L (ssHonest (.fst (Expr.v0 (O := OFig)))) (.pair (.nat 0) .none)
        (let matchHere : Expr OFig _ .bool :=
           .and
             (Expr.op (O := OFig) SimOp.eqWire (.pair (.fst .v0) (.snd (.snd .v2))))
             (boolEq (senderOfE (.fst (.fst (.snd .v0)))) (otherE (.fst (.snd .v2))))
         let idxPrev : Expr OFig _ .nat := .fst .v1
         let foundPrev : Expr OFig _ (.opt .nat) := .snd .v1
         .pair (.add idxPrev (.nat 1))
           (.caseOpt foundPrev
             (.ite matchHere (.some idxPrev) .none)
             (.some .v0)))).eval ρ₁ =
      List.foldr
        (fun (wc : List (BitVec 8) × SimFig8C Pt) (acc : ℕ × Option ℕ) =>
          (acc.1 + 1,
            match acc.2 with
            | none =>
              if (wc.1 == w.eval ρ &&
                  Party.senderOf wc.2.1.1 == (partyDec (qParty.eval ρ)).other) then
                some acc.1
              else none
            | some i => some i))
        (0, none) (simStateDec (s.eval ρ)).honest := by
    rw [expr_foldrB_eval, htake]
    congr 1; funext wc ⟨acc1, acc2⟩
    let ρ₂ := Env.cons (t := .prod (.base SimSort.wire) (fig8CTy PQ PQC Pt ℓ)) wc
      (Env.cons (t := .prod .nat (.opt .nat)) (acc1, acc2) ρ₁)
    rw [expr_pair_eval]
    refine Prod.ext rfl ?_
    rw [expr_caseOpt_eval]
    have hacc2 : (Expr.snd (Expr.v1 (O := OFig))).eval ρ₂ = acc2 := rfl
    rw [hacc2]
    cases acc2 with
    | some i => rfl
    | none =>
      have hsnd : (senderOfE (O' := OFig) (.fst (.fst (.snd .v0)))).eval ρ₂ =
          partyEnc (Party.senderOf wc.2.1.1) :=
        senderOfE_eval (O' := OFig) (.fst (.fst (.snd .v0))) ρ₂
      have hoth : (otherE (O' := OFig) (.fst (.snd .v2))).eval ρ₂ =
          partyEnc (partyDec (qParty.eval ρ)).other := by
        simp [ρ₂, ρ₁, otherE, partyEnc_other, partyEnc_partyDec, Expr.eval, Expr.v2]
      have hbeq := boolEq_eval (O' := OFig)
        (senderOfE (.fst (.fst (.snd .v0)))) (otherE (.fst (.snd .v2))) ρ₂
      rw [ite_eval]
      have hcond : (Expr.and
          (Expr.op (O := OFig) SimOp.eqWire (.pair (.fst .v0) (.snd (.snd .v2))))
          (boolEq (senderOfE (.fst (.fst (.snd .v0)))) (otherE (.fst (.snd .v2))))).eval ρ₂ =
          (wc.1 == w.eval ρ && Party.senderOf wc.2.1.1 == (partyDec (qParty.eval ρ)).other) := by
        rw [Expr.eval, hbeq, hsnd, hoth, partyEnc_beq]
        rfl
      rw [hcond]
      split_ifs <;> rfl
  exact (congrArg Prod.snd hfold).trans
    (congrArg Prod.snd (foldr_findIdx_rev _ (simStateDec (s.eval ρ)).honest))

omit [SampleableType PQC] in
theorem initSimCE_eval {Γ} (pqrKey : Expr OFig Γ (.base .bv256)) (ρ : Env Γ) :
    simStateCDec ((initSimCE P Dh encPt encT decT lam K toKemCoins pqrKey).eval ρ) =
      initSimC (P.spqr.init .a2b (pqrKey.eval ρ)) (P.spqr.init .b2a (pqrKey.eval ρ)) := by
  unfold initSimCE initSimC
  rw [letE_eval]
  have hbase :
      (ssMk initSimMirE
        (.pair (Expr.op (O := OFig) SimOp.spqrInitA .v0)
          (Expr.op (O := OFig) SimOp.spqrInitB .v0))
        (.pair (Expr.op (O := OFig) SimOp.zeroU32 .unit)
          (Expr.op (O := OFig) SimOp.zeroU32 .unit))
        (.bool true) .nil
        (.pair (.cons (initChainAFigE P Dh encPt encT decT lam K toKemCoins) .nil) .nil)
        (.nat 0) (.bool false)).eval (Env.cons (pqrKey.eval ρ) ρ) =
      simStateEnc (initSim (P.spqr.init .a2b (pqrKey.eval ρ))
        (P.spqr.init .b2a (pqrKey.eval ρ))) := by
    simp [initChainAFigE, initSimMirE, initSim, ssMk, mMk, simOpsUnitCost,
      simStateEnc, simMirEnc, ghostChainEnc, Expr.eval, Expr.v0]
    rfl
  simp only [scMk, simStateCDec, Expr.eval, hbase, simStateDec_simStateEnc,
    keptUnknownE_eval, List.map_nil]
  congr 1
  funext Q; cases Q <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem fsClampSim_receive_eq (B : ℕ)
    (idOf : Party → IdentityKey)
    (v : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
    (hdr : Header Pt) (ct : ℕ × LibsignalCiphertextWithSalt32) (hi : ct.1 ≤ B) :
    (fsClampSim B (lFS P.C P.codec ℓ encT idOf 25000)).receive v hdr ct =
      (lFS P.C P.codec ℓ encT idOf 25000).receive v hdr ct := by
  dsimp only [fsClampSim, lFS, FSAEAD.fromAEADPRG]
  rcases ct with ⟨i, e⟩
  dsimp only at hi ⊢
  rcases v.skippedKeys.lookup i with _ | key
  · dsimp only []
    split_ifs
    · rfl
    · rcases ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        ((lChainPRG P.C.F (i - 1)).gen
          (FSAEAD.skipKeys (lChainPRG P.C.F) (i - v.lastIndex - 1)
            v.chainKey v.lastIndex v.skippedKeys).1).2
        (i, hdr) e with _ | pm
      · rfl
      · simp [Option.map, Nat.min_eq_left hi]
  · dsimp only []
    rcases ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        key (i, hdr) e with _ | pm
    · rfl
    · simp [Option.map, Nat.min_eq_left hi]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem lFS_receive_index_eq
    (idOf : Party → IdentityKey)
    (v v' : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
    (hdr : Header Pt) (ct : ℕ × LibsignalCiphertextWithSalt32) (i_out : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : (lFS P.C P.codec ℓ encT idOf 25000).receive v hdr ct = some (v', i_out, pm)) :
    i_out = ct.1 := by
  dsimp only [lFS, FSAEAD.fromAEADPRG] at h
  rcases ct with ⟨i, e⟩
  dsimp only at h ⊢
  rcases hlk : v.skippedKeys.lookup i with _ | key
  · rw [hlk] at h
    dsimp only [] at h
    split_ifs at h
    rcases hdec : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        ((lChainPRG P.C.F (i - 1)).gen
          (FSAEAD.skipKeys (lChainPRG P.C.F) (i - v.lastIndex - 1)
            v.chainKey v.lastIndex v.skippedKeys).1).2
        (i, hdr) e with _ | pm'
    · rw [hdec] at h; cases h
    · rw [hdec] at h
      injection h with h
      injection h with _ h2
      injection h2 with h2 _
      exact h2.symm
  · rw [hlk] at h
    dsimp only [] at h
    rcases hdec : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        key (i, hdr) e with _ | pm'
    · rw [hdec] at h; cases h
    · rw [hdec] at h
      injection h with h
      injection h with _ h2
      injection h2 with h2 _
      exact h2.symm

omit [DecidableEq Pt] [SampleableType PQC] in
theorem lFig8_receive_epoch_index_eq
    (idOf : Party → IdentityKey)
    (st st' : SimFig8St Pt) (c' : SimFig8C Pt) (t_out i_out : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c' =
      some (st', t_out, i_out, pm)) :
    t_out = c'.1.1 ∧ i_out = c'.2.1 := by
  dsimp only [lFig8, SM.Construction.scheme, SM.Construction.receive] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i s₁ _
      split at h
      · cases h
      · rename_i v _
        rcases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive v c'.1 c'.2 with
          _ | ⟨v', i', pm'⟩
        · rw [hfs] at h; cases h
        · rw [hfs] at h
          dsimp only [] at h
          have hi' := lFS_receive_index_eq P encT idOf v v' c'.1 c'.2 i' pm' hfs
          injection h with h
          injection h with _ h2
          injection h2 with ht_out h3
          injection h3 with hi_out _
          exact ⟨ht_out.symm, hi_out.symm.trans hi'⟩

omit [DecidableEq Pt] [SampleableType PQC] in
theorem fig8Clamp_receive_eq (B : ℕ)
    (idOf : Party → IdentityKey)
    (st : SimFig8St Pt) (c' : SimFig8C Pt)
    (ht : c'.1.1 ≤ B) (hi : c'.2.1 ≤ B) :
    (fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)).receive st c' =
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c' := by
  dsimp only [fig8Clamp]
  rcases h : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c' with
    _ | ⟨st', t_out, i_out, pm⟩
  · rfl
  · obtain ⟨rfl, rfl⟩ := lFig8_receive_epoch_index_eq P Dh encPt encT lam idOf st st' c'
      t_out i_out pm h
    simp [Option.map, Nat.min_eq_left ht, Nat.min_eq_left hi]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem simKDecryptFig8_eq_kDecryptFig8 (B : ℕ) (Q : Party)
    (w : List (BitVec 8)) (c' : SimFig8C Pt) (seed : List (BitVec 8))
    (ht : c'.1.1 ≤ B) (hi : c'.2.1 ≤ B) :
    simKDecryptFig8 P ℓ B (partyEnc Q) w c' seed =
      kDecryptFig8 P ℓ Q w c' seed := by
  dsimp only [simKDecryptFig8, kDecryptFig8, decryptWithKnownSeed]
  rw [partyDec_partyEnc]
  rcases lPubOf P.codec c'.2.2 with _ | pub
  · rfl
  · rcases SignalMessage.tryFrom P.codec w with _ | msg
    · rfl
    · dsimp only [Except.toOption, Option.bind]
      split_ifs <;> try rfl
      all_goals
        cases aesCbcDecrypt P.C.D
          (deriveMessageKeys P.C.F (some c'.2.2.2) seed).1.1
          (deriveMessageKeys P.C.F (some c'.2.2.2) seed).1.2
          msg.ciphertext <;>
        simp [Nat.min_eq_left ht, Nat.min_eq_left hi]

omit [DecidableEq Pt] [SampleableType PQC] in
theorem kept_eval_fig8Clamp_eq (B : ℕ) (idOf : Party → IdentityKey)
    (k : Kept Pt) (c' : SimFig8C Pt)
    (ht : c'.1.1 ≤ B) (hi : c'.2.1 ≤ B) :
    Kept.eval
      (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam))
      (fs := fsClampSim B (lFS P.C P.codec ℓ encT idOf 25000))
      c' k =
    Kept.eval
      (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000)
      c' k := by
  unfold Kept.eval
  rcases k.full with _ | st <;> dsimp only []
  · congr 1; funext v
    rw [fsClampSim_receive_eq P encT B idOf v c'.1 c'.2 hi]
  · rw [fig8Clamp_receive_eq P Dh encPt encT lam B idOf st c' ht hi]

omit [Zero Pt] [SampleableType PQC] in
theorem sentEval_fsClampSim_eq (B : ℕ) (idOf : Party → IdentityKey)
    (sent : List (SimFig8C Pt × FSAEAD.RatchetSenderState (BitVec 256)))
    (c c' : SimFig8C Pt) (hi : c'.2.1 ≤ B) :
    sentEval (fs := fsClampSim B (lFS P.C P.codec ℓ encT idOf 25000)) sent c c' =
      sentEval (fs := lFS P.C P.codec ℓ encT idOf 25000) sent c c' := by
  unfold sentEval
  congr 1; funext e
  rw [fsClampSim_receive_eq P encT B idOf ⟨e.2.chainKey, e.2.lastIndex, []⟩ c'.1 c'.2 hi]

omit [SampleableType PQC] in
theorem evalCKClamp_eq_evalCK (B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : List (BitVec 8))
    (c c' : SimFig8C Pt)
    (ht : c'.1.1 ≤ B) (hi : c'.2.1 ≤ B) :
    evalCKClamp P Dh encPt encT lam B sC Q w c c' =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' := by
  unfold evalCKClamp predictReceiveWithSnapshots predictReceive
  dsimp only []
  rw [kept_eval_fig8Clamp_eq P Dh encPt encT lam B _ (sC.kept Q) c' ht hi,
    sentEval_fsClampSim_eq P encT B _ sC.sent c c' hi]
  have hkd : simKDecryptFig8 P ℓ B (partyEnc Q) w c' = kDecryptFig8 P ℓ Q w c' :=
    funext fun seed => simKDecryptFig8_eq_kDecryptFig8 P B Q w c' seed ht hi
  rw [hkd]

def kemCoinsEnc : CryptoVerification.SpqrV1Sync.Braid.Coins → SimKemCoins
  | .init => .init
  | .seed s => .seed s
  | .both s r => .both s r

def kemTrackEnc {F : ShaCompress}
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState F) :
    SimKemFailTrack F :=
  { e := tr.e
    auth := tr.auth
    c := kemCoinsEnc tr.c
    st := tr.st
    sentB := tr.sentB
    sendCtr := tr.sendCtr
    cand := tr.cand }

@[simp]
theorem kemCoinsEnc_nextCoins (F : ShaCompress)
    (c : CryptoVerification.SpqrV1Sync.Braid.Coins)
    (st : SimBraidSt F) (tape : List (BitVec 8)) :
    kemCoinsEnc (CryptoVerification.SpqrV1Sync.Braid.nextCoins F c st tape) =
      simNextKemCoins F (kemCoinsEnc c) st tape := by
  cases c <;> cases st <;>
    simp only [CryptoVerification.SpqrV1Sync.Braid.nextCoins, simNextKemCoins, kemCoinsEnc]
  all_goals
    split_ifs <;> rfl

theorem simEkSideIsA_bne_eq (e : BitVec 64) (Q : Party) :
    (simEkSideIsA e != (Q == .A)) =
      (CryptoVerification.SpqrV1Sync.Braid.ekSide e !=
        CryptoGames.LibsignalSM.Proofs.Refinement.kemBraidParty Q) := by
  cases Q <;>
    by_cases h : e.toNat % 2 = 1 <;>
    simp only [simEkSideIsA, CryptoVerification.SpqrV1Sync.Braid.ekSide,
      CryptoGames.LibsignalSM.Proofs.Refinement.kemBraidParty, h, ↓reduceIte] <;>
    decide

@[simp]
theorem simStepKemFailSend_kemTrackEnc (F : ShaCompress)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState F)
    (Q : Party) (r : BitVec 512) :
    simStepKemFailSend F K (kemTrackEnc tr) Q r =
      kemTrackEnc (CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend F K tr Q r) := by
  unfold simStepKemFailSend CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend
  dsimp only [kemTrackEnc]
  rcases (tr.st Q).send K (CryptoVerification.LibsignalSpqrV1.coinBytes r) with err | ⟨out, _⟩ <;>
    simp only [kemCoinsEnc_nextCoins, simEkSideIsA_bne_eq] <;>
    congr 1 <;>
    rcases tr.cand with _ | p <;>
    rcases tr.c with _ | s | ⟨s, r₀⟩ <;>
    rcases tr.st Q <;>
    rfl

@[simp]
theorem simStepKemFailDeliver_kemTrackEnc (F : ShaCompress)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState F)
    (Q : Party) (j : ℕ) :
    simStepKemFailDeliver F K (kemTrackEnc tr) Q j =
      kemTrackEnc (CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailDeliver F K tr Q j) := by
  unfold simStepKemFailDeliver CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailDeliver
  dsimp only [kemTrackEnc]
  rcases tr.sentB[j]? with _ | ⟨m, ctr⟩
  · rfl
  · dsimp only []
    rcases (tr.st Q).recv K m with err | out
    · rfl
    · dsimp only [CryptoVerification.SpqrV1Sync.Braid.noneMsg]
      by_cases hm : m = { epoch := tr.e + 1#64, payload := .none }
      · rcases tr.c with _ | s | ⟨s, r₀⟩ <;>
          simp [hm, kemCoinsEnc, simAuthNext,
            CryptoVerification.SpqrV1Sync.Braid.authNext,
            CryptoVerification.SpqrV1Sync.Braid.secOf,
            CryptoVerification.SpqrV1Sync.Braid.ss0Of,
            CryptoVerification.SpqrV1Sync.Braid.encOf,
            CryptoVerification.SpqrV1Sync.InSync.hdrOf,
            simBe64, CryptoVerification.SpqrV1Sync.Braid.be64]
      · simp [hm]

def onAcceptPure (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    Option (RecvResult (Plain ℓ)) × SimState PQ Pt ℓ :=
  let cs := match ci? with
    | some ci => (s.chains Q).modify ci (·.accept i)
    | none => pushChain (s.chains Q) (GhostChain.accept ⟨some T, t, 0, []⟩ i)
  let s' := { s with
    chains := Function.update s.chains Q cs
    pq := Function.update s.pq Q pq'
    unackA := s.unackA && Q != Party.A }
  if isDel then
    match s.mir.inTransit Q.other w with
    | none => (none, s)
    | some r =>
      (some (.accepted t i (if s.mir.chall.contains r.pos then none else some m)),
        { s' with mir := s.mir.accept Q () r.pos })
  else
    if qep + 1 < t then (some .rejected, s)
    else
      let pos : SM.Pos := ⟨Q.other, t, i⟩
      if s.mir.trivial 3 pos then
        (some (.accepted t i (some m)), { s' with mir := s.mir.accept Q () pos })
      else
        (some .rejected, { s with mir := { s.mir with win := true } })

def onAnswerPure (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    Option (RecvResult (Plain ℓ)) × SimState PQ Pt ℓ :=
  match res with
  | some (.accepted t i pm) =>
    onAcceptPure qep Q w isDel t i ((pm.map (·.2)).getD default) ci? T pq' s
  | _ => (some .rejected, s)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem onAccept_run_eq_pure (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    (onAccept qep Q w isDel t i m ci? T pq').run s =
      pure (onAcceptPure qep Q w isDel t i m ci? T pq' s) := by
  unfold onAccept onAcceptPure
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> rfl
  · simp only [↓reduceIte]
    rcases s.mir.inTransit Q.other w with _ | r <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem onAnswer_run_eq_pure (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    (onAnswer qep Q w isDel ci? T pq' res).run s =
      pure (onAnswerPure qep Q w isDel ci? T pq' res s) := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · rfl
  · rfl
  · exact onAccept_run_eq_pure qep Q w isDel t i ((pm.map (·.2)).getD default) ci? T pq' s

omit [SampleableType PQC] in
theorem onAcceptFigE_eval_pure (L qep : ℕ) {Γ}
    (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (w : Expr OFig Γ (.base .wire)) (isDel : Expr OFig Γ .bool)
    (t i : Expr OFig Γ .nat) (m : Expr OFig Γ (.base .plain))
    (ciOpt : Expr OFig Γ (.opt .nat)) (T : Expr OFig Γ (.base .pk))
    (pq' : Expr OFig Γ (.base .pq)) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hBound : SimStateBounded L st)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (onAcceptFigE P Dh encPt encT decT lam K toKemCoins L qep
      s qParty w isDel t i m ciOpt T pq').eval ρ =
    Prod.map (Option.map SM.smRrEnc) simStateEnc
      (onAcceptPure qep Q (w.eval ρ) (isDel.eval ρ) (t.eval ρ) (i.eval ρ) (m.eval ρ)
        (ciOpt.eval ρ) (T.eval ρ) (pq'.eval ρ) st) := by
  have h := onAcceptFigE_eval P Dh encPt encT decT lam K toKemCoins L qep
    s qParty w isDel t i m ciOpt T pq' ρ st Q hBound hs hq
  rw [onAccept_run_eq_pure, map_pure] at h
  injection h

omit [SampleableType PQC] in
theorem onAnswerFigE_eval_pure (L qep : ℕ) {Γ}
    (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (w : Expr OFig Γ (.base .wire)) (isDel : Expr OFig Γ .bool)
    (ciOpt : Expr OFig Γ (.opt .nat)) (T : Expr OFig Γ (.base .pk))
    (pq' : Expr OFig Γ (.base .pq))
    (resE : Expr OFig Γ (.opt (fig8RrTy PQ PQC Pt ℓ))) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hBound : SimStateBounded L st)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q)
    (hres : resE.eval ρ = res.map SM.smRrEnc) :
    (onAnswerFigE P Dh encPt encT decT lam K toKemCoins L qep
      s qParty w isDel ciOpt T pq' resE).eval ρ =
    Prod.map (Option.map SM.smRrEnc) simStateEnc
      (onAnswerPure qep Q (w.eval ρ) (isDel.eval ρ) (ciOpt.eval ρ) (T.eval ρ) (pq'.eval ρ)
        res st) := by
  have h := onAnswerFigE_eval P Dh encPt encT decT lam K toKemCoins L qep
    s qParty w isDel ciOpt T pq' resE ρ st Q res hBound hs hq hres
  rw [onAnswer_run_eq_pure, map_pure] at h
  injection h

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem onAcceptPure_preserves_inv (qep L m : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (msg : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (st : SimState PQ Pt ℓ) (hInv : SimStateInv L m st) :
    SimStateInv L m (onAcceptPure qep Q w isDel t i msg ci? T pq' st).2 := by
  have h := onAccept_preserves_inv qep L m Q w isDel t i msg ci? T pq' st hInv
    (onAcceptPure qep Q w isDel t i msg ci? T pq' st)
  rw [onAccept_run_eq_pure] at h
  exact h (by simp)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem onAnswerPure_preserves_inv (qep L m : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (st : SimState PQ Pt ℓ) (hInv : SimStateInv L m st) :
    SimStateInv L m (onAnswerPure qep Q w isDel ci? T pq' res st).2 := by
  have h := onAnswer_preserves_inv qep L m Q w isDel ci? T pq' res st hInv
    (onAnswerPure qep Q w isDel ci? T pq' res st)
  rw [onAnswer_run_eq_pure] at h
  exact h (by simp)

/-- List-length bounds on `LibsignalToModularSchemeSimState PQ Pt ℓ` required for `L`-bounded `simHandleHookC`. -/
structure SimCStateBounded (L : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) : Prop where
  base : SimStateBounded L sC.base
  sent_le : sC.sent.length ≤ L
  snaps_le : sC.snaps.length ≤ L

/-- Query-budget invariant on `LibsignalToModularSchemeSimState PQ Pt ℓ` with `m` adversary queries remaining. -/
def SimCStateInv (L m : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) : Prop :=
  SimStateInv L m sC.base ∧ sC.sent.length + m ≤ L ∧ sC.snaps.length + m ≤ L

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem SimCStateInv.mono {L m₁ m₂ : ℕ} {sC : LibsignalToModularSchemeSimState PQ Pt ℓ}
    (hle : m₁ ≤ m₂) (h : SimCStateInv L m₂ sC) : SimCStateInv L m₁ sC :=
  ⟨h.1.mono hle, by have := h.2.1; omega, by have := h.2.2; omega⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem SimCStateInv.toBounded {L m : ℕ} {sC : LibsignalToModularSchemeSimState PQ Pt ℓ}
    (h : SimCStateInv L m sC) : SimCStateBounded L sC := by
  rcases h.1.2.2.2.1 with ⟨U, hUlen, hCU, htrU⟩
  exact ⟨{ trans_le := by have := h.1.1; omega
           chall_le := by have := h.1.2.1; omega
           honest_le := by have := h.1.2.2.1; omega
           comp_u := ⟨U, by omega, hCU, htrU⟩
           chainsA_le := h.1.2.2.2.2.1
           chainsB_le := h.1.2.2.2.2.2 },
         by have := h.2.1; omega,
         by have := h.2.2; omega⟩

/-- Semantic hook callbacks over extra state `Ex` in `OracleComp T`. -/
structure SemHook (PQC Pt : Type) (ℓ : ℕ) {ι : Type} (T : OracleSpec ι) (Ex : Type) where
  sampleBv256 : OracleComp T (BitVec 256)
  samplePqc : OracleComp T PQC
  onSendCoins : Party → PQC → Ex → OracleComp T (Ex × Ex)
  onTr : Party → LibsignalMsgPublicPart × Plain ℓ → Option (BitVec 256) → Ex →
    OracleComp T (Option (SimFig8C Pt) × Ex)
  onCh : Party → LibsignalMsgPublicPart × Plain ℓ → LibsignalMsgPublicPart × Plain ℓ → Option (BitVec 256) → Ex →
    OracleComp T (Option (SimFig8C Pt) × Ex)
  onDl : Party → SimFig8C Pt → Ex →
    OracleComp T (Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) × Ex)
  onIj : Party → SimFig8C Pt → Ex →
    OracleComp T (Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) × Ex)
  onCr : Party → Ex → OracleComp T (Option (SimFig8St Pt) × Ex)
  onProbe : Party → SimFig8C Pt → Ex → OracleComp T Ex
  onDeliverPost : Party → Option ℕ → Option (RecvResult (Plain ℓ)) → Ex → OracleComp T Ex

/-- Stepwise evaluation agreement between `SimHookC` and `SemHook`. -/
structure HookMatch {ι : Type} {T : OracleSpec ι} {I : Iface S T} {σExtra : Ty S}
    {Ex : Type} (exEnc : Ex → σExtra.denote) (ExBound : ℕ → Ex → Prop) (L : ℕ)
    (hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra)
    (sh : SemHook PQC Pt ℓ T Ex) : Prop where
  sampleBv256_eval : ∀ {Γ} (ρ : Env Γ), hk.sampleBv256.eval ρ = sh.sampleBv256
  samplePqc_eval : ∀ {Γ} (ρ : Env Γ), hk.samplePqc.eval ρ = sh.samplePqc
  onSendCoins_eval : ∀ {Γ} (qB : Expr OFig Γ .bool) (rq : Expr OFig Γ (.base .pqc))
    (ex : Expr OFig Γ σExtra) (ρ : Env Γ) (Q : Party) (ex₀ : Ex),
    qB.eval ρ = partyEnc Q → ex.eval ρ = exEnc ex₀ →
    (hk.onSendCoins qB rq ex).eval ρ =
      Prod.map exEnc exEnc <$> sh.onSendCoins Q (rq.eval ρ) ex₀
  onTr_eval : ∀ {Γ} (arg : Expr OFig Γ _) (ex : Expr OFig Γ σExtra) (ρ : Env Γ)
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256)) (ex₀ : Ex),
    arg.eval ρ = (partyEnc Q, (m, rc)) → ex.eval ρ = exEnc ex₀ →
    (hk.onTr arg ex).eval ρ =
      Prod.map id exEnc <$> sh.onTr Q m rc ex₀
  onCh_eval : ∀ {Γ} (arg : Expr OFig Γ _) (ex : Expr OFig Γ σExtra) (ρ : Env Γ)
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256)) (ex₀ : Ex),
    arg.eval ρ = (partyEnc Q, (m₀, (m₁, rc))) → ex.eval ρ = exEnc ex₀ →
    (hk.onCh arg ex).eval ρ =
      Prod.map id exEnc <$> sh.onCh Q m₀ m₁ rc ex₀
  onDl_eval : ∀ {Γ} (arg : Expr OFig Γ _) (ex : Expr OFig Γ σExtra) (ρ : Env Γ)
    (Q : Party) (c : SimFig8C Pt) (ex₀ : Ex),
    ExBound L ex₀ →
    arg.eval ρ = (partyEnc Q, c) → ex.eval ρ = exEnc ex₀ →
    (hk.onDl arg ex).eval ρ =
      Prod.map (Option.map SM.smRrEnc) exEnc <$> sh.onDl Q c ex₀
  onIj_eval : ∀ {Γ} (arg : Expr OFig Γ _) (ex : Expr OFig Γ σExtra) (ρ : Env Γ)
    (Q : Party) (c : SimFig8C Pt) (ex₀ : Ex),
    ExBound L ex₀ →
    arg.eval ρ = (partyEnc Q, c) → ex.eval ρ = exEnc ex₀ →
    (hk.onIj arg ex).eval ρ =
      Prod.map (Option.map SM.smRrEnc) exEnc <$> sh.onIj Q c ex₀
  onCr_eval : ∀ {Γ} (qB : Expr OFig Γ .bool) (ex : Expr OFig Γ σExtra) (ρ : Env Γ)
    (Q : Party) (ex₀ : Ex),
    ExBound L ex₀ →
    qB.eval ρ = partyEnc Q → ex.eval ρ = exEnc ex₀ →
    (hk.onCr qB ex).eval ρ =
      Prod.map id exEnc <$> sh.onCr Q ex₀
  onProbe_eval : ∀ {Γ} (arg : Expr OFig Γ _) (ex : Expr OFig Γ σExtra) (ρ : Env Γ)
    (Q : Party) (c' : SimFig8C Pt) (ex₀ : Ex),
    ExBound L ex₀ →
    arg.eval ρ = (partyEnc Q, c') → ex.eval ρ = exEnc ex₀ →
    (hk.onProbe arg ex).eval ρ =
      exEnc <$> sh.onProbe Q c' ex₀
  onDeliverPost_eval : ∀ {Γ} (qB : Expr OFig Γ .bool) (j? : Expr OFig Γ (.opt .nat))
    (res : Expr OFig Γ (.opt (simRrTy PQ PQC Pt ℓ))) (ex : Expr OFig Γ σExtra) (ρ : Env Γ)
    (Q : Party) (rr : Option (RecvResult (Plain ℓ))) (ex₀ : Ex),
    qB.eval ρ = partyEnc Q → res.eval ρ = rr.map SM.smRrEnc → ex.eval ρ = exEnc ex₀ →
    (hk.onDeliverPost qB j? res ex).eval ρ =
      exEnc <$> sh.onDeliverPost Q (j?.eval ρ) rr ex₀
  onDeliverPost_congr : ∀ {Γ} (qB : Expr OFig Γ .bool) (j? : Expr OFig Γ (.opt .nat))
    (res : Expr OFig Γ (.opt (simRrTy PQ PQC Pt ℓ))) (ex : Expr OFig Γ σExtra) (ρ₁ ρ₂ : Env Γ),
    qB.eval ρ₁ = qB.eval ρ₂ → j?.eval ρ₁ = j?.eval ρ₂ →
    res.eval ρ₁ = res.eval ρ₂ → ex.eval ρ₁ = ex.eval ρ₂ →
    (hk.onDeliverPost qB j? res ex).eval ρ₁ = (hk.onDeliverPost qB j? res ex).eval ρ₂

def semDrawSendCoins {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (r : Option PQC) :
    OracleComp T (PQC × Option (BitVec 256)) :=
  match r with
  | none => do
    let rq ← sh.samplePqc
    return (rq, none)
  | some rq => do
    let rc ← sh.sampleBv256
    return (rq, some rc)

omit [SampleableType PQC] in
theorem simDrawSendCoinsHookC_eval {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {σExtra : Ty S} {Ex : Type} {exEnc : Ex → σExtra.denote}
    {ExBound : ℕ → Ex → Prop} {L : ℕ}
    {hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra}
    {sh : SemHook PQC Pt ℓ T Ex}
    (h_hk : HookMatch P Dh encPt encT decT lam K toKemCoins exEnc ExBound L hk sh)
    {Γ} (r : Expr OFig Γ (.opt (.base .pqc))) (ρ : Env Γ) :
    (simDrawSendCoinsHookC P Dh encPt encT decT lam K toKemCoins hk r).eval ρ =
      semDrawSendCoins sh (r.eval ρ) := by
  simp only [simDrawSendCoinsHookC, semDrawSendCoins, Comp.eval, Expr.eval,
    h_hk.samplePqc_eval, h_hk.sampleBv256_eval]
  cases r.eval ρ <;> rfl

def semSendHook {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    OracleComp T (Option (List (BitVec 8)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) := do
  if sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q) then
    return (none, (sC, ex))
  else
    match sC.base.mir.epMgmt 3 qep Q r.isSome with
    | none => return (none, (sC, ex))
    | some s₁ =>
      if chal.isSome && !(s₁.safeCh 3 Q) then
        return (none, (sC, ex))
      else
        let (rq, rc) ← semDrawSendCoins sh r
        let (exOk, exFail) ← sh.onSendCoins Q rq ex
        let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then
          BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
        match mkPub (P := P) sC.base Q rq pn with
        | none => return (none, (sC, exFail))
        | some (pq', pub) =>
          (match chal with
            | none => sh.onTr Q (pub, m₀) rc exOk
            | some m₁ => sh.onCh Q (pub, m₀) (pub, m₁) rc exOk) >>= fun (res, ex₂) =>
          match res with
          | none => pure (none, (sC, exFail))
          | some c =>
            let sC' := scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ chal.isSome pq' pn c
            pure (some (toWire c), (sC', ex₂))

omit [SampleableType PQC] in
theorem simSendHookC_eval {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {σExtra : Ty S} {Ex : Type} {exEnc : Ex → σExtra.denote}
    {ExBound : ℕ → Ex → Prop} {L : ℕ}
    {hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra}
    {sh : SemHook PQC Pt ℓ T Ex}
    (h_hk : HookMatch P Dh encPt encT decT lam K toKemCoins exEnc ExBound L hk sh)
    (qep B : ℕ) {Γ}
    (st : Expr OFig Γ (.prod simStateCTy σExtra))
    (qParty : Expr OFig Γ .bool) (m₀ : Expr OFig Γ (.base .plain))
    (chal : Expr OFig Γ (.opt (.base .plain))) (r : Expr OFig Γ (.opt (.base .pqc)))
    (ρ : Env Γ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hsC : simStateCDec (st.eval ρ).1 = sC₀)
    (hex : (st.eval ρ).2 = exEnc ex₀)
    (hq : qParty.eval ρ = partyEnc Q) :
    Prod.map id (Prod.map simStateCDec id) <$>
      (simSendHookC P Dh encPt encT decT lam K toKemCoins hk qep B
        st qParty m₀ chal r).eval ρ =
    Prod.map id (Prod.map id exEnc) <$>
      semSendHook P Dh encPt encT lam sh qep sC₀ ex₀ Q
        (m₀.eval ρ) (chal.eval ρ) (r.eval ρ) := by
  unfold simSendHookC semSendHook
  rw [comp_eval_bind_ret]
  have h0 : (Expr.pair st (.pair qParty (.pair m₀ (.pair chal r)))).eval ρ =
      (st.eval ρ, partyEnc Q, m₀.eval ρ, chal.eval ρ, r.eval ρ) := by
    simp [Expr.eval, hq]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (.prod simStateCTy σExtra)
      (.prod .bool (.prod (.base SimSort.plain)
        (.prod (.opt (.base SimSort.plain)) (.opt (.base SimSort.pqc))))))
    (st.eval ρ, partyEnc Q, m₀.eval ρ, chal.eval ρ, r.eval ρ) ρ
  have hs0 : (scBase (.fst (.fst (Expr.v0 (O := OFig))))).eval ρ₁ = simStateEnc sC₀.base := by
    rw [scBase_eval]; exact congrArg (simStateEnc ∘ LibsignalToModularSchemeSimState.base) hsC
  rw [comp_eval_ite]
  have href :
      (orE (ssStopped (scBase (.fst (.fst (Expr.v0 (O := OFig))))))
        (orE (mWin (ssMir (scBase (.fst (.fst .v0)))))
          (.not (mNoBobEpoch0E (ssMir (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))))).eval ρ₁ =
      (sC₀.base.stopped || sC₀.base.mir.win || !(noBobSendInEpoch0 sC₀.base.mir Q)) := by
    have hnb := mNoBobEpoch0E_eval (O' := OFig)
      (ssMir (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)) ρ₁ sC₀.base.mir Q
      (by simp [ssMir, hs0, simStateEnc]) rfl
    rw [orE_eval, orE_eval]
    dsimp only [Expr.eval, ssStopped, mWin]
    rw [hnb]
    dsimp only [ssMir, Expr.eval]
    rw [hs0]
    simp only [simStateEnc, simMirEnc, Bool.or_assoc]
  rw [href]
  by_cases h1 : (sC₀.base.stopped || sC₀.base.mir.win || !(noBobSendInEpoch0 sC₀.base.mir Q)) = true
  · simp [ρ₁, h1, hsC, hex, Prod.map, Expr.eval, Expr.v0]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [comp_eval_caseOpt]
    have hep : (mEpMgmtE qep (ssMir (scBase (.fst (.fst (Expr.v0 (O := OFig))))))
        (.fst (.snd .v0)) (isSomeE (.snd (.snd (.snd (.snd .v0)))))).eval ρ₁ =
        (sC₀.base.mir.epMgmt 3 qep Q (r.eval ρ).isSome).map simMirEnc := by
      rw [mEpMgmtE_eval qep (ssMir (scBase (.fst (.fst .v0)))) (.fst (.snd .v0))
        (isSomeE (.snd (.snd (.snd (.snd .v0))))) ρ₁ sC₀.base.mir Q
        (by simp [ssMir, hs0, simStateEnc]) rfl]
      simp [ρ₁, isSomeE_eval, Expr.eval, Expr.v0]
    rw [hep]
    rcases sC₀.base.mir.epMgmt 3 qep Q (r.eval ρ).isSome with _ | s₁
    · simp [ρ₁, hsC, hex, Prod.map, Expr.eval, Expr.v0]
    · simp only [Option.map_some]
      set ρ₂ := Env.cons (t := simMirTy) (simMirEnc s₁) ρ₁
      rw [comp_eval_ite]
      have hsc : (Expr.and (isSomeE (.fst (.snd (.snd (.snd (Expr.v1 (O := OFig)))))))
          (.not (mSafeChE .v0 (.fst (.snd .v1))))).eval ρ₂ =
          ((chal.eval ρ).isSome && !(s₁.safeCh 3 Q)) := by
        have hs' := mSafeChE_eval (O' := OFig) .v0 (.fst (.snd .v1)) ρ₂ s₁ Q rfl rfl
        dsimp only [Expr.eval]
        rw [isSomeE_eval, hs']
        rfl
      rw [hsc]
      by_cases h2 : ((chal.eval ρ).isSome && !(s₁.safeCh 3 Q)) = true
      · simp [ρ₂, ρ₁, h2, hsC, hex, Prod.map, Expr.eval, Expr.v1]
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        rw [comp_eval_bind, simDrawSendCoinsHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk,
          map_bind, map_bind]
        refine bind_congr fun ⟨rq, rc⟩ => ?_
        set ρ₃ := Env.cons (t := .prod (.base SimSort.pqc) (.opt (.base SimSort.bv256))) (rq, rc) ρ₂
        rw [comp_eval_bind, h_hk.onSendCoins_eval (.fst (.snd .v2)) (.fst .v0) (.snd (.fst .v2))
          ρ₃ Q ex₀ rfl hex, bind_map_left, map_bind, map_bind]
        refine bind_congr fun ⟨exOk, exFail⟩ => ?_
        dsimp only [Prod.map]
        set ρ₄ := Env.cons (t := .prod σExtra σExtra) (exEnc exOk, exEnc exFail) ρ₃
        set pn := if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
          BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q
        have hpn : (Expr.ite (.not (.eqN (pGet (mEpoch (Expr.v2 (O := OFig))) (.fst (.snd .v3)))
            (pGet (mEpoch (ssMir (scBase (.fst (.fst .v3))))) (.fst (.snd .v3)))))
          (Expr.op (O := OFig) SimOp.natToU32
            (.sub (pGet (mIdx (ssMir (scBase (.fst (.fst .v3))))) (.fst (.snd .v3))) (.nat 1)))
          (pGet (ssPn (scBase (.fst (.fst .v3)))) (.fst (.snd .v3)))).eval ρ₄ = pn := by
          cases Q <;>
            simp [ρ₄, ρ₃, ρ₂, ρ₁, pn, hsC, pGet_eval, mEpoch, mIdx, ssMir, ssPn,
              simStateEnc, simMirEnc, partyEnc, simOpsUnitCost, Expr.eval,
              Expr.v2, Expr.v3]
        have hpub : (spqrSendPubFigE P Dh encPt encT decT lam K toKemCoins
            (.pair (.fst (.snd .v3)) (.pair (ssUnackA (scBase (.fst (.fst .v3))))
              (.pair (pGet (ssPq (scBase (.fst (.fst .v3)))) (.fst (.snd .v3)))
                (.pair (.fst .v1)
                  (.ite (.not (.eqN (pGet (mEpoch .v2) (.fst (.snd .v3)))
                      (pGet (mEpoch (ssMir (scBase (.fst (.fst .v3))))) (.fst (.snd .v3)))))
                    (Expr.op (O := OFig) SimOp.natToU32
                      (.sub (pGet (mIdx (ssMir (scBase (.fst (.fst .v3)))))
                        (.fst (.snd .v3))) (.nat 1)))
                    (pGet (ssPn (scBase (.fst (.fst .v3)))) (.fst (.snd .v3))))))))).eval ρ₄ =
            mkPub (P := P) sC₀.base Q rq pn := by
          rw [← simSpqrSendPub_eq P sC₀.base Q rq pn]
          refine spqrSendPubFigE_eval P Dh encPt encT decT lam K toKemCoins _ ρ₄
            (partyEnc Q) sC₀.base.unackA (sC₀.base.pq Q) rq pn ?_
          rw [expr_pair_eval, expr_pair_eval, expr_pair_eval, expr_pair_eval, hpn]
          cases Q <;>
            simp [ρ₄, ρ₃, ρ₂, ρ₁, hsC, ssUnackA, ssPq, pGet_eval, simStateEnc, partyEnc,
              Expr.eval, Expr.v1, Expr.v3]
        rw [comp_eval_caseOpt, hpub]
        dsimp only [pn]
        rcases mkPub (P := P) sC₀.base Q rq
          (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1)
           else sC₀.base.pn Q) with _ | ⟨pq', pub⟩
        · simp [ρ₄, ρ₃, ρ₂, ρ₁, hsC, Prod.map, Expr.eval, Expr.v0, Expr.v3]
        · dsimp only []
          set ρ₅ := Env.cons (t := .prod (.base SimSort.pq) (.base SimSort.lpub)) (pq', pub) ρ₄
          have hq_chal :
              (Comp.caseOpt (.fst (.snd (.snd (.snd (Expr.v4 (O := OFig))))))
                (hk.onTr (.pair (.fst (.snd .v4))
                  (.pair (.pair (.snd .v0) (.fst (.snd (.snd .v4)))) (.snd .v2))) (.fst .v1))
                (hk.onCh (.pair (.fst (.snd .v5))
                  (.pair (.pair (.snd .v1) (.fst (.snd (.snd .v5))))
                    (.pair (.pair (.snd .v1) .v0) (.snd .v3)))) (.fst .v2))).eval ρ₅ =
              Prod.map id exEnc <$> (match chal.eval ρ with
                | none => sh.onTr Q (pub, m₀.eval ρ) rc exOk
                | some m₁ => sh.onCh Q (pub, m₀.eval ρ) (pub, m₁) rc exOk) := by
            rw [comp_eval_caseOpt]
            have hch4 : (Expr.fst (.snd (.snd (.snd (Expr.v4 (O := OFig)))))).eval ρ₅ =
                chal.eval ρ := rfl
            rw [hch4]
            rcases chal.eval ρ with _ | m₁
            · exact h_hk.onTr_eval _ _ ρ₅ Q (pub, m₀.eval ρ) rc exOk rfl rfl
            · exact h_hk.onCh_eval _ _ (Env.cons m₁ ρ₅) Q (pub, m₀.eval ρ) (pub, m₁) rc exOk rfl rfl
          rw [comp_eval_bind, hq_chal, bind_map_left, map_bind, map_bind]
          refine congrArg₂ Bind.bind (by cases chal.eval ρ <;> rfl)
            (funext fun ⟨res, ex₂⟩ => ?_)
          dsimp only [Prod.map, id_eq]
          set ρ₆ := Env.cons (t := .prod (.opt (fig8CTy PQ PQC Pt ℓ)) σExtra) (res, exEnc ex₂) ρ₅
          rw [comp_eval_caseOpt]
          have hr5 : (Expr.fst (Expr.v0 (O := OFig))).eval ρ₆ = res := rfl
          rw [hr5]
          rcases res with _ | c
          · simp [ρ₆, ρ₅, ρ₄, ρ₃, ρ₂, ρ₁, hsC, Prod.map,
              Expr.eval, Expr.v2, Expr.v5]
          · dsimp only []
            set ρ₇ := Env.cons (t := fig8CTy PQ PQC Pt ℓ) c ρ₆
            have hps := scPostSendE_eval P Dh encPt encT decT lam K toKemCoins B
              (.fst (.fst .v6)) .v5 (.fst (.snd .v6)) (.fst (.snd (.snd .v6)))
              (isSomeE (.fst (.snd (.snd (.snd .v6))))) (.fst .v2)
              (.ite (.not (.eqN (pGet (mEpoch .v5) (.fst (.snd .v6)))
                  (pGet (mEpoch (ssMir (scBase (.fst (.fst .v6))))) (.fst (.snd .v6)))))
                (Expr.op (O := OFig) SimOp.natToU32
                  (.sub (pGet (mIdx (ssMir (scBase (.fst (.fst .v6)))))
                    (.fst (.snd .v6))) (.nat 1)))
                (pGet (ssPn (scBase (.fst (.fst .v6)))) (.fst (.snd .v6))))
              .v0 ρ₇ s₁ rfl
            have hpn7 : (Expr.ite (.not (.eqN (pGet (mEpoch (Expr.v5 (O := OFig)))
                  (.fst (.snd .v6)))
                (pGet (mEpoch (ssMir (scBase (.fst (.fst .v6))))) (.fst (.snd .v6)))))
              (Expr.op (O := OFig) SimOp.natToU32
                (.sub (pGet (mIdx (ssMir (scBase (.fst (.fst .v6)))))
                  (.fst (.snd .v6))) (.nat 1)))
              (pGet (ssPn (scBase (.fst (.fst .v6)))) (.fst (.snd .v6)))).eval ρ₇ = pn := by
              cases Q <;>
                simp [ρ₇, ρ₆, ρ₅, ρ₄, ρ₃, ρ₂, ρ₁, pn, hsC, pGet_eval, mEpoch, mIdx, ssMir, ssPn,
                  simStateEnc, simMirEnc, partyEnc, simOpsUnitCost, Expr.eval,
                  Expr.v5, Expr.v6]
            rw [comp_eval_ret, map_pure]
            simp only [Prod.map, id_eq, expr_pair_eval, expr_some_eval, expr_fst_eval,
              expr_snd_eval, hps.1, hps.2, hpn7]
            simp [ρ₇, ρ₆, ρ₅, ρ₄, ρ₃, ρ₂, ρ₁, pn, hsC, partyDec_partyEnc, isSomeE_eval,
              Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v6]

def semFwdAnswerHook {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    OracleComp T (Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) :=
  let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  let inT := sC.base.honest.any fun wc =>
    decide (wc.2 = c') && (sC.base.mir.inTransit Q.other wc.1).isSome
  (if inT then sh.onDl Q c' ex else sh.onIj Q c' ex) >>= fun (res, ex₁) =>
    let sC₂ : LibsignalToModularSchemeSimState PQ Pt ℓ := match res with
      | some (.accepted _ _ _) =>
        { sC with
          kept := Function.update sC.kept Q (Kept.recv (fig := fig) (fs := fs) c' (sC.kept Q)) }
      | _ => sC
    let (rr, base') := onAnswerPure qep Q w isDel ci? Tpk pq' res sC.base
    pure (rr, ({ sC₂ with base := base' }, ex₁))

omit [SampleableType PQC] in
theorem fwdAnswerHookC_eval {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {σExtra : Ty S} {Ex : Type} {exEnc : Ex → σExtra.denote}
    {ExBound : ℕ → Ex → Prop} {L : ℕ}
    {hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra}
    {sh : SemHook PQC Pt ℓ T Ex}
    (h_hk : HookMatch P Dh encPt encT decT lam K toKemCoins exEnc ExBound L hk sh)
    (qep B : ℕ) {Γ}
    (sC : Expr OFig Γ simStateCTy) (ex : Expr OFig Γ σExtra)
    (qParty : Expr OFig Γ .bool) (w : Expr OFig Γ (.base .wire))
    (isDel : Expr OFig Γ .bool) (ci? : Expr OFig Γ (.opt .nat))
    (Tpk : Expr OFig Γ (.base .pk)) (pq' : Expr OFig Γ (.base .pq))
    (c' : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) (ρ : Env Γ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hBound : SimStateBounded L sC₀.base)
    (hEx : ExBound L ex₀)
    (hsC : simStateCDec (sC.eval ρ) = sC₀)
    (hex : ex.eval ρ = exEnc ex₀)
    (hq : qParty.eval ρ = partyEnc Q) :
    Prod.map id (Prod.map simStateCDec id) <$>
      (fwdAnswerHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
        sC ex qParty w isDel ci? Tpk pq' c').eval ρ =
    Prod.map (Option.map SM.smRrEnc) (Prod.map id exEnc) <$>
      semFwdAnswerHook P Dh encPt encT lam sh qep sC₀ ex₀ Q
        (w.eval ρ) (isDel.eval ρ) (ci?.eval ρ) (Tpk.eval ρ) (pq'.eval ρ) (c'.eval ρ) := by
  unfold fwdAnswerHookC semFwdAnswerHook
  rw [comp_eval_bind_ret]
  dsimp only [Expr.eval]
  set ρ₁ := Env.cons
    (t := .prod simStateCTy (.prod σExtra (.prod .bool (.prod (.base SimSort.wire)
      (.prod .bool (.prod (.opt .nat) (.prod (.base SimSort.pk)
        (.prod (.base SimSort.pq) (fig8CTy PQ PQC Pt ℓ)))))))))
    (sC.eval ρ, ex.eval ρ, qParty.eval ρ, w.eval ρ, isDel.eval ρ, ci?.eval ρ,
      Tpk.eval ρ, pq'.eval ρ, c'.eval ρ) ρ
  have hs0 : (scBase (.fst (Expr.v0 (O := OFig)))).eval ρ₁ = simStateEnc sC₀.base := by
    rw [scBase_eval]; exact congrArg (simStateEnc ∘ LibsignalToModularSchemeSimState.base) hsC
  have hinT := inTFigE_eval P Dh encPt encT decT lam K toKemCoins L
    (scBase (.fst .v0)) (.fst (.snd (.snd .v0)))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
    ρ₁ sC₀.base Q (c'.eval ρ) hBound.trans_le hBound.honest_le hs0 hq rfl
  have hq_fwd :
      (Comp.ite
        (inTFigE P Dh encPt encT decT lam K toKemCoins L
          (scBase (.fst .v0)) (.fst (.snd (.snd .v0)))
          (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))))
        (hk.onDl (.pair (.fst (.snd (.snd .v0)))
          (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))) (.fst (.snd .v0)))
        (hk.onIj (.pair (.fst (.snd (.snd .v0)))
          (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))) (.fst (.snd .v0)))).eval ρ₁ =
      Prod.map (Option.map SM.smRrEnc) exEnc <$>
        (if (sC₀.base.honest.any fun wc =>
            decide (wc.2 = c'.eval ρ) && (sC₀.base.mir.inTransit Q.other wc.1).isSome)
         then sh.onDl Q (c'.eval ρ) ex₀
         else sh.onIj Q (c'.eval ρ) ex₀) := by
    rw [comp_eval_ite, hinT]
    split_ifs
    · exact h_hk.onDl_eval _ _ ρ₁ Q (c'.eval ρ) ex₀ hEx
        (by simp [ρ₁, hq, Expr.eval, Expr.v0]) hex
    · exact h_hk.onIj_eval _ _ ρ₁ Q (c'.eval ρ) ex₀ hEx
        (by simp [ρ₁, hq, Expr.eval, Expr.v0]) hex
  rw [comp_eval_bind, hq_fwd, bind_map_left, map_bind, map_bind]
  refine bind_congr fun ⟨res, ex₁⟩ => ?_
  dsimp only [Prod.map, id_eq]
  set ρ₂ := Env.cons (t := .prod (.opt (fig8RrTy PQ PQC Pt ℓ)) σExtra)
    (res.map SM.smRrEnc, exEnc ex₁) ρ₁
  let sC2_expr : Expr OFig
      (.prod (.opt (fig8RrTy PQ PQC Pt ℓ)) σExtra ::
        .prod simStateCTy (.prod σExtra (.prod .bool (.prod (.base SimSort.wire)
          (.prod .bool (.prod (.opt .nat) (.prod (.base SimSort.pk)
            (.prod (.base SimSort.pq) (fig8CTy PQ PQC Pt ℓ)))))))) :: Γ)
      simStateCTy :=
    scPostFwdKeptE P Dh encPt encT decT lam K toKemCoins B
      (.fst .v1) (.fst (.snd (.snd .v1)))
      (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))) (.fst .v0)
  have hpfk := scPostFwdKeptE_eval P Dh encPt encT decT lam K toKemCoins B
    (.fst .v1) (.fst (.snd (.snd .v1)))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))) (.fst .v0)
    ρ₂ res rfl
  have hsC2_base : (scBase sC2_expr).eval ρ₂ = simStateEnc sC₀.base := by
    rw [scBase_eval, hpfk]
    rcases res with _ | (_ | ⟨t, i, m⟩) <;>
      (dsimp only []; exact congrArg (simStateEnc ∘ LibsignalToModularSchemeSimState.base) hsC)
  have hona := onAnswerFigE_eval_pure P Dh encPt encT decT lam K toKemCoins L qep
    (scBase sC2_expr) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
    (.fst (.snd (.snd (.snd (.snd .v1)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
    (.fst .v0) ρ₂ sC₀.base Q res hBound hsC2_base hq rfl
  dsimp only [sC2_expr] at hona
  rw [comp_eval_ret, map_pure, map_pure]
  simp only [expr_pair_eval, expr_fst_eval, expr_snd_eval, hona, Prod.map, id_eq]
  congr 1
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  rw [scSetBase_eval sC2_expr _ ρ₂ _ (by rw [expr_snd_eval, hona]; rfl)]
  change ({ simStateCDec (sC2_expr.eval ρ₂) with base := _ } : LibsignalToModularSchemeSimState PQ Pt ℓ) = _
  rw [hpfk]
  have hsC1 : simStateCDec ((Expr.fst (Expr.v1 (O := OFig))).eval ρ₂) = sC₀ := hsC
  have hq1 : partyDec ((Expr.fst (.snd (.snd (Expr.v1 (O := OFig))))).eval ρ₂) = Q := by
    change partyDec (qParty.eval ρ) = Q
    rw [hq, partyDec_partyEnc]
  rcases res with _ | (_ | ⟨t, i, m⟩) <;>
    (dsimp only []; rw [hsC1]; try rw [hq1]) <;> rfl

def semResyncHook {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    OracleComp T (Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) :=
  let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  match r with
  | none => return (some .rejected, (sC, ex))
  | some (t, i, (_, m')) => do
    let (res, ex₁) ← sh.onDl Q c ex
    match res with
    | some (.accepted _ _ _) =>
      let sC₅ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        { sC with
          kept := Function.update sC.kept Q (Kept.recv (fig := fig) (fs := fs) c (sC.kept Q)) }
      let (rr, base') := onAcceptPure qep Q w true t i m' ci? Tpk pq' sC.base
      return (rr, ({ sC₅ with base := base' }, ex₁))
    | _ => return (some .rejected, (sC, ex₁))

omit [SampleableType PQC] in
theorem resyncHookC_eval {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {σExtra : Ty S} {Ex : Type} {exEnc : Ex → σExtra.denote}
    {ExBound : ℕ → Ex → Prop} {L : ℕ}
    {hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra}
    {sh : SemHook PQC Pt ℓ T Ex}
    (h_hk : HookMatch P Dh encPt encT decT lam K toKemCoins exEnc ExBound L hk sh)
    (qep B : ℕ) {Γ}
    (sC : Expr OFig Γ simStateCTy) (ex : Expr OFig Γ σExtra)
    (qParty : Expr OFig Γ .bool) (w : Expr OFig Γ (.base .wire))
    (ci? : Expr OFig Γ (.opt .nat)) (Tpk : Expr OFig Γ (.base .pk))
    (pq' : Expr OFig Γ (.base .pq)) (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ))
    (r : Expr OFig Γ (.opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ)))))
    (ρ : Env Γ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hBound : SimStateBounded L sC₀.base)
    (hEx : ExBound L ex₀)
    (hsC : simStateCDec (sC.eval ρ) = sC₀)
    (hex : ex.eval ρ = exEnc ex₀)
    (hq : qParty.eval ρ = partyEnc Q) :
    Prod.map id (Prod.map simStateCDec id) <$>
      (resyncHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
        sC ex qParty w ci? Tpk pq' c r).eval ρ =
    Prod.map (Option.map SM.smRrEnc) (Prod.map id exEnc) <$>
      semResyncHook P Dh encPt encT lam sh qep sC₀ ex₀ Q
        (w.eval ρ) (ci?.eval ρ) (Tpk.eval ρ) (pq'.eval ρ) (c.eval ρ) (r.eval ρ) := by
  unfold resyncHookC semResyncHook
  rw [comp_eval_bind_ret]
  dsimp only [Expr.eval]
  set ρ₁ := Env.cons
    (t := .prod simStateCTy (.prod σExtra (.prod .bool (.prod (.base SimSort.wire)
      (.prod (.opt .nat) (.prod (.base SimSort.pk) (.prod (.base SimSort.pq)
        (.prod (fig8CTy PQ PQC Pt ℓ)
          (.opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ))))))))))))
    (sC.eval ρ, ex.eval ρ, qParty.eval ρ, w.eval ρ, ci?.eval ρ,
      Tpk.eval ρ, pq'.eval ρ, c.eval ρ, r.eval ρ) ρ
  rw [comp_eval_caseOpt]
  have hr0 :
      (Expr.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (Expr.v0 (O := OFig)))))))))).eval ρ₁ =
      r.eval ρ := rfl
  rw [hr0]
  rcases r.eval ρ with _ | ⟨t, i, pub', m'⟩
  · simp [ρ₁, hsC, hex, SM.smRrEnc, Prod.map, Expr.eval, Expr.v0]
  · dsimp only []
    set ρ₂ := Env.cons (t := .prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ)))
      (t, i, pub', m') ρ₁
    rw [comp_eval_bind,
      h_hk.onDl_eval _ _ ρ₂ Q (c.eval ρ) ex₀ hEx
        (by simp [ρ₂, ρ₁, hq, Expr.eval, Expr.v1]) hex,
      bind_map_left, map_bind, map_bind]
    refine bind_congr fun ⟨res, ex₁⟩ => ?_
    dsimp only [Prod.map, id_eq]
    set ρ₃ := Env.cons (t := .prod (.opt (fig8RrTy PQ PQC Pt ℓ)) σExtra)
      (res.map SM.smRrEnc, exEnc ex₁) ρ₂
    rw [comp_eval_caseOpt]
    have hres3 : (Expr.fst (Expr.v0 (O := OFig))).eval ρ₃ = res.map SM.smRrEnc := rfl
    rw [hres3]
    rcases res with _ | (_ | ⟨t_dl, i_dl, pm_dl⟩)
    · simp [ρ₃, ρ₂, ρ₁, hsC, SM.smRrEnc, Prod.map, Expr.eval, Expr.v0, Expr.v2]
    · dsimp only [Option.map_some, SM.smRrEnc, Comp.eval]
      simp [ρ₃, ρ₂, ρ₁, hsC, SM.smRrEnc, Prod.map, Expr.eval, Expr.v2, Expr.v4]
    · dsimp only [Option.map_some, SM.smRrEnc, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero]
      set ρ₄ := Env.cons
        (t := .prod .nat (.prod .nat (.opt (lpubPlainTy PQ PQC Pt ℓ))))
        (t_dl, i_dl, pm_dl)
        (Env.cons (t := fig8RrTy PQ PQC Pt ℓ) (Sum.inr (t_dl, i_dl, pm_dl)) ρ₃)
      let sC5_expr : Expr OFig
          (.prod .nat (.prod .nat (.opt (lpubPlainTy PQ PQC Pt ℓ))) ::
            fig8RrTy PQ PQC Pt ℓ ::
            .prod (.opt (fig8RrTy PQ PQC Pt ℓ)) σExtra ::
            .prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ)) ::
            .prod simStateCTy (.prod σExtra (.prod .bool (.prod (.base SimSort.wire)
              (.prod (.opt .nat) (.prod (.base SimSort.pk) (.prod (.base SimSort.pq)
                (.prod (fig8CTy PQ PQC Pt ℓ)
                  (.opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ))))))))))) :: Γ)
          simStateCTy :=
        scMk (scBase (.fst .v4))
          (pSet (scKept (.fst .v4)) (.fst (.snd (.snd .v4)))
            (keptRecvE P Dh encPt encT decT lam K toKemCoins B
              (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4))))))))
              (pGet (scKept (.fst .v4)) (.fst (.snd (.snd .v4))))))
          (scSent (.fst .v4)) (scSnaps (.fst .v4))
      have hs4 : (scBase (.fst (Expr.v4 (O := OFig)))).eval ρ₄ = simStateEnc sC₀.base := by
        rw [scBase_eval]; exact congrArg (simStateEnc ∘ LibsignalToModularSchemeSimState.base) hsC
      have hsC5 : simStateCDec (sC5_expr.eval ρ₄) =
          { sC₀ with
            kept := Function.update sC₀.kept Q
              (Kept.recv
                (fig := lFig8 Dh encPt P.C P.codec ℓ encT
                  (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
                (fs := lFS P.C P.codec ℓ encT
                  (fun R => if R == Party.A then P.idA else P.idB) 25000)
                (c.eval ρ) (sC₀.kept Q)) } := by
        dsimp only [sC5_expr]
        rw [scMk_pSet_kept_eval _ _ _ _ _ _ ρ₄ sC₀.base hs4]
        simp only [ρ₄, ρ₃, ρ₂, ρ₁, keptRecvE_eval, scKept_pGet_eval, scSent_eval, scSnaps_eval,
          List.map_map, Function.comp_def, snapDec_snapEnc, List.map_id', hsC, hq,
          partyDec_partyEnc, Expr.eval, Expr.v4, Env.get_cons_zero, Env.get_cons_succ]
      have hsC5_base : (scBase sC5_expr).eval ρ₄ = simStateEnc sC₀.base := by
        rw [scBase_eval, hsC5]
      have hacc := onAcceptFigE_eval_pure P Dh encPt encT decT lam K toKemCoins L qep
        (scBase sC5_expr) (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4))))
        (.bool true) (.fst .v3) (.fst (.snd .v3)) (.snd (.snd (.snd .v3)))
        (.fst (.snd (.snd (.snd (.snd .v4)))))
        (.fst (.snd (.snd (.snd (.snd (.snd .v4))))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))
        ρ₄ sC₀.base Q hBound hsC5_base hq
      dsimp only [sC5_expr] at hacc
      rw [map_pure, map_pure]
      simp only [hacc, Prod.map, id_eq]
      congr 1
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      rw [scSetBase_eval sC5_expr _ ρ₄ _ (by rw [expr_snd_eval, hacc]; rfl),
        hsC5]
      rfl

def semFwdHook {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ)
    (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt) :
    OracleComp T (Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) :=
  match honestC with
  | none => semFwdAnswerHook P Dh encPt encT lam sh qep sC ex Q w isDel ci? Tpk pq' c'
  | some c =>
    if !(decide (c = c')) && (isDel && !(sC.base.mir.safeInj 3)) then
      match evalCKClamp P Dh encPt encT lam B sC Q w c c' with
      | none => do
        let ex₁ ← sh.onProbe Q c' ex
        return (some .rejected, (sC, ex₁))
      | some r =>
        semResyncHook P Dh encPt encT lam sh qep sC ex Q w ci? Tpk pq' c r
    else
      semFwdAnswerHook P Dh encPt encT lam sh qep sC ex Q w isDel ci? Tpk pq' c'

omit [SampleableType PQC] in
theorem fwdHookC_eval {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {σExtra : Ty S} {Ex : Type} {exEnc : Ex → σExtra.denote}
    {ExBound : ℕ → Ex → Prop} {L : ℕ}
    {hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra}
    {sh : SemHook PQC Pt ℓ T Ex}
    (h_hk : HookMatch P Dh encPt encT decT lam K toKemCoins exEnc ExBound L hk sh)
    (qep B : ℕ) {Γ}
    (sC : Expr OFig Γ simStateCTy) (ex : Expr OFig Γ σExtra)
    (qParty : Expr OFig Γ .bool) (w : Expr OFig Γ (.base .wire))
    (isDel : Expr OFig Γ .bool) (ci? : Expr OFig Γ (.opt .nat))
    (Tpk : Expr OFig Γ (.base .pk)) (pq' : Expr OFig Γ (.base .pq))
    (honestC : Expr OFig Γ (.opt (fig8CTy PQ PQC Pt ℓ)))
    (c' : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) (ρ : Env Γ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hBound : SimCStateBounded L sC₀)
    (hEx : ExBound L ex₀)
    (hsC : simStateCDec (sC.eval ρ) = sC₀)
    (hex : ex.eval ρ = exEnc ex₀)
    (hq : qParty.eval ρ = partyEnc Q) :
    Prod.map id (Prod.map simStateCDec id) <$>
      (fwdHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
        sC ex qParty w isDel ci? Tpk pq' honestC c').eval ρ =
    Prod.map (Option.map SM.smRrEnc) (Prod.map id exEnc) <$>
      semFwdHook P Dh encPt encT lam sh qep B sC₀ ex₀ Q
        (w.eval ρ) (isDel.eval ρ) (ci?.eval ρ) (Tpk.eval ρ) (pq'.eval ρ)
        (honestC.eval ρ) (c'.eval ρ) := by
  unfold fwdHookC semFwdHook
  rw [comp_eval_bind_ret]
  dsimp only [Expr.eval]
  set ρ₁ := Env.cons
    (t := .prod simStateCTy (.prod σExtra (.prod .bool (.prod (.base SimSort.wire)
      (.prod .bool (.prod (.opt .nat) (.prod (.base SimSort.pk) (.prod (.base SimSort.pq)
        (.prod (.opt (fig8CTy PQ PQC Pt ℓ)) (fig8CTy PQ PQC Pt ℓ))))))))))
    (sC.eval ρ, ex.eval ρ, qParty.eval ρ, w.eval ρ, isDel.eval ρ, ci?.eval ρ,
      Tpk.eval ρ, pq'.eval ρ, honestC.eval ρ, c'.eval ρ) ρ
  rw [comp_eval_caseOpt]
  have hhc0 :
      (Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (Expr.v0 (O := OFig))))))))))).eval
        ρ₁ = honestC.eval ρ := rfl
  rw [hhc0]
  rcases honestC.eval ρ with _ | c
  · exact fwdAnswerHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk qep B
      (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
      (.fst (.snd (.snd (.snd (.snd .v0))))) (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
      (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
      (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
      (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))))
      ρ₁ sC₀ ex₀ Q hBound.base hEx hsC hex hq
  · dsimp only []
    set ρ₂ := Env.cons (t := fig8CTy PQ PQC Pt ℓ) c ρ₁
    rw [comp_eval_ite]
    have hs1 : (scBase (.fst (Expr.v1 (O := OFig)))).eval ρ₂ = simStateEnc sC₀.base := by
      rw [scBase_eval]; exact congrArg (simStateEnc ∘ LibsignalToModularSchemeSimState.base) hsC
    have hsi := mSafeInjE_eval (O' := OFig) (ssMir (scBase (.fst .v1))) ρ₂ sC₀.base.mir
      (by simp [ssMir, hs1, simStateEnc])
    have hcond :
        (Expr.and (.not (Expr.op (O := OFig) SimOp.eqFig8C
            (.pair .v0 (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))))))
          (.and (.fst (.snd (.snd (.snd (.snd .v1)))))
            (.not (mSafeInjE (ssMir (scBase (.fst .v1))))))).eval ρ₂ =
        (!(decide (c = c'.eval ρ)) && (isDel.eval ρ && !(sC₀.base.mir.safeInj 3))) := by
      dsimp only [Expr.eval]
      rw [hsi]
      rfl
    rw [hcond]
    split_ifs with hc_cond
    · rw [comp_eval_caseOpt]
      have heck := evalCKE_eval P Dh encPt encT decT lam K toKemCoins L B
        (.fst .v1) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))) .v0
        (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))))
        ρ₂ (by rw [show (Expr.fst (Expr.v1 (O := OFig))).eval ρ₂ = sC.eval ρ from rfl, hsC];
               exact hBound.sent_le)
           (by rw [show (Expr.fst (Expr.v1 (O := OFig))).eval ρ₂ = sC.eval ρ from rfl, hsC];
               exact hBound.snaps_le)
      have hsC2 : simStateCDec ((Expr.fst (Expr.v1 (O := OFig))).eval ρ₂) = sC₀ := hsC
      have hq2 : partyDec ((Expr.fst (.snd (.snd (Expr.v1 (O := OFig))))).eval ρ₂) = Q := by
        change partyDec (qParty.eval ρ) = Q
        rw [hq, partyDec_partyEnc]
      have hw2 : (Expr.fst (.snd (.snd (.snd (Expr.v1 (O := OFig)))))).eval ρ₂ = w.eval ρ := rfl
      have hc0 : (Expr.v0 (O := OFig)).eval ρ₂ = c := rfl
      have hc'2 :
          (Expr.snd (.snd (.snd (.snd (.snd (.snd
            (.snd (.snd (.snd (Expr.v1 (O := OFig))))))))))).eval ρ₂ = c'.eval ρ := rfl
      rw [hsC2, hq2, hw2, hc0, hc'2] at heck
      rw [heck]
      rcases evalCKClamp P Dh encPt encT lam B sC₀ Q (w.eval ρ) c (c'.eval ρ) with _ | r
      · rw [comp_eval_bind,
          h_hk.onProbe_eval _ _ ρ₂ Q (c'.eval ρ) ex₀ hEx
            (by simp [ρ₂, ρ₁, hq, Expr.eval, Expr.v1]) hex,
          bind_map_left, map_bind, map_bind]
        refine bind_congr fun ex₁ => ?_
        simp [ρ₂, ρ₁, hsC, SM.smRrEnc, Prod.map, Expr.eval, Expr.v0, Expr.v2]
      · dsimp only []
        set ρ₃ := Env.cons
          (t := .opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ)))) r ρ₂
        exact resyncHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk qep B
          (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2))) (.fst (.snd (.snd (.snd .v2))))
          (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
          (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v2)))))))
          (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))))
          .v1 .v0 ρ₃ sC₀ ex₀ Q hBound.base hEx hsC hex hq
    · exact fwdAnswerHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk qep B
        (.fst .v1) (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
        (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
        (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))))
        ρ₂ sC₀ ex₀ Q hBound.base hEx hsC hex hq

def semFwdEvictHook {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    OracleComp T (Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) :=
  if isDel && !(sC.base.mir.safeInj 3) then do
    let ex₁ ← sh.onProbe Q c' ex
    return (some .rejected, (sC, ex₁))
  else
    semFwdAnswerHook P Dh encPt encT lam sh qep sC ex Q w isDel none Tpk pq' c'

omit [SampleableType PQC] in
theorem fwdEvictHookC_eval {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {σExtra : Ty S} {Ex : Type} {exEnc : Ex → σExtra.denote}
    {ExBound : ℕ → Ex → Prop} {L : ℕ}
    {hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra}
    {sh : SemHook PQC Pt ℓ T Ex}
    (h_hk : HookMatch P Dh encPt encT decT lam K toKemCoins exEnc ExBound L hk sh)
    (qep B : ℕ) {Γ}
    (sC : Expr OFig Γ simStateCTy) (ex : Expr OFig Γ σExtra)
    (qParty : Expr OFig Γ .bool) (w : Expr OFig Γ (.base .wire))
    (isDel : Expr OFig Γ .bool) (Tpk : Expr OFig Γ (.base .pk))
    (pq' : Expr OFig Γ (.base .pq)) (c' : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ))
    (ρ : Env Γ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hBound : SimStateBounded L sC₀.base)
    (hEx : ExBound L ex₀)
    (hsC : simStateCDec (sC.eval ρ) = sC₀)
    (hex : ex.eval ρ = exEnc ex₀)
    (hq : qParty.eval ρ = partyEnc Q) :
    Prod.map id (Prod.map simStateCDec id) <$>
      (fwdEvictHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
        sC ex qParty w isDel Tpk pq' c').eval ρ =
    Prod.map (Option.map SM.smRrEnc) (Prod.map id exEnc) <$>
      semFwdEvictHook P Dh encPt encT lam sh qep sC₀ ex₀ Q
        (w.eval ρ) (isDel.eval ρ) (Tpk.eval ρ) (pq'.eval ρ) (c'.eval ρ) := by
  unfold fwdEvictHookC semFwdEvictHook
  rw [comp_eval_bind_ret]
  dsimp only [Expr.eval]
  set ρ₁ := Env.cons
    (t := .prod simStateCTy (.prod σExtra (.prod .bool (.prod (.base SimSort.wire)
      (.prod .bool (.prod (.base SimSort.pk) (.prod (.base SimSort.pq) (fig8CTy PQ PQC Pt ℓ))))))))
    (sC.eval ρ, ex.eval ρ, qParty.eval ρ, w.eval ρ, isDel.eval ρ,
      Tpk.eval ρ, pq'.eval ρ, c'.eval ρ) ρ
  rw [comp_eval_ite]
  have hs0 : (scBase (.fst (Expr.v0 (O := OFig)))).eval ρ₁ = simStateEnc sC₀.base := by
    rw [scBase_eval]; exact congrArg (simStateEnc ∘ LibsignalToModularSchemeSimState.base) hsC
  have hsi := mSafeInjE_eval (O' := OFig) (ssMir (scBase (.fst .v0))) ρ₁ sC₀.base.mir
    (by simp [ssMir, hs0, simStateEnc])
  have hcond :
      (Expr.and (.fst (.snd (.snd (.snd (.snd (Expr.v0 (O := OFig)))))))
        (.not (mSafeInjE (ssMir (scBase (.fst .v0)))))).eval ρ₁ =
      (isDel.eval ρ && !(sC₀.base.mir.safeInj 3)) := by
    dsimp only [Expr.eval]
    rw [hsi]
    rfl
  rw [hcond]
  split_ifs
  · rw [comp_eval_bind,
      h_hk.onProbe_eval _ _ ρ₁ Q (c'.eval ρ) ex₀ hEx
        (by simp [ρ₁, hq, Expr.eval, Expr.v0]) hex,
      bind_map_left, map_bind, map_bind]
    refine bind_congr fun ex₁ => ?_
    simp [ρ₁, hsC, SM.smRrEnc, Prod.map, Expr.eval, Expr.v0, Expr.v1]
  · exact fwdAnswerHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk qep B
      (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
      (.fst (.snd (.snd (.snd (.snd .v0))))) .none
      (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
      (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
      (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
      ρ₁ sC₀ ex₀ Q hBound hEx hsC hex hq

def semRecvHook {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    OracleComp T (Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) := do
  let refuse :=
    sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w)))
  if refuse then
    return (none, (sC, ex))
  else
    match simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with
    | none => return (some .rejected, (sC, ex))
    | some (pq', (i, (pk, (T?, lct)))) =>
      let honestC := (sC.base.honest.find? fun wc =>
        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
      let mkC (t : ℕ) (T : Option Pt) : SimFig8C Pt :=
        match honestC with
        | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
        | none => ((t, T), lct)
      match (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with
      | none =>
        let evicted := (honestC.map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true
        let saltEq := (honestC.map fun c => decide (c.2.2.2 = lct.2.2)) == some true
        let amb := inReceiveOnlyEpoch sC.base.mir Q || (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
        let sCAmb : LibsignalToModularSchemeSimState PQ Pt ℓ :=
          { sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }
        if evicted && saltEq then
          return (some .rejected, (sC, ex))
        else if T? == some 0 then
          return (some .rejected, (sC, ex))
        else if inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i) then
          return (some .rejected, (sCAmb, ex))
        else
          match T? with
          | none => return (some .rejected, (sCAmb, ex))
          | some T =>
            if evicted then
              semFwdEvictHook P Dh encPt encT lam sh qep sCAmb ex Q w isDel pk pq'
                ((sC.base.mir.epoch Q + 1, some T), lct)
            else
              semFwdHook P Dh encPt encT lam sh qep B sCAmb ex Q w isDel none pk pq'
                honestC (mkC (sC.base.mir.epoch Q + 1) (some T))
      | some ci =>
        let g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
        if g.rejects i then
          return (some .rejected, (sC, ex))
        else
          semFwdHook P Dh encPt encT lam sh qep B sC ex Q w isDel (some ci) pk pq'
            honestC (mkC g.epoch T?)

omit [SampleableType PQC] in
theorem simRecvHookC_eval {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {σExtra : Ty S} {Ex : Type} {exEnc : Ex → σExtra.denote}
    {ExBound : ℕ → Ex → Prop} {L : ℕ}
    {hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra}
    {sh : SemHook PQC Pt ℓ T Ex}
    (h_hk : HookMatch P Dh encPt encT decT lam K toKemCoins exEnc ExBound L hk sh)
    (qep B : ℕ) {Γ}
    (st : Expr OFig Γ (.prod simStateCTy σExtra))
    (qParty : Expr OFig Γ .bool) (w : Expr OFig Γ (.base .wire))
    (isDel : Expr OFig Γ .bool) (ρ : Env Γ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hBound : SimCStateBounded L sC₀)
    (hEx : ExBound L ex₀)
    (hsC : simStateCDec (st.eval ρ).1 = sC₀)
    (hex : (st.eval ρ).2 = exEnc ex₀)
    (hq : qParty.eval ρ = partyEnc Q) :
    Prod.map id (Prod.map simStateCDec id) <$>
      (simRecvHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
        st qParty w isDel).eval ρ =
    Prod.map (Option.map SM.smRrEnc) (Prod.map id exEnc) <$>
      semRecvHook P Dh encPt encT decT lam sh qep B sC₀ ex₀ Q (w.eval ρ) (isDel.eval ρ) := by
  unfold simRecvHookC semRecvHook
  rw [comp_eval_bind_ret]
  dsimp only [Expr.eval]
  set ρ₁ := Env.cons
    (t := .prod (.prod simStateCTy σExtra) (.prod .bool (.prod (.base SimSort.wire) .bool)))
    (st.eval ρ, qParty.eval ρ, w.eval ρ, isDel.eval ρ) ρ
  have hs0 : (scBase (.fst (.fst (Expr.v0 (O := OFig))))).eval ρ₁ = simStateEnc sC₀.base := by
    rw [scBase_eval]; exact congrArg (simStateEnc ∘ LibsignalToModularSchemeSimState.base) hsC
  rw [comp_eval_ite]
  have href :
      (orE (ssStopped (scBase (.fst (.fst (Expr.v0 (O := OFig))))))
        (orE (mWin (ssMir (scBase (.fst (.fst .v0)))))
          (orE (.and (.snd (.snd (.snd .v0)))
              (.not (isSomeE (mInTransitFigE P Dh encPt encT decT lam K toKemCoins L
                (ssMir (scBase (.fst (.fst .v0)))) (otherE (.fst (.snd .v0)))
                (.fst (.snd (.snd .v0)))))))
            (.and (.not (.snd (.snd (.snd .v0))))
              (orE (isSomeE (mInTransitFigE P Dh encPt encT decT lam K toKemCoins L
                  (ssMir (scBase (.fst (.fst .v0)))) (otherE (.fst (.snd .v0)))
                  (.fst (.snd (.snd .v0)))))
                (orE (.not (mSafeInjE (ssMir (scBase (.fst (.fst .v0))))))
                  (.not (Expr.op (O := OFig) SimOp.injOK (.fst (.snd (.snd .v0))))))))))).eval ρ₁ =
      (sC₀.base.stopped || sC₀.base.mir.win ||
        (isDel.eval ρ && (sC₀.base.mir.inTransit Q.other (w.eval ρ)).isNone) ||
        (!isDel.eval ρ && ((sC₀.base.mir.inTransit Q.other (w.eval ρ)).isSome ||
          !(sC₀.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT (w.eval ρ))))) := by
    have hinTr := mInTransitFigE_eval P Dh encPt encT decT lam K toKemCoins L
      (ssMir (scBase (.fst (.fst .v0)))) (otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
      ρ₁ sC₀.base.mir Q.other hBound.base.trans_le
      (by simp [ssMir, hs0, simStateEnc])
      (by simp [ρ₁, hq, otherE, partyEnc_other, Expr.eval, Expr.v0])
    have his := isSomeE_eval
      (mInTransitFigE P Dh encPt encT decT lam K toKemCoins L
        (ssMir (scBase (.fst (.fst .v0)))) (otherE (.fst (.snd .v0)))
        (.fst (.snd (.snd .v0)))) ρ₁
    have hsi := mSafeInjE_eval (O' := OFig) (ssMir (scBase (.fst (.fst .v0)))) ρ₁ sC₀.base.mir
      (by simp [ssMir, hs0, simStateEnc])
    rw [orE_eval, orE_eval, orE_eval]
    dsimp only [Expr.eval]
    rw [orE_eval, orE_eval]
    dsimp only [Expr.eval, ssStopped, mWin]
    rw [his, hinTr, hsi]
    dsimp only [ssMir, Expr.eval]
    rw [hs0]
    simp [ρ₁, simStateEnc, simMirEnc, simOpsUnitCost,
      Bool.or_assoc, Expr.eval, Expr.v0]
  rw [href]
  by_cases h1 :
      (sC₀.base.stopped || sC₀.base.mir.win ||
        (isDel.eval ρ && (sC₀.base.mir.inTransit Q.other (w.eval ρ)).isNone) ||
        (!isDel.eval ρ && ((sC₀.base.mir.inTransit Q.other (w.eval ρ)).isSome ||
          !(sC₀.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT (w.eval ρ))))) = true
  · simp [ρ₁, h1, hsC, hex, Prod.map, Expr.eval, Expr.v0]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [comp_eval_caseOpt]
    have hparse := parseRecvFigCE_eval P Dh encPt encT decT lam K toKemCoins (2 ^ 32)
      (.pair (.fst (.snd .v0)) (.pair (pGet (ssPq (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))
        (.fst (.snd (.snd .v0)))))
      ρ₁ (partyEnc Q) (sC₀.base.pq Q) (w.eval ρ)
      (by cases Q <;>
            simp [ρ₁, hsC, hq, pGet_eval, ssPq, simStateEnc, partyEnc, Expr.eval, Expr.v0])
    rw [hparse]
    rcases simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC₀.base.pq Q) (w.eval ρ) with
      _ | ⟨pq', i, pk, T?, lct⟩
    · simp [ρ₁, hsC, hex, SM.smRrEnc, Prod.map, Expr.eval, Expr.v0]
    · dsimp only []
      set ρ₂ := Env.cons
        (t := parsedRecvTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        (pq', i, pk, T?, lct) ρ₁
      have hs1 : (scBase (.fst (.fst (Expr.v1 (O := OFig))))).eval ρ₂ = simStateEnc sC₀.base := hs0
      have hfindC :
          (findChainFigE P Dh encPt encT decT lam K toKemCoins
            (.pair (pGet (ssChains (scBase (.fst (.fst .v1)))) (.fst (.snd .v1)))
              (.fst (.snd (.snd .v0))))).eval ρ₂ =
          match (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with
          | some ci => some (ci, ghostChainEnc ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩))
          | none => none := by
        refine (findChainFigE_eval P Dh encPt encT decT lam K toKemCoins _ ρ₂
          ((sC₀.base.chains Q).map ghostChainEnc) pk
          (by rw [List.length_map]; exact hBound.base.chains_le Q) ?_).trans
          (simFindChain_map_ghostChainEnc (sC₀.base.chains Q) pk)
        cases Q <;>
          simp [ρ₂, ρ₁, hsC, hq, pGet_eval, ssChains, simStateEnc, partyEnc,
            Expr.eval, Expr.v0, Expr.v1]
      rw [comp_eval_caseOpt, hfindC]
      set honestC := (sC₀.base.honest.find? fun wc =>
        wc.1 == w.eval ρ && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
      set mkC : ℕ → Option Pt → SimFig8C Pt := fun t T =>
        match honestC with
        | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
        | none => ((t, T), lct)
      have hhc1 := honestCFigE_eval P Dh encPt encT decT lam K toKemCoins L
        (scBase (.fst (.fst .v1))) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
        ρ₂ sC₀.base Q (w.eval ρ) hBound.base.honest_le hs1 hq rfl
      clear hfindC
      rcases hidx : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · have hev1 := evictedHonestFigE_eval P Dh encPt encT decT lam K toKemCoins
          (scBase (.fst (.fst .v1))) (.fst (.snd .v1))
          (honestCFigE P Dh encPt encT decT lam K toKemCoins L
            (scBase (.fst (.fst .v1))) (.fst (.snd .v1)) (.fst (.snd (.snd .v1))))
          ρ₂ sC₀.base Q hs1 hq
        have hse1 := honestSaltEqFigE_eval P Dh encPt encT decT lam K toKemCoins
          (honestCFigE P Dh encPt encT decT lam K toKemCoins L
            (scBase (.fst (.fst .v1))) (.fst (.snd .v1)) (.fst (.snd (.snd .v1))))
          (.snd (.snd (.snd (.snd .v0)))) ρ₂
        rw [hhc1] at hev1 hse1
        have hsAmb1 := sAmbFigE_eval P Dh encPt encT decT lam K toKemCoins
          (scBase (.fst (.fst .v1))) (.fst (.snd .v1)) ρ₂ sC₀.base Q
          (hBound.base.chains_le Q) hs1 hq
        set amb := inReceiveOnlyEpoch sC₀.base.mir Q || (Q == Party.A && (sC₀.base.chains Q).any (·.key.isNone))
        set sCAmb : LibsignalToModularSchemeSimState PQ Pt ℓ :=
          { sC₀ with base := if amb then { sC₀.base with amb := sC₀.base.amb + 1 } else sC₀.base }
        have hsCAmb1 : simStateCDec
            ((scSetBase (.fst (.fst .v1))
              (sAmbFigE P Dh encPt encT decT lam K toKemCoins
                (scBase (.fst (.fst .v1))) (.fst (.snd .v1)))).eval ρ₂) = sCAmb := by
          rw [scSetBase_eval _ _ ρ₂ _ hsAmb1]
          exact congrArg (fun x => { x with base := sCAmb.base }) hsC
        rw [comp_eval_ite]
        have hcond1 : (Expr.and
            (evictedHonestFigE P Dh encPt encT decT lam K toKemCoins
              (scBase (.fst (.fst .v1))) (.fst (.snd .v1))
              (honestCFigE P Dh encPt encT decT lam K toKemCoins L
                (scBase (.fst (.fst .v1))) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))))
            (honestSaltEqFigE P Dh encPt encT decT lam K toKemCoins
              (honestCFigE P Dh encPt encT decT lam K toKemCoins L
                (scBase (.fst (.fst .v1))) (.fst (.snd .v1)) (.fst (.snd (.snd .v1))))
              (.snd (.snd (.snd (.snd .v0)))))).eval ρ₂ =
            (((honestC.map fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true) &&
             ((honestC.map fun c => decide (c.2.2.2 = lct.2.2)) == some true)) := by
          dsimp only [Expr.eval]
          rw [hev1, hse1]
          rfl
        rw [hcond1]
        by_cases hc1 :
            (((honestC.map fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true) &&
             ((honestC.map fun c => decide (c.2.2.2 = lct.2.2)) == some true)) = true
        · simp only [hc1, ↓reduceIte]
          rw [comp_eval_ret, map_pure]
          simp [ρ₂, ρ₁, hsC, hex, SM.smRrEnc, Prod.map, Expr.eval, Expr.v1]
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
          rw [comp_eval_ite]
          have hzero : (Expr.op (O := OFig) SimOp.isZeroPt
              (.fst (.snd (.snd (.snd .v0))))).eval ρ₂ = (T? == some 0) := rfl
          rw [hzero]
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte]
            rw [comp_eval_ret, map_pure]
            simp [ρ₂, ρ₁, hsC, hex, SM.smRrEnc, Prod.map, Expr.eval, Expr.v1]
          · simp only [hz, Bool.false_eq_true, ↓reduceIte]
            rw [comp_eval_ite]
            have hcond2 :
                (orE (mInWinE (ssMir (scBase (.fst (.fst (Expr.v1 (O := OFig))))))
                    (.fst (.snd .v1)))
                  (orE (.lt (.nat 25000) (.sub (.fst (.snd .v0)) (.nat 1)))
                    (leN (.nat (2 ^ 32)) (.fst (.snd .v0))))).eval ρ₂ =
                (inReceiveOnlyEpoch sC₀.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) := by
              rw [orE_eval, orE_eval,
                mInWinE_eval (O' := OFig) (ssMir (scBase (.fst (.fst .v1)))) (.fst (.snd .v1))
                  ρ₂ sC₀.base.mir Q (by simp [ssMir, hs1, simStateEnc]) hq,
                leN_eval, Bool.or_assoc]
              rfl
            rw [hcond2]
            by_cases hc2 :
                (inReceiveOnlyEpoch sC₀.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte]
              rw [comp_eval_ret, map_pure]
              simp only [expr_pair_eval, expr_some_eval, Prod.map, hsCAmb1]
              simp [ρ₂, ρ₁, hex, SM.smRrEnc, Expr.eval, Expr.v1]
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
              rw [comp_eval_caseOpt]
              have hT0 : (Expr.fst (.snd (.snd (.snd (Expr.v0 (O := OFig)))))).eval ρ₂ = T? := rfl
              rw [hT0]
              rcases T? with _ | T <;> dsimp only []
              · rw [comp_eval_ret, map_pure]
                simp only [expr_pair_eval, expr_some_eval, Prod.map, hsCAmb1]
                simp [ρ₂, ρ₁, hex, SM.smRrEnc, Expr.eval, Expr.v1]
              · set ρ₃ := Env.cons (t := .base SimSort.pt) T ρ₂
                have hBoundAmb : SimCStateBounded L sCAmb := by
                  refine ⟨?_, hBound.sent_le, hBound.snaps_le⟩
                  dsimp only [sCAmb]
                  split_ifs
                  · exact ⟨hBound.base.1, hBound.base.2, hBound.base.3,
                      hBound.base.4, hBound.base.5, hBound.base.6⟩
                  · exact hBound.base
                have hs2 : (scBase (.fst (.fst (Expr.v2 (O := OFig))))).eval ρ₃ =
                    simStateEnc sC₀.base := hs1
                have hsAmb2 := sAmbFigE_eval P Dh encPt encT decT lam K toKemCoins
                  (scBase (.fst (.fst .v2))) (.fst (.snd .v2)) ρ₃ sC₀.base Q
                  (hBound.base.chains_le Q) hs2 hq
                have hsCAmb2 : simStateCDec
                    ((scSetBase (.fst (.fst (Expr.v2 (O := OFig))))
                      (sAmbFigE P Dh encPt encT decT lam K toKemCoins
                        (scBase (.fst (.fst .v2))) (.fst (.snd .v2)))).eval ρ₃) = sCAmb := by
                  rw [scSetBase_eval _ _ ρ₃ _ hsAmb2]
                  exact congrArg (fun x => { x with base := sCAmb.base }) hsC
                have hhc2 :
                    (honestCFigE P Dh encPt encT decT lam K toKemCoins L
                      (scBase (.fst (.fst .v2))) (.fst (.snd .v2))
                      (.fst (.snd (.snd .v2)))).eval ρ₃ = honestC :=
                  honestCFigE_eval P Dh encPt encT decT lam K toKemCoins L
                    (scBase (.fst (.fst .v2))) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))
                    ρ₃ sC₀.base Q (w.eval ρ) hBound.base.honest_le hs2 hq rfl
                have hev2 : (evictedHonestFigE P Dh encPt encT decT lam K toKemCoins
                    (scBase (.fst (.fst .v2))) (.fst (.snd .v2))
                    (honestCFigE P Dh encPt encT decT lam K toKemCoins L
                      (scBase (.fst (.fst .v2))) (.fst (.snd .v2))
                      (.fst (.snd (.snd .v2))))).eval ρ₃ =
                    ((honestC.map fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) ==
                      some true) := by
                  rw [evictedHonestFigE_eval P Dh encPt encT decT lam K toKemCoins
                    (scBase (.fst (.fst .v2))) (.fst (.snd .v2)) _ ρ₃ sC₀.base Q hs2 hq, hhc2]
                have hep2 :
                    (Expr.add (pGet (mEpoch (ssMir (scBase (.fst (.fst (Expr.v2 (O := OFig)))))))
                      (.fst (.snd .v2))) (.nat 1)).eval ρ₃ = sC₀.base.mir.epoch Q + 1 := by
                  cases Q <;>
                    simp [ρ₃, ρ₂, ρ₁, hsC, hq, pGet_eval, mEpoch, ssMir, simStateEnc, simMirEnc,
                      partyEnc, Expr.eval, Expr.v2]
                rw [comp_eval_ite, hev2]
                by_cases hev_b :
                    ((honestC.map fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) ==
                      some true) = true
                · simp only [hev_b, ↓reduceIte]
                  have hc'2 :
                      (Expr.pair
                        (.pair (.add (pGet (mEpoch (ssMir (scBase (.fst (.fst .v2)))))
                            (.fst (.snd .v2))) (.nat 1))
                          (.some (Expr.v0 (O := OFig))))
                        (.snd (.snd (.snd (.snd .v1))))).eval ρ₃ =
                      ((sC₀.base.mir.epoch Q + 1, some T), lct) := by
                    rw [expr_pair_eval, expr_pair_eval, hep2, expr_some_eval]; rfl
                  rw [fwdEvictHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk qep B
                    _ (.snd (.fst .v2)) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))
                    (.snd (.snd (.snd .v2))) (.fst (.snd (.snd .v1))) (.fst .v1) _
                    ρ₃ sCAmb ex₀ Q hBoundAmb.base hEx hsCAmb2 hex hq, hc'2]
                  rfl
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte]
                  have hmk2 :
                      (mkCFigE P Dh encPt encT decT lam K toKemCoins
                        (honestCFigE P Dh encPt encT decT lam K toKemCoins L
                          (scBase (.fst (.fst .v2))) (.fst (.snd .v2)) (.fst (.snd (.snd .v2))))
                        (.snd (.snd (.snd (.snd .v1))))
                        (.add (pGet (mEpoch (ssMir (scBase (.fst (.fst .v2)))))
                          (.fst (.snd .v2))) (.nat 1))
                        (.some .v0)).eval ρ₃ =
                      mkC (sC₀.base.mir.epoch Q + 1) (some T) := by
                    rw [mkCFigE_eval, hhc2, hep2]
                    dsimp only [mkC, Expr.eval]
                    cases honestC <;> rfl
                  rw [fwdHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk qep B
                    _ (.snd (.fst .v2)) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))
                    (.snd (.snd (.snd .v2))) .none (.fst (.snd (.snd .v1))) (.fst .v1)
                    _ _ ρ₃ sCAmb ex₀ Q hBoundAmb hEx hsCAmb2 hex hq, hhc2, hmk2]
                  rfl
      · set g := (sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩
        set ρ₃ := Env.cons (t := .prod .nat (ghostChainTy PQ PQC Pt ℓ))
          (ci, ghostChainEnc g) ρ₂
        rw [comp_eval_ite]
        have hrej : (Expr.op (O := OFig) SimOp.chainRejects
            (.pair (.snd (.snd (.snd .v0))) (.fst (.snd .v1)))).eval ρ₃ = g.rejects i := by
          simp [ρ₃, ρ₂, simOpsUnitCost, Expr.eval, Expr.v0, Expr.v1]
        rw [hrej]
        by_cases hrej_b : g.rejects i = true
        · simp only [hrej_b, ↓reduceIte]
          rw [comp_eval_ret, map_pure]
          simp [ρ₃, ρ₂, ρ₁, hsC, hex, SM.smRrEnc, Prod.map, Expr.eval, Expr.v2]
        · simp only [hrej_b, Bool.false_eq_true, ↓reduceIte]
          have hs2 : (scBase (.fst (.fst (Expr.v2 (O := OFig))))).eval ρ₃ =
              simStateEnc sC₀.base := hs1
          have hhc3 :
              (honestCFigE P Dh encPt encT decT lam K toKemCoins L
                (scBase (.fst (.fst .v2))) (.fst (.snd .v2))
                (.fst (.snd (.snd .v2)))).eval ρ₃ = honestC :=
            honestCFigE_eval P Dh encPt encT decT lam K toKemCoins L
              (scBase (.fst (.fst .v2))) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))
              ρ₃ sC₀.base Q (w.eval ρ) hBound.base.honest_le hs2 hq rfl
          have hmk3 :
              (mkCFigE P Dh encPt encT decT lam K toKemCoins
                (honestCFigE P Dh encPt encT decT lam K toKemCoins L
                  (scBase (.fst (.fst .v2))) (.fst (.snd .v2)) (.fst (.snd (.snd .v2))))
                (.snd (.snd (.snd (.snd .v1))))
                (.fst (.snd (.snd .v0)))
                (.fst (.snd (.snd (.snd .v1))))).eval ρ₃ = mkC g.epoch T? := by
            rw [mkCFigE_eval, hhc3]
            dsimp only [mkC, Expr.eval]
            cases honestC <;> rfl
          rw [fwdHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk qep B
            (.fst (.fst .v2)) (.snd (.fst .v2)) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))
            (.snd (.snd (.snd .v2))) (.some (.fst .v0)) (.fst (.snd (.snd .v1))) (.fst .v1)
            _ _ ρ₃ sC₀ ex₀ Q hBound hEx hsC hex hq, hhc3, hmk3]
          rfl

def semCorrHook {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex) (Q : Party) :
    OracleComp T (Option (GhostState PQ) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) := do
  if sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
     inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) then
    return (none, (sC, ex))
  else
    let (res, ex₁) ← sh.onCr Q ex
    match res with
    | none => return (none, (sC, ex₁))
    | some fig8st =>
      let chains' : Party → List GhostChain :=
        if Q == Party.B && sC.base.mir.epoch Party.B == 0 then
          match fig8st.γ with
          | .exp x => Function.update sC.base.chains Party.A
              ((sC.base.chains Party.A).map fun g =>
                if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => sC.base.chains
        else sC.base.chains
      let base' : SimState PQ Pt ℓ :=
        { sC.base with mir := sC.base.mir.afterCorr Q, chains := chains' }
      let ghostOut := toGhost P { sC.base with chains := chains' } Q fig8st
      let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        { base := base'
          kept := Function.update sC.kept Q (Kept.ofSt fig8st)
          sent := sC.sent
          snaps := (Q, sC.base.mir.epoch Q, ghostOut) :: sC.snaps }
      return (some ghostOut, (sC', ex₁))

def semCorrHookDedup {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex) (Q : Party) :
    OracleComp T (Option (GhostState PQ) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) := do
  if sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
     inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) then
    return (none, (sC, ex))
  else
    let (res, ex₁) ← sh.onCr Q ex
    match res with
    | none => return (none, (sC, ex₁))
    | some fig8st =>
      let chains' : Party → List GhostChain :=
        if Q == Party.B && sC.base.mir.epoch Party.B == 0 then
          match fig8st.γ with
          | .exp x => Function.update sC.base.chains Party.A
              ((sC.base.chains Party.A).map fun g =>
                if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => sC.base.chains
        else sC.base.chains
      let base' : SimState PQ Pt ℓ :=
        { sC.base with mir := afterCorrDedup sC.base.mir Q, chains := chains' }
      let ghostOut := toGhost P { sC.base with chains := chains' } Q fig8st
      let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        { base := base'
          kept := Function.update sC.kept Q (Kept.ofSt fig8st)
          sent := sC.sent
          snaps := (Q, sC.base.mir.epoch Q, ghostOut) :: sC.snaps }
      return (some ghostOut, (sC', ex₁))

omit [SampleableType PQC] in
theorem simCorrHookC_eval {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {σExtra : Ty S} {Ex : Type} {exEnc : Ex → σExtra.denote}
    {ExBound : ℕ → Ex → Prop} {L : ℕ}
    {hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra}
    {sh : SemHook PQC Pt ℓ T Ex}
    (h_hk : HookMatch P Dh encPt encT decT lam K toKemCoins exEnc ExBound L hk sh)
    {Γ} (st : Expr OFig Γ (.prod simStateCTy σExtra)) (qParty : Expr OFig Γ .bool)
    (ρ : Env Γ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hBound : SimStateBounded L sC₀.base)
    (hEx : ExBound L ex₀)
    (hsC : simStateCDec (st.eval ρ).1 = sC₀)
    (hex : (st.eval ρ).2 = exEnc ex₀)
    (hq : qParty.eval ρ = partyEnc Q) :
    Prod.map id (Prod.map simStateCDec id) <$>
      (simCorrHookC P Dh encPt encT decT lam K toKemCoins hk L st qParty).eval ρ =
    Prod.map id (Prod.map id exEnc) <$>
      semCorrHookDedup P Dh encT sh sC₀ ex₀ Q := by
  unfold simCorrHookC semCorrHookDedup
  rw [comp_eval_bind_ret]
  dsimp only [Expr.eval]
  set ρ₁ := Env.cons (t := .prod (.prod simStateCTy σExtra) .bool)
    (st.eval ρ, qParty.eval ρ) ρ
  have hs0 : (scBase (.fst (.fst (Expr.v0 (O := OFig))))).eval ρ₁ = simStateEnc sC₀.base := by
    rw [scBase_eval]; exact congrArg (simStateEnc ∘ LibsignalToModularSchemeSimState.base) hsC
  rw [comp_eval_ite]
  have href :
      (orE (ssStopped (scBase (.fst (.fst (Expr.v0 (O := OFig))))))
        (orE (mWin (ssMir (scBase (.fst (.fst .v0)))))
          (orE (.not (mCorrAllowedE L (ssMir (scBase (.fst (.fst .v0)))) (.snd .v0)))
            (orE (mInWinE (ssMir (scBase (.fst (.fst .v0)))) (.snd .v0))
              (.not (mNoSpkCorrE (ssMir (scBase (.fst (.fst .v0)))) (.snd .v0))))))).eval ρ₁ =
      (sC₀.base.stopped || sC₀.base.mir.win || !(sC₀.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC₀.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)) := by
    have hca := mCorrAllowedE_eval (O' := OFig) L
      (ssMir (scBase (.fst (.fst .v0)))) (.snd .v0) ρ₁ sC₀.base.mir Q
      hBound.trans_le hBound.chall_le hBound.comp_le
      (by simp [ssMir, hs0, simStateEnc]) hq
    have hinw := mInWinE_eval (O' := OFig) (ssMir (scBase (.fst (.fst .v0)))) (.snd .v0)
      ρ₁ sC₀.base.mir Q (by simp [ssMir, hs0, simStateEnc]) hq
    have hnspk := mNoSpkCorrE_eval (O' := OFig) (ssMir (scBase (.fst (.fst .v0)))) (.snd .v0)
      ρ₁ sC₀.base.mir Q (by simp [ssMir, hs0, simStateEnc]) hq
    rw [orE_eval, orE_eval, orE_eval, orE_eval]
    dsimp only [Expr.eval, ssStopped, mWin]
    rw [hca, hinw, hnspk]
    dsimp only [ssMir, Expr.eval]
    rw [hs0]
    simp only [simStateEnc, simMirEnc, Bool.or_assoc]
  rw [href]
  by_cases h1 :
      (sC₀.base.stopped || sC₀.base.mir.win || !(sC₀.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC₀.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)) = true
  · simp [ρ₁, h1, hsC, hex, Prod.map, Expr.eval, Expr.v0]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [comp_eval_bind, h_hk.onCr_eval (.snd .v0) (.snd (.fst .v0)) ρ₁ Q ex₀ hEx hq hex,
      bind_map_left, map_bind, map_bind]
    refine bind_congr fun ⟨res, ex₁⟩ => ?_
    dsimp only [Prod.map, id_eq]
    set ρ₂ := Env.cons (t := .prod (.opt (.base SimSort.fig8st)) σExtra) (res, exEnc ex₁) ρ₁
    rw [comp_eval_caseOpt]
    have hres2 : (Expr.fst (Expr.v0 (O := OFig))).eval ρ₂ = res := rfl
    rw [hres2]
    rcases res with _ | fig8st
    · simp [ρ₂, ρ₁, hsC, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · dsimp only []
      set ρ₃ := Env.cons (t := .base SimSort.fig8st) fig8st ρ₂
      have hs2 : (scBase (.fst (.fst (Expr.v2 (O := OFig))))).eval ρ₃ = simStateEnc sC₀.base := hs0
      set chains' : Party → List GhostChain :=
        if Q == Party.B && sC₀.base.mir.epoch Party.B == 0 then
          match fig8st.γ with
          | .exp x => Function.update sC₀.base.chains Party.A
              ((sC₀.base.chains Party.A).map fun g =>
                if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => sC₀.base.chains
        else sC₀.base.chains
      let chains'_expr :
          Expr OFig
            (.base SimSort.fig8st ::
              .prod (.opt (.base SimSort.fig8st)) σExtra ::
              .prod (.prod simStateCTy σExtra) .bool :: Γ)
            (.prod (.list (ghostChainTy PQ PQC Pt ℓ))
              (.list (ghostChainTy PQ PQC Pt ℓ))) :=
        .ite (.and (.snd .v2) (.eqN (.snd (mEpoch (ssMir (scBase (.fst (.fst .v2)))))) (.nat 0)))
          (.pair
            (revealSpkChainsFigE P Dh encPt encT decT lam K toKemCoins
              (.pair (.fst (ssChains (scBase (.fst (.fst .v2))))) .v0))
            (.snd (ssChains (scBase (.fst (.fst .v2))))))
          (ssChains (scBase (.fst (.fst .v2))))
      have hchains : chains'_expr.eval ρ₃ =
          ((chains' .A).map ghostChainEnc, (chains' .B).map ghostChainEnc) := by
        dsimp only [chains'_expr]
        rw [ite_eval]
        have hcond : (Expr.and (.snd (Expr.v2 (O := OFig)))
            (.eqN (.snd (mEpoch (ssMir (scBase (.fst (.fst .v2)))))) (.nat 0))).eval ρ₃ =
            (Q == Party.B && sC₀.base.mir.epoch Party.B == 0) := by
          cases Q <;>
            simp [ρ₃, ρ₂, ρ₁, hsC, hq, mEpoch, ssMir, simStateEnc, simMirEnc, partyEnc, BEq.beq,
              Expr.eval, Expr.v2]
        rw [hcond]
        by_cases hc : (Q == Party.B && sC₀.base.mir.epoch Party.B == 0) = true
        · simp only [hc, ↓reduceIte, chains', expr_pair_eval]
          have hA : ((ssChains (scBase (.fst (.fst (Expr.v2 (O := OFig)))))).eval ρ₃).1 =
              (sC₀.base.chains .A).map ghostChainEnc := by
            simp [ssChains, hs2, simStateEnc]
          have hB : ((ssChains (scBase (.fst (.fst (Expr.v2 (O := OFig)))))).eval ρ₃).2 =
              (sC₀.base.chains .B).map ghostChainEnc := by
            simp [ssChains, hs2, simStateEnc]
          have hrev := revealSpkChainsFigE_eval P Dh encPt encT decT lam K toKemCoins
            (.pair (.fst (ssChains (scBase (.fst (.fst .v2))))) .v0) ρ₃
            ((sC₀.base.chains .A).map ghostChainEnc) fig8st
            (by rw [List.length_map]; exact hBound.chains_le .A)
            (by rw [expr_pair_eval]; exact Prod.ext hA rfl)
          rw [hrev, expr_snd_eval, hB, simRevealSpkChains_map_ghostChainEnc]
          rcases fig8st.γ with _ | x <;> simp [Function.update]
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, chains', ssChains, Expr.eval, hs2,
            simStateEnc]
      have hafc := mAfterCorrE_eval (O' := OFig) L
        (ssMir (scBase (.fst (.fst .v2)))) (.snd .v2) ρ₃ sC₀.base.mir Q
        hBound.trans_le hBound.comp_u (by simp [ssMir, hs2, simStateEnc]) hq
      have hpchains : (pGet chains'_expr (.snd .v2)).eval ρ₃ =
          (chains' Q).map ghostChainEnc := by
        rw [pGet_eval, hchains]
        cases Q <;> simp [ρ₃, ρ₂, ρ₁, hq, partyEnc, Expr.eval, Expr.v2]
      have hchains'_le : (chains' Q).length ≤ 5 := by
        dsimp only [chains']
        split_ifs
        · rcases fig8st.γ with _ | x
          · exact hBound.chains_le Q
          · cases Q <;> simp [Function.update, hBound.chains_le .A, hBound.chains_le .B]
        · exact hBound.chains_le Q
      have hghost :
          (toGhostFigE P Dh encPt encT decT lam K toKemCoins
            (.pair (.snd .v2)
              (.pair .v0
                (.pair (pGet (ssPn (scBase (.fst (.fst .v2)))) (.snd .v2))
                  (.pair (pGet chains'_expr (.snd .v2))
                    (.pair (ssUnackA (scBase (.fst (.fst .v2))))
                      (.pair (pGet (ssPq (scBase (.fst (.fst .v2)))) (.snd .v2))
                        (pGet (mEpoch (ssMir (scBase (.fst (.fst .v2)))))
                          (.snd .v2))))))))).eval ρ₃ =
          toGhost P { sC₀.base with chains := chains' } Q fig8st := by
        rw [← simToGhost_eq P { sC₀.base with chains := chains' } Q fig8st]
        refine toGhostFigE_eval P Dh encPt encT decT lam K toKemCoins _ ρ₃
          (partyEnc Q) fig8st (sC₀.base.pn Q) ((chains' Q).map ghostChainEnc)
          sC₀.base.unackA (sC₀.base.pq Q) (sC₀.base.mir.epoch Q)
          (by rw [List.length_map]; exact hchains'_le) ?_
        simp only [expr_pair_eval, hpchains]
        cases Q <;>
          simp [ρ₃, ρ₂, ρ₁, hsC, hq, pGet_eval, ssPn, ssUnackA, ssPq, mEpoch, ssMir,
            simStateEnc, simMirEnc, partyEnc, Expr.eval, Expr.v0, Expr.v2]
      dsimp only [chains'_expr] at hghost
      have hbase' :
          (ssMk (mAfterCorrE L (ssMir (scBase (.fst (.fst .v2)))) (.snd .v2))
            (ssPq (scBase (.fst (.fst .v2)))) (ssPn (scBase (.fst (.fst .v2))))
            (ssUnackA (scBase (.fst (.fst .v2)))) (ssHonest (scBase (.fst (.fst .v2))))
            chains'_expr
            (ssAmb (scBase (.fst (.fst .v2))))
            (ssStopped (scBase (.fst (.fst .v2))))).eval ρ₃ =
          simStateEnc { sC₀.base with mir := afterCorrDedup sC₀.base.mir Q, chains := chains' } := by
        simp only [ssMk, ssPq, ssPn, ssUnackA, ssHonest, ssAmb, ssStopped,
          expr_pair_eval, expr_fst_eval, expr_snd_eval, hafc, hchains, hs2, simStateEnc]
      rw [comp_eval_ret, map_pure, map_pure]
      simp only [expr_pair_eval, expr_some_eval, hghost, Prod.map, id_eq]
      congr 1
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      rw [scMk_pSet_kept_eval _ _ _ _ _ _ ρ₃ _ hbase']
      have hepQ : (pGet (mEpoch (ssMir (scBase (.fst (.fst (Expr.v2 (O := OFig)))))))
          (.snd .v2)).eval ρ₃ = sC₀.base.mir.epoch Q := by
        cases Q <;>
          simp [ρ₃, ρ₂, ρ₁, hsC, hq, pGet_eval, mEpoch, ssMir, simStateEnc, simMirEnc,
            partyEnc, Expr.eval, Expr.v2]
      have hsnaps3 :
          ((Expr.cons
            (.pair (.snd .v2)
              (.pair (pGet (mEpoch (ssMir (scBase (.fst (.fst .v2))))) (.snd .v2))
                (toGhostFigE P Dh encPt encT decT lam K toKemCoins
                  (.pair (.snd .v2)
                    (.pair .v0
                      (.pair (pGet (ssPn (scBase (.fst (.fst .v2)))) (.snd .v2))
                        (.pair (pGet chains'_expr (.snd .v2))
                          (.pair (ssUnackA (scBase (.fst (.fst .v2))))
                            (.pair (pGet (ssPq (scBase (.fst (.fst .v2)))) (.snd .v2))
                              (pGet (mEpoch (ssMir (scBase (.fst (.fst .v2)))))
                                (.snd .v2)))))))))))
            (scSnaps (.fst (.fst .v2)))).eval ρ₃).map snapDec =
          (Q, sC₀.base.mir.epoch Q,
            toGhost P { sC₀.base with chains := chains' } Q fig8st) :: sC₀.snaps := by
        change snapDec ((Expr.snd (Expr.v2 (O := OFig))).eval ρ₃,
            (pGet (mEpoch (ssMir (scBase (.fst (.fst .v2))))) (.snd .v2)).eval ρ₃,
            (toGhostFigE P Dh encPt encT decT lam K toKemCoins _).eval ρ₃) ::
          List.map snapDec ((scSnaps (.fst (.fst .v2))).eval ρ₃) = _
        rw [hepQ, hghost, scSnaps_eval, List.map_map]
        simp only [Function.comp_def, snapDec_snapEnc]
        simp [ρ₃, ρ₂, ρ₁, hsC, hq, snapDec, partyDec_partyEnc, Expr.eval, Expr.v2]
      dsimp only [chains'_expr] at hsnaps3
      rw [hsnaps3, keptOfStE_eval, scSent_eval]
      dsimp only [chains']
      rcases fig8st.γ with _ | x <;>
        simp [ρ₃, ρ₂, ρ₁, hsC, hq, partyDec_partyEnc, Expr.eval, Expr.v0, Expr.v2]

def semHandleHook {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep B : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex) :
    OracleComp T
      ((SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range t ×
        (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) :=
  match t with
  | .inl (.inl (.inl (.inl (Q, m, r)))) =>
    semSendHook P Dh encPt encT lam sh qep sC ex Q m none r
  | .inl (.inl (.inl (.inr (Q, m₀, m₁, r)))) =>
    semSendHook P Dh encPt encT lam sh qep sC ex Q m₀ (some m₁) r
  | .inl (.inl (.inr (Q, w))) => do
    let j? := sC.base.honest.reverse.findIdx? (fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let (rr, (sC₁, ex₁)) ← semRecvHook P Dh encPt encT decT lam sh qep B sC ex Q w true
    let ex₂ ← sh.onDeliverPost Q j? rr ex₁
    return (rr, (sC₁, ex₂))
  | .inl (.inr (Q, w)) =>
    semRecvHook P Dh encPt encT decT lam sh qep B sC ex Q w false
  | .inr Q =>
    semCorrHook P Dh encT sh sC ex Q

def semHandleHookDedup {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep B : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex) :
    OracleComp T
      ((SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range t ×
        (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) :=
  match t with
  | .inl (.inl (.inl (.inl (Q, m, r)))) =>
    semSendHook P Dh encPt encT lam sh qep sC ex Q m none r
  | .inl (.inl (.inl (.inr (Q, m₀, m₁, r)))) =>
    semSendHook P Dh encPt encT lam sh qep sC ex Q m₀ (some m₁) r
  | .inl (.inl (.inr (Q, w))) => do
    let j? := sC.base.honest.reverse.findIdx? (fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let (rr, (sC₁, ex₁)) ← semRecvHook P Dh encPt encT decT lam sh qep B sC ex Q w true
    let ex₂ ← sh.onDeliverPost Q j? rr ex₁
    return (rr, (sC₁, ex₂))
  | .inl (.inr (Q, w)) =>
    semRecvHook P Dh encPt encT decT lam sh qep B sC ex Q w false
  | .inr Q =>
    semCorrHookDedup P Dh encT sh sC ex Q

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp]
theorem option_map_smRrDec_smRrEnc (rr : Option (RecvResult (Plain ℓ))) :
    (rr.map SM.smRrEnc).map SM.smRrDec = rr := by
  rcases rr with _ | (_ | ⟨t, i, m⟩) <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem comp_eval_caseSum_inl {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι}
    {I : Iface S' T} {Γ} {a b u : Ty S'} (e : Expr O' Γ (.sum a b))
    (l : Comp O' I (a :: Γ) u) (r : Comp O' I (b :: Γ) u) (ρ : Env Γ) (x : a.denote)
    (he : e.eval ρ = .inl x) :
    (Comp.caseSum e l r).eval ρ = l.eval (Env.cons x ρ) := by
  simp [Comp.eval, he]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem comp_eval_caseSum_inr {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι}
    {I : Iface S' T} {Γ} {a b u : Ty S'} (e : Expr O' Γ (.sum a b))
    (l : Comp O' I (a :: Γ) u) (r : Comp O' I (b :: Γ) u) (ρ : Env Γ) (y : b.denote)
    (he : e.eval ρ = .inr y) :
    (Comp.caseSum e l r).eval ρ = r.eval (Env.cons y ρ) := by
  simp [Comp.eval, he]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem map_semRecv_eq {ι : Type} {T : OracleSpec ι} {σExtra : Ty S} {Ex : Type}
    (exEnc : Ex → σExtra.denote)
    (oa : OracleComp T (Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex))) :
    Prod.map id (Prod.map id exEnc) <$> oa =
      Prod.map (Option.map SM.smRrDec) id <$>
        (Prod.map (Option.map SM.smRrEnc) (Prod.map id exEnc) <$> oa) := by
  rw [Functor.map_map]
  congr 1
  funext ⟨rr, sC, ex⟩
  rcases rr with _ | (_ | ⟨t, i, m⟩) <;> rfl

omit [SampleableType PQC] in
theorem handlerImpl_simHandleHookC_eval {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {σExtra : Ty S} {Ex : Type} {exEnc : Ex → σExtra.denote}
    {ExBound : ℕ → Ex → Prop} {L : ℕ}
    {hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra}
    {sh : SemHook PQC Pt ℓ T Ex}
    (h_hk : HookMatch P Dh encPt encT decT lam K toKemCoins exEnc ExBound L hk sh)
    (qep B : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st_raw : (Ty.prod simStateCTy σExtra).denote)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex)
    (hBound : SimCStateBounded L sC₀)
    (hEx : ExBound L ex₀)
    (hsC : simStateCDec st_raw.1 = sC₀)
    (hex : st_raw.2 = exEnc ex₀) :
    Prod.map id (Prod.map simStateCDec id) <$>
      ((handlerImpl (C := simCodec PQ PQC Pt ℓ)
        (simHandleHookC P Dh encPt encT decT lam K toKemCoins hk L qep B)
        (.inr t)).run st_raw) =
    Prod.map id (Prod.map id exEnc) <$>
      semHandleHookDedup P Dh encPt encT decT lam sh qep B t sC₀ ex₀ := by
  rcases t with ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · unfold handlerImpl simHandleHookC simCodec semHandleHookDedup
    simp only [StateT.run_mk]
    rw [comp_eval_caseSum_inl _ _ _ _ _ rfl,
      comp_eval_caseSum_inl _ _ _ _ _ rfl,
      comp_eval_caseSum_inl _ _ _ _ _ rfl,
      comp_eval_caseSum_inl _ _ _ _ _ rfl,
      comp_eval_bind]
    simp only [comp_eval_ret, bind_assoc, pure_bind, Prod.mk.eta, bind_pure,
      Expr.eval, Expr.v0, Env.get_cons_zero]
    exact simSendHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk qep B
      .v4 (.fst .v0) (.fst (.snd .v0)) .none (.snd (.snd .v0)) _
      sC₀ ex₀ Q hsC hex rfl
  · unfold handlerImpl simHandleHookC simCodec semHandleHookDedup
    simp only [StateT.run_mk]
    rw [comp_eval_caseSum_inl _ _ _ _ _ rfl,
      comp_eval_caseSum_inl _ _ _ _ _ rfl,
      comp_eval_caseSum_inl _ _ _ _ _ rfl,
      comp_eval_caseSum_inr _ _ _ _ _ rfl,
      comp_eval_bind]
    simp only [comp_eval_ret, bind_assoc, pure_bind, Prod.mk.eta, bind_pure,
      Expr.eval, Expr.v0, Env.get_cons_zero]
    exact simSendHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk qep B
      .v4 (.fst .v0) (.fst (.snd .v0)) (.some (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0))) _
      sC₀ ex₀ Q hsC hex rfl
  · unfold handlerImpl simHandleHookC simCodec semHandleHookDedup
    simp only [StateT.run_mk]
    rw [comp_eval_caseSum_inl _ _ _ _ _ rfl,
      comp_eval_caseSum_inl _ _ _ _ _ rfl,
      comp_eval_caseSum_inr _ _ _ _ _ rfl]
    set ρ₀ := Env.cons (t := .prod .bool (.base SimSort.wire)) (partyEnc Q, w)
      (Env.cons
        (t := .sum (.sum (.prod .bool (.prod (.base SimSort.plain) (.opt (.base SimSort.pqc))))
            (.prod .bool (.prod (.base SimSort.plain)
              (.prod (.base SimSort.plain) (.opt (.base SimSort.pqc))))))
          (.prod .bool (.base SimSort.wire)))
        (Sum.inr (partyEnc Q, w))
        (Env.cons
          (t := .sum (.sum (.sum
                (.prod .bool (.prod (.base SimSort.plain) (.opt (.base SimSort.pqc))))
                (.prod .bool (.prod (.base SimSort.plain)
                  (.prod (.base SimSort.plain) (.opt (.base SimSort.pqc))))))
              (.prod .bool (.base SimSort.wire)))
            (.prod .bool (.base SimSort.wire)))
          (Sum.inl (Sum.inr (partyEnc Q, w)))
          (Env.cons (t := .prod simStateCTy σExtra) st_raw
            (Env.cons (t := (simCodec PQ PQC Pt ℓ).Q)
              (Sum.inl (Sum.inl (Sum.inr (partyEnc Q, w)))) .nil))))
    have hs3 : simStateDec ((scBase (.fst (Expr.v3 (O := OFig)))).eval ρ₀) = sC₀.base := by
      rw [scBase_eval, simStateDec_simStateEnc]
      exact congrArg LibsignalToModularSchemeSimState.base hsC
    have hfr := findRevHonestIdxE_eval P Dh encPt encT decT lam K toKemCoins L
      (scBase (.fst .v3)) (.fst .v0) (.snd .v0) ρ₀
      (by rw [hs3]; exact hBound.base.honest_le)
    have hq0 : partyDec ((Expr.fst (Expr.v0 (O := OFig))).eval ρ₀) = Q :=
      partyDec_partyEnc Q
    have hw0 : (Expr.snd (Expr.v0 (O := OFig))).eval ρ₀ = w := rfl
    rw [hs3, hq0, hw0] at hfr
    set j? := sC₀.base.honest.reverse.findIdx? (fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    rw [comp_eval_bind_ret, expr_pair_eval, hfr]
    have hq_ev : (Expr.fst (Expr.v0 (O := OFig))).eval ρ₀ = partyEnc Q := rfl
    rw [hq_ev]
    set ρ₁ := Env.cons (t := .prod .bool (.opt .nat)) (partyEnc Q, j?) ρ₀
    have hindep : ∀ x : (Ty.prod (.opt (simRrTy PQ PQC Pt ℓ)) (.prod simStateCTy σExtra)).denote,
        (hk.onDeliverPost (.fst .v1) (.snd .v1) (.fst .v0) (.snd (.snd .v0))).eval
          (Env.cons x ρ₁) =
        (hk.onDeliverPost (.fst .v1) (.snd .v1) (.fst .v0) (.snd (.snd .v0))).eval
          (Env.cons (x.1, (st_raw.1, x.2.2)) ρ₁) :=
      fun x => h_hk.onDeliverPost_congr _ _ _ _ _ _ rfl rfl rfl rfl
    have hrec := simRecvHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk qep B
      .v4 (.fst .v1) (.snd .v1) (.bool true) ρ₁ sC₀ ex₀ Q hBound hEx hsC hex rfl
    simp only [comp_eval_bind, comp_eval_ret, bind_assoc, pure_bind]
    trans ((Prod.map id (Prod.map simStateCDec id) <$>
        (simRecvHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
          .v4 (.fst .v1) (.snd .v1) (.bool true)).eval ρ₁) >>= fun y =>
      (hk.onDeliverPost (.fst .v1) (.snd .v1) (.fst .v0) (.snd (.snd .v0))).eval
        (Env.cons (y.1, (st_raw.1, y.2.2)) ρ₁) >>= fun ex2 =>
      pure (Option.map SM.smRrDec y.1, (y.2.1, ex2)))
    · rw [map_bind, bind_map_left]
      refine bind_congr fun x => ?_
      rw [hindep x, map_bind]
      simp only [map_pure]
      rfl
    · rw [hrec, bind_map_left, map_bind]
      refine bind_congr fun ⟨rr, sC₁, ex₁⟩ => ?_
      dsimp only [Prod.map, id_eq]
      rw [h_hk.onDeliverPost_eval (.fst .v1) (.snd .v1) (.fst .v0) (.snd (.snd .v0))
        (Env.cons (rr.map SM.smRrEnc, (st_raw.1, exEnc ex₁)) ρ₁) Q rr ex₁ rfl rfl rfl,
        option_map_smRrDec_smRrEnc, bind_map_left, map_bind]
      simp only [map_pure]
      rfl
  · unfold handlerImpl simHandleHookC simCodec semHandleHookDedup
    simp only [StateT.run_mk]
    rw [comp_eval_caseSum_inl _ _ _ _ _ rfl,
      comp_eval_caseSum_inr _ _ _ _ _ rfl,
      comp_eval_bind]
    set ρ₀ := Env.cons (t := .prod .bool (.base SimSort.wire)) (partyEnc Q, w)
      (Env.cons
        (t := .sum (.sum (.sum
              (.prod .bool (.prod (.base SimSort.plain) (.opt (.base SimSort.pqc))))
              (.prod .bool (.prod (.base SimSort.plain)
                (.prod (.base SimSort.plain) (.opt (.base SimSort.pqc))))))
            (.prod .bool (.base SimSort.wire)))
          (.prod .bool (.base SimSort.wire)))
        (Sum.inr (partyEnc Q, w))
        (Env.cons (t := .prod simStateCTy σExtra) st_raw
          (Env.cons (t := (simCodec PQ PQC Pt ℓ).Q)
            (Sum.inl (Sum.inr (partyEnc Q, w))) .nil)))
    have hrec := simRecvHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk qep B
      .v2 (.fst .v0) (.snd .v0) (.bool false) ρ₀ sC₀ ex₀ Q hBound hEx hsC hex rfl
    have hw0 : (Expr.snd (Expr.v0 (O := OFig))).eval ρ₀ = w := rfl
    have hbf : (Expr.bool (O := OFig) false).eval ρ₀ = false := rfl
    rw [hw0, hbf] at hrec
    rw [map_semRecv_eq exEnc, ← hrec, bind_assoc, map_bind, Functor.map_map,
      map_eq_bind_pure_comp]
    refine bind_congr fun x => ?_
    rcases x with ⟨rr, sC, ex⟩
    rw [comp_eval_ret, pure_bind, map_pure]
    rfl
  · unfold handlerImpl simHandleHookC simCodec semHandleHookDedup
    simp only [StateT.run_mk]
    rw [comp_eval_caseSum_inr _ _ _ _ _ rfl, comp_eval_bind]
    simp only [comp_eval_ret, bind_assoc, pure_bind, Prod.mk.eta, bind_pure,
      Expr.eval, Expr.v0, Env.get_cons_zero]
    exact simCorrHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk
      .v1 .v0 _ sC₀ ex₀ Q hBound.base hEx hsC hex rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem epMgmt_lists (st s₁ : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (Δ qep : ℕ) (Q : Party) (bad : Bool) (h : st.epMgmt Δ qep Q bad = some s₁) :
    s₁.trans = st.trans ∧ s₁.chall = st.chall ∧ s₁.comp = st.comp := by
  unfold GameState.epMgmt at h
  split_ifs at h
  all_goals
    simp only [Option.some.injEq] at h
    subst h
    simp [GameState.leak]

omit [DecidableEq Pt] [SampleableType PQC] in
theorem scPostSendPure_preserves_inv {L m : ℕ}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {s₁ : GameState Unit (Plain ℓ) (List (BitVec 8))}
    {Q : Party} {qep : ℕ} {hasCoins : Bool}
    (hep : sC.base.mir.epMgmt 3 qep Q hasCoins = some s₁)
    (m₀ : Plain ℓ) (isChall : Bool) (pq' : PQ) (pn : BitVec 32) (c : SimFig8C Pt)
    (hInv : SimCStateInv L (m + 1) sC) :
    SimCStateInv L m (scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ isChall pq' pn c) := by
  have hInv0 : SimCStateInv L m sC := hInv.mono (Nat.le_succ m)
  obtain ⟨htr, hch, hcp⟩ := epMgmt_lists sC.base.mir s₁ 3 qep Q hasCoins hep
  refine ⟨⟨?_, ?_, ?_, ?_, hInv0.1.2.2.2.2.1, hInv0.1.2.2.2.2.2⟩, ?_, hInv0.2.2⟩
  · simp only [scPostSendPure, GameState.record, List.length_cons, htr]
    have := hInv.1.1; omega
  · simp only [scPostSendPure, GameState.record, hch]
    cases isChall <;>
      simp only [↓reduceIte, Bool.false_eq_true, List.length_cons] <;>
      (have := hInv.1.2.1; omega)
  · simp only [scPostSendPure, List.length_cons]
    have := hInv.1.2.2.1; omega
  · rcases hInv.1.2.2.2.1 with ⟨U, hUlen, hCU, htrU⟩
    refine ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩ :: U,
      by simp only [List.length_cons]; omega, ?_, ?_⟩
    · simp only [scPostSendPure, GameState.record, hcp]
      cases s₁.safeCh 3 Q
      · exact countLe_cons_cons _ hCU
      · exact countLe_cons_right _ hCU
    · intro r' hr'
      simp only [scPostSendPure, GameState.record, htr, List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · simp
      · exact List.mem_cons_of_mem _ (htrU r' hr')
  · dsimp only [scPostSendPure]
    rcases (sC.kept Q).full with _ | st
    · exact hInv0.2.1
    · dsimp only []
      split_ifs
      · exact hInv0.2.1
      · rcases st.vS with _ | v
        · exact hInv0.2.1
        · simp only [List.length_cons]; have := hInv.2.1; omega

omit [DecidableEq Pt] [SampleableType PQC] in
theorem semSendHook_preserves_sC_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (L m qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (hInv : SimCStateInv L (m + 1) sC₀) :
    ∀ x ∈ support (semSendHook P Dh encPt encT lam sh qep sC₀ ex₀ Q m₀ chal r),
      SimCStateInv L m x.2.1 := by
  have hInv0 : SimCStateInv L m sC₀ := hInv.mono (Nat.le_succ m)
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semSendHook at hx
  by_cases href : (sC₀.base.stopped || sC₀.base.mir.win || !(noBobSendInEpoch0 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC₀.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;>
      simp only [hep] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl, _⟩; exact hInv0
    · by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hch, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨_, rfl, _⟩; exact hInv0
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
        obtain ⟨⟨rq, rc⟩, -, ⟨exOk, exFail⟩, -, hx⟩ := hx
        rcases hpub : mkPub P sC₀.base Q rq
          (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
            BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) with _ | ⟨pq', pub⟩ <;>
          simp only [hpub] at hx
        · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, _⟩; exact hInv0
        · simp only [mem_support_bind_iff] at hx
          obtain ⟨⟨res, ex₂⟩, -, hx⟩ := hx
          rcases res with _ | c <;>
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          · rcases hx with ⟨_, rfl, _⟩; exact hInv0
          · rcases hx with ⟨_, rfl, _⟩
            exact scPostSendPure_preserves_inv P Dh encPt encT lam hep m₀ chal.isSome pq' _ c hInv

omit [SampleableType PQC] in
theorem semFwdAnswerHook_preserves_sC_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (L m qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hInv : SimCStateInv L m sC₀) :
    ∀ x ∈ support (semFwdAnswerHook P Dh encPt encT lam sh qep sC₀ ex₀ Q w isDel ci? Tpk pq' c'),
      SimCStateInv L m x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdAnswerHook at hx
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
  obtain ⟨⟨res, ex'⟩, -, _, rfl, _⟩ := hx
  refine ⟨onAnswerPure_preserves_inv qep L m Q w isDel ci? Tpk pq' res sC₀.base hInv.1, ?_, ?_⟩
  · rcases res with _ | (_ | ⟨t, i, pm⟩) <;> exact hInv.2.1
  · rcases res with _ | (_ | ⟨t, i, pm⟩) <;> exact hInv.2.2

omit [DecidableEq Pt] [SampleableType PQC] in
theorem semResyncHook_preserves_sC_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (L m qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (c : SimFig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hInv : SimCStateInv L m sC₀) :
    ∀ x ∈ support (semResyncHook P Dh encPt encT lam sh qep sC₀ ex₀ Q w ci? Tpk pq' c r),
      SimCStateInv L m x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semResyncHook at hx
  rcases r with _ | ⟨t, i, _, m'⟩
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hInv
  · simp only [mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, -, hx⟩ := hx
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl, _⟩; exact hInv
    · rcases hx with ⟨_, rfl, _⟩; exact hInv
    · rcases hx with ⟨_, rfl, _⟩
      exact ⟨onAcceptPure_preserves_inv qep L m Q w true t i m' ci? Tpk pq' sC₀.base hInv.1,
        hInv.2.1, hInv.2.2⟩

omit [SampleableType PQC] in
theorem semFwdHook_preserves_sC_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (L m qep B : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ)
    (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hInv : SimCStateInv L m sC₀) :
    ∀ x ∈ support
        (semFwdHook P Dh encPt encT lam sh qep B sC₀ ex₀ Q w isDel ci? Tpk pq' honestC c'),
      SimCStateInv L m x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdHook at hx
  rcases honestC with _ | c
  · exact semFwdAnswerHook_preserves_sC_inv P Dh encPt encT lam sh L m qep
      sC₀ ex₀ Q w isDel ci? Tpk pq' c' hInv _ hx
  · dsimp only [] at hx
    split_ifs at hx
    · rcases hev : evalCKClamp P Dh encPt encT lam B sC₀ Q w c c' with _ | r <;>
        simp only [hev] at hx
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        obtain ⟨_, -, _, rfl, _⟩ := hx; exact hInv
      · exact semResyncHook_preserves_sC_inv P Dh encPt encT lam sh L m qep
          sC₀ ex₀ Q w ci? Tpk pq' c r hInv _ hx
    · exact semFwdAnswerHook_preserves_sC_inv P Dh encPt encT lam sh L m qep
        sC₀ ex₀ Q w isDel ci? Tpk pq' c' hInv _ hx

omit [SampleableType PQC] in
theorem semFwdEvictHook_preserves_sC_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (L m qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hInv : SimCStateInv L m sC₀) :
    ∀ x ∈ support (semFwdEvictHook P Dh encPt encT lam sh qep sC₀ ex₀ Q w isDel Tpk pq' c'),
      SimCStateInv L m x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdEvictHook at hx
  split_ifs at hx
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨_, -, _, rfl, _⟩ := hx; exact hInv
  · exact semFwdAnswerHook_preserves_sC_inv P Dh encPt encT lam sh L m qep
      sC₀ ex₀ Q w isDel none Tpk pq' c' hInv _ hx

omit [SampleableType PQC] in
theorem semRecvHook_preserves_sC_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (L m qep B : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool)
    (hInv : SimCStateInv L m sC₀) :
    ∀ x ∈ support (semRecvHook P Dh encPt encT decT lam sh qep B sC₀ ex₀ Q w isDel),
      SimCStateInv L m x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semRecvHook at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win ||
        (isDel && (sC₀.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC₀.base.mir.inTransit Q.other w).isSome ||
          !(sC₀.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hInv
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hparse : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC₀.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;>
      simp only [hparse] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl, _⟩; exact hInv
    · rcases hidx : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · have hInvAmb : SimCStateInv L m
            { sC₀ with base :=
                if inReceiveOnlyEpoch sC₀.base.mir Q || (Q == Party.A && (sC₀.base.chains Q).any (·.key.isNone))
                then { sC₀.base with amb := sC₀.base.amb + 1 } else sC₀.base } := by
          refine ⟨?_, hInv.2.1, hInv.2.2⟩
          split_ifs <;> exact hInv.1
        by_cases hc1 :
            ((((sC₀.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true &&
             (((sC₀.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [hc1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, _⟩; exact hInv
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hx
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨_, rfl, _⟩; exact hInv
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hx
            by_cases hc2 :
                (inReceiveOnlyEpoch sC₀.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
              rcases hx with ⟨_, rfl, _⟩; exact hInvAmb
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hx
              rcases hT : T? with _ | T <;>
                simp only [hT] at hx
              · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
                rcases hx with ⟨_, rfl, _⟩; exact hInvAmb
              · by_cases hev_b :
                    ((((sC₀.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte] at hx
                  exact semFwdEvictHook_preserves_sC_inv P Dh encPt encT lam sh L m qep
                    _ ex₀ Q w isDel pk pq' _ hInvAmb _ hx
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte] at hx
                  exact semFwdHook_preserves_sC_inv P Dh encPt encT lam sh L m qep B
                    _ ex₀ Q w isDel none pk pq' _ _ hInvAmb _ hx
      · by_cases hrej : ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, _⟩; exact hInv
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hx
          exact semFwdHook_preserves_sC_inv P Dh encPt encT lam sh L m qep B
            sC₀ ex₀ Q w isDel (some ci) pk pq' _ _ hInv _ hx

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem semCorrHookDedup_preserves_sC_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (L m : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hInv : SimCStateInv L (m + 1) sC₀) :
    ∀ x ∈ support (semCorrHookDedup P Dh encT sh sC₀ ex₀ Q),
      SimCStateInv L m x.2.1 := by
  have hInv0 : SimCStateInv L m sC₀ := hInv.mono (Nat.le_succ m)
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semCorrHookDedup at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win || !(sC₀.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC₀.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, -, hx⟩ := hx
    rcases res with _ | fig8st <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl, _⟩; exact hInv0
    · rcases hx with ⟨_, rfl, _⟩
      have hchA : ((if Q == Party.B && sC₀.base.mir.epoch Party.B == 0 then
          match fig8st.γ with
          | .exp x => Function.update sC₀.base.chains Party.A
              ((sC₀.base.chains Party.A).map fun g =>
                if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => sC₀.base.chains
        else sC₀.base.chains) .A).length ≤ 5 := by
        split_ifs
        · rcases fig8st.γ with _ | x <;> simp [Function.update, hInv0.1.2.2.2.2.1]
        · exact hInv0.1.2.2.2.2.1
      have hchB : ((if Q == Party.B && sC₀.base.mir.epoch Party.B == 0 then
          match fig8st.γ with
          | .exp x => Function.update sC₀.base.chains Party.A
              ((sC₀.base.chains Party.A).map fun g =>
                if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => sC₀.base.chains
        else sC₀.base.chains) .B).length ≤ 5 := by
        split_ifs
        · rcases fig8st.γ with _ | x <;> simp [Function.update, hInv0.1.2.2.2.2.2]
        · exact hInv0.1.2.2.2.2.2
      refine ⟨⟨hInv0.1.1, hInv0.1.2.1, hInv0.1.2.2.1, ?_, hchA, hchB⟩, hInv0.2.1, ?_⟩
      · rcases hInv0.1.2.2.2.1 with ⟨U, hUlen, hCU, htrU⟩
        refine ⟨U, hUlen, ?_, htrU⟩
        dsimp only [afterCorrDedup, GameState.leak]
        refine countLe_dedupPrepend hCU ?_
        intro x hx
        rcases List.mem_map.mp hx with ⟨r', hr', rfl⟩
        exact htrU r' (List.mem_of_mem_filter hr')
      · simp only [List.length_cons]; have := hInv.2.2; omega

omit [SampleableType PQC] in
theorem semHandleHookDedup_preserves_sC_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (L m qep B : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex)
    (hInv : SimCStateInv L (m + 1) sC₀) :
    ∀ x ∈ support (semHandleHookDedup P Dh encPt encT decT lam sh qep B t sC₀ ex₀),
      SimCStateInv L m x.2.1 := by
  have hInv0 : SimCStateInv L m sC₀ := hInv.mono (Nat.le_succ m)
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_preserves_sC_inv P Dh encPt encT lam sh L m qep sC₀ ex₀ Q m₀ none r hInv
  · exact semSendHook_preserves_sC_inv P Dh encPt encT lam sh L m qep sC₀ ex₀ Q m₀ (some m₁) r hInv
  · rintro ⟨_, sC₁, ex₁⟩ hx
    unfold semHandleHookDedup at hx
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨rr, sC', ex'⟩, hrec, ex₂, -, _, rfl, rfl⟩ := hx
    exact semRecvHook_preserves_sC_inv P Dh encPt encT decT lam sh L m qep B
      sC₀ ex₀ Q w true hInv0 (rr, sC₁, ex') hrec
  · exact semRecvHook_preserves_sC_inv P Dh encPt encT decT lam sh L m qep B
      sC₀ ex₀ Q w false hInv0
  · exact semCorrHookDedup_preserves_sC_inv P Dh encT sh L m sC₀ ex₀ Q hInv

/-- Invariant preservation conditions on a `SemHook` for `L`-bounded execution. -/
structure SemHookInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (ExBound : ℕ → Ex → Prop) (ExInv : ℕ → ℕ → Ex → Prop) (L : ℕ)
    (sh : SemHook PQC Pt ℓ T Ex) : Prop where
  mono : ∀ {m₁ m₂ ex}, m₁ ≤ m₂ → ExInv L m₂ ex → ExInv L m₁ ex
  toBound : ∀ {m ex}, ExInv L m ex → ExBound L ex
  onSendCoins_inv : ∀ {m Q rq ex}, ExInv L m ex →
    ∀ y ∈ support (sh.onSendCoins Q rq ex), ExInv L m y.1 ∧ ExInv L m y.2
  onTr_inv : ∀ {m Q msg rc ex}, ExInv L (m + 1) ex →
    ∀ y ∈ support (sh.onTr Q msg rc ex), ExInv L m y.2
  onCh_inv : ∀ {m Q m₀ m₁ rc ex}, ExInv L (m + 1) ex →
    ∀ y ∈ support (sh.onCh Q m₀ m₁ rc ex), ExInv L m y.2
  onDl_inv : ∀ {m Q c ex}, ExInv L m ex →
    ∀ y ∈ support (sh.onDl Q c ex), ExInv L m y.2
  onIj_inv : ∀ {m Q c ex}, ExInv L m ex →
    ∀ y ∈ support (sh.onIj Q c ex), ExInv L m y.2
  onCr_inv : ∀ {m Q ex}, ExInv L (m + 1) ex →
    ∀ y ∈ support (sh.onCr Q ex), ExInv L m y.2
  onProbe_inv : ∀ {m Q c' ex}, ExInv L m ex →
    ∀ ex' ∈ support (sh.onProbe Q c' ex), ExInv L m ex'
  onDeliverPost_inv : ∀ {m Q j? rr ex}, ExInv L m ex →
    ∀ ex' ∈ support (sh.onDeliverPost Q j? rr ex), ExInv L m ex'

omit [DecidableEq Pt] [SampleableType PQC] in
theorem semSendHook_preserves_ex_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {ExBound : ℕ → Ex → Prop} {ExInv : ℕ → ℕ → Ex → Prop} {L : ℕ}
    {sh : SemHook PQC Pt ℓ T Ex} (h_inv : SemHookInv ExBound ExInv L sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (hEx : ExInv L (m + 1) ex₀) :
    ∀ x ∈ support (semSendHook P Dh encPt encT lam sh qep sC₀ ex₀ Q m₀ chal r),
      ExInv L m x.2.2 := by
  have hEx0 : ExInv L m ex₀ := h_inv.mono (Nat.le_succ m) hEx
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semSendHook at hx
  by_cases href : (sC₀.base.stopped || sC₀.base.mir.win || !(noBobSendInEpoch0 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, _, rfl⟩; exact hEx0
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC₀.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;>
      simp only [hep] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, _, rfl⟩; exact hEx0
    · by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hch, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨_, _, rfl⟩; exact hEx0
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
        obtain ⟨⟨rq, rc⟩, -, ⟨exOk, exFail⟩, hsc, hx⟩ := hx
        obtain ⟨hOk, hFail⟩ := h_inv.onSendCoins_inv hEx (exOk, exFail) hsc
        have hFail0 : ExInv L m exFail := h_inv.mono (Nat.le_succ m) hFail
        rcases hpub : mkPub P sC₀.base Q rq
          (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
            BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) with _ | ⟨pq', pub⟩ <;>
          simp only [hpub] at hx
        · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, _, rfl⟩; exact hFail0
        · simp only [mem_support_bind_iff] at hx
          obtain ⟨⟨res, ex₂⟩, hq, hx⟩ := hx
          have hEx2 : ExInv L m ex₂ := by
            rcases chal with _ | m₁
            · exact h_inv.onTr_inv hOk (res, ex₂) hq
            · exact h_inv.onCh_inv hOk (res, ex₂) hq
          rcases res with _ | c <;>
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          · rcases hx with ⟨_, _, rfl⟩; exact hFail0
          · rcases hx with ⟨_, _, rfl⟩; exact hEx2

omit [SampleableType PQC] in
theorem semFwdAnswerHook_preserves_ex_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {ExBound : ℕ → Ex → Prop} {ExInv : ℕ → ℕ → Ex → Prop} {L : ℕ}
    {sh : SemHook PQC Pt ℓ T Ex} (h_inv : SemHookInv ExBound ExInv L sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hEx : ExInv L m ex₀) :
    ∀ x ∈ support (semFwdAnswerHook P Dh encPt encT lam sh qep sC₀ ex₀ Q w isDel ci? Tpk pq' c'),
      ExInv L m x.2.2 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdAnswerHook at hx
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
  obtain ⟨⟨res, ex'⟩, hq, _, _, rfl⟩ := hx
  split_ifs at hq
  · exact h_inv.onDl_inv hEx (res, ex₁) hq
  · exact h_inv.onIj_inv hEx (res, ex₁) hq

omit [DecidableEq Pt] [SampleableType PQC] in
theorem semResyncHook_preserves_ex_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {ExBound : ℕ → Ex → Prop} {ExInv : ℕ → ℕ → Ex → Prop} {L : ℕ}
    {sh : SemHook PQC Pt ℓ T Ex} (h_inv : SemHookInv ExBound ExInv L sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (c : SimFig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hEx : ExInv L m ex₀) :
    ∀ x ∈ support (semResyncHook P Dh encPt encT lam sh qep sC₀ ex₀ Q w ci? Tpk pq' c r),
      ExInv L m x.2.2 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semResyncHook at hx
  rcases r with _ | ⟨t, i, _, m'⟩
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, _, rfl⟩; exact hEx
  · simp only [mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, hdl, hx⟩ := hx
    have hEx' := h_inv.onDl_inv hEx (res, ex') hdl
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx <;>
      (rcases hx with ⟨_, _, rfl⟩; exact hEx')

omit [SampleableType PQC] in
theorem semFwdHook_preserves_ex_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {ExBound : ℕ → Ex → Prop} {ExInv : ℕ → ℕ → Ex → Prop} {L : ℕ}
    {sh : SemHook PQC Pt ℓ T Ex} (h_inv : SemHookInv ExBound ExInv L sh)
    (m qep B : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ)
    (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hEx : ExInv L m ex₀) :
    ∀ x ∈ support
        (semFwdHook P Dh encPt encT lam sh qep B sC₀ ex₀ Q w isDel ci? Tpk pq' honestC c'),
      ExInv L m x.2.2 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdHook at hx
  rcases honestC with _ | c
  · exact semFwdAnswerHook_preserves_ex_inv P Dh encPt encT lam h_inv m qep
      sC₀ ex₀ Q w isDel ci? Tpk pq' c' hEx _ hx
  · dsimp only [] at hx
    split_ifs at hx
    · rcases hev : evalCKClamp P Dh encPt encT lam B sC₀ Q w c c' with _ | r <;>
        simp only [hev] at hx
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        obtain ⟨ex', hpr, _, _, rfl⟩ := hx
        exact h_inv.onProbe_inv hEx ex₁ hpr
      · exact semResyncHook_preserves_ex_inv P Dh encPt encT lam h_inv m qep
          sC₀ ex₀ Q w ci? Tpk pq' c r hEx _ hx
    · exact semFwdAnswerHook_preserves_ex_inv P Dh encPt encT lam h_inv m qep
        sC₀ ex₀ Q w isDel ci? Tpk pq' c' hEx _ hx

omit [SampleableType PQC] in
theorem semFwdEvictHook_preserves_ex_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {ExBound : ℕ → Ex → Prop} {ExInv : ℕ → ℕ → Ex → Prop} {L : ℕ}
    {sh : SemHook PQC Pt ℓ T Ex} (h_inv : SemHookInv ExBound ExInv L sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hEx : ExInv L m ex₀) :
    ∀ x ∈ support (semFwdEvictHook P Dh encPt encT lam sh qep sC₀ ex₀ Q w isDel Tpk pq' c'),
      ExInv L m x.2.2 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdEvictHook at hx
  split_ifs at hx
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨ex', hpr, _, _, rfl⟩ := hx
    exact h_inv.onProbe_inv hEx ex₁ hpr
  · exact semFwdAnswerHook_preserves_ex_inv P Dh encPt encT lam h_inv m qep
      sC₀ ex₀ Q w isDel none Tpk pq' c' hEx _ hx

omit [SampleableType PQC] in
theorem semRecvHook_preserves_ex_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {ExBound : ℕ → Ex → Prop} {ExInv : ℕ → ℕ → Ex → Prop} {L : ℕ}
    {sh : SemHook PQC Pt ℓ T Ex} (h_inv : SemHookInv ExBound ExInv L sh)
    (m qep B : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool)
    (hEx : ExInv L m ex₀) :
    ∀ x ∈ support (semRecvHook P Dh encPt encT decT lam sh qep B sC₀ ex₀ Q w isDel),
      ExInv L m x.2.2 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semRecvHook at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win ||
        (isDel && (sC₀.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC₀.base.mir.inTransit Q.other w).isSome ||
          !(sC₀.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, _, rfl⟩; exact hEx
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hparse : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC₀.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;>
      simp only [hparse] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, _, rfl⟩; exact hEx
    · rcases hidx : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · by_cases hc1 :
            ((((sC₀.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true &&
             (((sC₀.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [hc1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, _, rfl⟩; exact hEx
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hx
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨_, _, rfl⟩; exact hEx
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hx
            by_cases hc2 :
                (inReceiveOnlyEpoch sC₀.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
              rcases hx with ⟨_, _, rfl⟩; exact hEx
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hx
              rcases hT : T? with _ | T <;>
                simp only [hT] at hx
              · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
                rcases hx with ⟨_, _, rfl⟩; exact hEx
              · by_cases hev_b :
                    ((((sC₀.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte] at hx
                  exact semFwdEvictHook_preserves_ex_inv P Dh encPt encT lam h_inv m qep
                    _ ex₀ Q w isDel pk pq' _ hEx _ hx
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte] at hx
                  exact semFwdHook_preserves_ex_inv P Dh encPt encT lam h_inv m qep B
                    _ ex₀ Q w isDel none pk pq' _ _ hEx _ hx
      · by_cases hrej : ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, _, rfl⟩; exact hEx
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hx
          exact semFwdHook_preserves_ex_inv P Dh encPt encT lam h_inv m qep B
            sC₀ ex₀ Q w isDel (some ci) pk pq' _ _ hEx _ hx

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem semCorrHookDedup_preserves_ex_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {ExBound : ℕ → Ex → Prop} {ExInv : ℕ → ℕ → Ex → Prop} {L : ℕ}
    {sh : SemHook PQC Pt ℓ T Ex} (h_inv : SemHookInv ExBound ExInv L sh)
    (m : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hEx : ExInv L (m + 1) ex₀) :
    ∀ x ∈ support (semCorrHookDedup P Dh encT sh sC₀ ex₀ Q),
      ExInv L m x.2.2 := by
  have hEx0 : ExInv L m ex₀ := h_inv.mono (Nat.le_succ m) hEx
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semCorrHookDedup at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win || !(sC₀.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC₀.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, _, rfl⟩; exact hEx0
  · simp only [href, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, hcr, hx⟩ := hx
    have hEx' := h_inv.onCr_inv hEx (res, ex') hcr
    rcases res with _ | fig8st <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx <;>
      (rcases hx with ⟨_, _, rfl⟩; exact hEx')

omit [SampleableType PQC] in
theorem semHandleHookDedup_preserves_ex_inv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {ExBound : ℕ → Ex → Prop} {ExInv : ℕ → ℕ → Ex → Prop} {L : ℕ}
    {sh : SemHook PQC Pt ℓ T Ex} (h_inv : SemHookInv ExBound ExInv L sh)
    (m qep B : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex)
    (hEx : ExInv L (m + 1) ex₀) :
    ∀ x ∈ support (semHandleHookDedup P Dh encPt encT decT lam sh qep B t sC₀ ex₀),
      ExInv L m x.2.2 := by
  have hEx0 : ExInv L m ex₀ := h_inv.mono (Nat.le_succ m) hEx
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_preserves_ex_inv P Dh encPt encT lam h_inv m qep sC₀ ex₀ Q m₀ none r hEx
  · exact semSendHook_preserves_ex_inv P Dh encPt encT lam h_inv m qep sC₀ ex₀ Q m₀ (some m₁) r hEx
  · rintro ⟨_, sC₁, ex₁⟩ hx
    unfold semHandleHookDedup at hx
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨rr, sC', ex'⟩, hrec, ex₂, hpost, _, rfl, rfl⟩ := hx
    have hEx' := semRecvHook_preserves_ex_inv P Dh encPt encT decT lam h_inv m qep B
      sC₀ ex₀ Q w true hEx0 (rr, sC₁, ex') hrec
    exact h_inv.onDeliverPost_inv hEx' ex₁ hpost
  · exact semRecvHook_preserves_ex_inv P Dh encPt encT decT lam h_inv m qep B
      sC₀ ex₀ Q w false hEx0
  · exact semCorrHookDedup_preserves_ex_inv P Dh encT h_inv m sC₀ ex₀ Q hEx

/-- Combined raw-state invariant on `(simStateCTy × σExtra).denote` for `simHandleHookC`. -/
def SimHookRawInv {σExtra : Ty S} {Ex : Type}
    (exEnc : Ex → σExtra.denote) (ExInv : ℕ → ℕ → Ex → Prop) (L m : ℕ)
    (st_raw : (Ty.prod simStateCTy σExtra).denote) : Prop :=
  SimCStateInv L m (simStateCDec st_raw.1) ∧
  ∃ ex₀ : Ex, st_raw.2 = exEnc ex₀ ∧ ExInv L m ex₀

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem SimHookRawInv.mono {ι : Type} {T : OracleSpec ι} {σExtra : Ty S} {Ex : Type}
    {exEnc : Ex → σExtra.denote} {ExBound : ℕ → Ex → Prop} {ExInv : ℕ → ℕ → Ex → Prop} {L : ℕ}
    {sh : SemHook PQC Pt ℓ T Ex} (h_inv : SemHookInv ExBound ExInv L sh)
    {m₁ m₂ : ℕ} {st_raw : (Ty.prod simStateCTy σExtra).denote}
    (hle : m₁ ≤ m₂) (h : SimHookRawInv exEnc ExInv L m₂ st_raw) :
    SimHookRawInv exEnc ExInv L m₁ st_raw := by
  rcases h with ⟨hsC, ex₀, hex, hexInv⟩
  exact ⟨hsC.mono hle, ex₀, hex, h_inv.mono hle hexInv⟩

omit [SampleableType PQC] in
theorem simHandleHookC_step {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {σExtra : Ty S} {Ex : Type}
    {exEnc : Ex → σExtra.denote} {exDec : σExtra.denote → Ex}
    (hexDec : ∀ x, exDec (exEnc x) = x)
    {ExBound : ℕ → Ex → Prop} {ExInv : ℕ → ℕ → Ex → Prop} {L : ℕ}
    {hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra}
    {sh : SemHook PQC Pt ℓ T Ex}
    (h_hk : HookMatch P Dh encPt encT decT lam K toKemCoins exEnc ExBound L hk sh)
    (h_inv : SemHookInv ExBound ExInv L sh)
    (qep B m : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st_raw : (Ty.prod simStateCTy σExtra).denote)
    (hInv : SimHookRawInv exEnc ExInv L (m + 1) st_raw) :
    (Prod.map id (Prod.map simStateCDec exDec) <$>
      ((handlerImpl (C := simCodec PQ PQC Pt ℓ)
        (simHandleHookC P Dh encPt encT decT lam K toKemCoins hk L qep B)
        (.inr t)).run st_raw)) =
      semHandleHookDedup P Dh encPt encT decT lam sh qep B t
        (simStateCDec st_raw.1) (exDec st_raw.2) ∧
    ∀ r ∈ support
      ((handlerImpl (C := simCodec PQ PQC Pt ℓ)
        (simHandleHookC P Dh encPt encT decT lam K toKemCoins hk L qep B)
        (.inr t)).run st_raw),
      SimHookRawInv exEnc ExInv L m r.2 := by
  rcases hInv with ⟨hsCInv, ex₀, hex, hexInv⟩
  have hraw := handlerImpl_simHandleHookC_eval P Dh encPt encT decT lam K toKemCoins h_hk qep B
    t st_raw (simStateCDec st_raw.1) ex₀ hsCInv.toBounded (h_inv.toBound hexInv) rfl hex
  refine ⟨?_, ?_⟩
  · have hmap := congrArg (Functor.map (Prod.map id (Prod.map id exDec))) hraw
    simp only [Functor.map_map, Prod.map, id_eq, hexDec, Prod.mk.eta] at hmap
    rw [hex, hexDec]
    exact hmap.trans (id_map _)
  · rintro ⟨resp, s₁_raw, ex₁_raw⟩ hr
    have hmem : Prod.map id (Prod.map simStateCDec id) (resp, s₁_raw, ex₁_raw) ∈
        support (Prod.map id (Prod.map simStateCDec id) <$>
          ((handlerImpl (C := simCodec PQ PQC Pt ℓ)
            (simHandleHookC P Dh encPt encT decT lam K toKemCoins hk L qep B)
            (.inr t)).run st_raw)) := by
      rw [support_map]; exact ⟨_, hr, rfl⟩
    rw [hraw, support_map, Set.mem_image] at hmem
    obtain ⟨⟨resp', sC₁, ex₁⟩, hsem, hEq⟩ := hmem
    simp only [Prod.map, Prod.mk.injEq] at hEq
    rcases hEq with ⟨_, hsC₁, hex₁⟩
    refine ⟨?_, ex₁, hex₁.symm, ?_⟩
    · rw [← hsC₁]
      exact semHandleHookDedup_preserves_sC_inv P Dh encPt encT decT lam sh L m qep B
        t (simStateCDec st_raw.1) ex₀ hsCInv _ hsem
    · exact semHandleHookDedup_preserves_ex_inv P Dh encPt encT decT lam h_inv m qep B
        t (simStateCDec st_raw.1) ex₀ hexInv _ hsem

def deliverForgeSemHook :
    SemHook PQC Pt ℓ
      (unifSpec + SM.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt))
      (List (SimFig8C Pt)) where
  sampleBv256 := liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
  samplePqc := liftM ($ᵗ PQC : ProbComp PQC)
  onSendCoins _ _ ex := pure (ex, ex)
  onTr Q m rc ex := do
    let res ← SM.Construction.DeliverForge.transmitQueryDF
      (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := SimFig8C Pt) Q m rc
    return (res, match res with | none => ex | some c => c :: ex)
  onCh Q m₀ m₁ rc ex := do
    let res ← SM.Construction.DeliverForge.challQueryDF
      (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := SimFig8C Pt)
      Q m₀ m₁ rc
    return (res, match res with | none => ex | some c => c :: ex)
  onDl Q c ex := do
    let res ← SM.Construction.DeliverForge.deliverQueryDF
      (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := SimFig8C Pt) Q c
    return (res, ex)
  onIj Q c ex := do
    let res ← SM.Construction.DeliverForge.injectQueryDF
      (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := SimFig8C Pt) Q c
    return (res, ex)
  onCr Q ex := do
    let res ← SM.Construction.DeliverForge.corrQueryDF
      (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := SimFig8C Pt) Q
    return (res, ex)
  onProbe Q c' ex :=
    match ex.find? (fun c => CryptoGames.LibsignalSM.Proofs.Refinement.sameWireFig8 c c') with
    | none => pure ex
    | some c => do
      let _ ← SM.Construction.DeliverForge.deliverForgeQuery
        (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := SimFig8C Pt)
        Q c c'
      return ex
  onDeliverPost _ _ _ ex := pure ex

@[simp] theorem query_trDF_eval {Γ}
    (e : Expr OFig Γ (.prod .bool (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base .bv256)))))
    (ρ : Env Γ) :
    (Comp.query (I := SIfaceDF) SMTagDF.tr e).eval ρ =
      SM.Construction.DeliverForge.transmitQueryDF
        (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := SimFig8C Pt)
        (partyDec (e.eval ρ).1) (e.eval ρ).2.1 (e.eval ρ).2.2 := by
  simp [Comp.eval, simIfaceDF, simParamIfaceDF, SM.Construction.DeliverForge.transmitQueryDF]

@[simp] theorem query_chDF_eval {Γ}
    (e : Expr OFig Γ (.prod .bool
      (.prod (lpubPlainTy PQ PQC Pt ℓ)
        (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base .bv256))))))
    (ρ : Env Γ) :
    (Comp.query (I := SIfaceDF) SMTagDF.ch e).eval ρ =
      SM.Construction.DeliverForge.challQueryDF
        (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := SimFig8C Pt)
        (partyDec (e.eval ρ).1) (e.eval ρ).2.1 (e.eval ρ).2.2.1 (e.eval ρ).2.2.2 := by
  simp [Comp.eval, simIfaceDF, simParamIfaceDF, SM.Construction.DeliverForge.challQueryDF]

@[simp] theorem query_dlDF_eval {Γ}
    (e : Expr OFig Γ (.prod .bool (fig8CTy PQ PQC Pt ℓ))) (ρ : Env Γ) :
    (Comp.query (I := SIfaceDF) SMTagDF.dl e).eval ρ =
      Option.map SM.smRrEnc <$>
        SM.Construction.DeliverForge.deliverQueryDF
          (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := SimFig8C Pt)
          (partyDec (e.eval ρ).1) (e.eval ρ).2 := by
  simp [Comp.eval, simIfaceDF, simParamIfaceDF, SM.Construction.DeliverForge.deliverQueryDF]

@[simp] theorem query_ijDF_eval {Γ}
    (e : Expr OFig Γ (.prod .bool (fig8CTy PQ PQC Pt ℓ))) (ρ : Env Γ) :
    (Comp.query (I := SIfaceDF) SMTagDF.ij e).eval ρ =
      Option.map SM.smRrEnc <$>
        SM.Construction.DeliverForge.injectQueryDF
          (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := SimFig8C Pt)
          (partyDec (e.eval ρ).1) (e.eval ρ).2 := by
  simp [Comp.eval, simIfaceDF, simParamIfaceDF, SM.Construction.DeliverForge.injectQueryDF]

@[simp] theorem query_crDF_eval {Γ}
    (e : Expr OFig Γ .bool) (ρ : Env Γ) :
    (Comp.query (I := SIfaceDF) SMTagDF.cr e).eval ρ =
      SM.Construction.DeliverForge.corrQueryDF
        (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := SimFig8C Pt)
        (partyDec (e.eval ρ)) := by
  simp [Comp.eval, simIfaceDF, simParamIfaceDF, SM.Construction.DeliverForge.corrQueryDF]

@[simp] theorem query_dfDF_eval {Γ}
    (e : Expr OFig Γ (.prod .bool (.prod (fig8CTy PQ PQC Pt ℓ) (fig8CTy PQ PQC Pt ℓ))))
    (ρ : Env Γ) :
    (Comp.query (I := SIfaceDF) SMTagDF.df e).eval ρ =
      Option.map SM.smRrEnc <$>
        SM.Construction.DeliverForge.deliverForgeQuery
          (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := SimFig8C Pt)
          (partyDec (e.eval ρ).1) (e.eval ρ).2.1 (e.eval ρ).2.2 := by
  simp [Comp.eval, simIfaceDF, simParamIfaceDF, SM.Construction.DeliverForge.deliverForgeQuery]

theorem deliverForgeHookMatch (L : ℕ) :
    HookMatch P Dh encPt encT decT lam K toKemCoins
      (id : List (SimFig8C Pt) → List (SimFig8C Pt))
      (fun L ex => ex.length ≤ L) L
      (deliverForgeHookC P Dh encPt encT decT lam K toKemCoins L)
      (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) where
  sampleBv256_eval _ := rfl
  samplePqc_eval _ := rfl
  onSendCoins_eval _ _ _ _ _ _ _ hex := by
    simp [deliverForgeHookC, deliverForgeSemHook, Expr.eval, hex]
  onTr_eval _ _ _ _ _ _ _ harg hex := by
    unfold deliverForgeHookC deliverForgeSemHook
    rw [comp_eval_bind_ret, expr_pair_eval, harg, hex, comp_eval_bind, query_trDF_eval]
    simp only [comp_eval_ret, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, Env.get_cons_succ,
      partyDec_partyEnc, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    refine bind_congr fun res => ?_
    cases res <;> rfl
  onCh_eval _ _ _ _ _ _ _ _ harg hex := by
    unfold deliverForgeHookC deliverForgeSemHook
    rw [comp_eval_bind_ret, expr_pair_eval, harg, hex, comp_eval_bind, query_chDF_eval]
    simp only [comp_eval_ret, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, Env.get_cons_succ,
      partyDec_partyEnc, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    refine bind_congr fun res => ?_
    cases res <;> rfl
  onDl_eval _ _ _ _ _ _ _ harg hex := by
    unfold deliverForgeHookC deliverForgeSemHook
    rw [comp_eval_bind_ret, expr_pair_eval, harg, hex, comp_eval_bind, query_dlDF_eval]
    simp [Expr.eval, Expr.v0, Expr.v1,
      partyDec_partyEnc, map_eq_bind_pure_comp, bind_assoc, pure_bind, Prod.map]
  onIj_eval _ _ _ _ _ _ _ harg hex := by
    unfold deliverForgeHookC deliverForgeSemHook
    rw [comp_eval_bind_ret, expr_pair_eval, harg, hex, comp_eval_bind, query_ijDF_eval]
    simp [Expr.eval, Expr.v0, Expr.v1,
      partyDec_partyEnc, map_eq_bind_pure_comp, bind_assoc, pure_bind, Prod.map]
  onCr_eval _ _ _ _ _ _ hq hex := by
    unfold deliverForgeHookC deliverForgeSemHook
    rw [comp_eval_bind_ret, expr_pair_eval, hq, hex, comp_eval_bind, query_crDF_eval]
    simp [Expr.eval, Expr.v0, Expr.v1, partyDec_partyEnc, map_eq_bind_pure_comp]
  onProbe_eval _ _ ρ Q c' ex₀ hEx harg hex := by
    unfold deliverForgeHookC deliverForgeSemHook
    rw [comp_eval_bind_ret, comp_eval_caseOpt]
    have htake : ex₀.take L = ex₀ := List.take_of_length_le hEx
    have hfind :
        (Expr.findB L (.snd (Expr.v0 (O := OFig)))
          (Expr.op (O := OFig) SimOp.sameWireFig8
            (.pair .v0 (.snd (.fst .v1))))).eval
          (Env.cons (t := .prod (.prod .bool (fig8CTy PQ PQC Pt ℓ))
            (.list (fig8CTy PQ PQC Pt ℓ))) ((partyEnc Q, c'), ex₀) ρ) =
        ex₀.find? (fun c => CryptoGames.LibsignalSM.Proofs.Refinement.sameWireFig8 c c') := by
      simp [Expr.eval, Expr.v0, Expr.v1, htake, simOpsUnitCost,
        CryptoGames.LibsignalSM.Proofs.Refinement.sameWireFig8]
    rw [expr_pair_eval, harg, hex]
    dsimp only [id]
    rw [hfind]
    rcases ex₀.find? (fun c => CryptoGames.LibsignalSM.Proofs.Refinement.sameWireFig8 c c') with
      _ | c
    · simp [Expr.eval, Expr.v0]
    · dsimp only []
      rw [comp_eval_bind, query_dfDF_eval (PQ := PQ) (PQC := PQC)]
      simp [Expr.eval, Expr.v1, Expr.v2,
        partyDec_partyEnc, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  onDeliverPost_eval _ _ _ _ _ _ _ _ _ _ hex := by
    simp [deliverForgeHookC, deliverForgeSemHook, hex]
  onDeliverPost_congr _ _ _ _ _ _ _ _ _ hex := by
    simp [deliverForgeHookC, hex]

omit [Zero Pt] in
theorem deliverForgeSemHookInv (L : ℕ) :
    SemHookInv (PQC := PQC) (Pt := Pt) (ℓ := ℓ)
      (fun L (ex : List (SimFig8C Pt)) => ex.length ≤ L)
      (fun L m (ex : List (SimFig8C Pt)) => ex.length + m ≤ L) L
      (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) where
  mono hle h := by omega
  toBound h := by omega
  onSendCoins_inv hEx y hy := by
    simp only [deliverForgeSemHook, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact ⟨hEx, hEx⟩
  onTr_inv hEx y hy := by
    simp only [deliverForgeSemHook, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hy
    obtain ⟨res, -, rfl⟩ := hy
    cases res <;> simp <;> omega
  onCh_inv hEx y hy := by
    simp only [deliverForgeSemHook, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hy
    obtain ⟨res, -, rfl⟩ := hy
    cases res <;> simp <;> omega
  onDl_inv hEx y hy := by
    simp only [deliverForgeSemHook, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hy
    obtain ⟨_, -, rfl⟩ := hy; exact hEx
  onIj_inv hEx y hy := by
    simp only [deliverForgeSemHook, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hy
    obtain ⟨_, -, rfl⟩ := hy; exact hEx
  onCr_inv hEx y hy := by
    simp only [deliverForgeSemHook, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hy
    obtain ⟨_, -, rfl⟩ := hy; dsimp only []; omega
  onProbe_inv {m Q c' ex} hEx ex' hy := by
    unfold deliverForgeSemHook at hy
    rcases hfind : ex.find?
      (fun c => CryptoGames.LibsignalSM.Proofs.Refinement.sameWireFig8 c c') with _ | c <;>
      simp only [hfind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    · subst hy; exact hEx
    · obtain ⟨_, -, rfl⟩ := hy; exact hEx
  onDeliverPost_inv hEx ex' hy := by
    simp only [deliverForgeSemHook, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact hEx

def simStateCCanon (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    LibsignalToModularSchemeSimState PQ Pt ℓ :=
  { sC with base := simStateCanon sC.base }

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem simStateCCanon_idem (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    simStateCCanon (simStateCCanon sC) = simStateCCanon sC := by
  simp [simStateCCanon, simStateCanon_idem]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem onAcceptPure_simStateCanon (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (msg : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    Prod.map id simStateCanon (onAcceptPure qep Q w isDel t i msg ci? T pq' s) =
      Prod.map id simStateCanon (onAcceptPure qep Q w isDel t i msg ci? T pq' (simStateCanon s)) := by
  have hmir : (simStateCanon s).mir = canonComp s.mir := rfl
  have hch : (simStateCanon s).chains = s.chains := rfl
  have hpq : (simStateCanon s).pq = s.pq := rfl
  have hun : (simStateCanon s).unackA = s.unackA := rfl
  unfold onAcceptPure
  dsimp only [Prod.map, id_eq]
  rw [hmir, hch, hpq, hun]
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hqep : qep + 1 < t
    · simp [hqep, simStateCanon_idem]
    · simp only [hqep, ↓reduceIte]
      rw [canonComp_trivial s.mir 3 ⟨Q.other, t, i⟩]
      cases s.mir.trivial 3 ⟨Q.other, t, i⟩
      · simp [simStateCanon, canonComp, List.dedup_idem]
      · simp only [↓reduceIte, Prod.mk.injEq, true_and]
        rw [← canonComp_accept s.mir Q () ⟨Q.other, t, i⟩]
        simp [simStateCanon, canonComp, List.dedup_idem]
  · simp only [↓reduceIte,
      show (canonComp s.mir).inTransit Q.other w = s.mir.inTransit Q.other w from rfl]
    rcases s.mir.inTransit Q.other w with _ | r
    · simp [simStateCanon_idem]
    · simp only [show (canonComp s.mir).chall = s.mir.chall from rfl, Prod.mk.injEq, true_and]
      rw [← canonComp_accept s.mir Q () r.pos]
      simp [simStateCanon, canonComp, List.dedup_idem]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem onAnswerPure_simStateCanon (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (s : SimState PQ Pt ℓ) :
    Prod.map id simStateCanon (onAnswerPure qep Q w isDel ci? T pq' res s) =
      Prod.map id simStateCanon (onAnswerPure qep Q w isDel ci? T pq' res (simStateCanon s)) := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · simp [onAnswerPure, Prod.map, simStateCanon_idem]
  · simp [onAnswerPure, Prod.map, simStateCanon_idem]
  · exact onAcceptPure_simStateCanon qep Q w isDel t i
      ((pm.map (·.2)).getD default) ci? T pq' s

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem scPostSendPure_simStateCCanon
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s₁ : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (Q : Party) (m₀ : Plain ℓ) (isChall : Bool) (pq' : PQ)
    (pn : BitVec 32) (c : SimFig8C Pt) :
    simStateCCanon (scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ isChall pq' pn c) =
      simStateCCanon (scPostSendPure P Dh encPt encT lam
        (simStateCCanon sC) (canonComp s₁) Q m₀ isChall pq' pn c) := by
  simp only [simStateCCanon, simStateCanon, scPostSendPure]
  congr 2
  exact canonComp_record s₁ 3 Q () _ isChall

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem semSendHook_simStateCCanon {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semSendHook P Dh encPt encT lam sh qep sC ex Q m₀ chal r =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semSendHook P Dh encPt encT lam sh qep (simStateCCanon sC) ex Q m₀ chal r := by
  unfold semSendHook
  have h1 : ((simStateCCanon sC).base.stopped || (simStateCCanon sC).base.mir.win ||
      !(noBobSendInEpoch0 (simStateCCanon sC).base.mir Q)) =
      (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) := rfl
  rw [h1]
  by_cases hc1 : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) = true
  · simp [hc1, Prod.map, simStateCCanon_idem]
  · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
    have hep_canon : (simStateCCanon sC).base.mir.epMgmt 3 qep Q r.isSome =
        Option.map canonComp (sC.base.mir.epMgmt 3 qep Q r.isSome) :=
      (canonComp_epMgmt sC.base.mir 3 qep Q r.isSome).symm
    rw [hep_canon]
    rcases sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · simp [Prod.map, simStateCCanon_idem]
    · dsimp only [Option.map]
      have h2 : (chal.isSome && !(canonComp s₁).safeCh 3 Q) =
          (chal.isSome && !(s₁.safeCh 3 Q)) := rfl
      rw [h2]
      by_cases hc2 : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp [hc2, Prod.map, simStateCCanon_idem]
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte, map_bind]
        refine bind_congr fun ⟨rq, rc⟩ => ?_
        refine bind_congr fun ⟨exOk, exFail⟩ => ?_
        have hmk : ∀ Q rq pn,
            mkPub (P := P) (simStateCCanon sC).base Q rq pn =
              mkPub (P := P) sC.base Q rq pn := fun _ _ _ => rfl
        dsimp only []
        simp only [hmk,
          show (canonComp s₁).epoch = s₁.epoch from rfl,
          show (simStateCCanon sC).base.mir.epoch = sC.base.mir.epoch from rfl,
          show (simStateCCanon sC).base.mir.idx = sC.base.mir.idx from rfl,
          show (simStateCCanon sC).base.pn = sC.base.pn from rfl]
        rcases mkPub (P := P) sC.base Q rq
            (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
             else sC.base.pn Q) with _ | ⟨pq', pub⟩
        · simp [Prod.map, simStateCCanon_idem]
        · simp only [map_bind]
          refine bind_congr fun ⟨res, ex₂⟩ => ?_
          rcases res with _ | c
          · simp [Prod.map, simStateCCanon_idem]
          · simp only [map_pure, Prod.map, id_eq]
            congr 1
            refine Prod.ext rfl (Prod.ext ?_ rfl)
            exact scPostSendPure_simStateCCanon P Dh encPt encT lam sC s₁ Q m₀ chal.isSome pq' _ c

omit [SampleableType PQC] in
private theorem semFwdAnswerHook_simStateCCanon {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semFwdAnswerHook P Dh encPt encT lam sh qep sC ex Q w isDel ci? Tpk pq' c' =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semFwdAnswerHook P Dh encPt encT lam sh qep (simStateCCanon sC) ex Q w isDel ci? Tpk pq' c' := by
  unfold semFwdAnswerHook
  have hinT :
      ((simStateCCanon sC).base.honest.any fun wc =>
        decide (wc.2 = c') && ((simStateCCanon sC).base.mir.inTransit Q.other wc.1).isSome) =
      (sC.base.honest.any fun wc =>
        decide (wc.2 = c') && (sC.base.mir.inTransit Q.other wc.1).isSome) := rfl
  dsimp only []
  rw [hinT, map_bind, map_bind]
  refine bind_congr fun ⟨res, ex₁⟩ => ?_
  have hon := onAnswerPure_simStateCanon qep Q w isDel ci? Tpk pq' res sC.base
  have hrr := congrArg Prod.fst hon
  have hst := congrArg Prod.snd hon
  dsimp only [Prod.map, id_eq] at hrr hst
  simp only [map_pure, Prod.map, id_eq, simStateCCanon]
  rw [← hrr, ← hst]
  rcases res with _ | (_ | ⟨t, i, pm⟩) <;> rfl

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem semResyncHook_simStateCCanon {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semResyncHook P Dh encPt encT lam sh qep sC ex Q w ci? Tpk pq' c r =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semResyncHook P Dh encPt encT lam sh qep (simStateCCanon sC) ex Q w ci? Tpk pq' c r := by
  unfold semResyncHook
  rcases r with _ | ⟨t, i, ⟨pub, m'⟩⟩
  · simp [Prod.map, simStateCCanon_idem]
  · simp only [map_bind]
    refine bind_congr fun ⟨res, ex₁⟩ => ?_
    rcases res with _ | (_ | ⟨t_dl, i_dl, pm_dl⟩)
    · simp [Prod.map, simStateCCanon_idem]
    · simp [Prod.map, simStateCCanon_idem]
    · have hon := onAcceptPure_simStateCanon qep Q w true t i m' ci? Tpk pq' sC.base
      have hrr := congrArg Prod.fst hon
      have hst := congrArg Prod.snd hon
      dsimp only [Prod.map, id_eq] at hrr hst
      simp only [map_pure, Prod.map, id_eq, simStateCCanon]
      rw [← hrr, ← hst]

omit [SampleableType PQC] in
private theorem semFwdEvictHook_simStateCCanon {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semFwdEvictHook P Dh encPt encT lam sh qep sC ex Q w isDel Tpk pq' c' =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semFwdEvictHook P Dh encPt encT lam sh qep (simStateCCanon sC) ex Q w isDel Tpk pq' c' := by
  unfold semFwdEvictHook
  have hsi : (simStateCCanon sC).base.mir.safeInj 3 = sC.base.mir.safeInj 3 := rfl
  rw [hsi]
  split_ifs
  · simp [Prod.map, simStateCCanon_idem]
  · exact semFwdAnswerHook_simStateCCanon P Dh encPt encT lam sh qep sC ex Q w isDel none Tpk pq' c'

omit [SampleableType PQC] in
private theorem semFwdHook_simStateCCanon {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ)
    (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semFwdHook P Dh encPt encT lam sh qep B sC ex Q w isDel ci? Tpk pq' honestC c' =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semFwdHook P Dh encPt encT lam sh qep B (simStateCCanon sC) ex Q w isDel ci? Tpk pq' honestC c' := by
  unfold semFwdHook
  rcases honestC with _ | c
  · exact semFwdAnswerHook_simStateCCanon P Dh encPt encT lam sh qep sC ex Q w isDel ci? Tpk pq' c'
  · have hsi : (simStateCCanon sC).base.mir.safeInj 3 = sC.base.mir.safeInj 3 := rfl
    have hev : evalCKClamp P Dh encPt encT lam B (simStateCCanon sC) Q w c c' =
        evalCKClamp P Dh encPt encT lam B sC Q w c c' := rfl
    dsimp only []
    rw [hsi, hev]
    split_ifs
    · rcases evalCKClamp P Dh encPt encT lam B sC Q w c c' with _ | r
      · simp [Prod.map, simStateCCanon_idem]
      · exact semResyncHook_simStateCCanon P Dh encPt encT lam sh qep sC ex Q w ci? Tpk pq' c r
    · exact semFwdAnswerHook_simStateCCanon P Dh encPt encT lam sh qep sC ex Q w isDel ci? Tpk pq' c'

omit [SampleableType PQC] in
private theorem semRecvHook_simStateCCanon {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semRecvHook P Dh encPt encT decT lam sh qep B sC ex Q w isDel =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semRecvHook P Dh encPt encT decT lam sh qep B (simStateCCanon sC) ex Q w isDel := by
  unfold semRecvHook
  have hstop : (simStateCCanon sC).base.stopped = sC.base.stopped := rfl
  have hwin : (simStateCCanon sC).base.mir.win = sC.base.mir.win := rfl
  have hin : (simStateCCanon sC).base.mir.inTransit Q.other w = sC.base.mir.inTransit Q.other w := rfl
  have hsi : (simStateCCanon sC).base.mir.safeInj 3 = sC.base.mir.safeInj 3 := rfl
  have hpq : (simStateCCanon sC).base.pq = sC.base.pq := rfl
  have hhon : (simStateCCanon sC).base.honest = sC.base.honest := rfl
  have hch : (simStateCCanon sC).base.chains = sC.base.chains := rfl
  have hep : (simStateCCanon sC).base.mir.epoch = sC.base.mir.epoch := rfl
  have hinw : inReceiveOnlyEpoch (simStateCCanon sC).base.mir Q = inReceiveOnlyEpoch sC.base.mir Q := rfl
  have hamb : (simStateCCanon sC).base.amb = sC.base.amb := rfl
  dsimp only []
  rw [hstop, hwin, hin, hsi, hpq, hhon, hch, hep, hinw, hamb]
  by_cases hr :
      (sC.base.stopped || sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
          !(ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp [hr, Prod.map, simStateCCanon_idem]
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]
    rcases simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩
    · simp [Prod.map, simStateCCanon_idem]
    · dsimp only []
      rcases hci : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci
      · rw [hci]; dsimp only []
        set honestC := (sC.base.honest.find? fun wc =>
          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
        set evicted := (honestC.map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true
        set saltEq := (honestC.map fun c => decide (c.2.2.2 = lct.2.2)) == some true
        set amb := inReceiveOnlyEpoch sC.base.mir Q ||
          (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
        set sCAmb : LibsignalToModularSchemeSimState PQ Pt ℓ :=
          { sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }
        set sCAmbRhs : LibsignalToModularSchemeSimState PQ Pt ℓ :=
          { base := if amb then
              { mir := (simStateCCanon sC).base.mir, pq := sC.base.pq,
                pn := (simStateCCanon sC).base.pn, unackA := (simStateCCanon sC).base.unackA,
                honest := sC.base.honest, chains := sC.base.chains,
                amb := sC.base.amb + 1, stopped := sC.base.stopped }
            else (simStateCCanon sC).base,
            kept := (simStateCCanon sC).kept,
            sent := (simStateCCanon sC).sent,
            snaps := (simStateCCanon sC).snaps }
        have hsCAmb : sCAmbRhs = simStateCCanon sCAmb := by
          dsimp only [sCAmbRhs, sCAmb, simStateCCanon, simStateCanon]
          split_ifs <;> rfl
        by_cases h1 : (evicted && saltEq) = true
        · simp [h1, Prod.map, simStateCCanon_idem]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte]
          by_cases h2 : (T? == some 0) = true
          · simp [h2, Prod.map, simStateCCanon_idem]
          · simp only [h2, Bool.false_eq_true, ↓reduceIte]
            by_cases h3 : (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) ||
                decide (2 ^ 32 ≤ i)) = true
            · simp only [h3, ↓reduceIte]
              rw [hsCAmb]
              simp [Prod.map, simStateCCanon_idem]
            · simp only [h3, Bool.false_eq_true, ↓reduceIte]
              rcases T? with _ | T
              · dsimp only []
                rw [hsCAmb]
                simp [Prod.map, simStateCCanon_idem]
              · dsimp only []
                rw [hsCAmb]
                by_cases h4 : evicted = true
                · simp only [h4, ↓reduceIte]
                  exact semFwdEvictHook_simStateCCanon P Dh encPt encT lam sh qep sCAmb ex Q w isDel pk pq' _
                · simp only [h4, Bool.false_eq_true, ↓reduceIte]
                  exact semFwdHook_simStateCCanon P Dh encPt encT lam sh qep B sCAmb ex Q w isDel none pk pq' _ _
      · rw [hci]; dsimp only []
        by_cases hrej : (((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i) = true
        · simp only [hrej, ↓reduceIte]
          simp [Prod.map, simStateCCanon_idem]
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte]
          exact semFwdHook_simStateCCanon P Dh encPt encT lam sh qep B sC ex Q w isDel (some ci) pk pq' _ _

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem semCorrHookDedup_simStateCCanon {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex) (Q : Party) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semCorrHookDedup P Dh encT sh sC ex Q =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semCorrHook P Dh encT sh (simStateCCanon sC) ex Q := by
  unfold semCorrHookDedup semCorrHook
  have hca : (simStateCCanon sC).base.mir.corrAllowed Q = sC.base.mir.corrAllowed Q :=
    canonComp_corrAllowed sC.base.mir Q
  have hcond :
      ((simStateCCanon sC).base.stopped || (simStateCCanon sC).base.mir.win ||
       !((simStateCCanon sC).base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch (simStateCCanon sC).base.mir Q ||
       !(noAliceCorrWhileAliceBelowEpoch10 (simStateCCanon sC).base.mir Q)) =
      (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) := by
    rw [hca]; rfl
  rw [hcond]
  by_cases hc :
      (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
  · simp [hc, Prod.map, simStateCCanon_idem]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, map_bind]
    refine bind_congr fun ⟨res, ex₁⟩ => ?_
    rcases res with _ | fig8st
    · simp [Prod.map, simStateCCanon_idem]
    · simp only [map_pure, Prod.map, id_eq,
        show (simStateCCanon sC).base.mir.epoch = sC.base.mir.epoch from rfl,
        show (simStateCCanon sC).base.chains = sC.base.chains from rfl,
        show (simStateCCanon sC).kept = sC.kept from rfl,
        show (simStateCCanon sC).sent = sC.sent from rfl,
        show (simStateCCanon sC).snaps = sC.snaps from rfl]
      have htg : ∀ cs, toGhost P { (simStateCCanon sC).base with chains := cs } Q fig8st =
          toGhost P { sC.base with chains := cs } Q fig8st := fun _ => rfl
      simp only [htg]
      congr 1
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      simp only [simStateCCanon, simStateCanon]
      congr 2
      exact canonComp_afterCorrDedup sC.base.mir Q

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem semCorrHook_simStateCCanon {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex) (Q : Party) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semCorrHook P Dh encT sh sC ex Q =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semCorrHook P Dh encT sh (simStateCCanon sC) ex Q := by
  unfold semCorrHook
  have hca : (simStateCCanon sC).base.mir.corrAllowed Q = sC.base.mir.corrAllowed Q :=
    canonComp_corrAllowed sC.base.mir Q
  have hcond :
      ((simStateCCanon sC).base.stopped || (simStateCCanon sC).base.mir.win ||
       !((simStateCCanon sC).base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch (simStateCCanon sC).base.mir Q ||
       !(noAliceCorrWhileAliceBelowEpoch10 (simStateCCanon sC).base.mir Q)) =
      (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) := by
    rw [hca]; rfl
  rw [hcond]
  by_cases hc :
      (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
  · simp [hc, Prod.map, simStateCCanon_idem]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, map_bind]
    refine bind_congr fun ⟨res, ex₁⟩ => ?_
    rcases res with _ | fig8st
    · simp [Prod.map, simStateCCanon_idem]
    · simp only [map_pure, Prod.map, id_eq,
        show (simStateCCanon sC).base.mir.epoch = sC.base.mir.epoch from rfl,
        show (simStateCCanon sC).base.chains = sC.base.chains from rfl,
        show (simStateCCanon sC).kept = sC.kept from rfl,
        show (simStateCCanon sC).sent = sC.sent from rfl,
        show (simStateCCanon sC).snaps = sC.snaps from rfl]
      have htg : ∀ cs, toGhost P { (simStateCCanon sC).base with chains := cs } Q fig8st =
          toGhost P { sC.base with chains := cs } Q fig8st := fun _ => rfl
      simp only [htg]
      congr 1
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      simp only [simStateCCanon, simStateCanon]
      congr 2
      exact canonComp_afterCorr sC.base.mir Q

omit [SampleableType PQC] in
private theorem semHandleHookDedup_simStateCCanon {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep B : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semHandleHookDedup P Dh encPt encT decT lam sh qep B t sC ex =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semHandleHook P Dh encPt encT decT lam sh qep B t (simStateCCanon sC) ex := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_simStateCCanon P Dh encPt encT lam sh qep sC ex Q m₀ none r
  · exact semSendHook_simStateCCanon P Dh encPt encT lam sh qep sC ex Q m₀ (some m₁) r
  · unfold semHandleHookDedup semHandleHook
    have hhon : (simStateCCanon sC).base.honest = sC.base.honest := rfl
    dsimp only []
    rw [hhon]
    have hrec := semRecvHook_simStateCCanon P Dh encPt encT decT lam sh qep B sC ex Q w true
    set j? := sC.base.honest.reverse.findIdx? (fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    have hpost : ∀ oa : OracleComp T
        (Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)),
        Prod.map id (Prod.map simStateCCanon id) <$>
          (oa >>= fun ⟨rr, sC₁, ex₁⟩ =>
            sh.onDeliverPost Q j? rr ex₁ >>= fun ex₂ => pure (rr, (sC₁, ex₂))) =
        (Prod.map id (Prod.map simStateCCanon id) <$> oa) >>= fun ⟨rr, sC₁, ex₁⟩ =>
          sh.onDeliverPost Q j? rr ex₁ >>= fun ex₂ => pure (rr, (sC₁, ex₂)) := by
      intro oa
      rw [map_bind, bind_map_left]
      refine bind_congr fun ⟨rr, sC₁, ex₁⟩ => ?_
      simp [Prod.map]
    rw [hpost, hrec, ← hpost]
  · exact semRecvHook_simStateCCanon P Dh encPt encT decT lam sh qep B sC ex Q w false
  · exact semCorrHookDedup_simStateCCanon P Dh encT sh sC ex Q

omit [SampleableType PQC] in
private theorem semHandleHook_simStateCCanon {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep B : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semHandleHook P Dh encPt encT decT lam sh qep B t sC ex =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semHandleHook P Dh encPt encT decT lam sh qep B t (simStateCCanon sC) ex := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_simStateCCanon P Dh encPt encT lam sh qep sC ex Q m₀ none r
  · exact semSendHook_simStateCCanon P Dh encPt encT lam sh qep sC ex Q m₀ (some m₁) r
  · unfold semHandleHook
    have hhon : (simStateCCanon sC).base.honest = sC.base.honest := rfl
    dsimp only []
    rw [hhon]
    have hrec := semRecvHook_simStateCCanon P Dh encPt encT decT lam sh qep B sC ex Q w true
    set j? := sC.base.honest.reverse.findIdx? (fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    have hpost : ∀ oa : OracleComp T
        (Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)),
        Prod.map id (Prod.map simStateCCanon id) <$>
          (oa >>= fun ⟨rr, sC₁, ex₁⟩ =>
            sh.onDeliverPost Q j? rr ex₁ >>= fun ex₂ => pure (rr, (sC₁, ex₂))) =
        (Prod.map id (Prod.map simStateCCanon id) <$> oa) >>= fun ⟨rr, sC₁, ex₁⟩ =>
          sh.onDeliverPost Q j? rr ex₁ >>= fun ex₂ => pure (rr, (sC₁, ex₂)) := by
      intro oa
      rw [map_bind, bind_map_left]
      refine bind_congr fun ⟨rr, sC₁, ex₁⟩ => ?_
      simp [Prod.map]
    rw [hpost, hrec, ← hpost]
  · exact semRecvHook_simStateCCanon P Dh encPt encT decT lam sh qep B sC ex Q w false
  · exact semCorrHook_simStateCCanon P Dh encT sh sC ex Q

def simDeliverForgeOracle (qep B : ℕ) :
    QueryImpl (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × List (SimFig8C Pt))
        (SM.Construction.DeliverForge.AdversaryCompDF
          (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)))
  | .inl n =>
    StateT.lift
      (query (spec := unifSpec +
        SM.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) (.inl n))
  | .inr t => StateT.mk fun ⟨sC, ex⟩ =>
    semHandleHook P Dh encPt encT decT lam deliverForgeSemHook qep B t sC ex

def simDeliverForgeOracleDedup (qep B : ℕ) :
    QueryImpl (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × List (SimFig8C Pt))
        (SM.Construction.DeliverForge.AdversaryCompDF
          (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)))
  | .inl n =>
    StateT.lift
      (query (spec := unifSpec +
        SM.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) (.inl n))
  | .inr t => StateT.mk fun ⟨sC, ex⟩ =>
    semHandleHookDedup P Dh encPt encT decT lam deliverForgeSemHook qep B t sC ex

private theorem run'_simulateQ_simDeliverForgeOracleDedup_eq (qep B : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (st : LibsignalToModularSchemeSimState PQ Pt ℓ × List (SimFig8C Pt)) :
    (simulateQ (simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B) A).run' st =
      (simulateQ (simDeliverForgeOracle P Dh encPt encT decT lam qep B) A).run' st := by
  refine run'_simulateQ_eq_of_idem_proj
    (simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B)
    (simDeliverForgeOracle P Dh encPt encT decT lam qep B)
    (Prod.map simStateCCanon id) ?_ ?_ A rfl
  · rintro (n | t) ⟨sC, ex⟩
    · simp [simDeliverForgeOracleDedup, simDeliverForgeOracle, StateT.run_lift, Prod.map,
        simStateCCanon_idem]
    · exact semHandleHookDedup_simStateCCanon P Dh encPt encT decT lam deliverForgeSemHook
        qep B t sC ex
  · rintro (n | t) ⟨sC, ex⟩
    · simp [simDeliverForgeOracle, StateT.run_lift, Prod.map, simStateCCanon_idem]
    · exact semHandleHook_simStateCCanon P Dh encPt encT decT lam deliverForgeSemHook
        qep B t sC ex

/-- `B`-clamped semantic counterpart of `simDeliverForge` matching `simDeliverForgeProg`. -/
def simDeliverForgeClamp (qep B : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    SM.Construction.DeliverForge.AdversaryCompDF
      (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) Bool := do
  let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
    SM.Construction.DeliverForge.AdversaryCompDF
      (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) (BitVec 256))
  let sC₀ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
  (simulateQ (simDeliverForgeOracle P Dh encPt encT decT lam qep B) A).run' (sC₀, [])

private theorem simDeliverForgeProg_init_eval (L qep B : ℕ) :
    (simDeliverForgeProg (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).init.eval
      (Env.cons () Env.nil) =
    (do
      let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
        SM.Construction.DeliverForge.AdversaryCompDF
          (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) (BitVec 256))
      return ((), ((initSimCE P Dh encPt encT decT lam K toKemCoins
        (Γ := [.base SimSort.bv256, .unit]) .v0).eval
        (Env.cons (t := (.base SimSort.bv256 : Ty S)) pqrKey
          (Env.cons (t := (.unit : Ty S)) () Env.nil)),
        []))) := rfl

/-- Evaluation agreement between `simDeliverForgeProg` and `simDeliverForgeClamp` for `q ≤ L` game queries. -/
theorem simDeliverForgeProg_eval (L qep B : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (q : ℕ) (hq : SM.MakesAtMostQueries A q) (hqL : q ≤ L) :
    (simDeliverForgeProg P Dh encPt encT decT lam K toKemCoins L qep B).eval (fun _ => A) () =
      simDeliverForgeClamp P Dh encPt encT decT lam qep B A := by
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  let prog := simDeliverForgeProg (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B
  have hinit_eval :
      Prod.map id (Prod.map (simStateCDec (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) id) <$>
        prog.init.eval (Env.cons () Env.nil) =
      (do
        let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          SM.Construction.DeliverForge.AdversaryCompDF
            (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) (BitVec 256))
        return ((), (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), []))) := by
    rw [show prog.init = (simDeliverForgeProg (ℓ := ℓ) P Dh encPt encT decT lam K
      toKemCoins L qep B).init from rfl, simDeliverForgeProg_init_eval, map_bind]
    refine bind_congr fun pqrKey => ?_
    rw [map_pure]
    simp only [Prod.map, id_eq, initSimCE_eval, Expr.eval, Expr.v0, Env.get_cons_zero]
  have hinit_inv :
      ∀ r ∈ support (prog.init.eval (Env.cons () Env.nil)),
        SimHookRawInv (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)
          id (fun L m (ex : List (SimFig8C Pt)) => ex.length + m ≤ L) L q r.2 := by
    rintro ⟨u₀, sC_raw, ex_raw⟩ hr
    rw [show prog.init = (simDeliverForgeProg (ℓ := ℓ) P Dh encPt encT decT lam K
      toKemCoins L qep B).init from rfl, simDeliverForgeProg_init_eval,
      mem_support_bind_iff] at hr
    obtain ⟨pqrKey, -, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    simp only [Prod.mk.injEq] at hr
    rcases hr with ⟨_, rfl, rfl⟩
    refine ⟨?_, [], rfl, by simp [hqL]⟩
    rw [initSimCE_eval]
    refine ⟨?_, by simp [initSimC, hqL], by simp [initSimC, hqL]⟩
    simp only [SimStateInv, initSimC, initSim, List.length_nil, zero_add]
    exact ⟨hqL, hqL, hqL, ⟨[], by simp [hqL], countLe_nil [], fun _ h => nomatch h⟩,
      by decide, by decide⟩
  have h1 := prog.eval_eq_simulateQ_of_abs
    (Prod.map (simStateCDec (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) id)
    (SimHookRawInv (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)
      id (fun L m (ex : List (SimFig8C Pt)) => ex.length + m ≤ L) L)
    (fun _ => do
      let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
        SM.Construction.DeliverForge.AdversaryCompDF
          (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) (BitVec 256))
      return ((), (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), [])))
    (simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B)
    (fun _ b' => pure b')
    q ()
    hinit_eval hinit_inv
    (fun n s => rfl)
    (fun m t v hv =>
      simHandleHookC_step P Dh encPt encT decT lam K toKemCoins (fun _ => rfl)
        (deliverForgeHookMatch P Dh encPt encT decT lam K toKemCoins L)
        (deliverForgeSemHookInv (PQC := PQC) (Pt := Pt) (ℓ := ℓ) L) qep B m t v hv)
    (fun s b' _ => rfl)
    (fun _ hle hv => hv.mono (deliverForgeSemHookInv (PQC := PQC) (Pt := Pt) (ℓ := ℓ) L) hle)
    (fun _ => A) (fun _ => hq')
  rw [h1]
  unfold simDeliverForgeClamp
  simp only [← run'_simulateQ_simDeliverForgeOracleDedup_eq P Dh encPt encT decT lam qep B A,
    StateT.run'_eq, bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]

abbrev KemExtraRaw (PQ PQC Pt : Type) [Zero Pt] (ℓ : ℕ) : Type :=
  (@kemExtraTy PQ PQC Pt ℓ).denote

def kemFailSemHook (L qep B : ℕ) :
    SemHook PQC Pt ℓ unifSpec (KemExtraRaw PQ PQC Pt ℓ) where
  sampleBv256 := ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
  samplePqc := ($ᵗ PQC : ProbComp PQC)
  onSendCoins Q rq ex :=
    ((kemFailHookC (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onSendCoins
      (Γ := [.prod .bool (.prod (.base .pqc) (@kemExtraTy PQ PQC Pt ℓ))])
      (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))).eval
      (Env.cons (partyEnc Q, rq, ex) Env.nil)
  onTr Q m rc ex :=
    ((kemFailHookC (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onTr
      (Γ := [.prod (.prod .bool (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base .bv256))))
        (@kemExtraTy PQ PQC Pt ℓ)])
      (.fst .v0) (.snd .v0)).eval
      (Env.cons ((partyEnc Q, m, rc), ex) Env.nil)
  onCh Q m₀ m₁ rc ex :=
    ((kemFailHookC (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onCh
      (Γ := [.prod (.prod .bool (.prod (lpubPlainTy PQ PQC Pt ℓ)
        (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base .bv256)))))
        (@kemExtraTy PQ PQC Pt ℓ)])
      (.fst .v0) (.snd .v0)).eval
      (Env.cons ((partyEnc Q, m₀, m₁, rc), ex) Env.nil)
  onDl Q c ex :=
    Prod.map (Option.map SM.smRrDec) id <$>
      ((kemFailHookC (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onDl
        (Γ := [.prod (.prod .bool (fig8CTy PQ PQC Pt ℓ)) (@kemExtraTy PQ PQC Pt ℓ)])
        (.fst .v0) (.snd .v0)).eval
        (Env.cons ((partyEnc Q, c), ex) Env.nil)
  onIj Q c ex :=
    Prod.map (Option.map SM.smRrDec) id <$>
      ((kemFailHookC (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onIj
        (Γ := [.prod (.prod .bool (fig8CTy PQ PQC Pt ℓ)) (@kemExtraTy PQ PQC Pt ℓ)])
        (.fst .v0) (.snd .v0)).eval
        (Env.cons ((partyEnc Q, c), ex) Env.nil)
  onCr Q ex :=
    ((kemFailHookC (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onCr
      (Γ := [.prod .bool (@kemExtraTy PQ PQC Pt ℓ)])
      (.fst .v0) (.snd .v0)).eval
      (Env.cons (partyEnc Q, ex) Env.nil)
  onProbe _ _ ex := pure ex
  onDeliverPost Q j? res ex :=
    ((kemFailHookC (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onDeliverPost
      (Γ := [.prod .bool (.prod (.opt .nat)
        (.prod (.opt (simRrTy PQ PQC Pt ℓ)) (@kemExtraTy PQ PQC Pt ℓ)))])
      (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))).eval
      (Env.cons (partyEnc Q, j?, res.map SM.smRrEnc, ex) Env.nil)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem map_smRrEnc_map_smRrDec {ι : Type} {T : OracleSpec ι} {α β : Type}
    (oa : OracleComp T (Option (Unit ⊕ ℕ × ℕ × Option α) × β)) :
    Prod.map (Option.map SM.smRrEnc) id <$> (Prod.map (Option.map SM.smRrDec) id <$> oa) = oa := by
  rw [Functor.map_map]
  suffices h :
      (fun a : Option (Unit ⊕ ℕ × ℕ × Option α) × β =>
        Prod.map (Option.map SM.smRrEnc) id (Prod.map (Option.map SM.smRrDec) id a)) = id by
    rw [h, id_map]
  funext ⟨rr, x⟩
  rcases rr with _ | (⟨⟩ | ⟨t, i, m⟩) <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem pGet_congr {S' : Sig} {O' : Ops S'} {Γ₁ Γ₂ t}
    (m₁ : Expr O' Γ₁ (.prod t t)) (p₁ : Expr O' Γ₁ .bool)
    (m₂ : Expr O' Γ₂ (.prod t t)) (p₂ : Expr O' Γ₂ .bool)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hm : m₁.eval ρ₁ = m₂.eval ρ₂) (hp : p₁.eval ρ₁ = p₂.eval ρ₂) :
    (pGet m₁ p₁).eval ρ₁ = (pGet m₂ p₂).eval ρ₂ := by
  unfold pGet
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, expr_pair_eval, expr_pair_eval, hm, hp]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem pSet_congr {S' : Sig} {O' : Ops S'} {Γ₁ Γ₂ t}
    (m₁ : Expr O' Γ₁ (.prod t t)) (p₁ : Expr O' Γ₁ .bool) (v₁ : Expr O' Γ₁ t)
    (m₂ : Expr O' Γ₂ (.prod t t)) (p₂ : Expr O' Γ₂ .bool) (v₂ : Expr O' Γ₂ t)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hm : m₁.eval ρ₁ = m₂.eval ρ₂) (hp : p₁.eval ρ₁ = p₂.eval ρ₂)
    (hv : v₁.eval ρ₁ = v₂.eval ρ₂) :
    (pSet m₁ p₁ v₁).eval ρ₁ = (pSet m₂ p₂ v₂).eval ρ₂ := by
  unfold pSet
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, expr_pair_eval, expr_pair_eval,
    expr_pair_eval, expr_pair_eval, hm, hp, hv]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem sendsInE_congr {S' : Sig} {O' : Ops S'} {Γ₁ Γ₂}
    (p₁ : Expr O' Γ₁ .bool) (t₁ : Expr O' Γ₁ .nat)
    (p₂ : Expr O' Γ₂ .bool) (t₂ : Expr O' Γ₂ .nat)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hp : p₁.eval ρ₁ = p₂.eval ρ₂) (ht : t₁.eval ρ₁ = t₂.eval ρ₂) :
    (sendsInE p₁ t₁).eval ρ₁ = (sendsInE p₂ t₂).eval ρ₂ := by
  unfold sendsInE
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, expr_pair_eval, expr_pair_eval, hp, ht]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mMk_congr {recT : Ty S} {O' : Ops S} {Γ₁ Γ₂}
    (b₁ win₁ : Expr O' Γ₁ .bool) (ep₁ idx₁ : Expr O' Γ₁ (.prod .nat .nat))
    (tL₁ : Expr O' Γ₁ (.opt .nat)) (tr₁ : Expr O' Γ₁ (.list recT))
    (ch₁ cp₁ : Expr O' Γ₁ (.list posTy)) (ma₁ : Expr O' Γ₁ (.prod (.tbl .nat) (.tbl .nat)))
    (lk₁ : Expr O' Γ₁ (.list .nat)) (cr₁ : Expr O' Γ₁ (.list (.prod .bool .nat)))
    (b₂ win₂ : Expr O' Γ₂ .bool) (ep₂ idx₂ : Expr O' Γ₂ (.prod .nat .nat))
    (tL₂ : Expr O' Γ₂ (.opt .nat)) (tr₂ : Expr O' Γ₂ (.list recT))
    (ch₂ cp₂ : Expr O' Γ₂ (.list posTy)) (ma₂ : Expr O' Γ₂ (.prod (.tbl .nat) (.tbl .nat)))
    (lk₂ : Expr O' Γ₂ (.list .nat)) (cr₂ : Expr O' Γ₂ (.list (.prod .bool .nat)))
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hb : b₁.eval ρ₁ = b₂.eval ρ₂) (hw : win₁.eval ρ₁ = win₂.eval ρ₂)
    (hep : ep₁.eval ρ₁ = ep₂.eval ρ₂) (hidx : idx₁.eval ρ₁ = idx₂.eval ρ₂)
    (htL : tL₁.eval ρ₁ = tL₂.eval ρ₂) (htr : tr₁.eval ρ₁ = tr₂.eval ρ₂)
    (hch : ch₁.eval ρ₁ = ch₂.eval ρ₂) (hcp : cp₁.eval ρ₁ = cp₂.eval ρ₂)
    (hma : ma₁.eval ρ₁ = ma₂.eval ρ₂) (hlk : lk₁.eval ρ₁ = lk₂.eval ρ₂)
    (hcr : cr₁.eval ρ₁ = cr₂.eval ρ₂) :
    (mMk b₁ win₁ ep₁ idx₁ tL₁ tr₁ ch₁ cp₁ ma₁ lk₁ cr₁).eval ρ₁ =
      (mMk b₂ win₂ ep₂ idx₂ tL₂ tr₂ ch₂ cp₂ ma₂ lk₂ cr₂).eval ρ₂ := by
  unfold mMk
  simp only [expr_pair_eval, hb, hw, hep, hidx, htL, htr, hch, hcp, hma, hlk, hcr]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mSafeChE_congr {recT : Ty S} {O' : Ops S} {Γ₁ Γ₂}
    (s₁ : Expr O' Γ₁ (mirTy recT)) (p₁ : Expr O' Γ₁ .bool)
    (s₂ : Expr O' Γ₂ (mirTy recT)) (p₂ : Expr O' Γ₂ .bool)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hs : s₁.eval ρ₁ = s₂.eval ρ₂) (hp : p₁.eval ρ₁ = p₂.eval ρ₂) :
    (mSafeChE s₁ p₁).eval ρ₁ = (mSafeChE s₂ p₂).eval ρ₂ := by
  unfold mSafeChE
  rw [letE_eval, letE_eval, expr_pair_eval, expr_pair_eval, hs, hp]
  simp only [healedByE_eval]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mSafeInjE_congr {recT : Ty S} {O' : Ops S} {Γ₁ Γ₂}
    (s₁ : Expr O' Γ₁ (mirTy recT)) (s₂ : Expr O' Γ₂ (mirTy recT))
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hs : s₁.eval ρ₁ = s₂.eval ρ₂) :
    (mSafeInjE s₁).eval ρ₁ = (mSafeInjE s₂).eval ρ₂ := by
  unfold mSafeInjE
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, hs]
  simp only [healedByE_eval, minN_eval]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mLeakE_congr {recT : Ty S} {O' : Ops S} {Γ₁ Γ₂}
    (s₁ : Expr O' Γ₁ (mirTy recT)) (l₁ : Expr O' Γ₁ .nat)
    (s₂ : Expr O' Γ₂ (mirTy recT)) (l₂ : Expr O' Γ₂ .nat)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hs : s₁.eval ρ₁ = s₂.eval ρ₂) (hl : l₁.eval ρ₁ = l₂.eval ρ₂) :
    (mLeakE s₁ l₁).eval ρ₁ = (mLeakE s₂ l₂).eval ρ₂ := by
  unfold mLeakE
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, expr_pair_eval, expr_pair_eval, hs, hl]
  generalize (s₂.eval ρ₂, l₂.eval ρ₂) = V
  refine mMk_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rfl rfl rfl rfl ?_ rfl rfl rfl rfl ?_ rfl
  · simp only [expr_some_eval, maxOptE_eval]; rfl
  · simp only [Expr.eval, maxOptE_eval]; rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem add_congr {S' : Sig} {O' : Ops S'} {Γ₁ Γ₂}
    (a₁ b₁ : Expr O' Γ₁ .nat) (a₂ b₂ : Expr O' Γ₂ .nat)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (ha : a₁.eval ρ₁ = a₂.eval ρ₂) (hb : b₁.eval ρ₁ = b₂.eval ρ₂) :
    (Expr.add a₁ b₁).eval ρ₁ = (Expr.add a₂ b₂).eval ρ₂ :=
  congrArg₂ (· + ·) ha hb

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem pair_congr {S' : Sig} {O' : Ops S'} {Γ₁ Γ₂ a b}
    (x₁ : Expr O' Γ₁ a) (y₁ : Expr O' Γ₁ b)
    (x₂ : Expr O' Γ₂ a) (y₂ : Expr O' Γ₂ b)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hx : x₁.eval ρ₁ = x₂.eval ρ₂) (hy : y₁.eval ρ₁ = y₂.eval ρ₂) :
    (Expr.pair x₁ y₁).eval ρ₁ = (Expr.pair x₂ y₂).eval ρ₂ :=
  congrArg₂ Prod.mk hx hy

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem fst_congr {S' : Sig} {O' : Ops S'} {Γ₁ Γ₂ a b}
    (x₁ : Expr O' Γ₁ (.prod a b)) (x₂ : Expr O' Γ₂ (.prod a b))
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hx : x₁.eval ρ₁ = x₂.eval ρ₂) :
    (Expr.fst x₁).eval ρ₁ = (Expr.fst x₂).eval ρ₂ :=
  congrArg Prod.fst hx

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem snd_congr {S' : Sig} {O' : Ops S'} {Γ₁ Γ₂ a b}
    (x₁ : Expr O' Γ₁ (.prod a b)) (x₂ : Expr O' Γ₂ (.prod a b))
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hx : x₁.eval ρ₁ = x₂.eval ρ₂) :
    (Expr.snd x₁).eval ρ₁ = (Expr.snd x₂).eval ρ₂ :=
  congrArg Prod.snd hx

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem some_congr {S' : Sig} {O' : Ops S'} {Γ₁ Γ₂ a}
    (x₁ : Expr O' Γ₁ a) (x₂ : Expr O' Γ₂ a)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hx : x₁.eval ρ₁ = x₂.eval ρ₂) :
    (Expr.some x₁).eval ρ₁ = (Expr.some x₂).eval ρ₂ :=
  congrArg some hx

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mEpMgmtE_congr {recT : Ty S} {O' : Ops S} {Γ₁ Γ₂} (qep : ℕ)
    (s₁ : Expr O' Γ₁ (mirTy recT)) (p₁ : Expr O' Γ₁ .bool) (bad₁ : Expr O' Γ₁ .bool)
    (s₂ : Expr O' Γ₂ (mirTy recT)) (p₂ : Expr O' Γ₂ .bool) (bad₂ : Expr O' Γ₂ .bool)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hs : s₁.eval ρ₁ = s₂.eval ρ₂) (hp : p₁.eval ρ₁ = p₂.eval ρ₂)
    (hbad : bad₁.eval ρ₁ = bad₂.eval ρ₂) :
    (mEpMgmtE qep s₁ p₁ bad₁).eval ρ₁ = (mEpMgmtE qep s₂ p₂ bad₂).eval ρ₂ := by
  unfold mEpMgmtE
  have hV₁ : (Expr.pair s₁ (.pair p₁ bad₁)).eval ρ₁ =
      (s₂.eval ρ₂, p₂.eval ρ₂, bad₂.eval ρ₂) := by
    simp only [expr_pair_eval, hs, hp, hbad]
  have hV₂ : (Expr.pair s₂ (.pair p₂ bad₂)).eval ρ₂ =
      (s₂.eval ρ₂, p₂.eval ρ₂, bad₂.eval ρ₂) := by
    simp only [expr_pair_eval]
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, hV₁, hV₂]
  set V : (Ty.prod (mirTy recT) (.prod .bool .bool)).denote :=
    (s₂.eval ρ₂, p₂.eval ρ₂, bad₂.eval ρ₂)
  have hepP : (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd .v0))).eval (Env.cons V ρ₁) =
      (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd .v0))).eval (Env.cons V ρ₂) :=
    pGet_congr _ _ _ _ _ _ rfl rfl
  have hepNext : (Expr.add (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd .v0)))
      (.nat 1)).eval (Env.cons V ρ₁) =
    (Expr.add (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd .v0)))
      (.nat 1)).eval (Env.cons V ρ₂) :=
    add_congr _ _ _ _ _ _ hepP rfl
  have hsends : (sendsInE (.fst (.snd (Expr.v0 (O := O'))))
      (.add (pGet (mEpoch (.fst .v0)) (.fst (.snd .v0))) (.nat 1))).eval (Env.cons V ρ₁) =
    (sendsInE (.fst (.snd (Expr.v0 (O := O'))))
      (.add (pGet (mEpoch (.fst .v0)) (.fst (.snd .v0))) (.nat 1))).eval (Env.cons V ρ₂) :=
    sendsInE_congr _ _ _ _ _ _ rfl hepNext
  rw [ite_eval _ _ _ (Env.cons V ρ₁), ite_eval _ _ _ (Env.cons V ρ₂), hsends]
  split_ifs
  · rw [ite_eval _ _ _ (Env.cons V ρ₁), ite_eval _ _ _ (Env.cons V ρ₂)]
    have hlt1 : (Expr.lt (.nat qep)
        (.add (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd .v0))) (.nat 1))).eval
        (Env.cons V ρ₁) =
      (Expr.lt (.nat qep)
        (.add (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd .v0))) (.nat 1))).eval
        (Env.cons V ρ₂) :=
      congrArg (fun n => decide (qep < n)) hepNext
    rw [hlt1]
    split_ifs
    · rfl
    · rw [letE_eval _ _ (Env.cons V ρ₁), letE_eval _ _ (Env.cons V ρ₂)]
      have hs1 : (Expr.ite (.and (.snd (.snd (Expr.v0 (O := O'))))
          (.not (mSafeChE (.fst .v0) (.fst (.snd .v0)))))
          (mLeakE (.fst .v0) (.add (pGet (mEpoch (.fst .v0)) (.fst (.snd .v0))) (.nat 1)))
          (.fst .v0)).eval (Env.cons V ρ₁) =
        (Expr.ite (.and (.snd (.snd (Expr.v0 (O := O'))))
          (.not (mSafeChE (.fst .v0) (.fst (.snd .v0)))))
          (mLeakE (.fst .v0) (.add (pGet (mEpoch (.fst .v0)) (.fst (.snd .v0))) (.nat 1)))
          (.fst .v0)).eval (Env.cons V ρ₂) := by
        rw [ite_eval _ _ _ (Env.cons V ρ₁), ite_eval _ _ _ (Env.cons V ρ₂)]
        have hsc : (mSafeChE (.fst (Expr.v0 (O := O'))) (.fst (.snd .v0))).eval (Env.cons V ρ₁) =
            (mSafeChE (.fst (Expr.v0 (O := O'))) (.fst (.snd .v0))).eval (Env.cons V ρ₂) :=
          mSafeChE_congr _ _ _ _ _ _ rfl rfl
        have hc : (Expr.and (.snd (.snd (Expr.v0 (O := O'))))
            (.not (mSafeChE (.fst .v0) (.fst (.snd .v0))))).eval (Env.cons V ρ₁) =
          (Expr.and (.snd (.snd (Expr.v0 (O := O'))))
            (.not (mSafeChE (.fst .v0) (.fst (.snd .v0))))).eval (Env.cons V ρ₂) :=
          congrArg₂ Bool.and rfl (congrArg Bool.not hsc)
        rw [hc]
        split_ifs
        · exact mLeakE_congr _ _ _ _ _ _ rfl hepNext
        · rfl
      rw [hs1]
      set s1 : (mirTy recT).denote :=
        (Expr.ite (.and (.snd (.snd (Expr.v0 (O := O'))))
          (.not (mSafeChE (.fst .v0) (.fst (.snd .v0)))))
          (mLeakE (.fst .v0) (.add (pGet (mEpoch (.fst .v0)) (.fst (.snd .v0))) (.nat 1)))
          (.fst .v0)).eval (Env.cons V ρ₂)
      simp only [expr_some_eval]
      refine congrArg some (mMk_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · rfl
      · rfl
      · refine pSet_congr _ _ _ _ _ _ _ _ ?_ ?_ ?_
        · rfl
        · rfl
        · refine add_congr _ _ _ _ _ _ ?_ ?_
          · refine pGet_congr _ _ _ _ _ _ ?_ ?_
            · rfl
            · rfl
          · rfl
      · refine pSet_congr _ _ _ _ _ _ _ _ ?_ ?_ ?_
        · rfl
        · rfl
        · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
  · rw [ite_eval _ _ _ (Env.cons V ρ₁), ite_eval _ _ _ (Env.cons V ρ₂)]
    have hlt2 : (Expr.lt (.nat qep)
        (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd .v0)))).eval (Env.cons V ρ₁) =
      (Expr.lt (.nat qep)
        (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd .v0)))).eval (Env.cons V ρ₂) :=
      congrArg (fun n => decide (qep < n)) hepP
    rw [hlt2]
    split_ifs <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mRecordE_congr {restT : Ty S} {O' : Ops S} {Γ₁ Γ₂}
    (s₁ : Expr O' Γ₁ (mirTy (.prod posTy restT))) (p₁ : Expr O' Γ₁ .bool)
    (r₁ : Expr O' Γ₁ (.prod posTy restT)) (ch₁ : Expr O' Γ₁ .bool)
    (s₂ : Expr O' Γ₂ (mirTy (.prod posTy restT))) (p₂ : Expr O' Γ₂ .bool)
    (r₂ : Expr O' Γ₂ (.prod posTy restT)) (ch₂ : Expr O' Γ₂ .bool)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hs : s₁.eval ρ₁ = s₂.eval ρ₂) (hp : p₁.eval ρ₁ = p₂.eval ρ₂)
    (hr : r₁.eval ρ₁ = r₂.eval ρ₂) (hch : ch₁.eval ρ₁ = ch₂.eval ρ₂) :
    (mRecordE s₁ p₁ r₁ ch₁).eval ρ₁ = (mRecordE s₂ p₂ r₂ ch₂).eval ρ₂ := by
  unfold mRecordE
  have hV₁ : (Expr.pair s₁ (.pair p₁ (.pair r₁ ch₁))).eval ρ₁ =
      (s₂.eval ρ₂, p₂.eval ρ₂, r₂.eval ρ₂, ch₂.eval ρ₂) := by
    simp only [expr_pair_eval, hs, hp, hr, hch]
  have hV₂ : (Expr.pair s₂ (.pair p₂ (.pair r₂ ch₂))).eval ρ₂ =
      (s₂.eval ρ₂, p₂.eval ρ₂, r₂.eval ρ₂, ch₂.eval ρ₂) := by
    simp only [expr_pair_eval]
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, hV₁, hV₂]
  set V : (Ty.prod (mirTy (.prod posTy restT))
      (.prod .bool (.prod (.prod posTy restT) .bool))).denote :=
    (s₂.eval ρ₂, p₂.eval ρ₂, r₂.eval ρ₂, ch₂.eval ρ₂)
  refine mMk_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · refine pSet_congr _ _ _ _ _ _ _ _ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
  · rfl
  · rfl
  · rw [ite_eval _ _ _ (Env.cons V ρ₁), ite_eval _ _ _ (Env.cons V ρ₂),
      show (Expr.snd (.snd (.snd (Expr.v0 (O := O'))))).eval (Env.cons V ρ₁) =
        (Expr.snd (.snd (.snd (Expr.v0 (O := O'))))).eval (Env.cons V ρ₂) from rfl]
    split_ifs <;> rfl
  · have hsc : (mSafeChE (.fst (Expr.v0 (O := O'))) (.fst (.snd .v0))).eval (Env.cons V ρ₁) =
        (mSafeChE (.fst (Expr.v0 (O := O'))) (.fst (.snd .v0))).eval (Env.cons V ρ₂) := by
      refine mSafeChE_congr _ _ _ _ _ _ ?_ ?_
      · rfl
      · rfl
    rw [ite_eval _ _ _ (Env.cons V ρ₁), ite_eval _ _ _ (Env.cons V ρ₂), hsc]
    split_ifs <;> rfl
  · rfl
  · rfl
  · rfl

omit [SampleableType PQC] in
private theorem fgInTransitE_congr (L : ℕ) {Γ₁ Γ₂}
    (m₁ : Expr OFig Γ₁ (mirTy fig8RecTy)) (q₁ : Expr OFig Γ₁ .bool)
    (c₁ : Expr OFig Γ₁ (fig8CTy PQ PQC Pt ℓ))
    (m₂ : Expr OFig Γ₂ (mirTy fig8RecTy)) (q₂ : Expr OFig Γ₂ .bool)
    (c₂ : Expr OFig Γ₂ (fig8CTy PQ PQC Pt ℓ))
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hm : m₁.eval ρ₁ = m₂.eval ρ₂) (hq : q₁.eval ρ₁ = q₂.eval ρ₂)
    (hc : c₁.eval ρ₁ = c₂.eval ρ₂) :
    (fgInTransitE P Dh encPt encT decT lam K toKemCoins L m₁ q₁ c₁).eval ρ₁ =
      (fgInTransitE P Dh encPt encT decT lam K toKemCoins L m₂ q₂ c₂).eval ρ₂ := by
  unfold fgInTransitE
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, expr_pair_eval, expr_pair_eval,
    expr_pair_eval, expr_pair_eval, hm, hq, hc]
  refine congrArg₂ List.find? (funext fun x => ?_) rfl
  exact congrArg₂ Bool.and rfl (congrArg ((OFig).eval SimOp.eqFig8C) rfl)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mDeleteE_congr {restT : Ty S} {O' : Ops S} {Γ₁ Γ₂} (K : ℕ)
    (s₁ : Expr O' Γ₁ (mirTy (.prod posTy restT))) (pos₁ : Expr O' Γ₁ posTy)
    (s₂ : Expr O' Γ₂ (mirTy (.prod posTy restT))) (pos₂ : Expr O' Γ₂ posTy)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hs : s₁.eval ρ₁ = s₂.eval ρ₂) (hpos : pos₁.eval ρ₁ = pos₂.eval ρ₂) :
    (mDeleteE K s₁ pos₁).eval ρ₁ = (mDeleteE K s₂ pos₂).eval ρ₂ := by
  unfold mDeleteE
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, expr_pair_eval, expr_pair_eval, hs, hpos]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem maxAccSet_congr {S' : Sig} {O' : Ops S'} {Γ₁ Γ₂}
    (ma₁ : Expr O' Γ₁ (.prod (.tbl .nat) (.tbl .nat))) (p₁ : Expr O' Γ₁ .bool)
    (ep₁ val₁ : Expr O' Γ₁ .nat)
    (ma₂ : Expr O' Γ₂ (.prod (.tbl .nat) (.tbl .nat))) (p₂ : Expr O' Γ₂ .bool)
    (ep₂ val₂ : Expr O' Γ₂ .nat)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hma : ma₁.eval ρ₁ = ma₂.eval ρ₂) (hp : p₁.eval ρ₁ = p₂.eval ρ₂)
    (hep : ep₁.eval ρ₁ = ep₂.eval ρ₂) (hval : val₁.eval ρ₁ = val₂.eval ρ₂) :
    (maxAccSet ma₁ p₁ ep₁ val₁).eval ρ₁ = (maxAccSet ma₂ p₂ ep₂ val₂).eval ρ₂ := by
  unfold maxAccSet
  have hV : (Expr.pair ma₁ (.pair p₁ (.pair ep₁ val₁))).eval ρ₁ =
      (ma₂.eval ρ₂, p₂.eval ρ₂, ep₂.eval ρ₂, val₂.eval ρ₂) := by
    simp only [expr_pair_eval, hma, hp, hep, hval]
  have hV₂ : (Expr.pair ma₂ (.pair p₂ (.pair ep₂ val₂))).eval ρ₂ =
      (ma₂.eval ρ₂, p₂.eval ρ₂, ep₂.eval ρ₂, val₂.eval ρ₂) := by
    simp only [expr_pair_eval]
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, hV, hV₂]
  set V : (Ty.prod (.prod (.tbl .nat) (.tbl .nat)) (.prod .bool (.prod .nat .nat))).denote :=
    (ma₂.eval ρ₂, p₂.eval ρ₂, ep₂.eval ρ₂, val₂.eval ρ₂)
  refine pSet_congr _ _ _ _ _ _ _ _ rfl rfl ?_
  have hg : (pGet (.fst (Expr.v0 (O := O'))) (.fst (.snd .v0))).eval (Env.cons V ρ₁) =
      (pGet (.fst (Expr.v0 (O := O'))) (.fst (.snd .v0))).eval (Env.cons V ρ₂) :=
    pGet_congr _ _ _ _ _ _ rfl rfl
  simp only [Expr.eval, hg]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mAcceptE_congr {restT : Ty S} {O' : Ops S} {Γ₁ Γ₂} (K : ℕ)
    (s₁ : Expr O' Γ₁ (mirTy (.prod posTy restT))) (p₁ : Expr O' Γ₁ .bool) (pos₁ : Expr O' Γ₁ posTy)
    (s₂ : Expr O' Γ₂ (mirTy (.prod posTy restT))) (p₂ : Expr O' Γ₂ .bool) (pos₂ : Expr O' Γ₂ posTy)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hs : s₁.eval ρ₁ = s₂.eval ρ₂) (hp : p₁.eval ρ₁ = p₂.eval ρ₂)
    (hpos : pos₁.eval ρ₁ = pos₂.eval ρ₂) :
    (mAcceptE K s₁ p₁ pos₁).eval ρ₁ = (mAcceptE K s₂ p₂ pos₂).eval ρ₂ := by
  unfold mAcceptE
  have hdel := mDeleteE_congr K s₁ pos₁ s₂ pos₂ ρ₁ ρ₂ hs hpos
  have hV₁ : (Expr.pair (mDeleteE K s₁ pos₁) (.pair p₁ pos₁)).eval ρ₁ =
      ((mDeleteE K s₂ pos₂).eval ρ₂, p₂.eval ρ₂, pos₂.eval ρ₂) := by
    simp only [expr_pair_eval, hdel, hp, hpos]
  have hV₂ : (Expr.pair (mDeleteE K s₂ pos₂) (.pair p₂ pos₂)).eval ρ₂ =
      ((mDeleteE K s₂ pos₂).eval ρ₂, p₂.eval ρ₂, pos₂.eval ρ₂) := by
    simp only [expr_pair_eval]
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, hV₁, hV₂]
  set V : (Ty.prod (mirTy (.prod posTy restT)) (.prod .bool posTy)).denote :=
    ((mDeleteE K s₂ pos₂).eval ρ₂, p₂.eval ρ₂, pos₂.eval ρ₂)
  refine mMk_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rfl rfl ?_ rfl rfl rfl rfl rfl ?_ rfl rfl
  · refine pSet_congr _ _ _ _ _ _ _ _ rfl rfl ?_
    have hg : (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd .v0))).eval (Env.cons V ρ₁) =
        (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd .v0))).eval (Env.cons V ρ₂) :=
      pGet_congr _ _ _ _ _ _ rfl rfl
    simp only [maxN_eval, hg]
    rfl
  · refine maxAccSet_congr _ _ _ _ _ _ _ _ _ _ rfl rfl rfl ?_
    have hg : (pGet (mMaxAcc (.fst (Expr.v0 (O := O')))) (.fst (.snd .v0))).eval (Env.cons V ρ₁) =
        (pGet (mMaxAcc (.fst (Expr.v0 (O := O')))) (.fst (.snd .v0))).eval (Env.cons V ρ₂) :=
      pGet_congr _ _ _ _ _ _ rfl rfl
    simp only [maxN_eval, maxAccGet, Expr.eval, hg]
    rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mChallContainsE_congr {recT : Ty S} {O' : Ops S} {Γ₁ Γ₂} (K : ℕ)
    (s₁ : Expr O' Γ₁ (mirTy recT)) (pos₁ : Expr O' Γ₁ posTy)
    (s₂ : Expr O' Γ₂ (mirTy recT)) (pos₂ : Expr O' Γ₂ posTy)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hs : s₁.eval ρ₁ = s₂.eval ρ₂) (hpos : pos₁.eval ρ₁ = pos₂.eval ρ₂) :
    (mChallContainsE K s₁ pos₁).eval ρ₁ = (mChallContainsE K s₂ pos₂).eval ρ₂ := by
  unfold mChallContainsE
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, expr_pair_eval, expr_pair_eval, hs, hpos]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mTrivialE_congr {restT : Ty S} {O' : Ops S} {Γ₁ Γ₂} (K : ℕ)
    (s₁ : Expr O' Γ₁ (mirTy (.prod posTy restT))) (pos₁ : Expr O' Γ₁ posTy)
    (s₂ : Expr O' Γ₂ (mirTy (.prod posTy restT))) (pos₂ : Expr O' Γ₂ posTy)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hs : s₁.eval ρ₁ = s₂.eval ρ₂) (hpos : pos₁.eval ρ₁ = pos₂.eval ρ₂) :
    (mTrivialE K s₁ pos₁).eval ρ₁ = (mTrivialE K s₂ pos₂).eval ρ₂ := by
  unfold mTrivialE
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, expr_pair_eval, expr_pair_eval, hs, hpos]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mSetWin_congr {recT : Ty S} {O' : Ops S} {Γ₁ Γ₂}
    (s₁ : Expr O' Γ₁ (mirTy recT)) (w₁ : Expr O' Γ₁ .bool)
    (s₂ : Expr O' Γ₂ (mirTy recT)) (w₂ : Expr O' Γ₂ .bool)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hs : s₁.eval ρ₁ = s₂.eval ρ₂) (hw : w₁.eval ρ₁ = w₂.eval ρ₂) :
    (mSetWin s₁ w₁).eval ρ₁ = (mSetWin s₂ w₂).eval ρ₂ := by
  unfold mSetWin
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, expr_pair_eval, expr_pair_eval, hs, hw]
  refine mMk_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mCorrAllowedE_congr {restT : Ty S} {O' : Ops S} {Γ₁ Γ₂} (K : ℕ)
    (s₁ : Expr O' Γ₁ (mirTy (.prod posTy restT))) (p₁ : Expr O' Γ₁ .bool)
    (s₂ : Expr O' Γ₂ (mirTy (.prod posTy restT))) (p₂ : Expr O' Γ₂ .bool)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hs : s₁.eval ρ₁ = s₂.eval ρ₂) (hp : p₁.eval ρ₁ = p₂.eval ρ₂) :
    (mCorrAllowedE K s₁ p₁).eval ρ₁ = (mCorrAllowedE K s₂ p₂).eval ρ₂ := by
  unfold mCorrAllowedE
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, expr_pair_eval, expr_pair_eval, hs, hp]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mAfterCorrE_mk_congr {restT : Ty S} {O' : Ops S} {Γ₁ Γ₂}
    (s2₁ : Expr O' Γ₁ (mirTy (.prod posTy restT)))
    (c₁ : Expr O' Γ₁ (.prod .bool .nat))
    (s2₂ : Expr O' Γ₂ (mirTy (.prod posTy restT)))
    (c₂ : Expr O' Γ₂ (.prod .bool .nat))
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hs2 : s2₁.eval ρ₁ = s2₂.eval ρ₂)
    (hc : c₁.eval ρ₁ = c₂.eval ρ₂) :
    (mMk (mB s2₁) (mWin s2₁) (mEpoch s2₁) (mIdx s2₁) (mTL s2₁)
      (mTrans s2₁) (mChall s2₁) (mComp s2₁) (mMaxAcc s2₁) (mLeaks s2₁)
      (.cons c₁ (mCorrs s2₁))).eval ρ₁ =
    (mMk (mB s2₂) (mWin s2₂) (mEpoch s2₂) (mIdx s2₂) (mTL s2₂)
      (mTrans s2₂) (mChall s2₂) (mComp s2₂) (mMaxAcc s2₂) (mLeaks s2₂)
      (.cons c₂ (mCorrs s2₂))).eval ρ₂ := by
  simp only [mMk, mB, mWin, mEpoch, mIdx, mTL, mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs,
    Expr.eval, hs2, hc]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mAfterCorrE_congr {restT : Ty S} {O' : Ops S} {Γ₁ Γ₂} (K : ℕ)
    (s₁ : Expr O' Γ₁ (mirTy (.prod posTy restT))) (p₁ : Expr O' Γ₁ .bool)
    (s₂ : Expr O' Γ₂ (mirTy (.prod posTy restT))) (p₂ : Expr O' Γ₂ .bool)
    (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂)
    (hs : s₁.eval ρ₁ = s₂.eval ρ₂) (hp : p₁.eval ρ₁ = p₂.eval ρ₂) :
    (mAfterCorrE K s₁ p₁).eval ρ₁ = (mAfterCorrE K s₂ p₂).eval ρ₂ := by
  unfold mAfterCorrE
  rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂, expr_pair_eval, expr_pair_eval, hs, hp]
  refine mAfterCorrE_mk_congr _ _ _ _ _ _ ?_ ?_
  · refine mLeakE_congr _ _ _ _ _ _ ?_ ?_
    · refine mMk_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · rfl
  · rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem letE_pair_fst_snd_eval {S' : Sig} {O' : Ops S'} {a b u : Ty S'}
    (body : Expr O' (.prod a b :: [.prod a b]) u) (x : a.denote) (y : b.denote) :
    (Expr.letE (.pair (.fst .v0) (.snd .v0)) body).eval (Env.cons (x, y) Env.nil) =
      body.eval (Env.cons (x, y) (Env.cons (x, y) Env.nil)) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem letE_triple_eval {S' : Sig} {O' : Ops S'} {a b c u : Ty S'}
    (body : Expr O' (.prod a (.prod b c) :: [.prod a (.prod b c)]) u)
    (x : a.denote) (y : b.denote) (z : c.denote) :
    (Expr.letE (.pair (.fst .v0) (.pair (.fst (.snd .v0)) (.snd (.snd .v0)))) body).eval
        (Env.cons (x, y, z) Env.nil) =
      body.eval (Env.cons (x, y, z) (Env.cons (x, y, z) Env.nil)) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem letE_quad_eval {S' : Sig} {O' : Ops S'} {a b c d u : Ty S'}
    (body : Expr O' (.prod a (.prod b (.prod c d)) :: [.prod a (.prod b (.prod c d))]) u)
    (w : a.denote) (x : b.denote) (y : c.denote) (z : d.denote) :
    (Expr.letE
      (.pair (.fst .v0)
        (.pair (.fst (.snd .v0))
          (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))))) body).eval
      (Env.cons (w, x, y, z) Env.nil) =
    body.eval (Env.cons (w, x, y, z) (Env.cons (w, x, y, z) Env.nil)) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem bind_ret_pair_fst_snd_eval {S' : Sig} {O' : Ops S'} {ι : Type}
    {T : OracleSpec ι} {I : Iface S' T} {a b u : Ty S'}
    (body : Comp O' I (.prod a b :: [.prod a b]) u) (x : a.denote) (y : b.denote) :
    (Comp.bind (.ret (.pair (.fst .v0) (.snd .v0))) body).eval (Env.cons (x, y) Env.nil) =
      body.eval (Env.cons (x, y) (Env.cons (x, y) Env.nil)) := rfl

omit [DecidableEq Pt] [Zero Pt] in
private theorem kemFailIface_liftP {α : Type} (p : ProbComp α) :
    (KIface).liftP p = p := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t mx ih =>
    simp only [Iface.liftP, simulateQ_query_bind] at ih ⊢
    exact congrArg (query (spec := unifSpec) t >>= ·) (funext ih)

theorem kemFailHookMatch (L qep B : ℕ) :
    HookMatch P Dh encPt encT decT lam K toKemCoins
      (id : KemExtraRaw PQ PQC Pt ℓ → KemExtraRaw PQ PQC Pt ℓ)
      (fun _ _ => True) L
      (kemFailHookC (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
      (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B) where
  sampleBv256_eval _ := rfl
  samplePqc_eval _ := kemFailIface_liftP ($ᵗ PQC)
  onSendCoins_eval qParty rq ex ρ Q ex₀ hq hex := by
    unfold kemFailSemHook kemFailHookC
    simp only [Prod.map_id, id_map]
    rw [comp_eval_ret, comp_eval_ret]
    refine congrArg pure ?_
    have hX : (Expr.pair qParty (.pair rq ex)).eval ρ = (partyEnc Q, rq.eval ρ, ex₀) := by
      simp only [expr_pair_eval, hq, hex, id_eq]
    rw [letE_triple_eval, letE_eval _ _ ρ, hX]
    set X : (Ty.prod .bool (.prod (.base SimSort.pqc) (@kemExtraTy PQ PQC Pt ℓ))).denote :=
      (partyEnc Q, rq.eval ρ, ex₀)
    set ρ₀ := Env.cons X Env.nil
    have hstep :
        (Expr.op (O := OFig) SimOp.stepKemFailSend
          (.pair (.fst (.snd (.snd (.snd .v0))))
            (.pair (.fst .v0) (.fst (.snd .v0))))).eval (Env.cons X ρ) =
        (Expr.op (O := OFig) SimOp.stepKemFailSend
          (.pair (.fst (.snd (.snd (.snd .v0))))
            (.pair (.fst .v0) (.fst (.snd .v0))))).eval (Env.cons X ρ₀) :=
      congrArg ((OFig).eval SimOp.stepKemFailSend) rfl
    simp only [expr_pair_eval, expr_fst_eval, expr_snd_eval, hstep]
    rfl
  onTr_eval _ _ ρ Q m rc ex₀ harg hex := by
    unfold kemFailSemHook kemFailHookC
    simp only [Prod.map_id, id_map]
    rw [comp_eval_bind_ret, bind_ret_pair_fst_snd_eval, expr_pair_eval, harg, hex]
    dsimp only [id]
    set X : (Ty.prod (.prod .bool (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base SimSort.bv256))))
        (@kemExtraTy PQ PQC Pt ℓ)).denote :=
      ((partyEnc Q, m, rc), ex₀)
    set ρ₀ := Env.cons X Env.nil
    rw [comp_eval_ite, comp_eval_ite]
    have hwin :
        (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig)))))).eval (Env.cons X ρ) =
        (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig)))))).eval (Env.cons X ρ₀) := rfl
    rw [hwin]
    split_ifs
    · rfl
    · rw [comp_eval_bind, comp_eval_bind]
      have hsam :
          (samIfNecFig8C P Dh encPt encT decT lam K toKemCoins
            (.snd (.snd (.fst .v0)))).eval (Env.cons X ρ) =
          (samIfNecFig8C P Dh encPt encT decT lam K toKemCoins
            (.snd (.snd (.fst .v0)))).eval (Env.cons X ρ₀) := by
        rcases rc with _ | c <;> rfl
      rw [hsam]
      refine bind_congr fun y => ?_
      rw [comp_eval_ret, comp_eval_ret]
      refine congrArg pure ?_
      have hep :
          (mEpMgmtE (O' := OFig) (qep + 1) (fgMir (.fst (.snd .v1)))
            (.fst (.fst .v1)) (.snd .v0)).eval (Env.cons y (Env.cons X ρ)) =
          (mEpMgmtE (O' := OFig) (qep + 1) (fgMir (.fst (.snd .v1)))
            (.fst (.fst .v1)) (.snd .v0)).eval (Env.cons y (Env.cons X ρ₀)) := by
        refine mEpMgmtE_congr (O' := OFig) (qep + 1) _ _ _ _ _ _ _ _ ?_ ?_ ?_
        · rfl
        · rfl
        · rfl
      rw [expr_caseOpt_eval _ _ _ (Env.cons y (Env.cons X ρ)),
        expr_caseOpt_eval _ _ _ (Env.cons y (Env.cons X ρ₀)), hep]
      rcases (mEpMgmtE (O' := OFig) (qep + 1) (fgMir (.fst (.snd .v1)))
        (.fst (.fst .v1)) (.snd .v0)).eval (Env.cons y (Env.cons X ρ₀)) with _ | mir2
      · rfl
      · have hst_get :
            (pGet (fgSt (.fst (.snd (Expr.v2 (O := OFig))))) (.fst (.fst .v2))).eval
              (Env.cons mir2 (Env.cons y (Env.cons X ρ))) =
            (pGet (fgSt (.fst (.snd (Expr.v2 (O := OFig))))) (.fst (.fst .v2))).eval
              (Env.cons mir2 (Env.cons y (Env.cons X ρ₀))) := by
          refine pGet_congr (O' := OFig) _ _ _ _ _ _ ?_ ?_
          · rfl
          · rfl
        have hout :
            (Expr.op (O := OFig) (SimOp.fig8SendStep B)
              (.pair (pGet (fgSt (.fst (.snd .v2))) (.fst (.fst .v2)))
                (.some (.pair (.fst (.snd (.fst .v2))) (.fst .v1))))).eval
              (Env.cons mir2 (Env.cons y (Env.cons X ρ))) =
            (Expr.op (O := OFig) (SimOp.fig8SendStep B)
              (.pair (pGet (fgSt (.fst (.snd .v2))) (.fst (.fst .v2)))
                (.some (.pair (.fst (.snd (.fst .v2))) (.fst .v1))))).eval
              (Env.cons mir2 (Env.cons y (Env.cons X ρ₀))) :=
          congrArg ((OFig).eval (SimOp.fig8SendStep B))
            (congrArg₂ Prod.mk hst_get rfl)
        refine pair_congr _ _ _ _ _ _ ?_ ?_
        · refine some_congr _ _ _ _ ?_
          refine snd_congr _ _ _ _ ?_
          refine snd_congr _ _ _ _ ?_
          exact hout
        · refine pair_congr _ _ _ _ _ _ ?_ ?_
          · refine pair_congr _ _ _ _ _ _ ?_ ?_
            · refine pSet_congr (O' := OFig) _ _ _ _ _ _ _ _ ?_ ?_ ?_
              · rfl
              · rfl
              · refine fst_congr _ _ _ _ ?_
                refine snd_congr _ _ _ _ ?_
                exact hout
            · refine mRecordE_congr (O' := OFig) _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
              · rfl
              · rfl
              · refine pair_congr _ _ _ _ _ _ ?_ ?_
                · refine pair_congr _ _ _ _ _ _ ?_ ?_
                  · rfl
                  · refine pair_congr _ _ _ _ _ _ ?_ ?_
                    · refine pGet_congr (O' := OFig) _ _ _ _ _ _ ?_ ?_
                      · rfl
                      · rfl
                    · refine add_congr _ _ _ _ _ _ ?_ ?_
                      · refine pGet_congr (O' := OFig) _ _ _ _ _ _ ?_ ?_
                        · rfl
                        · rfl
                      · rfl
                · refine pair_congr _ _ _ _ _ _ ?_ ?_
                  · rfl
                  · refine snd_congr _ _ _ _ ?_
                    refine snd_congr _ _ _ _ ?_
                    exact hout
              · rfl
          · rfl
  onCh_eval _ _ ρ Q m₀ m₁ rc ex₀ harg hex := by
    unfold kemFailSemHook kemFailHookC
    simp only [Prod.map_id, id_map]
    rw [comp_eval_bind_ret, bind_ret_pair_fst_snd_eval, expr_pair_eval, harg, hex]
    dsimp only [id]
    set X : (Ty.prod (.prod .bool (.prod (lpubPlainTy PQ PQC Pt ℓ)
          (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base SimSort.bv256)))))
        (@kemExtraTy PQ PQC Pt ℓ)).denote :=
      ((partyEnc Q, m₀, m₁, rc), ex₀)
    set ρ₀ := Env.cons X Env.nil
    rw [comp_eval_ite, comp_eval_ite]
    have hwin :
        (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig)))))).eval (Env.cons X ρ) =
        (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig)))))).eval (Env.cons X ρ₀) := rfl
    rw [hwin]
    split_ifs
    · rfl
    · rw [comp_eval_bind, comp_eval_bind]
      have hsam :
          (samIfNecFig8C P Dh encPt encT decT lam K toKemCoins
            (.snd (.snd (.snd (.fst .v0))))).eval (Env.cons X ρ) =
          (samIfNecFig8C P Dh encPt encT decT lam K toKemCoins
            (.snd (.snd (.snd (.fst .v0))))).eval (Env.cons X ρ₀) := by
        rcases rc with _ | c <;> rfl
      rw [hsam]
      refine bind_congr fun y => ?_
      rw [comp_eval_ret, comp_eval_ret]
      refine congrArg pure ?_
      have hep :
          (mEpMgmtE (O' := OFig) (qep + 1) (fgMir (.fst (.snd .v1)))
            (.fst (.fst .v1)) (.snd .v0)).eval (Env.cons y (Env.cons X ρ)) =
          (mEpMgmtE (O' := OFig) (qep + 1) (fgMir (.fst (.snd .v1)))
            (.fst (.fst .v1)) (.snd .v0)).eval (Env.cons y (Env.cons X ρ₀)) := by
        refine mEpMgmtE_congr (O' := OFig) (qep + 1) _ _ _ _ _ _ _ _ ?_ ?_ ?_
        · rfl
        · rfl
        · rfl
      rw [expr_caseOpt_eval _ _ _ (Env.cons y (Env.cons X ρ)),
        expr_caseOpt_eval _ _ _ (Env.cons y (Env.cons X ρ₀)), hep]
      rcases (mEpMgmtE (O' := OFig) (qep + 1) (fgMir (.fst (.snd .v1)))
        (.fst (.fst .v1)) (.snd .v0)).eval (Env.cons y (Env.cons X ρ₀)) with _ | mir2
      · rfl
      · dsimp only []
        rw [ite_eval _ _ _ (Env.cons mir2 (Env.cons y (Env.cons X ρ))),
          ite_eval _ _ _ (Env.cons mir2 (Env.cons y (Env.cons X ρ₀)))]
        have hsc0 :
            (mSafeChE .v0 (.fst (.fst (Expr.v2 (O := OFig))))).eval
              (Env.cons mir2 (Env.cons y (Env.cons X ρ))) =
            (mSafeChE .v0 (.fst (.fst (Expr.v2 (O := OFig))))).eval
              (Env.cons mir2 (Env.cons y (Env.cons X ρ₀))) := by
          refine mSafeChE_congr (O' := OFig) _ _ _ _ _ _ ?_ ?_
          · rfl
          · rfl
        have hsc :
            (Expr.not (mSafeChE .v0 (.fst (.fst (Expr.v2 (O := OFig)))))).eval
              (Env.cons mir2 (Env.cons y (Env.cons X ρ))) =
            (Expr.not (mSafeChE .v0 (.fst (.fst (Expr.v2 (O := OFig)))))).eval
              (Env.cons mir2 (Env.cons y (Env.cons X ρ₀))) :=
          congrArg Bool.not hsc0
        rw [hsc]
        split_ifs
        · rfl
        · have hm2 :
              (Expr.ite (mB .v0)
                (.fst (.snd (.snd (.fst (Expr.v2 (O := OFig))))))
                (.fst (.snd (.fst .v2)))).eval
                (Env.cons mir2 (Env.cons y (Env.cons X ρ))) =
              (Expr.ite (mB .v0)
                (.fst (.snd (.snd (.fst (Expr.v2 (O := OFig))))))
                (.fst (.snd (.fst .v2)))).eval
                (Env.cons mir2 (Env.cons y (Env.cons X ρ₀))) := by
            rw [ite_eval _ _ _ (Env.cons mir2 (Env.cons y (Env.cons X ρ))),
              ite_eval _ _ _ (Env.cons mir2 (Env.cons y (Env.cons X ρ₀))),
              show (mB (Expr.v0 (O := OFig))).eval (Env.cons mir2 (Env.cons y (Env.cons X ρ))) =
                (mB (Expr.v0 (O := OFig))).eval (Env.cons mir2 (Env.cons y (Env.cons X ρ₀)))
                from rfl]
            split_ifs <;> rfl
          have hst_get :
              (pGet (fgSt (.fst (.snd (Expr.v2 (O := OFig))))) (.fst (.fst .v2))).eval
                (Env.cons mir2 (Env.cons y (Env.cons X ρ))) =
              (pGet (fgSt (.fst (.snd (Expr.v2 (O := OFig))))) (.fst (.fst .v2))).eval
                (Env.cons mir2 (Env.cons y (Env.cons X ρ₀))) := by
            refine pGet_congr (O' := OFig) _ _ _ _ _ _ ?_ ?_
            · rfl
            · rfl
          have hout :
              (Expr.op (O := OFig) (SimOp.fig8SendStep B)
                (.pair (pGet (fgSt (.fst (.snd .v2))) (.fst (.fst .v2)))
                  (.some (.pair (.ite (mB .v0)
                    (.fst (.snd (.snd (.fst .v2)))) (.fst (.snd (.fst .v2))))
                    (.fst .v1))))).eval
                (Env.cons mir2 (Env.cons y (Env.cons X ρ))) =
              (Expr.op (O := OFig) (SimOp.fig8SendStep B)
                (.pair (pGet (fgSt (.fst (.snd .v2))) (.fst (.fst .v2)))
                  (.some (.pair (.ite (mB .v0)
                    (.fst (.snd (.snd (.fst .v2)))) (.fst (.snd (.fst .v2))))
                    (.fst .v1))))).eval
                (Env.cons mir2 (Env.cons y (Env.cons X ρ₀))) :=
            congrArg ((OFig).eval (SimOp.fig8SendStep B))
              (congrArg₂ Prod.mk hst_get (congrArg some (congrArg₂ Prod.mk hm2 rfl)))
          refine pair_congr _ _ _ _ _ _ ?_ ?_
          · refine some_congr _ _ _ _ ?_
            refine snd_congr _ _ _ _ ?_
            refine snd_congr _ _ _ _ ?_
            exact hout
          · refine pair_congr _ _ _ _ _ _ ?_ ?_
            · refine pair_congr _ _ _ _ _ _ ?_ ?_
              · refine pSet_congr (O' := OFig) _ _ _ _ _ _ _ _ ?_ ?_ ?_
                · rfl
                · rfl
                · refine fst_congr _ _ _ _ ?_
                  refine snd_congr _ _ _ _ ?_
                  exact hout
              · refine mRecordE_congr (O' := OFig) _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
                · rfl
                · rfl
                · refine pair_congr _ _ _ _ _ _ ?_ ?_
                  · refine pair_congr _ _ _ _ _ _ ?_ ?_
                    · rfl
                    · refine pair_congr _ _ _ _ _ _ ?_ ?_
                      · refine pGet_congr (O' := OFig) _ _ _ _ _ _ ?_ ?_
                        · rfl
                        · rfl
                      · refine add_congr _ _ _ _ _ _ ?_ ?_
                        · refine pGet_congr (O' := OFig) _ _ _ _ _ _ ?_ ?_
                          · rfl
                          · rfl
                        · rfl
                  · refine pair_congr _ _ _ _ _ _ ?_ ?_
                    · exact hm2
                    · refine snd_congr _ _ _ _ ?_
                      refine snd_congr _ _ _ _ ?_
                      exact hout
                · rfl
            · rfl
  onDl_eval _ _ ρ Q c ex₀ _ harg hex := by
    unfold kemFailSemHook
    rw [map_smRrEnc_map_smRrDec]
    unfold kemFailHookC
    rw [comp_eval_ret, comp_eval_ret]
    refine congrArg pure ?_
    rw [letE_pair_fst_snd_eval, letE_eval _ _ ρ, expr_pair_eval, harg, hex]
    dsimp only [id]
    set X : (Ty.prod (.prod .bool (fig8CTy PQ PQC Pt ℓ)) (@kemExtraTy PQ PQC Pt ℓ)).denote :=
      ((partyEnc Q, c), ex₀)
    set ρ₀ := Env.cons X Env.nil
    rw [ite_eval _ _ _ (Env.cons X ρ), ite_eval _ _ _ (Env.cons X ρ₀)]
    have hwin :
        (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig)))))).eval (Env.cons X ρ) =
        (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig)))))).eval (Env.cons X ρ₀) := rfl
    rw [hwin]
    split_ifs
    · rfl
    · have hinT :
          (fgInTransitE P Dh encPt encT decT lam K toKemCoins L
            (fgMir (.fst (.snd .v0))) (otherE (.fst (.fst .v0))) (.snd (.fst .v0))).eval
            (Env.cons X ρ) =
          (fgInTransitE P Dh encPt encT decT lam K toKemCoins L
            (fgMir (.fst (.snd .v0))) (otherE (.fst (.fst .v0))) (.snd (.fst .v0))).eval
            (Env.cons X ρ₀) := by
        refine fgInTransitE_congr P Dh encPt encT decT lam K toKemCoins L _ _ _ _ _ _ _ _ ?_ ?_ ?_
        · rfl
        · rfl
        · rfl
      rw [expr_caseOpt_eval _ _ _ (Env.cons X ρ), expr_caseOpt_eval _ _ _ (Env.cons X ρ₀), hinT]
      rcases (fgInTransitE P Dh encPt encT decT lam K toKemCoins L
        (fgMir (.fst (.snd .v0))) (otherE (.fst (.fst .v0))) (.snd (.fst .v0))).eval
        (Env.cons X ρ₀) with _ | rec1
      · rfl
      · dsimp only []
        rw [expr_caseOpt_eval _ _ _ (Env.cons rec1 (Env.cons X ρ)),
          expr_caseOpt_eval _ _ _ (Env.cons rec1 (Env.cons X ρ₀))]
        have hst_get :
            (pGet (fgSt (.fst (.snd (Expr.v1 (O := OFig))))) (.fst (.fst .v1))).eval
              (Env.cons rec1 (Env.cons X ρ)) =
            (pGet (fgSt (.fst (.snd (Expr.v1 (O := OFig))))) (.fst (.fst .v1))).eval
              (Env.cons rec1 (Env.cons X ρ₀)) := by
          refine pGet_congr (O' := OFig) _ _ _ _ _ _ ?_ ?_
          · rfl
          · rfl
        have hrec :
            (Expr.op (O := OFig) (SimOp.fig8Receive B)
              (.pair (pGet (fgSt (.fst (.snd .v1))) (.fst (.fst .v1))) (.snd (.fst .v1)))).eval
              (Env.cons rec1 (Env.cons X ρ)) =
            (Expr.op (O := OFig) (SimOp.fig8Receive B)
              (.pair (pGet (fgSt (.fst (.snd .v1))) (.fst (.fst .v1))) (.snd (.fst .v1)))).eval
              (Env.cons rec1 (Env.cons X ρ₀)) :=
          congrArg ((OFig).eval (SimOp.fig8Receive B)) (congrArg₂ Prod.mk hst_get rfl)
        rw [hrec]
        rcases (Expr.op (O := OFig) (SimOp.fig8Receive B)
          (.pair (pGet (fgSt (.fst (.snd .v1))) (.fst (.fst .v1))) (.snd (.fst .v1)))).eval
          (Env.cons rec1 (Env.cons X ρ₀)) with _ | out2
        · rfl
        · dsimp only []
          simp only [expr_pair_eval, expr_some_eval, inr_eval]
          refine congrArg₂ Prod.mk
            (congrArg some (congrArg Sum.inr (congrArg₂ Prod.mk rfl (congrArg₂ Prod.mk rfl ?_))))
            (congrArg₂ Prod.mk (congrArg₂ Prod.mk ?_ ?_) rfl)
          · have hch :
                (mChallContainsE (O' := OFig) L (fgMir (.fst (.snd .v2))) (.fst .v1)).eval
                  (Env.cons out2 (Env.cons rec1 (Env.cons X ρ))) =
                (mChallContainsE (O' := OFig) L (fgMir (.fst (.snd .v2))) (.fst .v1)).eval
                  (Env.cons out2 (Env.cons rec1 (Env.cons X ρ₀))) := by
              refine mChallContainsE_congr (O' := OFig) L _ _ _ _ _ _ ?_ ?_
              · rfl
              · rfl
            rw [ite_eval _ _ _ (Env.cons out2 (Env.cons rec1 (Env.cons X ρ))),
              ite_eval _ _ _ (Env.cons out2 (Env.cons rec1 (Env.cons X ρ₀))), hch]
            rfl
          · refine pSet_congr (O' := OFig) _ _ _ _ _ _ _ _ ?_ ?_ ?_
            · rfl
            · rfl
            · rfl
          · refine mAcceptE_congr (O' := OFig) L _ _ _ _ _ _ _ _ ?_ ?_ ?_
            · rfl
            · rfl
            · rfl
  onIj_eval _ _ ρ Q c ex₀ _ harg hex := by
    unfold kemFailSemHook
    rw [map_smRrEnc_map_smRrDec]
    unfold kemFailHookC
    rw [comp_eval_ret, comp_eval_ret]
    refine congrArg pure ?_
    rw [letE_pair_fst_snd_eval, letE_eval _ _ ρ, expr_pair_eval, harg, hex]
    dsimp only [id]
    set X : (Ty.prod (.prod .bool (fig8CTy PQ PQC Pt ℓ)) (@kemExtraTy PQ PQC Pt ℓ)).denote :=
      ((partyEnc Q, c), ex₀)
    set ρ₀ := Env.cons X Env.nil
    have hinT :
        (fgInTransitE P Dh encPt encT decT lam K toKemCoins L
          (fgMir (.fst (.snd .v0))) (otherE (.fst (.fst .v0))) (.snd (.fst .v0))).eval
          (Env.cons X ρ) =
        (fgInTransitE P Dh encPt encT decT lam K toKemCoins L
          (fgMir (.fst (.snd .v0))) (otherE (.fst (.fst .v0))) (.snd (.fst .v0))).eval
          (Env.cons X ρ₀) := by
      refine fgInTransitE_congr P Dh encPt encT decT lam K toKemCoins L _ _ _ _ _ _ _ _ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
    have hsi :
        (mSafeInjE (fgMir (.fst (.snd (Expr.v0 (O := OFig)))))).eval (Env.cons X ρ) =
        (mSafeInjE (fgMir (.fst (.snd (Expr.v0 (O := OFig)))))).eval (Env.cons X ρ₀) := by
      refine mSafeInjE_congr (O' := OFig) _ _ _ _ ?_
      rfl
    have href :
        (orE (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig))))))
          (orE (isSomeE (fgInTransitE P Dh encPt encT decT lam K toKemCoins L
              (fgMir (.fst (.snd .v0))) (otherE (.fst (.fst .v0))) (.snd (.fst .v0))))
            (.not (mSafeInjE (fgMir (.fst (.snd .v0))))))).eval (Env.cons X ρ) =
        (orE (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig))))))
          (orE (isSomeE (fgInTransitE P Dh encPt encT decT lam K toKemCoins L
              (fgMir (.fst (.snd .v0))) (otherE (.fst (.fst .v0))) (.snd (.fst .v0))))
            (.not (mSafeInjE (fgMir (.fst (.snd .v0))))))).eval (Env.cons X ρ₀) := by
      simp only [orE_eval, isSomeE_eval, Expr.eval, hinT, hsi]
      rfl
    rw [ite_eval _ _ _ (Env.cons X ρ), ite_eval _ _ _ (Env.cons X ρ₀), href]
    split_ifs
    · rfl
    · rw [expr_caseOpt_eval _ _ _ (Env.cons X ρ), expr_caseOpt_eval _ _ _ (Env.cons X ρ₀)]
      have hst_get :
          (pGet (fgSt (.fst (.snd (Expr.v0 (O := OFig))))) (.fst (.fst .v0))).eval
            (Env.cons X ρ) =
          (pGet (fgSt (.fst (.snd (Expr.v0 (O := OFig))))) (.fst (.fst .v0))).eval
            (Env.cons X ρ₀) := by
        refine pGet_congr (O' := OFig) _ _ _ _ _ _ ?_ ?_
        · rfl
        · rfl
      have hrec :
          (Expr.op (O := OFig) (SimOp.fig8Receive B)
            (.pair (pGet (fgSt (.fst (.snd .v0))) (.fst (.fst .v0))) (.snd (.fst .v0)))).eval
            (Env.cons X ρ) =
          (Expr.op (O := OFig) (SimOp.fig8Receive B)
            (.pair (pGet (fgSt (.fst (.snd .v0))) (.fst (.fst .v0))) (.snd (.fst .v0)))).eval
            (Env.cons X ρ₀) :=
        congrArg ((OFig).eval (SimOp.fig8Receive B)) (congrArg₂ Prod.mk hst_get rfl)
      rw [hrec]
      rcases (Expr.op (O := OFig) (SimOp.fig8Receive B)
        (.pair (pGet (fgSt (.fst (.snd .v0))) (.fst (.fst .v0))) (.snd (.fst .v0)))).eval
        (Env.cons X ρ₀) with _ | out1
      · rfl
      · dsimp only []
        rw [ite_eval _ _ _ (Env.cons out1 (Env.cons X ρ)),
          ite_eval _ _ _ (Env.cons out1 (Env.cons X ρ₀))]
        have hlt :
            (Expr.lt (.nat (qep + 2)) (.fst (.snd (Expr.v0 (O := OFig))))).eval
              (Env.cons out1 (Env.cons X ρ)) =
            (Expr.lt (.nat (qep + 2)) (.fst (.snd (Expr.v0 (O := OFig))))).eval
              (Env.cons out1 (Env.cons X ρ₀)) := rfl
        rw [hlt]
        split_ifs
        · rfl
        · have htriv :
              (mTrivialE (O' := OFig) L (fgMir (.fst (.snd .v1)))
                (.pair (otherE (.fst (.fst .v1)))
                  (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).eval
                (Env.cons out1 (Env.cons X ρ)) =
              (mTrivialE (O' := OFig) L (fgMir (.fst (.snd .v1)))
                (.pair (otherE (.fst (.fst .v1)))
                  (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).eval
                (Env.cons out1 (Env.cons X ρ₀)) := by
            refine mTrivialE_congr (O' := OFig) L _ _ _ _ _ _ ?_ ?_
            · rfl
            · rfl
          rw [ite_eval _ _ _ (Env.cons out1 (Env.cons X ρ)),
            ite_eval _ _ _ (Env.cons out1 (Env.cons X ρ₀)), htriv]
          split_ifs
          · simp only [expr_pair_eval, expr_some_eval, inr_eval]
            refine congrArg₂ Prod.mk rfl (congrArg₂ Prod.mk (congrArg₂ Prod.mk ?_ ?_) rfl)
            · refine pSet_congr (O' := OFig) _ _ _ _ _ _ _ _ ?_ ?_ ?_
              · rfl
              · rfl
              · rfl
            · refine mAcceptE_congr (O' := OFig) L _ _ _ _ _ _ _ _ ?_ ?_ ?_
              · rfl
              · rfl
              · rfl
          · refine pair_congr _ _ _ _ _ _ ?_ ?_
            · rfl
            · refine pair_congr _ _ _ _ _ _ ?_ ?_
              · refine pair_congr _ _ _ _ _ _ ?_ ?_
                · rfl
                · refine mSetWin_congr (O' := OFig) _ _ _ _ _ _ ?_ ?_
                  · rfl
                  · rfl
              · rfl
  onCr_eval _ _ ρ Q ex₀ _ hq hex := by
    unfold kemFailSemHook kemFailHookC
    simp only [Prod.map_id, id_map]
    rw [comp_eval_ret, comp_eval_ret]
    refine congrArg pure ?_
    rw [letE_pair_fst_snd_eval, letE_eval _ _ ρ, expr_pair_eval, hq, hex]
    dsimp only [id]
    set X : (Ty.prod .bool (@kemExtraTy PQ PQC Pt ℓ)).denote := (partyEnc Q, ex₀)
    set ρ₀ := Env.cons X Env.nil
    have hca :
        (mCorrAllowedE (O' := OFig) L (fgMir (.fst (.snd .v0))) (.fst .v0)).eval
          (Env.cons X ρ) =
        (mCorrAllowedE (O' := OFig) L (fgMir (.fst (.snd .v0))) (.fst .v0)).eval
          (Env.cons X ρ₀) := by
      refine mCorrAllowedE_congr (O' := OFig) L _ _ _ _ _ _ ?_ ?_
      · rfl
      · rfl
    have href :
        (orE (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig))))))
          (.not (mCorrAllowedE L (fgMir (.fst (.snd .v0))) (.fst .v0)))).eval
          (Env.cons X ρ) =
        (orE (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig))))))
          (.not (mCorrAllowedE L (fgMir (.fst (.snd .v0))) (.fst .v0)))).eval
          (Env.cons X ρ₀) := by
      simp only [orE_eval, Expr.eval, hca]
      rfl
    rw [ite_eval _ _ _ (Env.cons X ρ), ite_eval _ _ _ (Env.cons X ρ₀), href]
    split_ifs
    · rfl
    · refine pair_congr _ _ _ _ _ _ ?_ ?_
      · refine some_congr _ _ _ _ ?_
        refine pGet_congr (O' := OFig) _ _ _ _ _ _ ?_ ?_
        · rfl
        · rfl
      · refine pair_congr _ _ _ _ _ _ ?_ ?_
        · refine pair_congr _ _ _ _ _ _ ?_ ?_
          · rfl
          · refine mAfterCorrE_congr (O' := OFig) L _ _ _ _ _ _ ?_ ?_
            · rfl
            · rfl
        · rfl
  onProbe_eval _ _ _ _ _ _ _ _ hex := by
    simp [kemFailHookC, kemFailSemHook, Comp.eval, hex]
  onDeliverPost_eval _ j? _ _ ρ Q rr ex₀ hq hres hex := by
    unfold kemFailSemHook kemFailHookC
    simp only [id_map]
    rw [comp_eval_ret, comp_eval_ret]
    refine congrArg pure ?_
    rw [letE_quad_eval, letE_eval _ _ ρ,
      expr_pair_eval, expr_pair_eval, expr_pair_eval, hq, hres, hex]
    dsimp only [id]
    rcases rr with _ | (_ | rd)
    · rfl
    · rfl
    · rcases j?.eval ρ with _ | j
      · rfl
      · refine congrArg₂ Prod.mk rfl (congrArg₂ Prod.mk ?_ rfl)
        exact congrArg ((OFig).eval SimOp.stepKemFailDeliver) rfl
  onDeliverPost_congr _ j? res _ ρ₁ ρ₂ hq hj hres hex := by
    unfold kemFailHookC
    rw [comp_eval_ret, comp_eval_ret]
    refine congrArg pure ?_
    rw [letE_eval _ _ ρ₁, letE_eval _ _ ρ₂,
      expr_pair_eval, expr_pair_eval, expr_pair_eval,
      expr_pair_eval, expr_pair_eval, expr_pair_eval, hq, hj, hres, hex]
    rcases res.eval ρ₂ with _ | (_ | rd)
    · rfl
    · rfl
    · rcases j?.eval ρ₂ with _ | j
      · rfl
      · refine congrArg₂ Prod.mk rfl (congrArg₂ Prod.mk ?_ rfl)
        exact congrArg ((OFig).eval SimOp.stepKemFailDeliver) rfl

theorem kemFailSemHookInv (L qep B : ℕ) :
    SemHookInv (PQC := PQC) (Pt := Pt) (ℓ := ℓ)
      (fun _ (_ : KemExtraRaw PQ PQC Pt ℓ) => True)
      (fun _ _ (_ : KemExtraRaw PQ PQC Pt ℓ) => True) L
      (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B) where
  mono _ _ := trivial
  toBound _ := trivial
  onSendCoins_inv _ _ _ := ⟨trivial, trivial⟩
  onTr_inv _ _ _ := trivial
  onCh_inv _ _ _ := trivial
  onDl_inv _ _ _ := trivial
  onIj_inv _ _ _ := trivial
  onCr_inv _ _ _ := trivial
  onProbe_inv _ _ _ := trivial
  onDeliverPost_inv _ _ _ := trivial

def kemFailOracle (L qep B : ℕ) :
    QueryImpl (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemExtraRaw PQ PQC Pt ℓ) (OracleComp unifSpec))
  | .inl n => StateT.lift (query (spec := unifSpec) n)
  | .inr t => StateT.mk fun ⟨sC, ex⟩ =>
    semHandleHook P Dh encPt encT decT lam
      (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B) qep B t sC ex

def kemFailOracleDedup (L qep B : ℕ) :
    QueryImpl (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemExtraRaw PQ PQC Pt ℓ) (OracleComp unifSpec))
  | .inl n => StateT.lift (query (spec := unifSpec) n)
  | .inr t => StateT.mk fun ⟨sC, ex⟩ =>
    semHandleHookDedup P Dh encPt encT decT lam
      (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B) qep B t sC ex

private theorem map_run_simulateQ_kemFailOracleDedup_eq (L qep B : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (st : LibsignalToModularSchemeSimState PQ Pt ℓ × KemExtraRaw PQ PQC Pt ℓ) :
    ((simulateQ (kemFailOracleDedup P Dh encPt encT decT lam K toKemCoins L qep B) A).run st >>=
      fun x => pure x.2.2.2.2) =
    ((simulateQ (kemFailOracle P Dh encPt encT decT lam K toKemCoins L qep B) A).run st >>=
      fun x => pure x.2.2.2.2) := by
  have h := congrArg
    (Functor.map
      (fun x : Bool × (LibsignalToModularSchemeSimState PQ Pt ℓ × KemExtraRaw PQ PQC Pt ℓ) =>
        x.2.2.2.2))
    (map_run_simulateQ_eq_of_idem_proj
      (kemFailOracleDedup P Dh encPt encT decT lam K toKemCoins L qep B)
      (kemFailOracle P Dh encPt encT decT lam K toKemCoins L qep B)
      (Prod.map simStateCCanon id) ?_ ?_ A (s₁ := st) (s₂ := st) rfl)
  · simp only [Functor.map_map, Prod.map, id_eq] at h
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using h
  · rintro (n | t) ⟨sC, ex⟩
    · simp [kemFailOracleDedup, kemFailOracle, StateT.run_lift, Prod.map, simStateCCanon_idem]
    · exact semHandleHookDedup_simStateCCanon P Dh encPt encT decT lam
        (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B) qep B t sC ex
  · rintro (n | t) ⟨sC, ex⟩
    · simp [kemFailOracle, StateT.run_lift, Prod.map, simStateCCanon_idem]
    · exact semHandleHook_simStateCCanon P Dh encPt encT decT lam
        (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B) qep B t sC ex

/-- `B`-clamped semantic counterpart of `redKemFailHiddenSalt` matching `kemFailRedProg`. -/
def redKemFailHiddenSaltClamp (L qep B : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    OracleComp unifSpec (SimKemSeed × SimKemEncRand) := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
  let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
  let pqrKey ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
  let sC₀ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
  let gFig₀ : (@fig8GsTy PQ PQC Pt ℓ).denote :=
    ((OFig).eval SimOp.fig8Init (k1, k2),
     (b, false, (0, 0), (0, 0), none, [], [], [], (fun _ => 0, fun _ => 0), [], []))
  let trCand₀ := (OFig).eval SimOp.initKemFailTrack pqrKey
  let (_, (_, exFinal)) ←
    (simulateQ (kemFailOracle P Dh encPt encT decT lam K toKemCoins L qep B) A).run
      (sC₀, (gFig₀, trCand₀))
  return exFinal.2.2

private theorem kemFailRedProg_init_eval (L qep B : ℕ) :
    (kemFailRedProg (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).init.eval
      (Env.cons () Env.nil) =
    (do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      let pqrKey ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      let gFig₀ : (@fig8GsTy PQ PQC Pt ℓ).denote :=
        ((OFig).eval SimOp.fig8Init (k1, k2),
         (b, false, (0, 0), (0, 0), none, [], [], [], (fun _ => 0, fun _ => 0), [], []))
      let trCand₀ := (OFig).eval SimOp.initKemFailTrack pqrKey
      return ((), ((initSimCE P Dh encPt encT decT lam K toKemCoins
        (Γ := [.base SimSort.bv256, .base SimSort.bv256, .base SimSort.bv256, .bool, .unit])
        .v0).eval
        (Env.cons (t := (.base SimSort.bv256 : Ty S)) pqrKey
          (Env.cons (t := (.base SimSort.bv256 : Ty S)) k2
            (Env.cons (t := (.base SimSort.bv256 : Ty S)) k1
              (Env.cons (t := (.bool : Ty S)) b
                (Env.cons (t := (.unit : Ty S)) () Env.nil))))),
        (gFig₀, trCand₀)))) := rfl

/-- Evaluation agreement between `kemFailRedProg` and `redKemFailHiddenSaltClamp` for `q ≤ L` game queries. -/
theorem kemFailRedProg_eval (L qep B : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (q : ℕ) (hq : SM.MakesAtMostQueries A q) (hqL : q ≤ L) :
    (kemFailRedProg P Dh encPt encT decT lam K toKemCoins L qep B).eval (fun _ => A) () =
      redKemFailHiddenSaltClamp P Dh encPt encT decT lam K toKemCoins L qep B A := by
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  let prog := kemFailRedProg (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B
  let initSem : OracleComp unifSpec (Unit × (LibsignalToModularSchemeSimState PQ Pt ℓ × KemExtraRaw PQ PQC Pt ℓ)) := do
    let b ← ($ᵗ Bool : ProbComp Bool)
    let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
    let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
    let pqrKey ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
    let sC₀ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    let gFig₀ : (@fig8GsTy PQ PQC Pt ℓ).denote :=
      ((OFig).eval SimOp.fig8Init (k1, k2),
       (b, false, (0, 0), (0, 0), none, [], [], [], (fun _ => 0, fun _ => 0), [], []))
    let trCand₀ := (OFig).eval SimOp.initKemFailTrack pqrKey
    return ((), (sC₀, (gFig₀, trCand₀)))
  have hinit_eval :
      Prod.map id (Prod.map (simStateCDec (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) id) <$>
        prog.init.eval (Env.cons () Env.nil) = initSem := by
    rw [show prog.init = (kemFailRedProg (ℓ := ℓ) P Dh encPt encT decT lam K
      toKemCoins L qep B).init from rfl, kemFailRedProg_init_eval]
    dsimp only [initSem]
    rw [map_bind]; refine bind_congr fun b => ?_
    rw [map_bind]; refine bind_congr fun k1 => ?_
    rw [map_bind]; refine bind_congr fun k2 => ?_
    rw [map_bind]; refine bind_congr fun pqrKey => ?_
    rw [map_pure]
    simp only [Prod.map, id_eq, initSimCE_eval, Expr.eval, Expr.v0, Env.get_cons_zero]
  have hinit_inv :
      ∀ r ∈ support (prog.init.eval (Env.cons () Env.nil)),
        SimHookRawInv (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)
          id (fun _ _ (_ : KemExtraRaw PQ PQC Pt ℓ) => True) L q r.2 := by
    rintro ⟨u₀, sC_raw, ex_raw⟩ hr
    rw [show prog.init = (kemFailRedProg (ℓ := ℓ) P Dh encPt encT decT lam K
      toKemCoins L qep B).init from rfl, kemFailRedProg_init_eval,
      mem_support_bind_iff] at hr
    obtain ⟨b, -, hr⟩ := hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨k1, -, hr⟩ := hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨k2, -, hr⟩ := hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨pqrKey, -, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    simp only [Prod.mk.injEq] at hr
    rcases hr with ⟨_, rfl, rfl⟩
    refine ⟨?_, _, rfl, trivial⟩
    rw [initSimCE_eval]
    refine ⟨?_, by simp [initSimC, hqL], by simp [initSimC, hqL]⟩
    simp only [SimStateInv, initSimC, initSim, List.length_nil, zero_add]
    exact ⟨hqL, hqL, hqL, ⟨[], by simp [hqL], countLe_nil [], fun _ h => nomatch h⟩,
      by decide, by decide⟩
  have h1 := prog.eval_eq_simulateQ_of_abs
    (Prod.map (simStateCDec (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) id)
    (SimHookRawInv (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)
      id (fun _ _ (_ : KemExtraRaw PQ PQC Pt ℓ) => True) L)
    (fun _ => initSem)
    (kemFailOracleDedup P Dh encPt encT decT lam K toKemCoins L qep B)
    (fun s _ => pure s.2.2.2)
    q ()
    hinit_eval hinit_inv
    (fun n s => rfl)
    (fun m t v hv =>
      simHandleHookC_step P Dh encPt encT decT lam K toKemCoins (fun _ => rfl)
        (kemFailHookMatch P Dh encPt encT decT lam K toKemCoins L qep B)
        (kemFailSemHookInv P Dh encPt encT decT lam K toKemCoins L qep B) qep B m t v hv)
    (fun s b' _ => rfl)
    (fun _ hle hv => hv.mono (kemFailSemHookInv P Dh encPt encT decT lam K toKemCoins L qep B) hle)
    (fun _ => A) (fun _ => hq')
  rw [h1]
  unfold redKemFailHiddenSaltClamp
  simp only [initSem, bind_assoc, pure_bind]
  refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => ?_
  exact map_run_simulateQ_kemFailOracleDedup_eq P Dh encPt encT decT lam K toKemCoins L qep B A _

def runDFM {α : Type}
    (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ)
      (CryptoGames.LibsignalSM.Proofs.Refinement.DeliverForgeM Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) :
    SM.Construction.DeliverForge.AdversaryCompDF
      (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)
      (α × (LibsignalToModularSchemeSimState PQ Pt ℓ × List (SimFig8C Pt))) := do
  let ((a, sC'), ex') ← (x.run sC).run ex
  return (a, (sC', ex'))

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem simParseRecvC_bounds (qB : Bool) (pq : PQ) (w : List (BitVec 8))
    {pq' : PQ} {i : ℕ} {pk : PublicKey} {T? : Option Pt} {lct : ℕ × LibsignalCiphertextWithSalt32}
    (hp : simParseRecvC P decT (2 ^ 32) qB pq w = some (pq', (i, (pk, (T?, lct))))) :
    i = lct.1 ∧ lct.1 ≤ 2 ^ 32 := by
  unfold simParseRecvC at hp
  split_ifs at hp
  dsimp only [] at hp
  rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, _⟩
  · rw [hparse] at hp; cases hp
  · rw [hparse] at hp; dsimp only [] at hp
    split_ifs at hp
    rcases hspqr : P.spqr.recv pq h.pqRatchet with _ | ⟨pq1, salt⟩
    · rw [hspqr] at hp; cases hp
    · rw [hspqr] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      rcases hp with ⟨_, hi, _, _, hlct⟩
      have hlt : h.counter.toNat < 2 ^ 32 := h.counter.isLt
      rw [← hlct]
      exact ⟨hi.symm.trans (Nat.min_eq_left (by omega)), by omega⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem fig8ToDFImpl_liftM_probComp {α : Type} (p : ProbComp α)
    (ex : List (SimFig8C Pt)) :
    (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl Pt ℓ)
      (liftM p : OracleComp
        (unifSpec + SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) α)).run ex =
      ((liftM p : SM.Construction.DeliverForge.AdversaryCompDF
          (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α) >>=
        fun a => pure (a, ex)) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t mx ih =>
    change (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl Pt ℓ)
      (query (spec := unifSpec +
        SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) (.inl t) >>=
        fun u => liftM (mx u))).run ex =
      ((query (spec := unifSpec +
          SM.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) (.inl t) >>=
          fun u => liftM (mx u)) >>=
        fun a => pure (a, ex))
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    change (StateT.lift (query (spec := unifSpec +
        SM.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) (.inl t)) >>=
      fun u => simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl Pt ℓ)
        (liftM (mx u))).run ex = _
    simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
    exact bind_congr fun u => ih u

omit [Zero Pt] in
private theorem fig8ToDFImpl_transmitQuery (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ)
    (rc : Option (BitVec 256)) (ex : List (SimFig8C Pt)) :
    (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl Pt ℓ)
      (SM.transmitQuery Q m rc)).run ex =
      (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onTr Q m rc ex := by
  simp only [SM.transmitQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl,
    deliverForgeSemHook, StateT.run_bind, stateT_lift_run, pure_bind, bind_assoc]
  refine bind_congr fun res => ?_
  cases res <;> rfl

omit [Zero Pt] in
private theorem fig8ToDFImpl_challQuery (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ)
    (rc : Option (BitVec 256)) (ex : List (SimFig8C Pt)) :
    (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl Pt ℓ)
      (SM.challQuery Q m₀ m₁ rc)).run ex =
      (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onCh Q m₀ m₁ rc ex := by
  simp only [SM.challQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl,
    deliverForgeSemHook, StateT.run_bind, stateT_lift_run, pure_bind, bind_assoc]
  refine bind_congr fun res => ?_
  cases res <;> rfl

omit [Zero Pt] in
private theorem fig8ToDFImpl_deliverQuery (Q : Party) (c : SimFig8C Pt)
    (ex : List (SimFig8C Pt)) :
    (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl Pt ℓ)
      (SM.deliverQuery Q c)).run ex =
      (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onDl Q c ex := by
  simp only [SM.deliverQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  rfl

omit [Zero Pt] in
private theorem fig8ToDFImpl_injectQuery (Q : Party) (c : SimFig8C Pt)
    (ex : List (SimFig8C Pt)) :
    (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl Pt ℓ)
      (SM.injectQuery Q c)).run ex =
      (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onIj Q c ex := by
  simp only [SM.injectQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  rfl

omit [Zero Pt] in
private theorem fig8ToDFImpl_corrQuery (Q : Party) (ex : List (SimFig8C Pt)) :
    (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl Pt ℓ)
      (SM.corrQuery Q)).run ex =
      (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onCr Q ex := by
  simp only [SM.corrQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  rfl

omit [Zero Pt] [SampleableType PQC] in
@[simp] private theorem zoomB_deliverForge_run {α : Type}
    (x : StateT (SimState PQ Pt ℓ)
      (OracleComp (unifSpec +
        SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (runOnBaseState (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ) x).run sC =
      (do
        let (a, s') ← simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl Pt ℓ)
          (x.run sC.base)
        return (a, { sC with base := s' })) := rfl

omit [Zero Pt] [SampleableType PQC] in
@[simp] private theorem liftC_deliverForge_run {α : Type}
    (x : OracleComp (unifSpec +
      SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (LibsignalSimC.liftC (PQ := PQ) (Pt := Pt) (ℓ := ℓ)
      (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ) x).run sC =
      (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl Pt ℓ) x >>=
        fun a => pure (a, sC)) := rfl

private abbrev DFM (PQ Pt : Type) (ℓ : ℕ) :=
  StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (CryptoGames.LibsignalSM.Proofs.Refinement.DeliverForgeM Pt ℓ)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem runDFM_pure {α : Type} (a : α) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (SimFig8C Pt)) :
    runDFM (pure a) sC ex = pure (a, (sC, ex)) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem runDFM_guardC_neg {α : Type} (x : DFM PQ Pt ℓ (Option α))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt))
    (h : ¬sC.base.stopped = true) :
    runDFM (LibsignalSimC.guardC x) sC ex = runDFM x sC ex := by
  unfold runDFM LibsignalSimC.guardC
  simp [h]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem runDFM_get_bind {α : Type} (f : LibsignalToModularSchemeSimState PQ Pt ℓ → DFM PQ Pt ℓ α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) :
    runDFM (get >>= f) sC ex = runDFM (f sC) sC ex := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem runDFM_ite_modify {α : Type} (c : Bool) (k : DFM PQ Pt ℓ α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) :
    runDFM (if c then
        (modify (fun sC : LibsignalToModularSchemeSimState PQ Pt ℓ =>
          { sC with base := { sC.base with amb := sC.base.amb + 1 } }) >>= fun _ => k)
      else k) sC ex =
      runDFM k { sC with base := if c then { sC.base with amb := sC.base.amb + 1 } else sC.base }
        ex := by
  cases c <;> rfl

theorem semSendHook_deliverForge_eq (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    semSendHook P Dh encPt encT lam deliverForgeSemHook qep sC ex Q m₀ chal r =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      runDFM (LibsignalSimC.guardC (LibsignalSimC.simSendC (P := P) (qep := qep) (fig := fig)
        (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ) Q m₀ chal r))
        sC ex := by
  dsimp only []
  by_cases hstop : sC.base.stopped = true
  · unfold semSendHook runDFM LibsignalSimC.guardC; simp [hstop]
  · rw [runDFM_guardC_neg _ sC ex hstop]
    unfold semSendHook runDFM LibsignalSimC.simSendC simSend
      semDrawSendCoins coin liftQ scPostSendPure putS
    simp only [hstop, Bool.false_or, StateT.run_bind, StateT.run_get,
      zoomB_deliverForge_run, pure_bind, bind_assoc]
    by_cases href : (sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) = true
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte]
      rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
      · simp
      · dsimp only []
        by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
        · simp [hch]
        · simp only [hch, Bool.false_eq_true, ↓reduceIte]
          have hsc : (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onSendCoins =
              fun _ _ ex => pure (ex, ex) := rfl
          have hbv : (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).sampleBv256 =
              liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) := rfl
          have hpqc : (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).samplePqc =
              liftM ($ᵗ PQC : ProbComp PQC) := rfl
          rw [hsc, hbv, hpqc]
          rcases r with _ | rq
          · simp only [StateT.run_bind, stateT_lift_run,
              simulateQ_bind, fig8ToDFImpl_liftM_probComp, pure_bind, bind_assoc]
            refine bind_congr fun x => ?_
            rcases hpub : mkPub (P := P) sC.base Q x
              (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
               else sC.base.pn Q) with _ | ⟨pq', pub⟩
            · simp
            · dsimp only []
              cases chal <;> simp only [StateT.run_bind, stateT_lift_run, simulateQ_bind,
                fig8ToDFImpl_transmitQuery (PQC := PQC), fig8ToDFImpl_challQuery (PQC := PQC),
                deliverForgeSemHook, pure_bind, bind_assoc]
              all_goals
                refine bind_congr fun res => ?_
                rcases res with _ | c
                · simp
                · rcases hkept : (sC.kept Q).full with _ | st
                  · simp [hkept]
                  · simp [hkept]; rfl
          · simp only [bind_map_left, StateT.run_bind, stateT_lift_run,
              simulateQ_bind, fig8ToDFImpl_liftM_probComp, pure_bind, bind_assoc]
            refine bind_congr fun x => ?_
            rcases hpub : mkPub (P := P) sC.base Q rq
              (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
               else sC.base.pn Q) with _ | ⟨pq', pub⟩
            · simp
            · dsimp only []
              cases chal <;> simp only [StateT.run_bind, stateT_lift_run, simulateQ_bind,
                fig8ToDFImpl_transmitQuery (PQC := PQC), fig8ToDFImpl_challQuery (PQC := PQC),
                deliverForgeSemHook, pure_bind, bind_assoc]
              all_goals
                refine bind_congr fun res => ?_
                rcases res with _ | c
                · simp
                · rcases hkept : (sC.kept Q).full with _ | st
                  · simp [hkept]
                  · simp [hkept]; rfl

omit [Zero Pt] in
theorem semCorrHook_deliverForge_eq
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) (Q : Party) :
    semCorrHook P Dh encT deliverForgeSemHook sC ex Q =
      runDFM (LibsignalSimC.guardC (LibsignalSimC.simCorrC (P := P) (encT := encT)
        (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ) Dh Q))
        sC ex := by
  by_cases hstop : sC.base.stopped = true
  · unfold semCorrHook runDFM LibsignalSimC.guardC; simp [hstop]
  · rw [runDFM_guardC_neg _ sC ex hstop]
    unfold semCorrHook LibsignalSimC.simCorrC
    rw [runDFM_get_bind]
    have hcond : (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
        inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) =
      (sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
        inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) := by
      simp [hstop]
    rw [hcond]
    by_cases href : (sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
        inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
    · simp [href, runDFM_pure]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, runDFM,
        StateT.run_bind, liftC_deliverForge_run,
        fig8ToDFImpl_corrQuery (PQC := PQC), pure_bind, bind_assoc]
      refine bind_congr fun ⟨res, ex₁⟩ => ?_
      rcases res with _ | fig8st
      · simp
      · rcases fig8st.γ with _ | x <;> rfl

theorem semFwdAnswerHook_deliverForge_eq (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    semFwdAnswerHook P Dh encPt encT lam deliverForgeSemHook qep sC ex Q w isDel ci? Tpk pq' c' =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runDFM (fwdAnswerC (qep := qep) (fig := fig) (fs := fs)
        (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ)
        Q w isDel ci? Tpk pq' c') sC ex := by
  unfold semFwdAnswerHook runDFM fwdAnswerC
  simp only [StateT.run_bind, zoomB_deliverForge_run, fwd_run_eq, bind_assoc]
  split_ifs <;>
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      fig8ToDFImpl_deliverQuery (PQC := PQC), fig8ToDFImpl_injectQuery (PQC := PQC),
      pure_bind, bind_assoc] <;>
    (refine bind_congr fun ⟨res, ex₁⟩ => ?_;
     rcases res with _ | (_ | ⟨t, i, pm⟩) <;> simp [onAnswer_run_eq_pure])

theorem semResyncHook_deliverForge_eq (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt))
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    semResyncHook P Dh encPt encT lam deliverForgeSemHook qep sC ex Q w ci? Tpk pq' c r =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runDFM (resyncC (qep := qep) (fig := fig) (fs := fs)
        (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ)
        Q w ci? Tpk pq' c r) sC ex := by
  unfold semResyncHook runDFM resyncC
  rcases r with _ | ⟨t, i, ⟨pub, m'⟩⟩
  · simp
  · simp only [StateT.run_bind, liftC_deliverForge_run,
      fig8ToDFImpl_deliverQuery (PQC := PQC), pure_bind, bind_assoc]
    refine bind_congr fun ⟨res, ex₁⟩ => ?_
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp [zoomB_deliverForge_run, onAccept_run_eq_pure]

theorem semFwdEvictHook_deliverForge_eq (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    semFwdEvictHook P Dh encPt encT lam deliverForgeSemHook qep sC ex Q w isDel Tpk pq' c' =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runDFM (fwdEvictC (qep := qep) (fig := fig) (fs := fs)
        (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ)
        Q w isDel Tpk pq' c') sC ex := by
  unfold semFwdEvictHook fwdEvictC
  by_cases h : (isDel && !(sC.base.mir.safeInj 3)) = true
  · simp only [h, ↓reduceIte, runDFM, deliverForgeSemHook,
      CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook,
      StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_lift,
      pure_bind, bind_assoc]
    rcases ex.find? (fun c => CryptoGames.LibsignalSM.Proofs.Refinement.sameWireFig8 c c') with
      _ | c <;> simp
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rw [semFwdAnswerHook_deliverForge_eq]
    simp only [runDFM, StateT.run_bind, StateT.run_get, pure_bind, h, Bool.false_eq_true,
      ↓reduceIte]

theorem semFwdHook_deliverForge_eq (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hc' : ∀ c, honestC = some c → c ≠ c' → c'.1.1 ≤ B ∧ c'.2.1 ≤ B) :
    semFwdHook P Dh encPt encT lam deliverForgeSemHook qep B sC ex Q w isDel ci? Tpk pq'
      honestC c' =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runDFM (LibsignalSimC.fwdC (P := P) (qep := qep) (fig := fig) (fs := fs)
        (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ)
        Q w isDel ci? Tpk pq' honestC c') sC ex := by
  unfold semFwdHook LibsignalSimC.fwdC
  rcases honestC with _ | c
  · dsimp only []
    rw [semFwdAnswerHook_deliverForge_eq]
    simp [runDFM]
  · dsimp only []
    have hcond : (!(decide (c = c')) && (isDel && !(sC.base.mir.safeInj 3))) =
        (decide (c ≠ c') && isDel && !(sC.base.mir.safeInj 3)) := by
      rw [decide_not, Bool.and_assoc]
    rw [hcond]
    by_cases h : (decide (c ≠ c') && isDel && !(sC.base.mir.safeInj 3)) = true
    · have hne : c ≠ c' := of_decide_eq_true (by revert h; cases decide (c ≠ c') <;> simp)
      obtain ⟨ht, hi⟩ := hc' c rfl hne
      simp only [h, ↓reduceIte, evalCKClamp_eq_evalCK P Dh encPt encT lam B sC Q w c c' ht hi]
      rcases heval : predictReceiveWithSnapshots
          (fig := lFig8 Dh encPt P.C P.codec ℓ encT
            (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
          (fs := lFS P.C P.codec ℓ encT
            (fun R => if R == Party.A then P.idA else P.idB) 25000)
          P sC Q w c c' with _ | r
      · simp only [runDFM, deliverForgeSemHook,
          CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook,
          StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_lift,
          pure_bind, bind_assoc, h, ↓reduceIte, heval]
        rcases ex.find? (fun c => CryptoGames.LibsignalSM.Proofs.Refinement.sameWireFig8 c c') with
          _ | c₀ <;> simp
      · dsimp only []
        rw [semResyncHook_deliverForge_eq]
        simp only [runDFM, StateT.run_bind, StateT.run_get, pure_bind, h, ↓reduceIte, heval]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [semFwdAnswerHook_deliverForge_eq]
      simp only [runDFM, StateT.run_bind, StateT.run_get, pure_bind, h, Bool.false_eq_true,
        ↓reduceIte]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem getD_chains_epoch_le (cs : List GhostChain) (ci B : ℕ)
    (hch : ∀ g ∈ cs, g.epoch ≤ B) :
    (cs.getD ci ⟨none, 0, 0, []⟩).epoch ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : cs[ci]? with _ | g
  · exact Nat.zero_le B
  · exact hch g (List.mem_of_getElem? h)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem rejects_eq_false_le (g : GhostChain) (i : ℕ) (h : g.rejects i = false) :
    i ≤ g.last + 25001 := by
  unfold GhostChain.rejects at h
  split_ifs at h with hle
  · omega
  · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem getD_chains_last_le (cs : List GhostChain) (ci B : ℕ) (hB : 25001 ≤ B)
    (hch : ∀ g ∈ cs, g.last + 25001 ≤ B) :
    (cs.getD ci ⟨none, 0, 0, []⟩).last + 25001 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : cs[ci]? with _ | g
  · exact hB
  · exact hch g (List.mem_of_getElem? h)

theorem semRecvHook_deliverForge_eq (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (hB : 25001 ≤ B)
    (hep : sC.base.mir.epoch Q + 1 ≤ B)
    (hch : ∀ g ∈ sC.base.chains Q, g.epoch ≤ B)
    (hlast : 2 ^ 32 ≤ B ∨ ∀ g ∈ sC.base.chains Q, g.last + 25001 ≤ B) :
    semRecvHook P Dh encPt encT decT lam deliverForgeSemHook qep B sC ex Q w isDel =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runDFM (LibsignalSimC.guardC (LibsignalSimC.simRecvC (P := P) (encT := encT) (decT := decT)
        (qep := qep) (fig := fig) (fs := fs)
        (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ)
        Q w isDel)) sC ex := by
  dsimp only []
  by_cases hstop : sC.base.stopped = true
  · unfold semRecvHook runDFM LibsignalSimC.guardC; simp [hstop]
  · rw [runDFM_guardC_neg _ sC ex hstop]
    unfold semRecvHook LibsignalSimC.simRecvC
    have hcond : (sC.base.stopped || sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
          !(sC.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) =
      (sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
          !(sC.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) := by
      simp [hstop]
    rw [hcond, runDFM_get_bind]
    by_cases hwin : sC.base.mir.win = true
    · simp [hwin, runDFM_pure]
    · simp only [hwin, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      by_cases hdel : (isDel && (sC.base.mir.inTransit Q.other w).isNone) = true
      · simp [hdel, runDFM_pure]
      · simp only [hdel, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        by_cases hinj : (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
            !(sC.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w))) = true
        · simp [hinj, runDFM_pure]
        · simp only [hinj, Bool.false_eq_true, ↓reduceIte]
          unfold simParseRecvC
          rw [partyDec_partyEnc]
          by_cases hlen : w.length < 9
          · simp [hlen, runDFM_pure]
          · simp only [hlen, ↓reduceIte]
            rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
              _ | ⟨h, rest⟩
            · simp [runDFM_pure]
            · cases haddr : addressCheckPasses h.addresses (P.expectedAddrs Q)
              · simp [haddr, runDFM_pure]
              · cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet
                · dsimp only []
                  simp only [haddr, hpan, Bool.not_true, Bool.false_or, Bool.false_eq_true,
                    ↓reduceIte]
                  rcases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with _ | ⟨pq', salt⟩
                  · simp [runDFM_pure]
                  · have hlt : h.counter.toNat < 2 ^ 32 := h.counter.isLt
                    have hmin : min (h.counter.toNat + 1) (2 ^ 32) = h.counter.toNat + 1 :=
                      Nat.min_eq_left (by omega)
                    dsimp only []
                    simp only [hmin]
                    rcases hfind : (sC.base.chains Q).findIdx?
                        (fun g => g.key == some h.senderRatchetKey) with _ | ci <;>
                      simp only [hfind]
                    · by_cases hev : (((sC.base.honest.find? fun wc =>
                          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                            (fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true &&
                        ((sC.base.honest.find? fun wc =>
                          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                            (fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true) = true
                      · simp only [hev, ↓reduceIte, runDFM_pure]
                      · simp only [hev, Bool.false_eq_true, ↓reduceIte]
                        by_cases hT0 : (decT h.senderRatchetKey == some 0) = true
                        · simp [hT0, runDFM_pure]
                        · simp only [hT0, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel,
                            runDFM_ite_modify]
                          by_cases hexit : (inReceiveOnlyEpoch sC.base.mir Q ||
                              decide (25000 < h.counter.toNat) ||
                              decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
                          · simp only [hexit, ↓reduceIte, runDFM_pure]
                          · simp only [hexit, Bool.false_eq_true, ↓reduceIte]
                            have h25000 : h.counter.toNat ≤ 25000 := by
                              simp only [Bool.not_eq_true, Bool.or_eq_false_iff,
                                decide_eq_false_iff_not] at hexit
                              omega
                            rcases hT : decT h.senderRatchetKey with _ | T
                            · simp only [runDFM_pure]
                            · dsimp only []
                              by_cases hev1 : (((sC.base.honest.find? fun wc =>
                                  wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                                    (fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) ==
                                      some true) = true
                              · simp only [hev1, ↓reduceIte]
                                rw [semFwdEvictHook_deliverForge_eq]
                              · simp only [hev1, Bool.false_eq_true, ↓reduceIte]
                                rw [semFwdHook_deliverForge_eq P Dh encPt encT lam qep B]
                                · rfl
                                · intro c hc hne; rw [hc] at hne ⊢
                                  by_cases hs : c.2.2.2 = effectiveHkdfSalt32 salt
                                  · simp [hs] at hne
                                  · simp only [hs, ↓reduceIte]; exact ⟨hep, by omega⟩
                    · by_cases hrej :
                          ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects
                            (h.counter.toNat + 1) = true
                      · simp only [hrej, ↓reduceIte, runDFM_pure]
                      · simp only [hrej, Bool.false_eq_true, ↓reduceIte]
                        have hgep : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch ≤ B :=
                          getD_chains_epoch_le (sC.base.chains Q) ci B hch
                        have hgi : h.counter.toNat + 1 ≤ B := by
                          rcases hlast with hB32 | hgl
                          · omega
                          · have hr := rejects_eq_false_le _ _ (Bool.eq_false_iff.mpr hrej)
                            have hl := getD_chains_last_le (sC.base.chains Q) ci B hB hgl
                            omega
                        rw [semFwdHook_deliverForge_eq P Dh encPt encT lam qep B]
                        · rfl
                        · intro c hc hne
                          rw [hc] at hne ⊢
                          by_cases hs : c.2.2.2 = effectiveHkdfSalt32 salt
                          · simp [hs] at hne
                          · simp only [hs, ↓reduceIte]; exact ⟨hgep, hgi⟩
                · simp [haddr, hpan, runDFM_pure]

theorem semHandleHook_deliverForge_eq (qep B : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt))
    (hB : 25001 ≤ B)
    (hep : ∀ Q : Party, sC.base.mir.epoch Q + 1 ≤ B)
    (hch : ∀ Q : Party, ∀ g ∈ sC.base.chains Q, g.epoch ≤ B)
    (hlast : ∀ Q : Party, 2 ^ 32 ≤ B ∨ ∀ g ∈ sC.base.chains Q, g.last + 25001 ≤ B) :
    semHandleHook P Dh encPt encT decT lam deliverForgeSemHook qep B t sC ex =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runDFM (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
        (fig := fig) (fs := fs)
        (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ)
        Dh (.inr t)) sC ex := by
  rcases t with (((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
  · exact semSendHook_deliverForge_eq P Dh encPt encT lam qep sC ex Q m none r
  · exact semSendHook_deliverForge_eq P Dh encPt encT lam qep sC ex Q m₀ (some m₁) r
  · unfold semHandleHook
    have h1 := semRecvHook_deliverForge_eq P Dh encPt encT decT lam qep B sC ex Q w true
      hB (hep Q) (hch Q) (hlast Q)
    change (do
      let (rr, (sC₁, ex₁)) ← semRecvHook P Dh encPt encT decT lam deliverForgeSemHook qep B
        sC ex Q w true
      pure (rr, (sC₁, ex₁))) = _
    simp only [Prod.mk.eta, bind_pure, h1]
    rfl
  · exact semRecvHook_deliverForge_eq P Dh encPt encT decT lam qep B sC ex Q w false
      hB (hep Q) (hch Q) (hlast Q)
  · exact semCorrHook_deliverForge_eq P Dh encT sC ex Q

theorem simDeliverForgeOracle_inl_eq (qep B : ℕ) (n : unifSpec.Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) :
    (simDeliverForgeOracle P Dh encPt encT decT lam qep B (.inl n)).run (sC, ex) =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runDFM (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
        (fig := fig) (fs := fs)
        (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ)
        Dh (.inl n)) sC ex := by
  unfold simDeliverForgeOracle runDFM simImplC
  change (StateT.lift
    (query (spec := unifSpec +
      SM.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) (.inl n))).run
      (sC, ex) =
    (do
      let __x ← ((LibsignalSimC.liftC
        (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ)
        (query (spec := unifSpec +
          SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt))
          (.inl n))).run sC).run ex
      pure (__x.1.1, __x.1.2, __x.2))
  simp only [liftC_deliverForge_run, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl,
    StateT.run_bind, StateT.run_pure, stateT_lift_run, pure_bind, bind_assoc]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem run'_run'_eq_bind_runDFM {α : Type}
    (x : DFM PQ Pt ℓ α) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) :
    (x.run' sC).run' ex = (runDFM x sC ex >>= fun r => pure r.1) := by
  unfold runDFM
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

theorem simDeliverForge_eq_bind_runDFM (qep : ℕ)
    (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge P ℓ Dh encPt encT decT idOf lam qep
        A =
      ((liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          SM.Construction.DeliverForge.AdversaryCompDF
            (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) (BitVec 256)) >>=
        fun pqrKey =>
          let sC₀ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
          let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
          let fs := lFS P.C P.codec ℓ encT idOf 25000
          runDFM (simulateQ (simImplC (P := P) (encT := encT) (decT := decT)
            (qep := qep) (fig := fig) (fs := fs)
            (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ)
            Dh) A) sC₀ [] >>= fun r => pure r.1) := by
  subst hid
  unfold CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge simRunCWith
  change (StateT.run'
    (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.fig8ToDFImpl Pt ℓ)
      (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256))) >>= fun pqrKey =>
      StateT.run'
        (simulateQ (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
          (fig := lFig8 Dh encPt P.C P.codec ℓ encT
            (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
          (fs := lFS P.C P.codec ℓ encT
            (fun R => if R == Party.A then P.idA else P.idB) 25000)
          (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ) Dh) A)
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)))
    []) = _
  simp only [StateT.run'_eq, StateT.run_bind, fig8ToDFImpl_liftM_probComp,
    map_bind, pure_bind, bind_assoc]
  refine bind_congr fun pqrKey => ?_
  have h := run'_run'_eq_bind_runDFM
    (simulateQ (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
      (fig := lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
      (fs := lFS P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000)
      (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ) Dh) A)
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)) []
  simpa only [StateT.run'_eq] using h

def fig8RecEnc (r : Record (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) :
    (Bool × ℕ × ℕ) × (LibsignalMsgPublicPart × Plain ℓ) × SimFig8C Pt :=
  (posEnc r.pos, (r.msg, r.ct))

def fig8MirEnc (s : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) :
    (mirTy (@fig8RecTy PQ PQC Pt ℓ)).denote :=
  (s.b,
   (s.win,
    ((s.epoch .A, s.epoch .B),
     ((s.idx .A, s.idx .B),
      (s.tL,
       (s.trans.map fig8RecEnc,
        (s.chall.map posEnc,
         (s.comp.dedup.map posEnc,
          ((s.maxAcc .A, s.maxAcc .B),
           (s.leaks,
            s.corrs.map (fun pe => (partyEnc pe.1, pe.2))))))))))))

def fig8GsEnc (g : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) :
    (@fig8GsTy PQ PQC Pt ℓ).denote :=
  ((g.st .A, g.st .B), fig8MirEnc g)

def kemExtraEnc (g : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F) :
    KemExtraRaw PQ PQC Pt ℓ :=
  (fig8GsEnc g, (⟨P.C.F, kemTrackEnc tr⟩, simKemFailCand (kemTrackEnc tr)))

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mSafeChE_fig8_eval {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy fig8RecTy))
    (p : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) (Q : Party)
    (hs : s.eval ρ = fig8MirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mSafeChE s p).eval ρ = st.safeCh 3 Q := by
  simp only [mSafeChE, Expr.eval, hs, hp, healedByE_eval]
  cases Q <;> simp [GameState.safeCh, mTL, mEpoch, pGet, Expr.eval, Expr.v0, fig8MirEnc, partyEnc]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mSafeInjE_fig8_eval {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy fig8RecTy))
    (ρ : Env Γ) (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (hs : s.eval ρ = fig8MirEnc st) :
    (mSafeInjE s).eval ρ = st.safeInj 3 := by
  simp only [mSafeInjE, Expr.eval, hs, healedByE_eval, minN_eval]
  simp [GameState.safeInj, mTL, mEpoch, Expr.eval, Expr.v0, fig8MirEnc]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mLeakE_fig8_eval {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy fig8RecTy))
    (l : Expr O' Γ .nat) (ρ : Env Γ)
    (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (hs : s.eval ρ = fig8MirEnc st) :
    (mLeakE s l).eval ρ = fig8MirEnc (st.leak (l.eval ρ)) := by
  simp only [mLeakE, mMk, Expr.eval, hs, maxOptE_eval]
  simp [GameState.leak, mB, mWin, mEpoch, mIdx, mTL, mTrans, mChall,
    mComp, mMaxAcc, mLeaks, mCorrs, Expr.eval, Expr.v0, fig8MirEnc]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mEpMgmtE_fig8_eval {O' : Ops S} {Γ} (qep : ℕ)
    (s : Expr O' Γ (mirTy fig8RecTy)) (p : Expr O' Γ .bool) (bad : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) (Q : Party)
    (hs : s.eval ρ = fig8MirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mEpMgmtE qep s p bad).eval ρ = (st.epMgmt 3 qep Q (bad.eval ρ)).map fig8MirEnc := by
  unfold mEpMgmtE GameState.epMgmt
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair p bad)).eval ρ = (fig8MirEnc st, partyEnc Q, bad.eval ρ) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (mirTy fig8RecTy) (.prod .bool .bool))
    (fig8MirEnc st, partyEnc Q, bad.eval ρ) ρ
  rw [ite_eval]
  have hSends : (sendsInE (.fst (.snd (Expr.v0 (O := O'))))
      (.add (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
        (.nat 1))).eval ρ₁ = Q.sendsIn (st.epoch Q + 1) := by
    rw [sendsInE_eval _ _ ρ₁ Q rfl]
    congr 1
    cases Q <;> simp [ρ₁, pGet, mEpoch, fig8MirEnc, partyEnc, Expr.eval, Expr.v0]
  rw [hSends]
  by_cases h1 : Q.sendsIn (st.epoch Q + 1)
  · simp only [h1, ↓reduceIte]
    rw [ite_eval]
    have hlt1 : (Expr.lt (.nat qep) (.add (pGet (mEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O'))))) (.nat 1))).eval ρ₁ =
        decide (qep < st.epoch Q + 1) := by
      cases Q <;> simp [ρ₁, pGet, mEpoch, fig8MirEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt1]
    by_cases h2 : qep < st.epoch Q + 1
    · simp [h2, Expr.eval]
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte, Option.map_some]
      rw [letE_eval, ite_eval]
      have hCond : (Expr.and (.snd (.snd (Expr.v0 (O := O'))))
          (.not (mSafeChE (.fst (Expr.v0 (O := O')))
            (.fst (.snd (Expr.v0 (O := O'))))))).eval ρ₁ =
          (bad.eval ρ && !(st.safeCh 3 Q)) := by
        have hsafe := mSafeChE_fig8_eval (.fst (Expr.v0 (O := O')))
          (.fst (.snd (Expr.v0 (O := O')))) ρ₁ st Q rfl rfl
        simp only [Expr.eval, hsafe]
        rfl
      have hLeak : (mLeakE (.fst (Expr.v0 (O := O')))
          (.add (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
            (.nat 1))).eval ρ₁ = fig8MirEnc (st.leak (st.epoch Q + 1)) := by
        rw [mLeakE_fig8_eval (.fst (Expr.v0 (O := O'))) _ ρ₁ st rfl]
        congr 2
        cases Q <;> simp [ρ₁, pGet, mEpoch, fig8MirEnc, partyEnc, Expr.eval, Expr.v0]
      have hBase : (Expr.fst (Expr.v0 (O := O'))).eval ρ₁ = fig8MirEnc st := rfl
      rw [hCond, hLeak, hBase]
      set st₁ := if (bad.eval ρ && !(st.safeCh 3 Q)) = true then st.leak (st.epoch Q + 1) else st
      have hst₁ : (if (bad.eval ρ && !(st.safeCh 3 Q)) = true
          then (fig8MirEnc (st.leak (st.epoch Q + 1)) : (mirTy (@fig8RecTy PQ PQC Pt ℓ)).denote)
          else fig8MirEnc st) = fig8MirEnc st₁ := by
        dsimp only [st₁]; split_ifs <;> rfl
      rw [hst₁]
      cases Q <;>
        simp [ρ₁, mMk, mB, mWin, mEpoch, mIdx, mTL, mTrans, mChall, mComp,
          mMaxAcc, mLeaks, mCorrs, pGet, pSet, fig8MirEnc, partyEnc, Function.update,
          Expr.eval, Expr.v0, Expr.v1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [ite_eval]
    have hlt2 : (Expr.lt (.nat qep) (pGet (mEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O')))))).eval ρ₁ = decide (qep < st.epoch Q) := by
      cases Q <;> simp [ρ₁, pGet, mEpoch, fig8MirEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt2]
    by_cases h2 : qep < st.epoch Q <;> simp [ρ₁, h2, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mRecordE_fig8_eval {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy fig8RecTy))
    (p : Expr O' Γ .bool) (r : Expr O' Γ fig8RecTy) (isChall : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) (Q : Party)
    (st' : SimFig8St Pt) (rec_ : Record (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (hFresh : rec_.pos ∉ st.comp)
    (hs : s.eval ρ = fig8MirEnc st) (hp : p.eval ρ = partyEnc Q)
    (hr : r.eval ρ = fig8RecEnc rec_) :
    (mRecordE s p r isChall).eval ρ =
      fig8MirEnc (st.record 3 Q st' rec_ (isChall.eval ρ)) := by
  unfold mRecordE
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair p (.pair r isChall))).eval ρ =
      (fig8MirEnc st, partyEnc Q, fig8RecEnc rec_, isChall.eval ρ) := by
    simp [Expr.eval, hs, hp, hr]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (mirTy fig8RecTy) (.prod .bool (.prod fig8RecTy .bool)))
    (fig8MirEnc st, partyEnc Q, fig8RecEnc rec_, isChall.eval ρ) ρ
  have hSafe : (mSafeChE (.fst (Expr.v0 (O := O'))) (.fst (.snd (Expr.v0 (O := O'))))).eval ρ₁ =
      st.safeCh 3 Q :=
    mSafeChE_fig8_eval (.fst .v0) (.fst (.snd .v0)) ρ₁ st Q rfl rfl
  have hdedup : (rec_.pos :: st.comp).dedup = rec_.pos :: st.comp.dedup :=
    List.dedup_cons_of_notMem hFresh
  simp only [mMk, Expr.eval, hSafe]
  cases Q <;> cases hch : isChall.eval ρ <;>
  by_cases hsafeA : st.safeCh 3 .A <;> by_cases hsafeB : st.safeCh 3 .B <;>
  simp [ρ₁, GameState.record, mB, mWin, mEpoch, mIdx, mTL, mTrans,
    mChall, mComp, mMaxAcc, mLeaks, mCorrs, posIdx, pSet,
    hch, hsafeA, hsafeB, hdedup, fig8MirEnc, fig8RecEnc, posEnc, partyEnc, Function.update,
    Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mSetWin_fig8_eval {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy fig8RecTy))
    (w : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (hs : s.eval ρ = fig8MirEnc st) :
    (mSetWin s w).eval ρ = fig8MirEnc { st with win := w.eval ρ } := by
  simp [mSetWin, mMk, mB, mEpoch, mIdx, mTL, mTrans, mChall, mComp,
    mMaxAcc, mLeaks, mCorrs, hs, fig8MirEnc, Expr.eval, Expr.v0]

omit [SampleableType PQC] in
theorem fgInTransitE_eval {Γ} (L : ℕ) (s : Expr OFig Γ (mirTy fig8RecTy))
    (qParty : Expr OFig Γ .bool) (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) (ρ : Env Γ)
    (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) (Q : Party)
    (hL : st.trans.length ≤ L)
    (hs : s.eval ρ = fig8MirEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (fgInTransitE P Dh encPt encT decT lam K toKemCoins L s qParty c).eval ρ =
      (st.inTransit Q (c.eval ρ)).map fig8RecEnc := by
  have htake : ((st.trans.map fig8RecEnc).take L) = st.trans.map fig8RecEnc :=
    List.take_of_length_le (by simpa using hL)
  simp only [fgInTransitE, GameState.inTransit, mTrans, posSender,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    boolEq_eval, simOpsUnitCost, hs, hq, fig8MirEnc, htake]
  rw [find?_map_eq]
  congr 2
  funext ⟨⟨sender, ep, idx⟩, msg, ct⟩
  cases sender <;> cases Q <;> by_cases h : ct = c.eval ρ <;>
    simp [fig8RecEnc, posEnc, partyEnc, h]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mDeleteE_fig8_eval {O' : Ops S} {Γ} (L : ℕ) (s : Expr O' Γ (mirTy fig8RecTy))
    (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) (p : SM.Pos)
    (hTrans : st.trans.length ≤ L) (hChall : st.chall.length ≤ L)
    (hComp : st.comp.dedup.length ≤ L)
    (hs : s.eval ρ = fig8MirEnc st) (hp : pos.eval ρ = posEnc p) :
    (mDeleteE L s pos).eval ρ = fig8MirEnc (st.delete p) := by
  have ht1 : (st.trans.map fig8RecEnc).take L = st.trans.map fig8RecEnc :=
    List.take_of_length_le (by simpa using hTrans)
  have ht2 : (st.chall.map posEnc).take L = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have ht3 : (st.comp.dedup.map posEnc).take L = st.comp.dedup.map posEnc :=
    List.take_of_length_le (by simpa using hComp)
  simp only [mDeleteE, GameState.delete, mMk, mB, mWin, mEpoch, mIdx, mTL, mTrans,
    mChall, mComp, mMaxAcc, mLeaks, mCorrs, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hp, fig8MirEnc, ht1, ht2, ht3]
  rw [foldr_filter_map, foldr_filter_map, foldr_filter_map]
  simp [fig8RecEnc, posDec_posEnc, bne, dedup_filter_eq]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mAcceptE_fig8_eval {O' : Ops S} {Γ} (L : ℕ) (s : Expr O' Γ (mirTy fig8RecTy))
    (p : Expr O' Γ .bool) (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (st' : SimFig8St Pt) (pos₀ : SM.Pos)
    (hTrans : st.trans.length ≤ L) (hChall : st.chall.length ≤ L)
    (hComp : st.comp.dedup.length ≤ L)
    (hs : s.eval ρ = fig8MirEnc st) (hp : p.eval ρ = partyEnc Q)
    (hpos : pos.eval ρ = posEnc pos₀) :
    (mAcceptE L s p pos).eval ρ = fig8MirEnc (st.accept Q st' pos₀) := by
  have hdel := mDeleteE_fig8_eval L s pos ρ st pos₀ hTrans hChall hComp hs hpos
  simp only [mAcceptE, mMk, Expr.eval, hdel, hp, hpos]
  cases Q <;>
  · simp [GameState.accept, mB, mWin, mEpoch, mIdx, mTL, mTrans,
      mChall, mComp, mMaxAcc, mLeaks, mCorrs, posEpoch, posIdx, pGet, pSet,
      maxAccGet, maxAccSet, maxN_eval, fig8MirEnc, posEnc, partyEnc,
      Function.update, Expr.eval, Expr.v0]
    funext j; split_ifs with hj <;> simp [hj]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mCompContainsE_fig8_eval {O' : Ops S} {Γ} (L : ℕ) (s : Expr O' Γ (mirTy fig8RecTy))
    (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) (pos₀ : SM.Pos)
    (hComp : st.comp.dedup.length ≤ L)
    (hs : s.eval ρ = fig8MirEnc st) (hpos : pos.eval ρ = posEnc pos₀) :
    (mCompContainsE L s pos).eval ρ = st.comp.contains pos₀ := by
  have ht : (st.comp.dedup.map posEnc).take L = st.comp.dedup.map posEnc :=
    List.take_of_length_le (by simpa using hComp)
  simp only [mCompContainsE, mComp, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hpos, fig8MirEnc, ht]
  rw [any_map_eq]
  simp only [posDec_posEnc]
  exact (any_beq_eq_contains pos₀ st.comp.dedup).trans (canonComp_comp_contains st pos₀)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mChallContainsE_fig8_eval {O' : Ops S} {Γ} (L : ℕ) (s : Expr O' Γ (mirTy fig8RecTy))
    (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) (pos₀ : SM.Pos)
    (hChall : st.chall.length ≤ L)
    (hs : s.eval ρ = fig8MirEnc st) (hpos : pos.eval ρ = posEnc pos₀) :
    (mChallContainsE L s pos).eval ρ = st.chall.contains pos₀ := by
  have ht : (st.chall.map posEnc).take L = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  simp only [mChallContainsE, mChall, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hpos, fig8MirEnc, ht]
  rw [any_map_eq]
  simp only [posDec_posEnc]
  exact any_beq_eq_contains pos₀ st.chall

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mTrivialE_fig8_eval {O' : Ops S} {Γ} (L : ℕ) (s : Expr O' Γ (mirTy fig8RecTy))
    (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) (pos₀ : SM.Pos)
    (hTrans : st.trans.length ≤ L) (hComp : st.comp.dedup.length ≤ L)
    (hs : s.eval ρ = fig8MirEnc st) (hpos : pos.eval ρ = posEnc pos₀) :
    (mTrivialE L s pos).eval ρ = st.trivial 3 pos₀ := by
  have ht : (st.trans.map fig8RecEnc).take L = st.trans.map fig8RecEnc :=
    List.take_of_length_le (by simpa using hTrans)
  simp only [mTrivialE, Expr.eval, hs, hpos, orE_eval, healedByE_eval]
  rw [mCompContainsE_fig8_eval L _ _ _ st pos₀ hComp rfl rfl]
  simp only [GameState.trivial, mTrans, mTL, posEpoch,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    posEq_eval, fig8MirEnc, ht]
  rw [any_map_eq]
  simp [fig8RecEnc, posEnc, posDec]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mCorrAllowedE_fig8_eval {O' : Ops S} {Γ} (L : ℕ) (s : Expr O' Γ (mirTy fig8RecTy))
    (p : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) (Q : Party)
    (hTrans : st.trans.length ≤ L) (hChall : st.chall.length ≤ L)
    (hComp : st.comp.dedup.length ≤ L)
    (hs : s.eval ρ = fig8MirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mCorrAllowedE L s p).eval ρ = st.corrAllowed Q := by
  unfold mCorrAllowedE GameState.corrAllowed
  rw [letE_eval]
  have h0 : (Expr.pair s p).eval ρ = (fig8MirEnc st, partyEnc Q) := by simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (mirTy fig8RecTy) .bool) (fig8MirEnc st, partyEnc Q) ρ
  have htCh : (st.chall.map posEnc).take L = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have htTr : (st.trans.map fig8RecEnc).take L = st.trans.map fig8RecEnc :=
    List.take_of_length_le (by simpa using hTrans)
  have hCh0 : (mChall (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.chall.map posEnc := rfl
  have hTr0 : (mTrans (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.trans.map fig8RecEnc := rfl
  simp only [Expr.eval, hCh0, hTr0, htCh, htTr]
  congr 1
  · congr 1
    rw [any_map_eq]
    congr 1; funext pos
    simp [ρ₁, posSender, otherE, posEnc, ← partyEnc_other, partyEnc_beq, Expr.eval,
      Expr.v0, Expr.v1]
  · congr 1
    rw [any_map_eq]
    congr 1; funext r
    have hcomp := mCompContainsE_fig8_eval (O' := O') L (.fst .v1) (.fst .v0)
      (Env.cons (t := fig8RecTy) (fig8RecEnc r) ρ₁) st r.pos hComp rfl rfl
    rw [hcomp]
    simp [ρ₁, posSender, otherE, fig8RecEnc, posEnc, ← partyEnc_other, partyEnc_beq,
      Expr.eval, Expr.v0, Expr.v1]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mAfterCorrE_fig8_eval {O' : Ops S} {Γ} (L : ℕ) (s : Expr O' Γ (mirTy fig8RecTy))
    (p : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) (Q : Party)
    (hTrans : st.trans.length ≤ L)
    (hCompU : ∃ U : List SM.Pos, U.length ≤ L ∧ CountLe st.comp.dedup U ∧ ∀ r ∈ st.trans, r.pos ∈ U)
    (hs : s.eval ρ = fig8MirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mAfterCorrE L s p).eval ρ = fig8MirEnc (st.afterCorr Q) := by
  rcases hCompU with ⟨U, hUL, haccU, htransU⟩
  simp only [mAfterCorrE, mLeakE, maxOptE, mMk, mB, mWin, mEpoch, mIdx, mTL,
    mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs, posSender, otherE,
    Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ,
    boolEq_eval, posEq_eval, maxN_eval, hs, hp, fig8MirEnc]
  have hfold := foldr_dedup_map_eq (K := L) (encR := fig8RecEnc) (encP := posEnc)
    (posOf := Record.pos)
    (keep := fun r : Record (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) =>
      r.pos.sender == Q.other)
    (keepE := fun rE => rE.1.1 == !partyEnc Q)
    (posE := fun rE => rE.1)
    (eqP := fun p₁ p₂ => posDec p₁ == posDec p₂)
    (rs := st.trans) (acc := st.comp.dedup) (U := U)
    (by intro r; simp [fig8RecEnc, posEnc, ← partyEnc_other, partyEnc_beq])
    (by intro r; rfl)
    (by intro p₁ p₂; simp [posDec_posEnc])
    hTrans hUL haccU (fun r hr _ => htransU r hr)
  rw [hfold, ← dedup_append_eq_dedupPrepend]
  cases Q <;>
  · simp only [GameState.afterCorr, GameState.leak, maxOpt, pGet, partyEnc,
      Expr.eval, Expr.v0, Env.get_cons_zero]
    cases st.tL <;> rfl

omit [DecidableEq Pt] [SampleableType PQC] in
theorem lFig8_send_epoch_le
    (idOf : Party → IdentityKey)
    (st : SimFig8St Pt) (m : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256) :
    ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st m coins).2.1.1 ≤
      st.tcur + 1 := by
  dsimp only [lFig8, SM.Construction.scheme, SM.Construction.send]
  split <;> split_ifs <;> dsimp only [] <;> omega

omit [SampleableType PQC] in
theorem simOp_fig8SendStep_eq (B : ℕ) (st : SimFig8St Pt)
    (m : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256) (ht : st.tcur + 1 ≤ B) :
    (OFig).eval (SimOp.fig8SendStep B) (st, some (m, coins)) =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      (st.id.sendsIn (st.tcur + 1), fig.send st m coins) := by
  have hle := Nat.le_trans
    (lFig8_send_epoch_le P Dh encPt encT lam
      (fun R => if R == Party.A then P.idA else P.idB) st m coins) ht
  change
    (let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
     let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
     let (st', c) := fig.send st m coins
     (st.id.sendsIn (st.tcur + 1), (st', ((min c.1.1 B, c.1.2), c.2)))) = _
  simp only [Nat.min_eq_left hle, Prod.mk.eta]

omit [SampleableType PQC] in
theorem simOp_fig8Receive_eq (B : ℕ) (st : SimFig8St Pt) (c : SimFig8C Pt)
    (ht : c.1.1 ≤ B) (hi : c.2.1 ≤ B) :
    (OFig).eval (SimOp.fig8Receive B) (st, c) =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      fig.receive st c := by
  dsimp only [simOpsUnitCost, simParamOps]
  rcases h : (lFig8 Dh encPt P.C P.codec ℓ encT
    (fun R => if R == Party.A then P.idA else P.idB) 25000 lam).receive st c with
    _ | ⟨st', t, i, pm⟩
  · rfl
  · obtain ⟨rfl, rfl⟩ := lFig8_receive_epoch_index_eq P Dh encPt encT lam
      (fun R => if R == Party.A then P.idA else P.idB) st st' c t i pm h
    simp [Option.map, Nat.min_eq_left ht, Nat.min_eq_left hi]

theorem samIfNecFig8C_eval {Γ} (r : Expr OFig Γ (.opt (.base .bv256))) (ρ : Env Γ) :
    (samIfNecFig8C P Dh encPt encT decT lam K toKemCoins r).eval ρ =
      SM.samIfNec (r.eval ρ) := by
  unfold samIfNecFig8C SM.samIfNec
  rw [comp_eval_caseOpt]
  rcases r.eval ρ with _ | c
  · simp only [Comp.eval, kemFailIface_liftP]
    rfl
  · rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem stateT_liftM_probComp_run {σ α : Type} (p : ProbComp α) (s : σ) :
    (liftM p : StateT σ ProbComp α).run s = (p >>= fun x => pure (x, s)) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem epMgmt_st_b {St Msg C : Type}
    (s s₁ : GameState St Msg C) (Δ qep : ℕ) (Q : Party) (bad : Bool)
    (h : s.epMgmt Δ qep Q bad = some s₁) :
    s₁.st = s.st ∧ s₁.b = s.b := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> injection h with h <;> subst h <;> simp [GameState.leak]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem stepKemFailDeliver_cand (F : ShaCompress)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState F)
    (Q : Party) (j : ℕ) :
    (CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailDeliver F K tr Q j).cand = tr.cand := by
  unfold CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailDeliver
  rcases tr.sentB[j]? with _ | ⟨m, _⟩
  · rfl
  · dsimp only []
    rcases (tr.st Q).recv K m with _ | out
    · rfl
    · dsimp only []
      split_ifs
      · rcases tr.c <;> rfl
      · rfl

theorem kemFailSemHook_onSendCoins_eq (L qep B : ℕ)
    (Q : Party) (rq : PQC)
    (g : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F) :
    (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onSendCoins
      Q rq (kemExtraEnc P g tr) =
    let tr' := CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend
      P.C.F K tr Q (toKemCoins rq)
    pure (kemExtraEnc P g tr', kemExtraEnc P g { tr with cand := tr'.cand }) := by
  unfold kemFailSemHook kemFailHookC kemExtraEnc
  dsimp only []
  rw [comp_eval_ret]
  refine congrArg pure ?_
  rw [letE_triple_eval]
  simp only [expr_pair_eval, Expr.eval, Expr.v0,
    Env.get_cons_zero, simOpsUnitCost, simParamOps, partyDec_partyEnc,
    simStepKemFailSend_kemTrackEnc]
  rfl

theorem kemFailSemHook_onDeliverPost_eq (L qep B : ℕ)
    (Q : Party) (j? : Option ℕ) (res : Option (RecvResult (Plain ℓ)))
    (g : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F) :
    (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onDeliverPost
      Q j? res (kemExtraEnc P g tr) =
    match res, j? with
    | some (.accepted _ _ _), some j =>
      pure (kemExtraEnc P g
        (CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailDeliver P.C.F K tr Q j))
    | _, _ => pure (kemExtraEnc P g tr) := by
  unfold kemFailSemHook kemFailHookC
  dsimp only []
  rw [comp_eval_ret, letE_quad_eval]
  rcases res with _ | (_ | ⟨t, i, m⟩)
  · rfl
  · rfl
  · rcases j? with _ | j
    · rfl
    · refine congrArg pure ?_
      dsimp only [Option.map, SM.smRrEnc, kemExtraEnc,
        Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ,
        simOpsUnitCost, simParamOps]
      rw [partyDec_partyEnc, simStepKemFailDeliver_kemTrackEnc]
      dsimp only [kemTrackEnc, simKemFailCand]
      rw [stepKemFailDeliver_cand]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem pGet_fgSt_eval {O' : Ops S} {Γ}
    (g_e : Expr O' Γ fig8GsTy) (q_e : Expr O' Γ .bool)
    (ρ : Env Γ) (g : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) (Q : Party)
    (hg : g_e.eval ρ = fig8GsEnc g) (hq : q_e.eval ρ = partyEnc Q) :
    (pGet (fgSt g_e) q_e).eval ρ = g.st Q := by
  cases Q <;> simp [pGet_eval, fgSt, hg, hq, fig8GsEnc, partyEnc, Expr.eval]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem pSet_fgSt_eval {O' : Ops S} {Γ}
    (g_e : Expr O' Γ fig8GsTy) (q_e : Expr O' Γ .bool) (st'_e : Expr O' Γ (.base .fig8st))
    (ρ : Env Γ) (g : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (st' : SimFig8St Pt)
    (hg : g_e.eval ρ = fig8GsEnc g) (hq : q_e.eval ρ = partyEnc Q)
    (hst' : st'_e.eval ρ = st') :
    (pSet (fgSt g_e) q_e st'_e).eval ρ =
      ((Function.update g.st Q st') .A, (Function.update g.st Q st') .B) := by
  cases Q <;>
    simp [pSet_eval, fgSt, hg, hq, hst', fig8GsEnc, partyEnc, Function.update, Expr.eval]

theorem kemFailSemHook_onTr_eq (L qep B : ℕ)
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (g : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (ht : (g.st Q).tcur + 1 ≤ B) (hFresh : PosFreshInv g) :
    (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onTr
      Q m rc (kemExtraEnc P g tr) =
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    Prod.map id (fun g' => kemExtraEnc P g' tr) <$>
      (SM.transmitImpl fig 3 (qep + 1) (Q, m, rc)).run g := by
  unfold kemFailSemHook kemFailHookC SM.transmitImpl
  dsimp only []
  rw [bind_ret_pair_fst_snd_eval, comp_eval_ite]
  set X : (Ty.prod (.prod .bool (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base SimSort.bv256))))
      (@kemExtraTy PQ PQC Pt ℓ)).denote :=
    ((partyEnc Q, m, rc), kemExtraEnc P g tr)
  set ρ₀ := Env.cons X (Env.cons X Env.nil)
  have hwin : (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig)))))).eval ρ₀ = g.win := rfl
  rw [hwin]
  by_cases hw : g.win = true
  · simp only [hw, ↓reduceIte, Comp.eval, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind, map_pure]
    rfl
  · have hrc : (Expr.snd (.snd (.fst (Expr.v0 (O := OFig))))).eval ρ₀ = rc := rfl
    simp only [hw, Bool.false_eq_true, ↓reduceIte, comp_eval_bind, samIfNecFig8C_eval, hrc,
      StateT.run_bind, StateT.run_get, stateT_liftM_probComp_run,
      pure_bind, bind_assoc, map_bind]
    refine bind_congr fun ⟨coins, bad⟩ => ?_
    rw [comp_eval_ret, expr_caseOpt_eval]
    have hep := mEpMgmtE_fig8_eval (O' := OFig) (qep + 1)
      (fgMir (.fst (.snd .v1))) (.fst (.fst .v1)) (.snd .v0)
      (Env.cons (coins, bad) ρ₀) g Q rfl rfl
    have hbad : (Expr.snd (Expr.v0 (O := OFig))).eval (Env.cons (coins, bad) ρ₀) = bad := rfl
    rw [hbad] at hep
    dsimp only []
    rw [hep]
    rcases hmgmt : g.epMgmt 3 (qep + 1) Q bad with _ | s₁
    · rfl
    · obtain ⟨hst₁, _⟩ := epMgmt_st_b g s₁ 3 (qep + 1) Q bad hmgmt
      dsimp only [Option.map_some]
      set ρ₂ := Env.cons (t := mirTy (@fig8RecTy PQ PQC Pt ℓ)) (fig8MirEnc s₁)
        (Env.cons (t := .prod (.base SimSort.bv256) .bool) (coins, bad) ρ₀)
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let out := fig.send (s₁.st Q) m coins
      have hout_st : fig.send (g.st Q) m coins = out := by dsimp [out]; rw [hst₁]
      have hst_get :
          (pGet (fgSt (.fst (.snd (Expr.v2 (O := OFig))))) (.fst (.fst .v2))).eval ρ₂ = g.st Q :=
        pGet_fgSt_eval (.fst (.snd .v2)) (.fst (.fst .v2)) ρ₂ g Q rfl rfl
      have hout :
          (Expr.op (O := OFig) (SimOp.fig8SendStep B)
            (.pair (pGet (fgSt (.fst (.snd .v2))) (.fst (.fst .v2)))
              (.some (.pair (.fst (.snd (.fst .v2))) (.fst .v1))))).eval ρ₂ =
          ((g.st Q).id.sendsIn ((g.st Q).tcur + 1), out) := by
        change (OFig).eval (SimOp.fig8SendStep B)
          ((pGet (fgSt (.fst (.snd (Expr.v2 (O := OFig))))) (.fst (.fst .v2))).eval ρ₂,
           some (m, coins)) = _
        rw [hst_get,
          simOp_fig8SendStep_eq P Dh encPt encT decT lam K toKemCoins B (g.st Q) m coins ht]
        dsimp only []
        rw [hout_st]
      have hrec :
          (mRecordE (O' := OFig) .v0 (.fst (.fst .v2))
            (.pair (.pair (.fst (.fst .v2))
              (.pair (pGet (mEpoch .v0) (.fst (.fst .v2)))
                (.add (pGet (mIdx .v0) (.fst (.fst .v2))) (.nat 1))))
              (.pair (.fst (.snd (.fst .v2)))
                (.snd (.snd (Expr.op (O := OFig) (SimOp.fig8SendStep B)
                  (.pair (pGet (fgSt (.fst (.snd .v2))) (.fst (.fst .v2)))
                    (.some (.pair (.fst (.snd (.fst .v2))) (.fst .v1)))))))))
            (.bool false)).eval ρ₂ =
          fig8MirEnc (s₁.record 3 Q out.1 ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m, out.2⟩ false) := by
        apply mRecordE_fig8_eval
        · exact (hFresh.epMgmt hmgmt).notMem_comp_next Q
        · rfl
        · rfl
        · simp only [expr_pair_eval, expr_fst_eval, expr_snd_eval, hout]
          cases Q <;>
            simp [ρ₂, ρ₀, X, mEpoch, mIdx, pGet_eval, fig8MirEnc, fig8RecEnc,
              posEnc, partyEnc, Expr.eval, Expr.v0, Expr.v2]
      have hpSet :
          (pSet (fgSt (.fst (.snd (Expr.v2 (O := OFig))))) (.fst (.fst .v2))
            (.fst (.snd (Expr.op (O := OFig) (SimOp.fig8SendStep B)
              (.pair (pGet (fgSt (.fst (.snd .v2))) (.fst (.fst .v2)))
                (.some (.pair (.fst (.snd (.fst .v2))) (.fst .v1)))))))).eval ρ₂ =
          ((Function.update s₁.st Q out.1) .A, (Function.update s₁.st Q out.1) .B) := by
        rw [hst₁]
        apply pSet_fgSt_eval (.fst (.snd .v2)) (.fst (.fst .v2)) _ ρ₂ g Q out.1 rfl rfl
        simp only [expr_fst_eval, expr_snd_eval, hout]
      simp only [expr_pair_eval, expr_some_eval, expr_snd_eval,
        hout, hrec, hpSet, StateT.run_bind, StateT.run_set, StateT.run_pure,
        pure_bind, map_pure]
      rfl

theorem kemFailSemHook_onCh_eq (L qep B : ℕ)
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (g : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (ht : (g.st Q).tcur + 1 ≤ B) (hFresh : PosFreshInv g) :
    (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onCh
      Q m₀ m₁ rc (kemExtraEnc P g tr) =
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    Prod.map id (fun g' => kemExtraEnc P g' tr) <$>
      (SM.challImpl fig 3 (qep + 1) SM.Config.h1 (Q, m₀, m₁, rc)).run g := by
  unfold kemFailSemHook kemFailHookC SM.challImpl
  dsimp only []
  rw [bind_ret_pair_fst_snd_eval, comp_eval_ite]
  set X : (Ty.prod (.prod .bool (.prod (lpubPlainTy PQ PQC Pt ℓ)
        (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base SimSort.bv256)))))
      (@kemExtraTy PQ PQC Pt ℓ)).denote :=
    ((partyEnc Q, m₀, m₁, rc), kemExtraEnc P g tr)
  set ρ₀ := Env.cons X (Env.cons X Env.nil)
  have hwin : (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig)))))).eval ρ₀ = g.win := rfl
  rw [hwin]
  by_cases hw : g.win = true
  · simp only [hw, ↓reduceIte, Comp.eval, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind, map_pure]
    rfl
  · have hrc : (Expr.snd (.snd (.snd (.fst (Expr.v0 (O := OFig)))))).eval ρ₀ = rc := rfl
    simp only [hw, Bool.false_eq_true, ↓reduceIte, comp_eval_bind, samIfNecFig8C_eval, hrc,
      StateT.run_bind, StateT.run_get, stateT_liftM_probComp_run,
      pure_bind, bind_assoc, map_bind]
    refine bind_congr fun ⟨coins, bad⟩ => ?_
    rw [comp_eval_ret, expr_caseOpt_eval]
    have hep := mEpMgmtE_fig8_eval (O' := OFig) (qep + 1)
      (fgMir (.fst (.snd .v1))) (.fst (.fst .v1)) (.snd .v0)
      (Env.cons (coins, bad) ρ₀) g Q rfl rfl
    have hbad : (Expr.snd (Expr.v0 (O := OFig))).eval (Env.cons (coins, bad) ρ₀) = bad := rfl
    rw [hbad] at hep
    dsimp only []
    rw [hep]
    rcases hmgmt : g.epMgmt 3 (qep + 1) Q bad with _ | s₁
    · rfl
    · obtain ⟨hst₁, hb₁⟩ := epMgmt_st_b g s₁ 3 (qep + 1) Q bad hmgmt
      dsimp only [Option.map_some]
      set ρ₂ := Env.cons (t := mirTy (@fig8RecTy PQ PQC Pt ℓ)) (fig8MirEnc s₁)
        (Env.cons (t := .prod (.base SimSort.bv256) .bool) (coins, bad) ρ₀)
      rw [ite_eval]
      have hsc :
          (Expr.not (mSafeChE (O' := OFig) .v0 (.fst (.fst .v2)))).eval ρ₂ =
            !(s₁.safeCh 3 Q) := by
        simp only [Expr.eval, mSafeChE_fig8_eval (O' := OFig) .v0 (.fst (.fst .v2)) ρ₂ s₁ Q rfl rfl]
      rw [hsc]
      have hchallOK : SM.Config.h1.challAllowedIn (Msg := LibsignalMsgPublicPart × Plain ℓ) (s₁.epoch Q) = true := rfl
      have hchallMsg :
          (SM.Config.h1.challMsg (Msg := LibsignalMsgPublicPart × Plain ℓ) (s₁.epoch Q)).getD
            (if g.b then m₁ else m₀) = (if g.b then m₁ else m₀) := rfl
      simp only [hchallOK, Bool.not_true, Bool.or_false, hchallMsg]
      by_cases hsafe : (!(s₁.safeCh 3 Q)) = true
      · simp only [hsafe, ↓reduceIte]
        rfl
      · simp only [hsafe, Bool.false_eq_true, ↓reduceIte]
        let m := if g.b then m₁ else m₀
        let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let out := fig.send (s₁.st Q) m coins
        have hout_st : fig.send (g.st Q) m coins = out := by dsimp [out]; rw [hst₁]
        have hm2 :
            (Expr.ite (mB (Expr.v0 (O := OFig)))
              (.fst (.snd (.snd (.fst .v2)))) (.fst (.snd (.fst .v2)))).eval ρ₂ = m := by
          change (if s₁.b then m₁ else m₀) = m
          rw [hb₁]
        have hst_get :
            (pGet (fgSt (.fst (.snd (Expr.v2 (O := OFig))))) (.fst (.fst .v2))).eval ρ₂ = g.st Q :=
          pGet_fgSt_eval (.fst (.snd .v2)) (.fst (.fst .v2)) ρ₂ g Q rfl rfl
        have hout :
            (Expr.op (O := OFig) (SimOp.fig8SendStep B)
              (.pair (pGet (fgSt (.fst (.snd .v2))) (.fst (.fst .v2)))
                (.some (.pair (.ite (mB .v0)
                  (.fst (.snd (.snd (.fst .v2)))) (.fst (.snd (.fst .v2)))) (.fst .v1))))).eval ρ₂ =
            ((g.st Q).id.sendsIn ((g.st Q).tcur + 1), out) := by
          change (OFig).eval (SimOp.fig8SendStep B)
            ((pGet (fgSt (.fst (.snd (Expr.v2 (O := OFig))))) (.fst (.fst .v2))).eval ρ₂,
             some ((Expr.ite (mB (Expr.v0 (O := OFig)))
               (.fst (.snd (.snd (.fst .v2)))) (.fst (.snd (.fst .v2)))).eval ρ₂, coins)) = _
          rw [hst_get, hm2,
            simOp_fig8SendStep_eq P Dh encPt encT decT lam K toKemCoins B (g.st Q) m coins ht]
          dsimp only []
          rw [hout_st]
        have hrec :
            (mRecordE (O' := OFig) .v0 (.fst (.fst .v2))
              (.pair (.pair (.fst (.fst .v2))
                (.pair (pGet (mEpoch .v0) (.fst (.fst .v2)))
                  (.add (pGet (mIdx .v0) (.fst (.fst .v2))) (.nat 1))))
                (.pair (.ite (mB .v0) (.fst (.snd (.snd (.fst .v2)))) (.fst (.snd (.fst .v2))))
                  (.snd (.snd (Expr.op (O := OFig) (SimOp.fig8SendStep B)
                    (.pair (pGet (fgSt (.fst (.snd .v2))) (.fst (.fst .v2)))
                      (.some (.pair (.ite (mB .v0)
                        (.fst (.snd (.snd (.fst .v2)))) (.fst (.snd (.fst .v2)))) (.fst .v1)))))))))
              (.bool true)).eval ρ₂ =
            fig8MirEnc (s₁.record 3 Q out.1 ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m, out.2⟩ true) := by
          apply mRecordE_fig8_eval
          · exact (hFresh.epMgmt hmgmt).notMem_comp_next Q
          · rfl
          · rfl
          · simp only [expr_pair_eval, expr_fst_eval, expr_snd_eval, hm2, hout]
            cases Q <;>
              simp [ρ₂, ρ₀, X, mEpoch, mIdx, pGet_eval, fig8MirEnc, fig8RecEnc,
                posEnc, partyEnc, Expr.eval, Expr.v0, Expr.v2]
        have hpSet :
            (pSet (fgSt (.fst (.snd (Expr.v2 (O := OFig))))) (.fst (.fst .v2))
              (.fst (.snd (Expr.op (O := OFig) (SimOp.fig8SendStep B)
                (.pair (pGet (fgSt (.fst (.snd .v2))) (.fst (.fst .v2)))
                  (.some (.pair (.ite (mB .v0)
                    (.fst (.snd (.snd (.fst .v2)))) (.fst (.snd (.fst .v2)))) (.fst .v1)))))))).eval
              ρ₂ =
            ((Function.update s₁.st Q out.1) .A, (Function.update s₁.st Q out.1) .B) := by
          rw [hst₁]
          apply pSet_fgSt_eval (.fst (.snd .v2)) (.fst (.fst .v2)) _ ρ₂ g Q out.1 rfl rfl
          simp only [expr_fst_eval, expr_snd_eval, hout]
        simp only [expr_pair_eval, expr_some_eval, expr_snd_eval,
          hout, hrec, hpSet, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, map_pure]
        rfl

theorem kemFailSemHook_onCr_eq (L qep B : ℕ)
    (Q : Party)
    (g : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (hTrans : g.trans.length ≤ L) (hChall : g.chall.length ≤ L)
    (hComp : g.comp.dedup.length ≤ L)
    (hCompU : ∃ U : List SM.Pos, U.length ≤ L ∧ CountLe g.comp.dedup U ∧ ∀ r ∈ g.trans, r.pos ∈ U) :
    (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onCr
      Q (kemExtraEnc P g tr) =
    Prod.map id (fun g' => kemExtraEnc P g' tr) <$>
      (SM.corrImpl (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (C := SimFig8C Pt) Q).run g := by
  unfold kemFailSemHook kemFailHookC SM.corrImpl
  dsimp only []
  rw [comp_eval_ret, letE_pair_fst_snd_eval, ite_eval]
  set X : (Ty.prod .bool (@kemExtraTy PQ PQC Pt ℓ)).denote :=
    (partyEnc Q, kemExtraEnc P g tr)
  set ρ₀ := Env.cons X (Env.cons X Env.nil)
  have hca := mCorrAllowedE_fig8_eval (O' := OFig) L
    (fgMir (.fst (.snd .v0))) (.fst .v0) ρ₀ g Q hTrans hChall hComp rfl rfl
  have href :
      (orE (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig))))))
        (.not (mCorrAllowedE L (fgMir (.fst (.snd .v0))) (.fst .v0)))).eval ρ₀ =
      (g.win || !(g.corrAllowed Q)) := by
    simp only [orE_eval, Expr.eval, hca]
    rfl
  rw [href]
  by_cases h1 : (g.win || !(g.corrAllowed Q)) = true
  · simp only [h1, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind, map_pure]
    rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, pure_bind, map_pure]
    have hst_get : (pGet (fgSt (.fst (.snd (Expr.v0 (O := OFig))))) (.fst .v0)).eval ρ₀ = g.st Q :=
      pGet_fgSt_eval (.fst (.snd .v0)) (.fst .v0) ρ₀ g Q rfl rfl
    have hac := mAfterCorrE_fig8_eval (O' := OFig) L
      (fgMir (.fst (.snd .v0))) (.fst .v0) ρ₀ g Q hTrans hCompU rfl rfl
    simp only [expr_pair_eval, expr_some_eval, hst_get, hac]
    rfl

theorem kemFailSemHook_onDl_eq (L qep B : ℕ)
    (Q : Party) (c : SimFig8C Pt)
    (g : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (hTrans : g.trans.length ≤ L) (hChall : g.chall.length ≤ L)
    (hComp : g.comp.dedup.length ≤ L)
    (ht : c.1.1 ≤ B) (hi : c.2.1 ≤ B) :
    (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onDl
      Q c (kemExtraEnc P g tr) =
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    Prod.map id (fun g' => kemExtraEnc P g' tr) <$>
      (SM.deliverImpl fig SM.Config.h1 (Q, c)).run g := by
  unfold kemFailSemHook kemFailHookC SM.deliverImpl
  dsimp only []
  rw [comp_eval_ret, letE_pair_fst_snd_eval, ite_eval]
  set X : (Ty.prod (.prod .bool (fig8CTy PQ PQC Pt ℓ)) (@kemExtraTy PQ PQC Pt ℓ)).denote :=
    ((partyEnc Q, c), kemExtraEnc P g tr)
  set ρ₀ := Env.cons X (Env.cons X Env.nil)
  have hwin : (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig)))))).eval ρ₀ = g.win := rfl
  rw [hwin]
  by_cases hw : g.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind, map_pure]
    rfl
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    rw [expr_caseOpt_eval]
    have hinTr := fgInTransitE_eval P Dh encPt encT decT lam K toKemCoins L
      (fgMir (.fst (.snd .v0))) (otherE (.fst (.fst .v0))) (.snd (.fst .v0))
      ρ₀ g Q.other hTrans rfl (by simp [ρ₀, X, otherE, partyEnc_other, Expr.eval, Expr.v0])
    have hc0 : (Expr.snd (.fst (Expr.v0 (O := OFig)))).eval ρ₀ = c := rfl
    rw [hc0] at hinTr
    rw [hinTr]
    rcases htr : g.inTransit Q.other c with _ | r
    · rfl
    · dsimp only [Option.map_some]
      set ρ₁ := Env.cons (t := fig8RecTy) (fig8RecEnc r) ρ₀
      have hdw : SM.Config.h1.deliverWin (Msg := LibsignalMsgPublicPart × Plain ℓ) = false := rfl
      simp only [hdw, Bool.false_and]
      rw [expr_caseOpt_eval]
      have hst_get :
          (pGet (fgSt (.fst (.snd (Expr.v1 (O := OFig))))) (.fst (.fst .v1))).eval ρ₁ = g.st Q :=
        pGet_fgSt_eval (.fst (.snd .v1)) (.fst (.fst .v1)) ρ₁ g Q rfl rfl
      have hrcv :
          (Expr.op (O := OFig) (SimOp.fig8Receive B)
            (.pair (pGet (fgSt (.fst (.snd .v1))) (.fst (.fst .v1))) (.snd (.fst .v1)))).eval ρ₁ =
          (lFig8 Dh encPt P.C P.codec ℓ encT (fun R => if R == Party.A then P.idA else P.idB)
            25000 lam).receive (g.st Q) c := by
        change (OFig).eval (SimOp.fig8Receive B)
          ((pGet (fgSt (.fst (.snd (Expr.v1 (O := OFig))))) (.fst (.fst .v1))).eval ρ₁, c) = _
        rw [hst_get, simOp_fig8Receive_eq P Dh encPt encT decT lam K toKemCoins B (g.st Q) c ht hi]
      rw [hrcv]
      rcases (lFig8 Dh encPt P.C P.codec ℓ encT (fun R => if R == Party.A then P.idA else P.idB)
          25000 lam).receive (g.st Q) c with _ | ⟨st', t', i', m'⟩
      · rfl
      · dsimp only []
        set ρ₂ := Env.cons
          (t := .prod (.base SimSort.fig8st) (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ))))
          (st', t', i', m') ρ₁
        have hcc := mChallContainsE_fig8_eval (O' := OFig) L
          (fgMir (.fst (.snd .v2))) (.fst .v1) ρ₂ g r.pos hChall rfl rfl
        have hacc := mAcceptE_fig8_eval (O' := OFig) L
          (fgMir (.fst (.snd .v2))) (.fst (.fst .v2)) (.fst .v1)
          ρ₂ g Q st' r.pos hTrans hChall hComp rfl rfl rfl
        have hpSet :
            (pSet (fgSt (.fst (.snd (Expr.v2 (O := OFig))))) (.fst (.fst .v2)) (.fst .v0)).eval
              ρ₂ =
            ((Function.update g.st Q st') .A, (Function.update g.st Q st') .B) :=
          pSet_fgSt_eval (.fst (.snd .v2)) (.fst (.fst .v2)) (.fst .v0) ρ₂ g Q st' rfl rfl rfl
        simp only [expr_pair_eval, expr_some_eval, inr_eval, ite_eval, hcc, hacc, hpSet,
          Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, map_pure]
        cases g.chall.contains r.pos <;> rfl

theorem kemFailSemHook_onIj_eq (L qep B : ℕ)
    (Q : Party) (c : SimFig8C Pt)
    (g : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (hTrans : g.trans.length ≤ L) (hChall : g.chall.length ≤ L)
    (hComp : g.comp.dedup.length ≤ L)
    (ht : c.1.1 ≤ B) (hi : c.2.1 ≤ B) :
    (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onIj
      Q c (kemExtraEnc P g tr) =
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    Prod.map id (fun g' => kemExtraEnc P g' tr) <$>
      (SM.injectImpl fig 3 (qep + 1) SM.Config.h1 (Q, c)).run g := by
  unfold kemFailSemHook kemFailHookC SM.injectImpl
  dsimp only []
  rw [comp_eval_ret, letE_pair_fst_snd_eval, ite_eval]
  set X : (Ty.prod (.prod .bool (fig8CTy PQ PQC Pt ℓ)) (@kemExtraTy PQ PQC Pt ℓ)).denote :=
    ((partyEnc Q, c), kemExtraEnc P g tr)
  set ρ₀ := Env.cons X (Env.cons X Env.nil)
  have hinTr := fgInTransitE_eval P Dh encPt encT decT lam K toKemCoins L
    (fgMir (.fst (.snd .v0))) (otherE (.fst (.fst .v0))) (.snd (.fst .v0))
    ρ₀ g Q.other hTrans rfl (by simp [ρ₀, X, otherE, partyEnc_other, Expr.eval, Expr.v0])
  have hsi := mSafeInjE_fig8_eval (O' := OFig) (fgMir (.fst (.snd .v0))) ρ₀ g rfl
  have href :
      (orE (mWin (fgMir (.fst (.snd (Expr.v0 (O := OFig))))))
        (orE (isSomeE (fgInTransitE P Dh encPt encT decT lam K toKemCoins L
            (fgMir (.fst (.snd .v0))) (otherE (.fst (.fst .v0))) (.snd (.fst .v0))))
          (.not (mSafeInjE (fgMir (.fst (.snd .v0))))))).eval ρ₀ =
      (g.win || (g.inTransit Q.other c).isSome || !(g.safeInj 3)) := by
    simp only [orE_eval, isSomeE_eval, Expr.eval, hinTr, hsi, Option.isSome_map, Bool.or_assoc]
    rfl
  rw [href]
  by_cases h1 : (g.win || (g.inTransit Q.other c).isSome || !(g.safeInj 3)) = true
  · simp only [h1, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind, map_pure]
    rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    rw [expr_caseOpt_eval]
    have hst_get :
        (pGet (fgSt (.fst (.snd (Expr.v0 (O := OFig))))) (.fst (.fst .v0))).eval ρ₀ = g.st Q :=
      pGet_fgSt_eval (.fst (.snd .v0)) (.fst (.fst .v0)) ρ₀ g Q rfl rfl
    have hrcv :
        (Expr.op (O := OFig) (SimOp.fig8Receive B)
          (.pair (pGet (fgSt (.fst (.snd .v0))) (.fst (.fst .v0))) (.snd (.fst .v0)))).eval ρ₀ =
        (lFig8 Dh encPt P.C P.codec ℓ encT (fun R => if R == Party.A then P.idA else P.idB)
          25000 lam).receive (g.st Q) c := by
      change (OFig).eval (SimOp.fig8Receive B)
        ((pGet (fgSt (.fst (.snd (Expr.v0 (O := OFig))))) (.fst (.fst .v0))).eval ρ₀, c) = _
      rw [hst_get, simOp_fig8Receive_eq P Dh encPt encT decT lam K toKemCoins B (g.st Q) c ht hi]
    rw [hrcv]
    rcases (lFig8 Dh encPt P.C P.codec ℓ encT (fun R => if R == Party.A then P.idA else P.idB)
        25000 lam).receive (g.st Q) c with _ | ⟨st', t', i', m'⟩
    · rfl
    · dsimp only []
      set ρ₁ := Env.cons
        (t := .prod (.base SimSort.fig8st) (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ))))
        (st', t', i', m') ρ₀
      rw [ite_eval]
      have hlt : (Expr.lt (.nat (qep + 2)) (.fst (.snd (Expr.v0 (O := OFig))))).eval ρ₁ =
          decide (qep + 1 + 1 < t') := rfl
      rw [hlt]
      by_cases h2 : qep + 1 + 1 < t'
      · simp only [h2, decide_true, ↓reduceIte]
        rfl
      · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [ite_eval]
        have hpos :
            (Expr.pair (otherE (.fst (.fst (Expr.v1 (O := OFig)))))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))).eval ρ₁ =
            posEnc ⟨Q.other, t', i'⟩ := by
          simp [ρ₁, ρ₀, X, otherE, posEnc, partyEnc_other, Expr.eval, Expr.v0, Expr.v1]
        have htriv := mTrivialE_fig8_eval (O' := OFig) L
          (fgMir (.fst (.snd .v1)))
          (.pair (otherE (.fst (.fst .v1))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
          ρ₁ g ⟨Q.other, t', i'⟩ hTrans hComp rfl hpos
        rw [htriv]
        by_cases h3 : (g.trivial 3 ⟨Q.other, t', i'⟩) = true
        · simp only [h3, ↓reduceIte]
          have hacc := mAcceptE_fig8_eval (O' := OFig) L
            (fgMir (.fst (.snd .v1))) (.fst (.fst .v1))
            (.pair (otherE (.fst (.fst .v1))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            ρ₁ g Q st' ⟨Q.other, t', i'⟩ hTrans hChall hComp rfl rfl hpos
          have hpSet :
              (pSet (fgSt (.fst (.snd (Expr.v1 (O := OFig))))) (.fst (.fst .v1)) (.fst .v0)).eval
                ρ₁ =
              ((Function.update g.st Q st') .A, (Function.update g.st Q st') .B) :=
            pSet_fgSt_eval (.fst (.snd .v1)) (.fst (.fst .v1)) (.fst .v0) ρ₁ g Q st' rfl rfl rfl
          simp only [expr_pair_eval, expr_some_eval, hacc, hpSet,
            StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure]
          rfl
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          have hinjFull : SM.Config.h1.injectFull (Msg := LibsignalMsgPublicPart × Plain ℓ) t' = true := rfl
          have hsw := mSetWin_fig8_eval (O' := OFig)
            (fgMir (.fst (.snd .v1))) (.bool true) ρ₁ g rfl
          simp only [hinjFull, ↓reduceIte, expr_pair_eval, expr_some_eval, hsw,
            StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure]
          rfl
omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem transmitImpl_run_none_eq
    (fig : SMScheme (RootKey × BitVec 256) (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt))
    (d qepF : ℕ) (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r? : Option (BitVec 256))
    (g g' : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (h : (none, g') ∈ support ((SM.transmitImpl fig d qepF (Q, m, r?)).run g)) :
    g' = g := by
  simp only [SM.transmitImpl, StateT.run_bind, StateT.run_get, pure_bind] at h
  split_ifs at h with h1
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
    exact h.2
  · simp only [StateT.run_bind, stateT_liftM_probComp_run, bind_assoc, pure_bind,
      mem_support_bind_iff] at h
    rcases h with ⟨⟨r, bad⟩, _, h⟩
    split at h
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      exact h.2
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at h

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem challImpl_run_none_eq
    (fig : SMScheme (RootKey × BitVec 256) (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt))
    (d qepF : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (r? : Option (BitVec 256))
    (g g' : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (h : (none, g') ∈ support ((SM.challImpl fig d qepF cfg (Q, m₀, m₁, r?)).run g)) :
    g' = g := by
  simp only [SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind] at h
  by_cases h1 : g.win = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    exact h.2
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_liftM_probComp_run,
      bind_assoc, pure_bind, mem_support_bind_iff] at h
    rcases h with ⟨⟨r, bad⟩, _, h⟩
    split at h
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      exact h.2
    · next s₁ _ =>
      by_cases h2 : (!(s₁.safeCh d Q) || !(cfg.challAllowedIn (s₁.epoch Q))) = true
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at h
        exact h.2
      · simp only [h2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          reduceCtorEq, false_and] at h

omit [Zero Pt] [SampleableType PQC] in
private theorem fig8ImplH1_transmitQuery
    (fig : SMScheme (RootKey × BitVec 256) (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt))
    (qepF : ℕ) (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r? : Option (BitVec 256)) :
    simulateQ (fig8ImplH1 fig qepF) (SM.transmitQuery (St := SimFig8St Pt) Q m r?) =
      SM.transmitImpl fig (2 + 1) qepF (Q, m, r?) := by
  simp [fig8ImplH1, SM.transmitQuery, SM.oracleImpl]

omit [Zero Pt] [SampleableType PQC] in
private theorem fig8ImplH1_challQuery
    (fig : SMScheme (RootKey × BitVec 256) (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt))
    (qepF : ℕ) (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (r? : Option (BitVec 256)) :
    simulateQ (fig8ImplH1 fig qepF) (SM.challQuery (St := SimFig8St Pt) Q m₀ m₁ r?) =
      SM.challImpl fig (2 + 1) qepF SM.Config.h1 (Q, m₀, m₁, r?) := by
  simp [fig8ImplH1, SM.challQuery, SM.oracleImpl]

omit [Zero Pt] [SampleableType PQC] in
private theorem fig8ImplH1_deliverQuery
    (fig : SMScheme (RootKey × BitVec 256) (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt))
    (qepF : ℕ) (Q : Party) (c : SimFig8C Pt) :
    simulateQ (fig8ImplH1 fig qepF) (SM.deliverQuery (St := SimFig8St Pt) Q c) =
      SM.deliverImpl fig SM.Config.h1 (Q, c) := by
  simp [fig8ImplH1, SM.deliverQuery, SM.oracleImpl]

omit [Zero Pt] [SampleableType PQC] in
private theorem fig8ImplH1_injectQuery
    (fig : SMScheme (RootKey × BitVec 256) (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt))
    (qepF : ℕ) (Q : Party) (c : SimFig8C Pt) :
    simulateQ (fig8ImplH1 fig qepF) (SM.injectQuery (St := SimFig8St Pt) Q c) =
      SM.injectImpl fig (2 + 1) qepF SM.Config.h1 (Q, c) := by
  simp [fig8ImplH1, SM.injectQuery, SM.oracleImpl]

omit [Zero Pt] [SampleableType PQC] in
private theorem fig8ImplH1_corrQuery
    (fig : SMScheme (RootKey × BitVec 256) (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt))
    (qepF : ℕ) (Q : Party) :
    simulateQ (fig8ImplH1 fig qepF) (SM.corrQuery (St := SimFig8St Pt) Q) =
      SM.corrImpl (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (C := SimFig8C Pt) Q := by
  simp [fig8ImplH1, SM.corrQuery, SM.oracleImpl]

private abbrev ProbeSimM (PQ Pt : Type) (ℓ : ℕ) :=
  StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ)

private def runProbeM {α : Type} (x : ProbeSimM PQ Pt ℓ α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool) :
    ProbComp ((α × LibsignalToModularSchemeSimState PQ Pt ℓ) ×
      (GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)) :=
  (x.run sC).run gh

private def runKemFailM {F : ShaCompress} {α : Type}
    (x : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailSimM PQ Pt F ℓ α)
    (s : LibsignalToModularSchemeSimState PQ Pt ℓ × (GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool) ×
      CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState F) :
    ProbComp (α × (LibsignalToModularSchemeSimState PQ Pt ℓ ×
      (GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool) ×
      CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState F)) :=
  x.run s

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem runProbeM_pure {α : Type} (a : α) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool) :
    runProbeM (pure a) sC gh = pure ((a, sC), gh) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem runProbeM_guardC_neg {α : Type}
    (act : ProbeSimM PQ Pt ℓ (Option α))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (h : ¬sC.base.stopped = true) :
    runProbeM (LibsignalSimC.guardC act) sC gh = runProbeM act sC gh := by
  unfold runProbeM LibsignalSimC.guardC
  simp [h]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem runProbeM_get_bind {α : Type}
    (k : LibsignalToModularSchemeSimState PQ Pt ℓ → ProbeSimM PQ Pt ℓ α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool) :
    runProbeM (get >>= k) sC gh = runProbeM (k sC) sC gh := rfl

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem runKemFailM_runProbeStep (qep : ℕ) {α : Type}
    (step : ProbeSimM PQ Pt ℓ α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    runKemFailM (CryptoGames.LibsignalSM.Proofs.Refinement.runProbeStep
      P ℓ Dh encPt encT decT idOf lam qep step) (sC, gh, tr) =
      (do
        let ((a, sC'), gh') ← runProbeM step sC gh
        return (a, (sC', gh', tr))) := rfl
omit [Zero Pt] [SampleableType PQC] in
@[simp] private theorem probeHook_lift_run
    (fig : SMScheme (RootKey × BitVec 256) (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt)) (qepF : ℕ)
    {α : Type}
    (x : OracleComp (unifSpec +
      SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) α)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool) :
    ((probeHook fig qepF).lift x).run gh =
      (do
        let (a, g') ← (simulateQ (fig8ImplH1 fig qepF) x).run gh.1
        return (a, (g', gh.2))) := rfl

omit [Zero Pt] [SampleableType PQC] in
@[simp] private theorem zoomB_probe_run
    (fig : SMScheme (RootKey × BitVec 256) (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt)) (qepF : ℕ)
    {α : Type}
    (x : StateT (SimState PQ Pt ℓ)
      (OracleComp (unifSpec +
        SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool) :
    ((runOnBaseState (H := probeHook fig qepF) x).run sC).run gh =
      (do
        let ((a, s'), g') ← (simulateQ (fig8ImplH1 fig qepF) (x.run sC.base)).run gh.1
        return ((a, { sC with base := s' }), (g', gh.2))) := by
  change ((probeHook fig qepF).lift (x.run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })).run gh = _
  simp only [StateT.run_bind, StateT.run_pure, probeHook_lift_run, bind_assoc, pure_bind]

omit [Zero Pt] [SampleableType PQC] in
@[simp] private theorem liftC_probe_run
    (fig : SMScheme (RootKey × BitVec 256) (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt)) (qepF : ℕ)
    {α : Type}
    (x : OracleComp (unifSpec +
      SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool) :
    ((LibsignalSimC.liftC (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (H := probeHook fig qepF) x).run sC).run
        gh =
      (do
        let (a, g') ← (simulateQ (fig8ImplH1 fig qepF) x).run gh.1
        return ((a, sC), (g', gh.2))) := by
  unfold LibsignalSimC.liftC
  simp only [StateT.run_bind, StateT.run_pure, stateT_lift_run,
    probeHook_lift_run, bind_assoc, pure_bind]

private def probeStateProj (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    {α : Type}
    (r : (α × LibsignalToModularSchemeSimState PQ Pt ℓ) ×
      (GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)) :
    α × (LibsignalToModularSchemeSimState PQ Pt ℓ × KemExtraRaw PQ PQC Pt ℓ) :=
  (r.1.1, (r.1.2, kemExtraEnc P r.2.1 tr))

private def kemStateProj
    (s : LibsignalToModularSchemeSimState PQ Pt ℓ × (GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool) ×
      CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F) :
    LibsignalToModularSchemeSimState PQ Pt ℓ × KemExtraRaw PQ PQC Pt ℓ :=
  (s.1, kemExtraEnc P s.2.1.1 s.2.2)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem runProbeM_ite_modify_amb {α : Type} (c : Bool) (k : ProbeSimM PQ Pt ℓ α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool) :
    runProbeM (if c then
        (modify (fun sC : LibsignalToModularSchemeSimState PQ Pt ℓ =>
          { sC with base := { sC.base with amb := sC.base.amb + 1 } }) >>= fun _ => k)
      else k) sC gh =
      runProbeM k { sC with base := if c then { sC.base with amb := sC.base.amb + 1 } else sC.base }
        gh := by
  cases c <;> rfl

private theorem semCorrHook_kemFail_eq (L qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (Q : Party)
    (hTrans : gh.1.trans.length ≤ L) (hChall : gh.1.chall.length ≤ L)
    (hComp : gh.1.comp.dedup.length ≤ L)
    (hCompU : ∃ U : List SM.Pos, U.length ≤ L ∧ CountLe gh.1.comp.dedup U ∧
      ∀ r ∈ gh.1.trans, r.pos ∈ U) :
    semCorrHook P Dh encT
      (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
      sC (kemExtraEnc P gh.1 tr) Q =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      probeStateProj P tr <$>
        runProbeM (LibsignalSimC.guardC (LibsignalSimC.simCorrC (P := P) (encT := encT)
          (H := probeHook fig (qep + 1)) Dh Q)) sC gh := by
  dsimp only []
  by_cases hstop : sC.base.stopped = true
  · unfold semCorrHook runProbeM LibsignalSimC.guardC; simp [hstop, probeStateProj]
  · rw [runProbeM_guardC_neg _ sC gh hstop]
    unfold semCorrHook LibsignalSimC.simCorrC
    rw [runProbeM_get_bind]
    have hcond : (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
        inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) =
      (sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
        inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) := by
      simp [hstop]
    rw [hcond]
    by_cases href : (sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
        inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
    · simp [href, runProbeM_pure, probeStateProj]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, runProbeM,
        StateT.run_bind, liftC_probe_run, fig8ImplH1_corrQuery,
        kemFailSemHook_onCr_eq P Dh encPt encT decT lam K toKemCoins L qep B Q gh.1 tr
          hTrans hChall hComp hCompU,
        bind_map_left, map_bind, pure_bind, bind_assoc]
      refine bind_congr fun ⟨res, g'⟩ => ?_
      rcases res with _ | fig8st
      · simp [probeStateProj]
      · rcases fig8st.γ with _ | x <;> rfl

private theorem semFwdAnswerHook_kemFail_eq (L qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hTrans : gh.1.trans.length ≤ L) (hChall : gh.1.chall.length ≤ L)
    (hComp : gh.1.comp.dedup.length ≤ L)
    (hc' : c'.1.1 ≤ B ∧ c'.2.1 ≤ B) :
    semFwdAnswerHook P Dh encPt encT lam
      (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
      qep sC (kemExtraEnc P gh.1 tr) Q w isDel ci? Tpk pq' c' =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      probeStateProj P tr <$>
        runProbeM (fwdAnswerC (qep := qep) (fig := fig) (fs := fs)
          (H := probeHook fig (qep + 1)) Q w isDel ci? Tpk pq' c') sC gh := by
  unfold semFwdAnswerHook runProbeM fwdAnswerC
  simp only [StateT.run_bind, zoomB_probe_run, fwd_run_eq, bind_assoc]
  split_ifs <;>
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      fig8ImplH1_deliverQuery, fig8ImplH1_injectQuery,
      kemFailSemHook_onDl_eq P Dh encPt encT decT lam K toKemCoins L qep B Q c' gh.1 tr
        hTrans hChall hComp hc'.1 hc'.2,
      kemFailSemHook_onIj_eq P Dh encPt encT decT lam K toKemCoins L qep B Q c' gh.1 tr
        hTrans hChall hComp hc'.1 hc'.2,
      bind_map_left, map_bind, pure_bind, bind_assoc] <;>
    (refine bind_congr fun ⟨res, g'⟩ => ?_;
     rcases res with _ | (_ | ⟨t, i, pm⟩) <;> simp [onAnswer_run_eq_pure, probeStateProj])

private theorem semResyncHook_kemFail_eq (L qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hTrans : gh.1.trans.length ≤ L) (hChall : gh.1.chall.length ≤ L)
    (hComp : gh.1.comp.dedup.length ≤ L)
    (hc : c.1.1 ≤ B ∧ c.2.1 ≤ B) :
    semResyncHook P Dh encPt encT lam
      (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
      qep sC (kemExtraEnc P gh.1 tr) Q w ci? Tpk pq' c r =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      probeStateProj P tr <$>
        runProbeM (resyncC (qep := qep) (fig := fig) (fs := fs)
          (H := probeHook fig (qep + 1)) Q w ci? Tpk pq' c r) sC gh := by
  unfold semResyncHook runProbeM resyncC
  rcases r with _ | ⟨t, i, ⟨pub, m'⟩⟩
  · simp [probeStateProj]
  · simp only [StateT.run_bind, liftC_probe_run, fig8ImplH1_deliverQuery,
      kemFailSemHook_onDl_eq P Dh encPt encT decT lam K toKemCoins L qep B Q c gh.1 tr
        hTrans hChall hComp hc.1 hc.2,
      bind_map_left, map_bind, pure_bind, bind_assoc]
    refine bind_congr fun ⟨res, g'⟩ => ?_
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp [zoomB_probe_run, onAccept_run_eq_pure, probeStateProj]

private theorem semFwdEvictHook_kemFail_eq (L qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hTrans : gh.1.trans.length ≤ L) (hChall : gh.1.chall.length ≤ L)
    (hComp : gh.1.comp.dedup.length ≤ L)
    (hc' : c'.1.1 ≤ B ∧ c'.2.1 ≤ B) :
    semFwdEvictHook P Dh encPt encT lam
      (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
      qep sC (kemExtraEnc P gh.1 tr) Q w isDel Tpk pq' c' =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      probeStateProj P tr <$>
        runProbeM (fwdEvictC (qep := qep) (fig := fig) (fs := fs)
          (H := probeHook fig (qep + 1)) Q w isDel Tpk pq' c') sC gh := by
  unfold semFwdEvictHook fwdEvictC
  by_cases h : (isDel && !(sC.base.mir.safeInj 3)) = true
  · simp only [h, ↓reduceIte, runProbeM, StateT.run_bind, StateT.run_get, pure_bind]; rfl
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rw [semFwdAnswerHook_kemFail_eq P Dh encPt encT decT lam K toKemCoins L qep B
      sC gh tr Q w isDel none Tpk pq' c' hTrans hChall hComp hc']
    simp only [runProbeM, StateT.run_bind, StateT.run_get, pure_bind, h, Bool.false_eq_true,
      ↓reduceIte]

private theorem semFwdHook_kemFail_eq (L qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hTrans : gh.1.trans.length ≤ L) (hChall : gh.1.chall.length ≤ L)
    (hComp : gh.1.comp.dedup.length ≤ L)
    (hc : ∀ c, honestC = some c → c.1.1 ≤ B ∧ c.2.1 ≤ B)
    (hc' : c'.1.1 ≤ B ∧ c'.2.1 ≤ B) :
    semFwdHook P Dh encPt encT lam
      (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
      qep B sC (kemExtraEnc P gh.1 tr) Q w isDel ci? Tpk pq' honestC c' =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      probeStateProj P tr <$>
        runProbeM (LibsignalSimC.fwdC (P := P) (qep := qep) (fig := fig) (fs := fs)
          (H := probeHook fig (qep + 1)) Q w isDel ci? Tpk pq' honestC c') sC gh := by
  unfold semFwdHook LibsignalSimC.fwdC
  rcases honestC with _ | c
  · dsimp only []
    rw [semFwdAnswerHook_kemFail_eq P Dh encPt encT decT lam K toKemCoins L qep B
      sC gh tr Q w isDel ci? Tpk pq' c' hTrans hChall hComp hc']
    simp [runProbeM]
  · dsimp only []
    have hcond : (!(decide (c = c')) && (isDel && !(sC.base.mir.safeInj 3))) =
        (decide (c ≠ c') && isDel && !(sC.base.mir.safeInj 3)) := by
      rw [decide_not, Bool.and_assoc]
    rw [hcond]
    by_cases h : (decide (c ≠ c') && isDel && !(sC.base.mir.safeInj 3)) = true
    · simp only [h, ↓reduceIte, evalCKClamp_eq_evalCK P Dh encPt encT lam B sC Q w c c' hc'.1 hc'.2]
      rcases heval : predictReceiveWithSnapshots
          (fig := lFig8 Dh encPt P.C P.codec ℓ encT
            (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
          (fs := lFS P.C P.codec ℓ encT
            (fun R => if R == Party.A then P.idA else P.idB) 25000)
          P sC Q w c c' with _ | r
      · simp only [h, ↓reduceIte, heval, runProbeM, StateT.run_bind, StateT.run_get, pure_bind]
        rfl
      · dsimp only []
        rw [semResyncHook_kemFail_eq P Dh encPt encT decT lam K toKemCoins L qep B
          sC gh tr Q w ci? Tpk pq' c r hTrans hChall hComp (hc c rfl)]
        simp only [runProbeM, StateT.run_bind, StateT.run_get, pure_bind, h, ↓reduceIte, heval]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [semFwdAnswerHook_kemFail_eq P Dh encPt encT decT lam K toKemCoins L qep B
        sC gh tr Q w isDel ci? Tpk pq' c' hTrans hChall hComp hc']
      simp only [runProbeM, StateT.run_bind, StateT.run_get, pure_bind, h, Bool.false_eq_true,
        ↓reduceIte]

private theorem semRecvHook_kemFail_eq (L qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (hB : 25001 ≤ B)
    (hep : sC.base.mir.epoch Q + 1 ≤ B)
    (hch : ∀ g ∈ sC.base.chains Q, g.epoch ≤ B)
    (hlast : 2 ^ 32 ≤ B ∨ ∀ g ∈ sC.base.chains Q, g.last + 25001 ≤ B)
    (hhonest : ∀ wc ∈ sC.base.honest, wc.2.1.1 ≤ B ∧ wc.2.2.1 ≤ B)
    (hTrans : gh.1.trans.length ≤ L) (hChall : gh.1.chall.length ≤ L)
    (hComp : gh.1.comp.dedup.length ≤ L) :
    semRecvHook P Dh encPt encT decT lam
      (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
      qep B sC (kemExtraEnc P gh.1 tr) Q w isDel =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      probeStateProj P tr <$>
        runProbeM (LibsignalSimC.guardC (LibsignalSimC.simRecvC (P := P) (encT := encT)
          (decT := decT) (qep := qep) (fig := fig) (fs := fs)
          (H := probeHook fig (qep + 1)) Q w isDel)) sC gh := by
  dsimp only []
  have hhon : ∀ c,
      (sC.base.honest.find? fun wc =>
        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c →
      c.1.1 ≤ B ∧ c.2.1 ≤ B := by
    intro c hc
    rw [Option.map_eq_some_iff] at hc
    rcases hc with ⟨wc, hmem, rfl⟩
    exact hhonest wc (List.mem_of_find?_eq_some hmem)
  by_cases hstop : sC.base.stopped = true
  · unfold semRecvHook runProbeM LibsignalSimC.guardC; simp [hstop, probeStateProj]
  · rw [runProbeM_guardC_neg _ sC gh hstop]
    unfold semRecvHook LibsignalSimC.simRecvC
    have hcond : (sC.base.stopped || sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
          !(sC.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) =
      (sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
          !(sC.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) := by
      simp [hstop]
    rw [hcond, runProbeM_get_bind]
    by_cases hwin : (sC.base.mir.win || (isDel && (sC.base.mir.inTransit Q.other w).isNone)) = true
    · rcases Bool.or_eq_true_iff.mp hwin with hw | hd
      · simp [hw, runProbeM_pure, probeStateProj]
      · simp [hd, runProbeM_pure, probeStateProj]
    · rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hwin) with ⟨hw, hd⟩
      simp only [hw, hd, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      by_cases hinj : (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
          !(sC.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w))) = true
      · simp [hinj, runProbeM_pure, probeStateProj]
      · simp only [hinj, Bool.false_eq_true, ↓reduceIte]
        unfold simParseRecvC
        rw [partyDec_partyEnc]
        by_cases hlen : w.length < 9
        · simp [hlen, runProbeM_pure, probeStateProj]
        · simp only [hlen, ↓reduceIte]
          rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
            _ | ⟨h, rest⟩
          · simp [runProbeM_pure, probeStateProj]
          · cases haddr : addressCheckPasses h.addresses (P.expectedAddrs Q)
            · simp [haddr, runProbeM_pure, probeStateProj]
            · cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet
              · dsimp only []
                simp only [haddr, hpan, Bool.not_true, Bool.false_or, Bool.false_eq_true,
                  ↓reduceIte]
                rcases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with _ | ⟨pq', salt⟩
                · simp [runProbeM_pure, probeStateProj]
                · have hlt : h.counter.toNat < 2 ^ 32 := h.counter.isLt
                  have hmin : min (h.counter.toNat + 1) (2 ^ 32) = h.counter.toNat + 1 :=
                    Nat.min_eq_left (by omega)
                  dsimp only []
                  simp only [hmin]
                  rcases hfind : (sC.base.chains Q).findIdx?
                      (fun g => g.key == some h.senderRatchetKey) with _ | ci <;>
                    simp only [hfind]
                  · by_cases hev : (((sC.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                          (fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true &&
                      ((sC.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                          (fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true) = true
                    · simp only [hev, ↓reduceIte, runProbeM_pure, map_pure, probeStateProj]
                    · simp only [hev, Bool.false_eq_true, ↓reduceIte]
                      by_cases hT0 : (decT h.senderRatchetKey == some 0) = true
                      · simp [hT0, runProbeM_pure, probeStateProj]
                      · simp only [hT0, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel,
                          runProbeM_ite_modify_amb]
                        by_cases hexit : (inReceiveOnlyEpoch sC.base.mir Q ||
                            decide (25000 < h.counter.toNat) ||
                            decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
                        · simp only [hexit, ↓reduceIte, runProbeM_pure, map_pure, probeStateProj]
                        · simp only [hexit, Bool.false_eq_true, ↓reduceIte]
                          have h25000 : h.counter.toNat ≤ 25000 := by
                            simp only [Bool.not_eq_true, Bool.or_eq_false_iff,
                              decide_eq_false_iff_not] at hexit
                            omega
                          rcases hT : decT h.senderRatchetKey with _ | T
                          · simp only [runProbeM_pure, map_pure, probeStateProj]
                          · dsimp only []
                            by_cases hev1 : (((sC.base.honest.find? fun wc =>
                                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                                  (fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) ==
                                    some true) = true
                            · simp only [hev1, ↓reduceIte]
                              exact semFwdEvictHook_kemFail_eq P Dh encPt encT decT lam K
                                toKemCoins L qep B _ gh tr Q w isDel h.senderRatchetKey pq' _
                                hTrans hChall hComp ⟨hep, by dsimp only []; omega⟩
                            · simp only [hev1, Bool.false_eq_true, ↓reduceIte]
                              refine semFwdHook_kemFail_eq P Dh encPt encT decT lam K
                                toKemCoins L qep B _ gh tr Q w isDel none h.senderRatchetKey pq'
                                _ _ hTrans hChall hComp hhon ?_
                              rcases hfc : (sC.base.honest.find? fun wc =>
                                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) with
                                _ | c <;> simp only [hfc]
                              · exact ⟨hep, by omega⟩
                              · split_ifs with hs
                                · exact hhon c hfc
                                · exact ⟨hep, by dsimp only []; omega⟩
                  · by_cases hrej :
                        ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects
                          (h.counter.toNat + 1) = true
                    · simp only [hrej, ↓reduceIte, runProbeM_pure, map_pure, probeStateProj]
                    · simp only [hrej, Bool.false_eq_true, ↓reduceIte]
                      have hgep : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch ≤ B :=
                        getD_chains_epoch_le (sC.base.chains Q) ci B hch
                      have hgi : h.counter.toNat + 1 ≤ B := by
                        rcases hlast with hB32 | hgl
                        · omega
                        · have hr := rejects_eq_false_le _ _ (Bool.eq_false_iff.mpr hrej)
                          have hl := getD_chains_last_le (sC.base.chains Q) ci B hB hgl
                          omega
                      refine semFwdHook_kemFail_eq P Dh encPt encT decT lam K toKemCoins
                        L qep B sC gh tr Q w isDel (some ci) h.senderRatchetKey pq'
                        _ _ hTrans hChall hComp hhon ?_
                      rcases hfc : (sC.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) with _ | c <;>
                        simp only [hfc]
                      · exact ⟨hgep, hgi⟩
                      · split_ifs with hs
                        · exact hhon c hfc
                        · exact ⟨hgep, hgi⟩
              · simp [haddr, hpan, runProbeM_pure, probeStateProj]
private theorem semSendHook_kemFail_postCoins_eq
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (L qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s₁ : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ))
    (rq : BitVec 512) (rc : Option (BitVec 256))
    (htcur : (gh.1.st Q).tcur + 1 ≤ B) (hFresh : PosFreshInv gh.1) :
    let sh := kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K id L qep B
    let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then
      BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
    (do
      let (exOk, exFail) ← sh.onSendCoins Q rq (kemExtraEnc P gh.1 tr)
      match mkPub (P := P) sC.base Q rq pn with
      | none => return (none, (sC, exFail))
      | some (pq', pub) =>
        (match chal with
          | none => sh.onTr Q (pub, m₀) rc exOk
          | some m₁ => sh.onCh Q (pub, m₀) (pub, m₁) rc exOk) >>= fun (res, ex₂) =>
        match res with
        | none => pure (none, (sC, exFail))
        | some c =>
          let sC' := scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ chal.isSome pq' pn c
          pure (some (toWire c), (sC', ex₂))) =
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then
      BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
    let tr' := CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend P.C.F K tr Q rq
    Prod.map id (kemStateProj P) <$>
      (match mkPub (P := P) sC.base Q rq pn with
      | none => do
        set (sC, gh, { tr with cand := tr'.cand })
        return none
      | some (pq', pub) => do
        let qFig := match chal with
          | none => SM.transmitQuery (St := SimFig8St Pt) Q (pub, m₀) rc
          | some m₁ => SM.challQuery (St := SimFig8St Pt) Q (pub, m₀) (pub, m₁) rc
        let (res, gh') ← ((probeHook fig (qep + 1)).lift qFig).run gh
        match res with
        | none =>
          set (sC, gh', { tr with cand := tr'.cand })
          return none
        | some c =>
          let w := toWire c
          let rec' : Record (Plain ℓ) (List (BitVec 8)) :=
            ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
          let mir' := s₁.record 3 Q () rec' chal.isSome
          let base' : SimState PQ Pt ℓ :=
            { sC.base with
              mir := mir'
              pq := Function.update sC.base.pq Q pq'
              pn := Function.update sC.base.pn Q pn
              honest := (w, c) :: sC.base.honest }
          let sent' := match (sC.kept Q).full, base'.honest.head? with
            | some st, some (_, c₀) =>
              if st.id.sendsIn (st.tcur + 1) then sC.sent
              else match st.vS with
                | some v => (c₀, v) :: sC.sent
                | none => sC.sent
            | _, _ => sC.sent
          let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ :=
            { sC with
              base := base'
              kept := Function.update sC.kept Q (Kept.send (fig := fig) (sC.kept Q))
              sent := sent' }
          set (sC', gh', tr')
          return some w :
        CryptoGames.LibsignalSM.Proofs.Refinement.KemFailSimM PQ Pt P.C.F ℓ
          (Option (List (BitVec 8)))).run (sC, gh, tr) := by
  dsimp only []
  rw [kemFailSemHook_onSendCoins_eq P Dh encPt encT decT lam K id L qep B Q rq gh.1 tr, pure_bind]
  dsimp only [id_eq]
  rcases hpub : mkPub (P := P) sC.base Q rq
      (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
       else sC.base.pn Q) with _ | ⟨pq', pub⟩
  · simp [kemStateProj]
  · dsimp only []
    cases chal with
    | none =>
      simp only [kemFailSemHook_onTr_eq P Dh encPt encT decT lam K id L qep B Q (pub, m₀) rc gh.1
          (CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend P.C.F K tr Q rq) htcur hFresh,
        probeHook_lift_run, fig8ImplH1_transmitQuery, StateT.run_bind, stateT_liftM_probComp_run,
        bind_map_left, map_bind, pure_bind, bind_assoc]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨res, g'⟩ hmem => ?_
      rcases res with _ | c
      · have hg' := transmitImpl_run_none_eq _ 3 (qep + 1) Q (pub, m₀) rc gh.1 g' hmem
        subst hg'
        simp [kemStateProj]
      · rcases hkept : (sC.kept Q).full with _ | st <;>
          simp [scPostSendPure, hkept, kemStateProj]
    | some m₁ =>
      simp only [kemFailSemHook_onCh_eq P Dh encPt encT decT lam K id L qep B Q (pub, m₀) (pub, m₁)
          rc gh.1 (CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend P.C.F K tr Q rq)
          htcur hFresh,
        probeHook_lift_run, fig8ImplH1_challQuery, StateT.run_bind, stateT_liftM_probComp_run,
        bind_map_left, map_bind, pure_bind, bind_assoc]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨res, g'⟩ hmem => ?_
      rcases res with _ | c
      · have hg' := challImpl_run_none_eq _ 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁)
          rc gh.1 g' hmem
        subst hg'
        simp [kemStateProj]
      · rcases hkept : (sC.kept Q).full with _ | st <;>
          simp [scPostSendPure, hkept, kemStateProj]

private theorem semSendHook_kemFail_eq
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (toKemCoins : BitVec 512 → BitVec 512) (hto : toKemCoins = id)
    (L qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (htcur : (gh.1.st Q).tcur + 1 ≤ B) (hFresh : PosFreshInv gh.1) :
    semSendHook P Dh encPt encT lam
      (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
      qep sC (kemExtraEnc P gh.1 tr) Q m₀ chal r =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      Prod.map id (kemStateProj P) <$>
        runKemFailM (CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSendStep
          P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r) (sC, gh, tr) := by
  subst hto
  unfold semSendHook runKemFailM CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSendStep
    semDrawSendCoins
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases href : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) = true
  · simp [href, kemStateProj]
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · simp [kemStateProj]
    · dsimp only []
      by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp [hch, kemStateProj]
      · simp only [hch, Bool.false_eq_true, ↓reduceIte]
        have hbv : (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K id L qep B).sampleBv256 =
            ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) := rfl
        have hpqc : (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K id L qep B).samplePqc =
            ($ᵗ (BitVec 512) : ProbComp (BitVec 512)) := rfl
        rw [hbv, hpqc]
        rcases r with _ | rq
        · simp only [StateT.run_bind, stateT_liftM_probComp_run,
            pure_bind, bind_assoc, map_bind]
          refine bind_congr fun x => ?_
          exact semSendHook_kemFail_postCoins_eq P Dh encPt encT decT lam K L qep B
            sC s₁ gh tr Q m₀ chal x none htcur hFresh
        · simp only [bind_map_left, StateT.run_bind, stateT_liftM_probComp_run,
            pure_bind, bind_assoc, map_bind]
          refine bind_congr fun x => ?_
          exact semSendHook_kemFail_postCoins_eq P Dh encPt encT decT lam K L qep B
            sC s₁ gh tr Q m₀ chal rq (some x) htcur hFresh

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem probeStateProj_map_eq
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F) {α : Type}
    (p : ProbComp ((α × LibsignalToModularSchemeSimState PQ Pt ℓ) ×
      (GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool))) :
    probeStateProj P tr <$> p =
      Prod.map id (kemStateProj P) <$>
        (p >>= fun ⟨⟨a, sC'⟩, gh'⟩ => pure (a, (sC', gh', tr))) := by
  simp only [probeStateProj, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem runKemFailM_get_bind {F : ShaCompress} {α : Type}
    (k : (LibsignalToModularSchemeSimState PQ Pt ℓ × (GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool) ×
      CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState F) →
      CryptoGames.LibsignalSM.Proofs.Refinement.KemFailSimM PQ Pt F ℓ α)
    (s : LibsignalToModularSchemeSimState PQ Pt ℓ × (GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool) ×
      CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState F) :
    runKemFailM (get >>= k) s = runKemFailM (k s) s := rfl

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem runKemFailM_runProbeStep_bind
    (idOf : Party → IdentityKey) (qep : ℕ) {α β : Type}
    (step : ProbeSimM PQ Pt ℓ α)
    (k : α → CryptoGames.LibsignalSM.Proofs.Refinement.KemFailSimM PQ Pt P.C.F ℓ β)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F) :
    runKemFailM (CryptoGames.LibsignalSM.Proofs.Refinement.runProbeStep
      P ℓ Dh encPt encT decT idOf lam qep step >>= k) (sC, gh, tr) =
      (do
        let ((a, sC'), gh') ← runProbeM step sC gh
        runKemFailM (k a) (sC', gh', tr)) := by
  unfold runKemFailM
  rw [StateT.run_bind]
  change ((do
    let ((a, sC'), gh') ← runProbeM step sC gh
    return (a, (sC', gh', tr))) >>= fun p =>
      runKemFailM (k p.1) p.2) = _
  simp only [bind_assoc, pure_bind]
  rfl

private theorem semHandleHook_kemFail_eq
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (toKemCoins : BitVec 512 → BitVec 512) (hto : toKemCoins = id)
    (L qep B : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (hB : 25001 ≤ B)
    (hep : ∀ Q : Party, sC.base.mir.epoch Q + 1 ≤ B)
    (hch : ∀ Q : Party, ∀ g ∈ sC.base.chains Q, g.epoch ≤ B)
    (hlast : ∀ Q : Party, 2 ^ 32 ≤ B ∨ ∀ g ∈ sC.base.chains Q, g.last + 25001 ≤ B)
    (hhonest : ∀ wc ∈ sC.base.honest, wc.2.1.1 ≤ B ∧ wc.2.2.1 ≤ B)
    (htcur : ∀ Q : Party, (gh.1.st Q).tcur + 1 ≤ B)
    (hFresh : PosFreshInv gh.1)
    (hTrans : gh.1.trans.length ≤ L) (hChall : gh.1.chall.length ≤ L)
    (hComp : gh.1.comp.dedup.length ≤ L)
    (hCompU : ∃ U : List SM.Pos, U.length ≤ L ∧ CountLe gh.1.comp.dedup U ∧
      ∀ r ∈ gh.1.trans, r.pos ∈ U) :
    semHandleHook P Dh encPt encT decT lam
      (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
      qep B t sC (kemExtraEnc P gh.1 tr) =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      Prod.map id (kemStateProj P) <$>
        runKemFailM (CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSimImpl
          P K ℓ Dh encPt encT decT idOf lam qep (.inr t)) (sC, gh, tr) := by
  rcases t with (((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
  · exact semSendHook_kemFail_eq P Dh encPt encT decT lam K toKemCoins hto L qep B
      sC gh tr Q m none r (htcur Q) hFresh
  · exact semSendHook_kemFail_eq P Dh encPt encT decT lam K toKemCoins hto L qep B
      sC gh tr Q m₀ (some m₁) r (htcur Q) hFresh
  · let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    change (do
      let (rr, (sC₁, ex₁)) ← semRecvHook P Dh encPt encT decT lam
        (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
        qep B sC (kemExtraEnc P gh.1 tr) Q w true
      let j? := sC.base.honest.reverse.findIdx?
        (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
      let ex₂ ←
        (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B).onDeliverPost
          Q j? rr ex₁
      pure (rr, (sC₁, ex₂))) =
      Prod.map id (kemStateProj P) <$>
        runKemFailM (do
          let (sC₀, _, _) ← get
          let res ← CryptoGames.LibsignalSM.Proofs.Refinement.runProbeStep
            P ℓ Dh encPt encT decT idOf lam qep
            (LibsignalSimC.guardC
              (LibsignalSimC.simRecvC P encT decT qep fig fs (probeHook fig (qep + 1)) Q w true))
          let j? := sC₀.base.honest.reverse.findIdx?
            (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
          match res, j? with
          | some (.accepted _ _ _), some j => do
            modify (fun (sC', gh', tr') =>
              (sC', gh', CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailDeliver
                P.C.F K tr' Q j))
            return res
          | _, _ => return res) (sC, gh, tr)
    rw [runKemFailM_get_bind, runKemFailM_runProbeStep_bind,
      semRecvHook_kemFail_eq P Dh encPt encT decT lam K toKemCoins L qep B sC gh tr Q w true
        hB (hep Q) (hch Q) (hlast Q) hhonest hTrans hChall hComp]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun ⟨⟨res, sC'⟩, gh'⟩ => ?_
    dsimp only [probeStateProj]
    rw [kemFailSemHook_onDeliverPost_eq P Dh encPt encT decT lam K toKemCoins L qep B
      Q _ res gh'.1 tr]
    rcases res with _ | (_ | ⟨t', i', m'⟩) <;>
      cases sC.base.honest.reverse.findIdx?
        (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) <;>
      simp [runKemFailM, kemStateProj]
  · let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    change semRecvHook P Dh encPt encT decT lam
        (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
        qep B sC (kemExtraEnc P gh.1 tr) Q w false =
      Prod.map id (kemStateProj P) <$>
        runKemFailM (CryptoGames.LibsignalSM.Proofs.Refinement.runProbeStep
          P ℓ Dh encPt encT decT idOf lam qep
          (LibsignalSimC.guardC
            (LibsignalSimC.simRecvC P encT decT qep fig fs (probeHook fig (qep + 1)) Q w false)))
          (sC, gh, tr)
    rw [runKemFailM_runProbeStep,
      semRecvHook_kemFail_eq P Dh encPt encT decT lam K toKemCoins L qep B sC gh tr Q w false
        hB (hep Q) (hch Q) (hlast Q) hhonest hTrans hChall hComp,
      probeStateProj_map_eq]
  · let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    change semCorrHook P Dh encT
        (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
        sC (kemExtraEnc P gh.1 tr) Q =
      Prod.map id (kemStateProj P) <$>
        runKemFailM (CryptoGames.LibsignalSM.Proofs.Refinement.runProbeStep
          P ℓ Dh encPt encT decT idOf lam qep
          (LibsignalSimC.guardC
            (LibsignalSimC.simCorrC P encT (probeHook fig (qep + 1)) Dh Q)))
          (sC, gh, tr)
    rw [runKemFailM_runProbeStep,
      semCorrHook_kemFail_eq P Dh encPt encT decT lam K toKemCoins L qep B sC gh tr Q
        hTrans hChall hComp hCompU,
      probeStateProj_map_eq]

omit [SampleableType PQC] in
private theorem simulateQ_kemFailOracle_eq_of_inv
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (toKemCoins : BitVec 512 → BitVec 512) (hto : toKemCoins = id)
    (L qep B : ℕ) (hB : 25001 ≤ B)
    (Inv : ℕ → LibsignalToModularSchemeSimState PQ Pt ℓ →
      (GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool) →
      CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F → Prop)
    (hep : ∀ m sC gh tr, Inv (m + 1) sC gh tr → ∀ Q : Party, sC.base.mir.epoch Q + 1 ≤ B)
    (hch : ∀ m sC gh tr, Inv (m + 1) sC gh tr → ∀ Q : Party, ∀ g ∈ sC.base.chains Q, g.epoch ≤ B)
    (hlast : ∀ m sC gh tr, Inv (m + 1) sC gh tr →
      ∀ Q : Party, 2 ^ 32 ≤ B ∨ ∀ g ∈ sC.base.chains Q, g.last + 25001 ≤ B)
    (hhonest : ∀ m sC gh tr, Inv (m + 1) sC gh tr →
      ∀ wc ∈ sC.base.honest, wc.2.1.1 ≤ B ∧ wc.2.2.1 ≤ B)
    (htcur : ∀ m sC gh tr, Inv (m + 1) sC gh tr → ∀ Q : Party, (gh.1.st Q).tcur + 1 ≤ B)
    (hFresh : ∀ m sC gh tr, Inv (m + 1) sC gh tr → PosFreshInv gh.1)
    (hTrans : ∀ m sC gh tr, Inv (m + 1) sC gh tr → gh.1.trans.length ≤ L)
    (hChall : ∀ m sC gh tr, Inv (m + 1) sC gh tr → gh.1.chall.length ≤ L)
    (hComp : ∀ m sC gh tr, Inv (m + 1) sC gh tr → gh.1.comp.dedup.length ≤ L)
    (hCompU : ∀ m sC gh tr, Inv (m + 1) sC gh tr →
      ∃ U : List SM.Pos, U.length ≤ L ∧ CountLe gh.1.comp.dedup U ∧ ∀ r ∈ gh.1.trans, r.pos ∈ U)
    (hstep : ∀ m t sC gh tr, Inv (m + 1) sC gh tr →
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      ∀ r ∈ support (runKemFailM (CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSimImpl
          P K ℓ Dh encPt encT decT idOf lam qep (.inr t)) (sC, gh, tr)),
        Inv m r.2.1 r.2.2.1 r.2.2.2)
    {α : Type}
    (oa : OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
      α)
    (m : ℕ)
    (hm : oa.IsQueryBoundP
      (isGameQuery (G := SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))) m)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (hInv : Inv m sC gh tr) :
    (simulateQ (kemFailOracle P Dh encPt encT decT lam K toKemCoins L qep B) oa).run
        (sC, kemExtraEnc (PQC := BitVec 512) P gh.1 tr) =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      Prod.map id (kemStateProj (PQC := BitVec 512) P) <$>
        runKemFailM (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSimImpl
          P K ℓ Dh encPt encT decT idOf lam qep) oa) (sC, gh, tr) := by
  dsimp only []
  induction oa using OracleComp.inductionOn generalizing m sC gh tr with
  | pure a => rfl
  | query_bind qy u ih =>
    rw [isQueryBoundP_query_bind_iff] at hm
    rcases hm with ⟨hq0, hu⟩
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
      liftM, monadLift, MonadLift.monadLift]
    change _ = Prod.map id (kemStateProj (PQC := BitVec 512) P) <$>
      (runKemFailM (CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSimImpl
          P K ℓ Dh encPt encT decT (fun R => if R == Party.A then P.idA else P.idB) lam qep qy)
        (sC, gh, tr) >>=
        fun ⟨r, sC', gh', tr'⟩ =>
          runKemFailM (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSimImpl
            P K ℓ Dh encPt encT decT (fun R => if R == Party.A then P.idA else P.idB) lam qep)
            (u r)) (sC', gh', tr'))
    rw [map_bind]
    rcases qy with n | t
    · simp only [isGameQuery, ↓reduceIte] at hu
      have hinl :
          ((kemFailOracle P Dh encPt encT decT lam K toKemCoins L qep B (.inl n)).run
            (sC, kemExtraEnc (PQC := BitVec 512) P gh.1 tr) >>= fun p =>
            (simulateQ (kemFailOracle P Dh encPt encT decT lam K toKemCoins L qep B) (u p.1)).run
              p.2) =
          (query (spec := unifSpec) n >>= fun r =>
            (simulateQ (kemFailOracle P Dh encPt encT decT lam K toKemCoins L qep B) (u r)).run
              (sC, kemExtraEnc (PQC := BitVec 512) P gh.1 tr)) := by
        simp only [kemFailOracle, stateT_lift_run, bind_assoc, pure_bind]
        rfl
      have hinr :
          (runKemFailM (CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSimImpl
              P K ℓ Dh encPt encT decT (fun R => if R == Party.A then P.idA else P.idB) lam qep
              (.inl n)) (sC, gh, tr) >>= fun ⟨r, sC', gh', tr'⟩ =>
            Prod.map id (kemStateProj (PQC := BitVec 512) P) <$>
              runKemFailM (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSimImpl
                P K ℓ Dh encPt encT decT (fun R => if R == Party.A then P.idA else P.idB) lam qep)
                (u r)) (sC', gh', tr')) =
          (query (spec := unifSpec) n >>= fun r =>
            Prod.map id (kemStateProj (PQC := BitVec 512) P) <$>
              runKemFailM (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSimImpl
                P K ℓ Dh encPt encT decT (fun R => if R == Party.A then P.idA else P.idB) lam qep)
                (u r)) (sC, gh, tr)) := by
        change ((StateT.lift (query (spec := unifSpec) n)).run (sC, gh, tr) >>=
          fun ⟨r, sC', gh', tr'⟩ =>
            Prod.map id (kemStateProj (PQC := BitVec 512) P) <$>
              runKemFailM (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSimImpl
                P K ℓ Dh encPt encT decT (fun R => if R == Party.A then P.idA else P.idB) lam qep)
                (u r)) (sC', gh', tr')) = _
        simp only [stateT_lift_run, bind_assoc, pure_bind]
      rw [hinl, hinr]
      refine bind_congr fun r => ?_
      exact ih r m (hu r) sC gh tr hInv
    · simp only [isGameQuery, ↓reduceIte] at hq0 hu
      have hm_pos : 0 < m := hq0.resolve_left (by decide)
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hStep := semHandleHook_kemFail_eq P Dh encPt encT decT lam K toKemCoins hto L qep B
        t sC gh tr hB (hep m' sC gh tr hInv) (hch m' sC gh tr hInv) (hlast m' sC gh tr hInv)
        (hhonest m' sC gh tr hInv) (htcur m' sC gh tr hInv) (hFresh m' sC gh tr hInv)
        (hTrans m' sC gh tr hInv) (hChall m' sC gh tr hInv)
        (hComp m' sC gh tr hInv) (hCompU m' sC gh tr hInv)
      dsimp only [] at hStep
      change (semHandleHook P Dh encPt encT decT lam
        (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B)
        qep B t sC (kemExtraEnc (PQC := BitVec 512) P gh.1 tr) >>= _) = _
      rw [hStep]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨r, sC', gh', tr'⟩ hmem => ?_
      have hih := ih r m' (by simpa using hu r) sC' gh' tr'
        (hstep m' t sC gh tr hInv (r, (sC', gh', tr')) hmem)
      simpa only [Prod.map, id_eq, kemStateProj, map_eq_bind_pure_comp, Function.comp_def]
        using hih

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem evalDistEq_bind_bool_prod {α : Type}
    (f : Bool → BitVec 256 × BitVec 256 → ProbComp α) :
    (do
      let b ← $ᵗ Bool
      let k1 ← $ᵗ (BitVec 256)
      let k2 ← $ᵗ (BitVec 256)
      f b (k1, k2)) =ᵈ
    (do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      f b k) := by
  refine EvalDistEq.bind EvalDistEq.rfl fun b => ?_
  have hprod :
      (do
        let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        return (k1, k2)) =ᵈ
      ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :=
    EvalDistEq.of_forall_prEvent_eq fun p => by
      simpa only [prEvent_norm] using (SampleableType.prEvent_uniformSample_prod p).symm
  simpa only [bind_assoc, pure_bind] using EvalDistEq.bind hprod fun k => EvalDistEq.refl (f b k)

/-! ### Step-indexed clamp invariant -/

/-- Step-indexed clamp invariant on `s : SimState PQ Pt ℓ` for `m` remaining queries. -/
structure SimBaseClampInv (B m : ℕ) (s : SimState PQ Pt ℓ) : Prop where
  hep : ∀ Q : Party, s.mir.epoch Q + m + 1 ≤ B
  htrans : ∀ r ∈ s.mir.trans, r.pos.epoch + m + 1 ≤ B
  hch : ∀ Q : Party, ∀ g ∈ s.chains Q, g.epoch + m + 1 ≤ B
  hhonest : ∀ wc ∈ s.honest, wc.2.1.1 + m + 1 ≤ B ∧ wc.2.2.1 + m + 1 ≤ B

/-- Step-indexed clamp invariant on `gs : GameState` for `m` remaining queries. -/
structure Fig8GameClampInv (L B m : ℕ)
    (gs : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) : Prop where
  hmB : m + 3 ≤ B
  hmL : m ≤ L
  htcur : ∀ Q : Party, (gs.st Q).tcur + m + 1 ≤ B
  hvS : ∀ Q : Party, ∀ v, (gs.st Q).vS = some v → v.lastIndex + m + 1 ≤ B
  hFresh : PosFreshInv gs
  hTrans : gs.trans.length + m ≤ L
  hChall : gs.chall.length + m ≤ L
  hCompU : ∃ U : List SM.Pos, U.length + m ≤ L ∧
    (∀ p ∈ gs.comp, p ∈ U) ∧ (∀ r ∈ gs.trans, r.pos ∈ U)

/-- Combined step-indexed invariant on `(sC, gs)` for `m` remaining queries. -/
def SimGameClampInv (L B m : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gs : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) : Prop :=
  SimBaseClampInv B m sC.base ∧ Fig8GameClampInv L B m gs

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem SimBaseClampInv.mono {B m₁ m₂ : ℕ} {s : SimState PQ Pt ℓ}
    (hle : m₁ ≤ m₂) (h : SimBaseClampInv B m₂ s) : SimBaseClampInv B m₁ s where
  hep Q := by have := h.hep Q; omega
  htrans r hr := by have := h.htrans r hr; omega
  hch Q g hg := by have := h.hch Q g hg; omega
  hhonest wc hwc := by obtain ⟨h1, h2⟩ := h.hhonest wc hwc; exact ⟨by omega, by omega⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem Fig8GameClampInv.mono {L B m₁ m₂ : ℕ}
    {gs : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)}
    (hle : m₁ ≤ m₂) (h : Fig8GameClampInv L B m₂ gs) : Fig8GameClampInv L B m₁ gs where
  hmB := by have := h.hmB; omega
  hmL := by have := h.hmL; omega
  htcur Q := by have := h.htcur Q; omega
  hvS Q v hv := by have := h.hvS Q v hv; omega
  hFresh := h.hFresh
  hTrans := by have := h.hTrans; omega
  hChall := by have := h.hChall; omega
  hCompU := by
    rcases h.hCompU with ⟨U, hUL, hU1, hU2⟩
    exact ⟨U, by omega, hU1, hU2⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem Fig8GameClampInv.comp_dedup_le {L B m : ℕ}
    {gs : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)}
    (h : Fig8GameClampInv L B m gs) : gs.comp.dedup.length ≤ L := by
  rcases h.hCompU with ⟨U, hUL, hU1, _⟩
  exact (length_dedup_le_of_subset hU1).trans (by omega)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem Fig8GameClampInv.comp_u {L B m : ℕ}
    {gs : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)}
    (h : Fig8GameClampInv L B m gs) :
    ∃ U : List SM.Pos, U.length ≤ L ∧ CountLe gs.comp.dedup U ∧ ∀ r ∈ gs.trans, r.pos ∈ U := by
  rcases h.hCompU with ⟨U, hUL, hU1, hU2⟩
  exact ⟨U, by omega, countLe_dedup_of_subset hU1, hU2⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem epMgmt_bounds {St Msg C : Type}
    (s s₁ : GameState St Msg C) (Δ qep : ℕ) (Q : Party) (bad : Bool)
    (h : s.epMgmt Δ qep Q bad = some s₁) :
    (∀ R : Party, s₁.epoch R ≤ s.epoch R + 1) ∧
    s₁.trans = s.trans ∧ s₁.chall = s.chall ∧ s₁.comp = s.comp := by
  unfold GameState.epMgmt at h
  split_ifs at h with h1 h2 h3 h4 <;> injection h with h <;> subst h
  · refine ⟨fun R => ?_, rfl, rfl, rfl⟩
    by_cases hR : R = Q <;> simp [hR, GameState.leak]
  · refine ⟨fun R => ?_, rfl, rfl, rfl⟩
    by_cases hR : R = Q <;> simp [hR]
  · exact ⟨fun _ => Nat.le_add_right _ 1, rfl, rfl, rfl⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem accept_bounds {St Msg C : Type}
    (s : GameState St Msg C) (Q : Party) (st' : St) (pos : SM.Pos) :
    (∀ R : Party, (s.accept Q st' pos).epoch R ≤ max (s.epoch R) pos.epoch) ∧
    (∀ r ∈ (s.accept Q st' pos).trans, r ∈ s.trans) ∧
    (s.accept Q st' pos).trans.length ≤ s.trans.length ∧
    (s.accept Q st' pos).chall.length ≤ s.chall.length ∧
    (s.accept Q st' pos).comp.length ≤ s.comp.length := by
  dsimp only [GameState.accept, GameState.delete]
  refine ⟨fun R => ?_, fun r hr => (List.mem_filter.mp hr).1,
    List.length_filter_le _ _, List.length_filter_le _ _, List.length_filter_le _ _⟩
  by_cases hR : R = Q
  · subst hR; simp
  · simp [hR]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem afterCorr_bounds {St Msg C : Type}
    (s : GameState St Msg C) (Q : Party) :
    (s.afterCorr Q).st = s.st ∧
    (s.afterCorr Q).epoch = s.epoch ∧
    (s.afterCorr Q).trans = s.trans ∧
    (s.afterCorr Q).chall = s.chall ∧
    (s.afterCorr Q).comp.length ≤ s.trans.length + s.comp.length := by
  dsimp only [GameState.afterCorr, GameState.leak]
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  rw [List.length_append, List.length_map]
  exact Nat.add_le_add_right (List.length_filter_le _ _) _

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem lFig8_init_bounds (idOf : Party → IdentityKey) (k : RootKey × BitVec 256)
    (b : Bool) (Q : Party) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ((SM.initState fig k b).st Q).tcur = 0 ∧
    ∀ v, ((SM.initState fig k b).st Q).vS = some v → v.lastIndex = 0 := by
  dsimp only [SM.initState, lFig8, SM.Construction.scheme, SM.Construction.initParty,
    lFS, FSAEAD.fromAEADPRG]
  cases Q <;> refine ⟨rfl, fun v hv => ?_⟩
  · cases hv
  · injection hv with hv; subst hv; rfl

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem lFig8_send_bounds (idOf : Party → IdentityKey)
    (st : SimFig8St Pt) (m : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    (fig.send st m coins).1.tcur ≤ st.tcur + 1 ∧
    (fig.send st m coins).2.1.1 ≤ st.tcur + 1 ∧
    (∀ v', (fig.send st m coins).1.vS = some v' →
      v'.lastIndex ≤ 1 ∨ ∃ v, st.vS = some v ∧ v'.lastIndex = v.lastIndex + 1) ∧
    ((fig.send st m coins).2.2.1 ≤ 1 ∨
      ∃ v, st.vS = some v ∧ (fig.send st m coins).2.2.1 = v.lastIndex + 1) := by
  dsimp only [lFig8, SM.Construction.scheme, SM.Construction.send]
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · simp only [hs, ↓reduceIte, lFS, FSAEAD.fromAEADPRG]
    refine ⟨le_rfl, le_rfl, fun v' hv' => ?_, Or.inl le_rfl⟩
    injection hv' with hv'; subst hv'
    exact Or.inl le_rfl
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    cases hv : st.vS with
    | none =>
      refine ⟨Nat.le_add_right _ 1, Nat.le_add_right _ 1, fun v' hv' => ?_,
        Or.inl (Nat.zero_le 1)⟩
      rw [hv] at hv'; cases hv'
    | some v =>
      dsimp only [lFS, FSAEAD.fromAEADPRG]
      refine ⟨Nat.le_add_right _ 1, Nat.le_add_right _ 1, fun v' hv' => ?_, Or.inr ⟨v, rfl, rfl⟩⟩
      injection hv' with hv'; subst hv'
      exact Or.inr ⟨v, rfl, rfl⟩

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem lFig8_receive_bounds (idOf : Party → IdentityKey)
    (st st' : SimFig8St Pt) (c : SimFig8C Pt) (t i : ℕ) (m : LibsignalMsgPublicPart × Plain ℓ)
    (h : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c = some (st', t, i, m)) :
    t = c.1.1 ∧ i = c.2.1 ∧ t ≤ st.tcur + 1 ∧ st'.tcur ≤ st.tcur + 1 ∧ st'.vS = st.vS := by
  obtain ⟨rfl, rfl⟩ := lFig8_receive_epoch_index_eq P Dh encPt encT lam idOf st st' c t i m h
  refine ⟨rfl, rfl, ?_⟩
  dsimp only [lFig8, SM.Construction.scheme, SM.Construction.receive] at h
  split at h
  · cases h
  · rename_i h1
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at h1
    split at h
    · cases h
    · rename_i s₁ hs₁
      have hs₁_b : s₁.tcur ≤ st.tcur + 1 ∧ s₁.vS = st.vS := by
        split_ifs at hs₁ with heq
        · rcases hc12 : c.1.2 with _ | Tn <;> rw [hc12] at hs₁
          · cases hs₁
          · injection hs₁ with hs₁; subst hs₁
            exact ⟨h1.2, rfl⟩
        · injection hs₁ with hs₁; subst hs₁
          exact ⟨Nat.le_add_right _ 1, rfl⟩
      split at h
      · cases h
      · rename_i v _
        rcases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive v c.1 c.2 with
          _ | ⟨v', i', pm'⟩
        · rw [hfs] at h; cases h
        · rw [hfs] at h
          injection h with h
          injection h with hst' _
          subst hst'
          exact ⟨h1.2, hs₁_b.1, hs₁_b.2⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem simBaseClampInv_init (B q : ℕ) (pqA pqB : PQ) (hqB : q + 3 ≤ B) :
    SimBaseClampInv B q (initSim (Pt := Pt) (ℓ := ℓ) pqA pqB) where
  hep Q := by dsimp [initSim]; omega
  htrans r hr := by simp [initSim] at hr
  hch Q g hg := by
    cases Q <;> simp [initSim] at hg
    subst hg; dsimp; omega
  hhonest wc hwc := by simp [initSim] at hwc

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem fig8GameClampInv_init (idOf : Party → IdentityKey) (L B q : ℕ)
    (k : RootKey × BitVec 256) (b : Bool) (hqB : q + 3 ≤ B) (hqL : q ≤ L) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    Fig8GameClampInv L B q (SM.initState fig k b) where
  hmB := hqB
  hmL := hqL
  htcur Q := by
    rw [(lFig8_init_bounds P Dh encPt encT lam idOf k b Q).1]
    omega
  hvS Q v hv := by
    rw [(lFig8_init_bounds P Dh encPt encT lam idOf k b Q).2 v hv]
    omega
  hFresh := by
    dsimp only [SM.initState]
    exact PosFreshInv.init _ _
  hTrans := by simp [SM.initState, hqL]
  hChall := by simp [SM.initState, hqL]
  hCompU := by refine ⟨[], by simp [hqL], ?_, ?_⟩ <;> simp [SM.initState]

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem fig8GameClampInv_record (idOf : Party → IdentityKey) (L B m qep : ℕ)
    (gs s₁ : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (bad isChall : Bool) (msg : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256)
    (hfg : Fig8GameClampInv L B (m + 1) gs)
    (hep : gs.epMgmt 3 (qep + 1) Q bad = some s₁) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let out := fig.send (s₁.st Q) msg coins
    Fig8GameClampInv L B m
      (s₁.record 3 Q out.1 ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, msg, out.2⟩ isChall) ∧
    out.2.1.1 + m + 1 ≤ B ∧ out.2.2.1 + m + 1 ≤ B := by
  obtain ⟨hst, _⟩ := epMgmt_st_b gs s₁ 3 (qep + 1) Q bad hep
  obtain ⟨_, htr, hch, hcp⟩ := epMgmt_bounds gs s₁ 3 (qep + 1) Q bad hep
  obtain ⟨htcur', hc1, hvS', hc2⟩ := lFig8_send_bounds P Dh encPt encT lam idOf (s₁.st Q) msg coins
  have htQ : (s₁.st Q).tcur + (m + 1) + 1 ≤ B := by rw [hst]; exact hfg.htcur Q
  have hvSQ : ∀ v, (s₁.st Q).vS = some v → v.lastIndex + (m + 1) + 1 ≤ B := by
    rw [hst]; exact hfg.hvS Q
  have hmB := hfg.hmB
  have hmL := hfg.hmL
  refine ⟨{
    hmB := by omega
    hmL := by omega
    htcur := fun R => by
      dsimp only [GameState.record]
      by_cases hR : R = Q
      · cases hR; simp only [Function.update_self]; omega
      · simp only [Function.update_of_ne hR, hst]; have := hfg.htcur R; omega
    hvS := fun R v' hv' => by
      dsimp only [GameState.record] at hv'
      by_cases hR : R = Q
      · cases hR; simp only [Function.update_self] at hv'
        rcases hvS' v' hv' with h1 | ⟨v, hv, h2⟩
        · omega
        · have := hvSQ v hv; omega
      · simp only [Function.update_of_ne hR, hst] at hv'
        have := hfg.hvS R v' hv'; omega
    hFresh := (hfg.hFresh.epMgmt hep).record 3 Q _ _ isChall rfl
    hTrans := by
      dsimp only [GameState.record, List.length_cons]
      rw [htr]; have := hfg.hTrans; omega
    hChall := by
      dsimp only [GameState.record]
      split_ifs <;> simp only [List.length_cons, hch] <;> (have := hfg.hChall; omega)
    hCompU := by
      rcases hfg.hCompU with ⟨U, hUL, hU1, hU2⟩
      refine ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩ :: U, by simp only [List.length_cons]; omega, ?_, ?_⟩
      · intro p hp
        dsimp only [GameState.record] at hp
        split_ifs at hp
        · rw [hcp] at hp; exact List.mem_cons_of_mem _ (hU1 p hp)
        · rw [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact List.mem_cons_self
          · rw [hcp] at hp; exact List.mem_cons_of_mem _ (hU1 p hp)
      · intro r hr
        dsimp only [GameState.record] at hr
        rw [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact List.mem_cons_self
        · rw [htr] at hr; exact List.mem_cons_of_mem _ (hU2 r hr) }, by omega, ?_⟩
  rcases hc2 with h1 | ⟨v, hv, h2⟩
  · omega
  · have := hvSQ v hv; omega

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem fig8GameClampInv_transmitImpl (idOf : Party → IdentityKey) (L B m qep : ℕ)
    (gs gs' : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (msg : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (res : Option (SimFig8C Pt))
    (hfg : Fig8GameClampInv L B (m + 1) gs)
    (hmem : (res, gs') ∈ support ((SM.transmitImpl
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) (Q, msg, rc)).run gs)) :
    Fig8GameClampInv L B m gs' ∧ ∀ c, res = some c → c.1.1 + m + 1 ≤ B ∧ c.2.1 + m + 1 ≤ B := by
  unfold SM.transmitImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hfg.mono (Nat.le_succ m), fun _ hc => by cases hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      stateT_liftM_probComp_run, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
    rcases hep : gs.epMgmt 3 (qep + 1) Q bad with _ | s₁ <;>
      simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    · rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hfg.mono (Nat.le_succ m), fun _ hc => by cases hc⟩
    · rcases hmem with ⟨rfl, rfl⟩
      obtain ⟨hfg', hc1, hc2⟩ :=
        fig8GameClampInv_record P Dh encPt encT lam idOf L B m qep gs s₁ Q bad false msg coins
          hfg hep
      exact ⟨hfg', fun c hc => by injection hc with hc; subst hc; exact ⟨hc1, hc2⟩⟩

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem fig8GameClampInv_challImpl (idOf : Party → IdentityKey) (L B m qep : ℕ)
    (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs gs' : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (res : Option (SimFig8C Pt))
    (hfg : Fig8GameClampInv L B (m + 1) gs)
    (hmem : (res, gs') ∈ support ((SM.challImpl
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) cfg
      (Q, m₀, m₁, rc)).run gs)) :
    Fig8GameClampInv L B m gs' ∧ ∀ c, res = some c → c.1.1 + m + 1 ≤ B ∧ c.2.1 + m + 1 ≤ B := by
  unfold SM.challImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hfg.mono (Nat.le_succ m), fun _ hc => by cases hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      stateT_liftM_probComp_run, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
    rcases hep : gs.epMgmt 3 (qep + 1) Q bad with _ | s₁ <;>
      simp only [hep] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hfg.mono (Nat.le_succ m), fun _ hc => by cases hc⟩
    · by_cases hch : (!(s₁.safeCh 3 Q) || !(cfg.challAllowedIn (s₁.epoch Q))) = true
      · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨hfg.mono (Nat.le_succ m), fun _ hc => by cases hc⟩
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        obtain ⟨hfg', hc1, hc2⟩ :=
          fig8GameClampInv_record P Dh encPt encT lam idOf L B m qep gs s₁ Q bad true
            ((cfg.challMsg (s₁.epoch Q)).getD (if gs.b then m₁ else m₀)) coins hfg hep
        exact ⟨hfg', fun c hc => by injection hc with hc; subst hc; exact ⟨hc1, hc2⟩⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem Fig8GameClampInv.withWin {L B m : ℕ}
    {gs : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)}
    (h : Fig8GameClampInv L B m gs) (w : Bool) :
    Fig8GameClampInv L B m { gs with win := w } :=
  ⟨h.hmB, h.hmL, h.htcur, h.hvS, h.hFresh.setWin w, h.hTrans, h.hChall, h.hCompU⟩

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem fig8GameClampInv_accept (idOf : Party → IdentityKey) (L B m : ℕ)
    (gs : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (c : SimFig8C Pt) (st' : SimFig8St Pt) (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (pos : SM.Pos)
    (hfg : Fig8GameClampInv L B (m + 1) gs)
    (hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (gs.st Q) c =
      some (st', t, i, pm)) :
    Fig8GameClampInv L B m (gs.accept Q st' pos) ∧ t + m + 1 ≤ B := by
  obtain ⟨_, _, ht_le, hst'_tcur, hst'_vS⟩ :=
    lFig8_receive_bounds P Dh encPt encT lam idOf (gs.st Q) st' c t i pm hrcv
  obtain ⟨_, _, htr_le, hch_le, _⟩ := accept_bounds gs Q st' pos
  have htQ := hfg.htcur Q
  have hmB := hfg.hmB
  have hmL := hfg.hmL
  refine ⟨{
    hmB := by omega
    hmL := by omega
    htcur := fun R => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hR : R = Q
      · cases hR; simp only [Function.update_self]; omega
      · simp only [Function.update_of_ne hR]; have := hfg.htcur R; omega
    hvS := fun R v' hv' => by
      dsimp only [GameState.accept, GameState.delete] at hv'
      by_cases hR : R = Q
      · cases hR; simp only [Function.update_self, hst'_vS] at hv'
        have := hfg.hvS Q v' hv'; omega
      · simp only [Function.update_of_ne hR] at hv'
        have := hfg.hvS R v' hv'; omega
    hFresh := hfg.hFresh.accept Q st' pos
    hTrans := by have := hfg.hTrans; omega
    hChall := by have := hfg.hChall; omega
    hCompU := by
      rcases hfg.hCompU with ⟨U, hUL, hU1, hU2⟩
      refine ⟨U, by omega, fun p hp => ?_, fun r hr => ?_⟩
      · dsimp only [GameState.accept, GameState.delete] at hp
        exact hU1 p (List.mem_of_mem_filter hp)
      · dsimp only [GameState.accept, GameState.delete] at hr
        exact hU2 r (List.mem_of_mem_filter hr) }, by omega⟩

omit [SampleableType PQC] in
private theorem fig8GameClampInv_deliverImpl (idOf : Party → IdentityKey) (L B m : ℕ)
    (gs gs' : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (c : SimFig8C Pt)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hfg : Fig8GameClampInv L B (m + 1) gs)
    (hmem : (res, gs') ∈ support ((SM.deliverImpl
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) SM.Config.h1 (Q, c)).run gs)) :
    Fig8GameClampInv L B m gs' ∧ ∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B := by
  unfold SM.deliverImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hfg.mono (Nat.le_succ m), fun _ _ _ hc => by cases hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind] at hmem
    rcases htr : gs.inTransit Q.other c with _ | r <;> simp only [htr] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hfg.mono (Nat.le_succ m), fun _ _ _ hc => by cases hc⟩
    · rcases hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (gs.st Q) c with
        _ | ⟨st', t', i', m'⟩ <;> simp only [hrcv] at hmem
      · split_ifs at hmem <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
          (rcases hmem with ⟨rfl, rfl⟩;
           exact ⟨(hfg.mono (Nat.le_succ m)).withWin _, fun _ _ _ hc => by cases hc⟩)
      · obtain ⟨hfg', ht'⟩ :=
          fig8GameClampInv_accept P Dh encPt encT lam idOf L B m gs Q c st' t' i' m' r.pos hfg hrcv
        split_ifs at hmem <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
          (rcases hmem with ⟨rfl, rfl⟩;
           refine ⟨hfg'.withWin _, fun t i pm hc => ?_⟩;
           injection hc with hc; injection hc with ht _ _; subst ht; exact ht')

omit [SampleableType PQC] in
private theorem fig8GameClampInv_injectImpl (idOf : Party → IdentityKey) (L B m qep : ℕ)
    (gs gs' : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (c : SimFig8C Pt)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hfg : Fig8GameClampInv L B (m + 1) gs)
    (hmem : (res, gs') ∈ support ((SM.injectImpl
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
      (Q, c)).run gs)) :
    Fig8GameClampInv L B m gs' ∧ ∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B := by
  unfold SM.injectImpl at hmem
  by_cases hw : (gs.win || (gs.inTransit Q.other c).isSome || !(gs.safeInj 3)) = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hfg.mono (Nat.le_succ m), fun _ _ _ hc => by cases hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind] at hmem
    rcases hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (gs.st Q) c with
      _ | ⟨st', t', i', m'⟩ <;> simp only [hrcv] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hfg.mono (Nat.le_succ m), fun _ _ _ hc => by cases hc⟩
    · by_cases hqep : qep + 1 + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨hfg.mono (Nat.le_succ m), fun _ _ _ hc => by cases hc⟩
      · simp only [hqep, ↓reduceIte] at hmem
        obtain ⟨hfg', ht'⟩ :=
          fig8GameClampInv_accept P Dh encPt encT lam idOf L B m gs Q c st' t' i' m'
            ⟨Q.other, t', i'⟩ hfg hrcv
        by_cases htriv : gs.trivial 3 ⟨Q.other, t', i'⟩ = true
        · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩
          refine ⟨hfg', fun t i pm hc => ?_⟩
          injection hc with hc; injection hc with ht _ _; subst ht; exact ht'
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          split_ifs at hmem <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
            (rcases hmem with ⟨rfl, rfl⟩;
             exact ⟨(hfg.mono (Nat.le_succ m)).withWin _, fun _ _ _ hc => by cases hc⟩)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem fig8GameClampInv_corrImpl (L B m : ℕ)
    (gs gs' : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (res : Option (SimFig8St Pt))
    (hfg : Fig8GameClampInv L B (m + 1) gs)
    (hmem : (res, gs') ∈ support
      ((SM.corrImpl (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (C := SimFig8C Pt) Q).run gs)) :
    Fig8GameClampInv L B m gs' := by
  unfold SM.corrImpl at hmem
  by_cases hw : (gs.win || !(gs.corrAllowed Q)) = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact hfg.mono (Nat.le_succ m)
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    obtain ⟨hst, _, htr, hch, _⟩ := afterCorr_bounds gs Q
    have hmB := hfg.hmB
    have hmL := hfg.hmL
    have htr0 := hfg.hTrans
    have hch0 := hfg.hChall
    exact {
      hmB := by omega
      hmL := by omega
      htcur := fun R => by rw [hst]; have := hfg.htcur R; omega
      hvS := fun R v hv => by rw [hst] at hv; have := hfg.hvS R v hv; omega
      hFresh := hfg.hFresh.afterCorr Q
      hTrans := by rw [htr]; omega
      hChall := by rw [hch]; omega
      hCompU := by
        rcases hfg.hCompU with ⟨U, hUL, hU1, hU2⟩
        refine ⟨U, by omega, fun p hp => ?_, fun r hr => ?_⟩
        · dsimp only [GameState.afterCorr, GameState.leak] at hp
          simp only [List.mem_append, List.mem_map, List.mem_filter] at hp
          rcases hp with ⟨r, ⟨hr, _⟩, rfl⟩ | hp
          · exact hU2 r hr
          · exact hU1 p hp
        · rw [htr] at hr; exact hU2 r hr }

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem ghostChain_accept_epoch (g : GhostChain) (i : ℕ) :
    (g.accept i).epoch = g.epoch := by
  unfold GhostChain.accept
  split_ifs <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mem_modify_accept_epoch (cs : List GhostChain) (ci i : ℕ)
    {g' : GhostChain} (hg' : g' ∈ cs.modify ci (·.accept i)) :
    ∃ g ∈ cs, g'.epoch = g.epoch := by
  induction cs generalizing ci with
  | nil => simp at hg'
  | cons g gs ih =>
    cases ci with
    | zero =>
      change g' ∈ g.accept i :: gs at hg'
      rw [List.mem_cons] at hg'
      rcases hg' with rfl | hg'
      · exact ⟨g, List.mem_cons_self, ghostChain_accept_epoch g i⟩
      · exact ⟨g', List.mem_cons_of_mem g hg', rfl⟩
    | succ ci =>
      change g' ∈ g :: gs.modify ci (·.accept i) at hg'
      rw [List.mem_cons] at hg'
      rcases hg' with rfl | hg'
      · exact ⟨g', List.mem_cons_self, rfl⟩
      · obtain ⟨g₀, hg₀, heq⟩ := ih ci hg'
        exact ⟨g₀, List.mem_cons_of_mem g hg₀, heq⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mem_pushChain (cs : List GhostChain) (g₀ : GhostChain)
    {g' : GhostChain} (hg' : g' ∈ pushChain cs g₀) :
    g' = g₀ ∨ g' ∈ cs := by
  unfold pushChain at hg'
  have h1 := List.mem_of_mem_drop hg'
  rw [List.mem_append, List.mem_singleton] at h1
  exact h1.symm

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem mem_trans_of_inTransit {St Msg C : Type} [DecidableEq C]
    (gs : GameState St Msg C) (P : Party) (c : C) (r : Record Msg C)
    (h : gs.inTransit P c = some r) :
    r ∈ gs.trans :=
  List.mem_of_find?_eq_some h

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem onAcceptPure_clampInv (qep B m : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (msg : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (st : SimState PQ Pt ℓ) (hInv : SimBaseClampInv B m st) (ht : t + m + 1 ≤ B) :
    SimBaseClampInv B m (onAcceptPure qep Q w isDel t i msg ci? T pq' st).2 := by
  have hacc : ∀ (pos : SM.Pos), pos.epoch + m + 1 ≤ B →
      SimBaseClampInv B m
        { st with
          chains := Function.update st.chains Q
            (match ci? with
             | some ci => (st.chains Q).modify ci (·.accept i)
             | none => pushChain (st.chains Q) (GhostChain.accept ⟨some T, t, 0, []⟩ i)),
          pq := Function.update st.pq Q pq',
          unackA := st.unackA && Q != Party.A,
          mir := st.mir.accept Q () pos } := by
    intro pos hpos
    obtain ⟨hep_le, _, _, _, _⟩ := accept_bounds st.mir Q () pos
    refine {
      hep := fun R => by
        dsimp only []
        have h1 := hep_le R
        have h2 := hInv.hep R
        omega
      htrans := fun r hr => by
        dsimp only [GameState.accept, GameState.delete] at hr
        exact hInv.htrans r (List.mem_of_mem_filter hr)
      hch := fun R g' hg' => by
        dsimp only [] at hg'
        by_cases hR : R = Q
        · subst hR
          simp only [Function.update_self] at hg'
          rcases ci? with _ | ci
          · rcases mem_pushChain (st.chains R) (GhostChain.accept ⟨some T, t, 0, []⟩ i) hg' with
              rfl | hg'
            · rw [ghostChain_accept_epoch]; exact ht
            · exact hInv.hch R g' hg'
          · obtain ⟨g, hg, heq⟩ := mem_modify_accept_epoch (st.chains R) ci i hg'
            rw [heq]; exact hInv.hch R g hg
        · simp only [Function.update_of_ne hR] at hg'
          exact hInv.hch R g' hg'
      hhonest := hInv.hhonest }
  unfold onAcceptPure
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with h1 h2
    · exact hInv
    · exact hacc ⟨Q.other, t, i⟩ ht
    · exact ⟨hInv.hep, hInv.htrans, hInv.hch, hInv.hhonest⟩
  · simp only [↓reduceIte]
    rcases hin : st.mir.inTransit Q.other w with _ | r
    · exact hInv
    · exact hacc r.pos (hInv.htrans r (mem_trans_of_inTransit st.mir Q.other w r hin))

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem onAnswerPure_clampInv (qep B m : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (st : SimState PQ Pt ℓ) (hInv : SimBaseClampInv B m st)
    (hres : ∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B) :
    SimBaseClampInv B m (onAnswerPure qep Q w isDel ci? T pq' res st).2 := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hInv
  · exact hInv
  · exact onAcceptPure_clampInv qep B m Q w isDel t i ((pm.map (·.2)).getD default) ci? T pq'
      st hInv (hres t i pm rfl)

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem scPostSendPure_clampInv {B m : ℕ}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {s₁ : GameState Unit (Plain ℓ) (List (BitVec 8))}
    {Q : Party} {qep : ℕ} {hasCoins : Bool}
    (hep : sC.base.mir.epMgmt 3 qep Q hasCoins = some s₁)
    (m₀ : Plain ℓ) (isChall : Bool) (pq' : PQ) (pn : BitVec 32) (c : SimFig8C Pt)
    (hInv : SimBaseClampInv B (m + 1) sC.base)
    (hc : c.1.1 + m + 1 ≤ B ∧ c.2.1 + m + 1 ≤ B) :
    SimBaseClampInv B m (scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ isChall pq' pn c).base := by
  have hInv0 := hInv.mono (Nat.le_succ m)
  obtain ⟨hep_le, _, _, _⟩ := epMgmt_bounds sC.base.mir s₁ 3 qep Q hasCoins hep
  obtain ⟨htr_eq, _, _⟩ := epMgmt_lists sC.base.mir s₁ 3 qep Q hasCoins hep
  refine {
    hep := fun R => by
      dsimp only [scPostSendPure, GameState.record]
      have h1 := hep_le R
      have h2 := hInv.hep R
      omega
    htrans := fun r hr => by
      dsimp only [scPostSendPure, GameState.record] at hr
      rw [List.mem_cons] at hr
      rcases hr with rfl | hr
      · dsimp only []
        have h1 := hep_le Q
        have h2 := hInv.hep Q
        omega
      · rw [htr_eq] at hr
        exact hInv0.htrans r hr
    hch := hInv0.hch
    hhonest := fun wc hwc => by
      dsimp only [scPostSendPure] at hwc
      rw [List.mem_cons] at hwc
      rcases hwc with rfl | hwc
      · exact hc
      · exact hInv0.hhonest wc hwc }

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem kept_eval_fig8Clamp_epoch_le (B : ℕ) (idOf : Party → IdentityKey)
    (k : Kept Pt) (c' : SimFig8C Pt) (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : Kept.eval
      (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam))
      (fs := fsClampSim B (lFS P.C P.codec ℓ encT idOf 25000))
      c' k = some (some (t, i, pm))) :
    t ≤ c'.1.1 := by
  unfold Kept.eval at h
  rcases hfull : k.full with _ | st <;> simp only [hfull, Option.map] at h
  · rcases hrs : k.rs c'.1.1 with _ | v <;> simp only [hrs] at h
    · cases h
    · rcases hfs : (fsClampSim B (lFS P.C P.codec ℓ encT idOf 25000)).receive v c'.1 c'.2 with
        _ | ⟨v', i', pm'⟩ <;> simp only [hfs] at h
      · cases h
      · injection h with h; injection h with h; injection h with ht _
        omega
  · dsimp only [fig8Clamp] at h
    rcases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c' with
      _ | ⟨st', t_out, i_out, pm'⟩ <;> simp only [hfig, Option.map] at h
    · cases h
    · obtain ⟨rfl, _⟩ := lFig8_receive_epoch_index_eq P Dh encPt encT lam idOf st st' c'
        t_out i_out pm' hfig
      injection h with h; injection h with h; injection h with ht _
      omega

omit [Zero Pt] [SampleableType PQC] in
private theorem sentEval_epoch_le
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (sent : List (SimFig8C Pt × FSAEAD.RatchetSenderState (BitVec 256)))
    (c c' : SimFig8C Pt) (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : sentEval (fs := fs) sent c c' = some (some (t, i, pm))) :
    t ≤ c'.1.1 := by
  unfold sentEval at h
  rcases hfind : sent.find? (fun e => decide (e.1 = c)) with _ | e <;>
    simp only [hfind, Option.map] at h
  · cases h
  · rcases hfs : fs.receive ⟨e.2.chainKey, e.2.lastIndex, []⟩ c'.1 c'.2 with
      _ | ⟨v', i', pm'⟩ <;> simp only [hfs] at h
    · cases h
    · injection h with h; injection h with h; injection h with ht _
      omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem simKDecryptFig8_epoch_le (B : ℕ) (qB : Bool)
    (w : List (BitVec 8)) (c' : SimFig8C Pt) (seed : List (BitVec 8))
    (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : simKDecryptFig8 P ℓ B qB w c' seed = some (t, i, pm)) :
    t ≤ c'.1.1 := by
  dsimp only [simKDecryptFig8, decryptWithKnownSeed] at h
  rcases hl : lPubOf P.codec c'.2.2 with _ | pub <;> simp only [hl] at h
  · cases h
  · rcases htr : SignalMessage.tryFrom P.codec w with _ | msg <;> simp only [htr] at h
    · cases h
    · split_ifs at h <;> try cases h
      all_goals
        rcases hdec : aesCbcDecrypt P.C.D
            (deriveMessageKeys P.C.F (some c'.2.2.2) seed).1.1
            (deriveMessageKeys P.C.F (some c'.2.2.2) seed).1.2 msg.ciphertext with _ | m_raw <;>
          simp only [hdec] at h
        · cases h
        · injection h with h; injection h with ht _
          omega

omit [SampleableType PQC] in
private theorem evalCKClamp_epoch_le (B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : List (BitVec 8))
    (c c' : SimFig8C Pt) (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : evalCKClamp P Dh encPt encT lam B sC Q w c c' = some (some (t, i, pm))) :
    t ≤ c'.1.1 := by
  unfold evalCKClamp predictReceive at h
  dsimp only [Option.orElse] at h
  rcases hk : Kept.eval
      (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam))
      (fs := fsClampSim B (lFS P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000))
      c' (sC.kept Q) with _ | r
  · rw [hk] at h
    rcases hs : sentEval
        (fs := fsClampSim B (lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000))
        sC.sent c c' with _ | r'
    · rw [hs] at h
      rcases hks : snapshotMessageKeySeed P sC.snaps Q c.1.1 w with _ | seed
      · rw [hks] at h; cases h
      · rw [hks] at h
        injection h with h
        exact simKDecryptFig8_epoch_le P B (partyEnc Q) w c' seed t i pm h
    · rw [hs] at h
      exact sentEval_epoch_le _ sC.sent c c' t i pm (hs.trans h)
  · rw [hk] at h
    exact kept_eval_fig8Clamp_epoch_le P Dh encPt encT lam B _ (sC.kept Q) c' t i pm (hk.trans h)

private structure SemHookClampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (B : ℕ) (ExClampInv : ℕ → Ex → Prop)
    (sh : SemHook PQC Pt ℓ T Ex) : Prop where
  mono : ∀ {m₁ m₂ ex}, m₁ ≤ m₂ → ExClampInv m₂ ex → ExClampInv m₁ ex
  onSendCoins_inv : ∀ {m Q rq ex}, ExClampInv m ex →
    ∀ y ∈ support (sh.onSendCoins Q rq ex), ExClampInv m y.1 ∧ ExClampInv m y.2
  onTr_inv : ∀ {m Q msg rc ex}, ExClampInv (m + 1) ex →
    ∀ y ∈ support (sh.onTr Q msg rc ex),
      ExClampInv m y.2 ∧ ∀ c, y.1 = some c → c.1.1 + m + 1 ≤ B ∧ c.2.1 + m + 1 ≤ B
  onCh_inv : ∀ {m Q m₀ m₁ rc ex}, ExClampInv (m + 1) ex →
    ∀ y ∈ support (sh.onCh Q m₀ m₁ rc ex),
      ExClampInv m y.2 ∧ ∀ c, y.1 = some c → c.1.1 + m + 1 ≤ B ∧ c.2.1 + m + 1 ≤ B
  onDl_inv : ∀ {m Q c ex}, c.1.1 ≤ B ∧ c.2.1 ≤ B → ExClampInv (m + 1) ex →
    ∀ y ∈ support (sh.onDl Q c ex),
      ExClampInv m y.2 ∧ ∀ t i pm, y.1 = some (.accepted t i pm) → t + m + 1 ≤ B
  onIj_inv : ∀ {m Q c ex}, c.1.1 ≤ B ∧ c.2.1 ≤ B → ExClampInv (m + 1) ex →
    ∀ y ∈ support (sh.onIj Q c ex),
      ExClampInv m y.2 ∧ ∀ t i pm, y.1 = some (.accepted t i pm) → t + m + 1 ≤ B
  onCr_inv : ∀ {m Q ex}, ExClampInv (m + 1) ex →
    ∀ y ∈ support (sh.onCr Q ex), ExClampInv m y.2
  onProbe_inv : ∀ {m Q c' ex}, ExClampInv (m + 1) ex →
    ∀ ex' ∈ support (sh.onProbe Q c' ex), ExClampInv m ex'
  onDeliverPost_inv : ∀ {m Q j? rr ex}, ExClampInv m ex →
    ∀ ex' ∈ support (sh.onDeliverPost Q j? rr ex), ExClampInv m ex'

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem semSendHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (hBase : SimBaseClampInv B (m + 1) sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semSendHook P Dh encPt encT lam sh qep sC₀ ex₀ Q m₀ chal r),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  have hBase0 := hBase.mono (Nat.le_succ m)
  have hEx0 := h_clamp.mono (Nat.le_succ m) hEx
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semSendHook at hx
  by_cases href : (sC₀.base.stopped || sC₀.base.mir.win || !(noBobSendInEpoch0 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC₀.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;>
      simp only [hep] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
    · by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hch, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
        obtain ⟨⟨rq, rc⟩, -, ⟨exOk, exFail⟩, hsc, hx⟩ := hx
        obtain ⟨hOk, hFail⟩ := h_clamp.onSendCoins_inv hEx (exOk, exFail) hsc
        have hFail0 := h_clamp.mono (Nat.le_succ m) hFail
        rcases hpub : mkPub P sC₀.base Q rq
          (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
            BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) with _ | ⟨pq', pub⟩ <;>
          simp only [hpub] at hx
        · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hFail0⟩
        · simp only [mem_support_bind_iff] at hx
          obtain ⟨⟨res, ex₂⟩, hq, hx⟩ := hx
          have hEx2 : ExClampInv m ex₂ ∧
              ∀ c, res = some c → c.1.1 + m + 1 ≤ B ∧ c.2.1 + m + 1 ≤ B := by
            rcases chal with _ | m₁
            · exact h_clamp.onTr_inv hOk (res, ex₂) hq
            · exact h_clamp.onCh_inv hOk (res, ex₂) hq
          rcases res with _ | c <;>
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          · rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hFail0⟩
          · rcases hx with ⟨_, rfl, rfl⟩
            exact ⟨scPostSendPure_clampInv P Dh encPt encT lam hep m₀ chal.isSome pq' _ c
              hBase (hEx2.2 c rfl), hEx2.1⟩

omit [SampleableType PQC] in
private theorem semFwdAnswerHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hc' : c'.1.1 ≤ B ∧ c'.2.1 ≤ B)
    (hBase : SimBaseClampInv B m sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semFwdAnswerHook P Dh encPt encT lam sh qep sC₀ ex₀ Q w isDel ci? Tpk pq' c'),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdAnswerHook at hx
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
  obtain ⟨⟨res, ex'⟩, hq, _, rfl, rfl⟩ := hx
  have hq' : ExClampInv m ex₁ ∧ ∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B := by
    split_ifs at hq
    · exact h_clamp.onDl_inv hc' hEx (res, ex₁) hq
    · exact h_clamp.onIj_inv hc' hEx (res, ex₁) hq
  exact ⟨onAnswerPure_clampInv qep B m Q w isDel ci? Tpk pq' res sC₀.base hBase hq'.2, hq'.1⟩

omit [DecidableEq Pt] [SampleableType PQC] in
private theorem semResyncHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (c : SimFig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hc : c.1.1 ≤ B ∧ c.2.1 ≤ B)
    (hr : ∀ t i pm, r = some (t, i, pm) → t + m + 1 ≤ B)
    (hBase : SimBaseClampInv B m sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semResyncHook P Dh encPt encT lam sh qep sC₀ ex₀ Q w ci? Tpk pq' c r),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semResyncHook at hx
  rcases r with _ | ⟨t, i, pub, m'⟩
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, rfl⟩
    exact ⟨hBase, h_clamp.mono (Nat.le_succ m) hEx⟩
  · simp only [mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, hdl, hx⟩ := hx
    have hEx' := (h_clamp.onDl_inv hc hEx (res, ex') hdl).1
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase, hEx'⟩
    · rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase, hEx'⟩
    · rcases hx with ⟨_, rfl, rfl⟩
      exact ⟨onAcceptPure_clampInv qep B m Q w true t i m' ci? Tpk pq' sC₀.base
        hBase (hr t i (pub, m') rfl), hEx'⟩

omit [SampleableType PQC] in
private theorem semFwdHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ)
    (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hhc : ∀ c, honestC = some c → c.1.1 ≤ B ∧ c.2.1 ≤ B)
    (hc' : c'.1.1 + m + 1 ≤ B ∧ c'.2.1 ≤ B)
    (hBase : SimBaseClampInv B m sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support
        (semFwdHook P Dh encPt encT lam sh qep B sC₀ ex₀ Q w isDel ci? Tpk pq' honestC c'),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  have hc'0 : c'.1.1 ≤ B ∧ c'.2.1 ≤ B := ⟨by omega, hc'.2⟩
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdHook at hx
  rcases hhc_eq : honestC with _ | c <;> simp only [hhc_eq] at hx
  · exact semFwdAnswerHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
      sC₀ ex₀ Q w isDel ci? Tpk pq' c' hc'0 hBase hEx _ hx
  · split_ifs at hx
    · rcases hev : evalCKClamp P Dh encPt encT lam B sC₀ Q w c c' with _ | r <;>
        simp only [hev] at hx
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        obtain ⟨ex', hpr, _, rfl, rfl⟩ := hx
        exact ⟨hBase, h_clamp.onProbe_inv hEx ex₁ hpr⟩
      · refine semResyncHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
          sC₀ ex₀ Q w ci? Tpk pq' c r (hhc c hhc_eq) (fun t i pm hr => ?_) hBase hEx _ hx
        subst hr
        have htle := evalCKClamp_epoch_le P Dh encPt encT lam B sC₀ Q w c c' t i pm hev
        omega
    · exact semFwdAnswerHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
        sC₀ ex₀ Q w isDel ci? Tpk pq' c' hc'0 hBase hEx _ hx

omit [SampleableType PQC] in
private theorem semFwdEvictHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hc' : c'.1.1 ≤ B ∧ c'.2.1 ≤ B)
    (hBase : SimBaseClampInv B m sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semFwdEvictHook P Dh encPt encT lam sh qep sC₀ ex₀ Q w isDel Tpk pq' c'),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdEvictHook at hx
  split_ifs at hx
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨ex', hpr, _, rfl, rfl⟩ := hx
    exact ⟨hBase, h_clamp.onProbe_inv hEx ex₁ hpr⟩
  · exact semFwdAnswerHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
      sC₀ ex₀ Q w isDel none Tpk pq' c' hc' hBase hEx _ hx

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem SimBaseClampInv.withAmb {B m : ℕ} {s : SimState PQ Pt ℓ}
    (h : SimBaseClampInv B m s) (a : ℕ) :
    SimBaseClampInv B m { s with amb := a } :=
  ⟨h.hep, h.htrans, h.hch, h.hhonest⟩

omit [SampleableType PQC] in
private theorem semRecvHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (h232 : 2 ^ 32 ≤ B)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool)
    (hBase : SimBaseClampInv B (m + 1) sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semRecvHook P Dh encPt encT decT lam sh qep B sC₀ ex₀ Q w isDel),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  have hBase0 := hBase.mono (Nat.le_succ m)
  have hEx0 := h_clamp.mono (Nat.le_succ m) hEx
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semRecvHook at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win ||
        (isDel && (sC₀.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC₀.base.mir.inTransit Q.other w).isSome ||
          !(sC₀.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hparse : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC₀.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;>
      simp only [hparse] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
    · have hlct : lct.1 ≤ B :=
        (simParseRecvC_bounds P decT (partyEnc Q) (sC₀.base.pq Q) w hparse).2.trans h232
      have hhc : ∀ c,
          (sC₀.base.honest.find? fun wc =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c →
          c.1.1 + m + 1 ≤ B ∧ c.2.1 ≤ B := by
        intro c hc
        rw [Option.map_eq_some_iff] at hc
        rcases hc with ⟨wc, hmem, rfl⟩
        have h1 := hBase.hhonest wc (List.mem_of_find?_eq_some hmem)
        exact ⟨by have := h1.1; omega, by have := h1.2; omega⟩
      have hhc0 : ∀ c,
          (sC₀.base.honest.find? fun wc =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c →
          c.1.1 ≤ B ∧ c.2.1 ≤ B := fun c hc => ⟨by have := (hhc c hc).1; omega, (hhc c hc).2⟩
      have hmkC : ∀ (honestC : Option (SimFig8C Pt)),
          (∀ c, honestC = some c → c.1.1 + m + 1 ≤ B ∧ c.2.1 ≤ B) →
          ∀ (t : ℕ) (T1 : Option Pt), t + m + 1 ≤ B →
          (match honestC with
           | some c => if c.2.2.2 = lct.2.2 then c else ((t, T1), lct)
           | none => ((t, T1), lct)).1.1 + m + 1 ≤ B ∧
          (match honestC with
           | some c => if c.2.2.2 = lct.2.2 then c else ((t, T1), lct)
           | none => ((t, T1), lct)).2.1 ≤ B := by
        intro honestC hhc1 t T1 ht
        rcases honestC with _ | c
        · exact ⟨ht, hlct⟩
        · dsimp only []
          split_ifs
          · exact hhc1 c rfl
          · exact ⟨ht, hlct⟩
      rcases hidx : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · have hBaseAmb : SimBaseClampInv B m
            (if inReceiveOnlyEpoch sC₀.base.mir Q || (Q == Party.A && (sC₀.base.chains Q).any (·.key.isNone))
             then { sC₀.base with amb := sC₀.base.amb + 1 } else sC₀.base) := by
          split_ifs
          · exact hBase0.withAmb _
          · exact hBase0
        by_cases hc1 :
            ((((sC₀.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true &&
             (((sC₀.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [hc1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hx
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hx
            by_cases hc2 :
                (inReceiveOnlyEpoch sC₀.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
              rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBaseAmb, hEx0⟩
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hx
              rcases hT : T? with _ | T <;>
                simp only [hT] at hx
              · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
                rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBaseAmb, hEx0⟩
              · have hep1 : (sC₀.base.mir.epoch Q + 1) + m + 1 ≤ B := by
                  have := hBase.hep Q; omega
                by_cases hev_b :
                    ((((sC₀.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte] at hx
                  exact semFwdEvictHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
                    _ ex₀ Q w isDel pk pq' _ ⟨by dsimp only []; omega, hlct⟩ hBaseAmb hEx _ hx
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte] at hx
                  exact semFwdHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
                    _ ex₀ Q w isDel none pk pq' _ _ hhc0
                    (hmkC _ hhc (sC₀.base.mir.epoch Q + 1) (some T) hep1) hBaseAmb hEx _ hx
      · by_cases hrej : ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hx
          have hgep : ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch + m + 1 ≤ B := by
            rw [List.getD_eq_getElem?_getD]
            rcases h : (sC₀.base.chains Q)[ci]? with _ | g
            · dsimp only [Option.getD]; have := hBase.hep Q; omega
            · dsimp only [Option.getD]
              have := hBase.hch Q g (List.mem_of_getElem? h)
              omega
          exact semFwdHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
            sC₀ ex₀ Q w isDel (some ci) pk pq' _ _ hhc0
            (hmkC _ hhc ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch T? hgep)
            hBase0 hEx _ hx

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem semCorrHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hBase : SimBaseClampInv B (m + 1) sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semCorrHook P Dh encT sh sC₀ ex₀ Q),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  have hBase0 := hBase.mono (Nat.le_succ m)
  have hEx0 := h_clamp.mono (Nat.le_succ m) hEx
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semCorrHook at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win || !(sC₀.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC₀.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, hcr, hx⟩ := hx
    have hEx' := h_clamp.onCr_inv hEx (res, ex') hcr
    rcases res with _ | fig8st <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx'⟩
    · rcases hx with ⟨_, rfl, rfl⟩
      refine ⟨{
        hep := fun R => by
          dsimp only [GameState.afterCorr, GameState.leak]
          exact hBase0.hep R
        htrans := fun r hr => by
          dsimp only [GameState.afterCorr, GameState.leak] at hr
          exact hBase0.htrans r hr
        hch := fun R g' hg' => by
          dsimp only [] at hg'
          split_ifs at hg'
          · rcases hγ : fig8st.γ with _ | x <;> simp only [hγ] at hg'
            · exact hBase0.hch R g' hg'
            · by_cases hR : R = Party.A
              · subst hR
                simp only [Function.update_self, List.mem_map] at hg'
                obtain ⟨g, hg, hge⟩ := hg'
                have hg_ep : g'.epoch = g.epoch := by split_ifs at hge <;> (subst hge; rfl)
                rw [hg_ep]; exact hBase0.hch Party.A g hg
              · simp only [Function.update_of_ne hR] at hg'
                exact hBase0.hch R g' hg'
          · exact hBase0.hch R g' hg'
        hhonest := hBase0.hhonest }, hEx'⟩

omit [SampleableType PQC] in
private theorem semHandleHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (h232 : 2 ^ 32 ≤ B)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex)
    (hBase : SimBaseClampInv B (m + 1) sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semHandleHook P Dh encPt encT decT lam sh qep B t sC₀ ex₀),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep sC₀ ex₀ Q m₀ none r
      hBase hEx
  · exact semSendHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep sC₀ ex₀ Q m₀ (some m₁) r
      hBase hEx
  · rintro ⟨_, sC₁, ex₁⟩ hx
    unfold semHandleHook at hx
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨rr, sC', ex'⟩, hrec, ex₂, hpost, _, rfl, rfl⟩ := hx
    obtain ⟨hB', hE'⟩ := semRecvHook_preserves_clampInv P Dh encPt encT decT lam h_clamp m qep h232
      sC₀ ex₀ Q w true hBase hEx (rr, sC₁, ex') hrec
    exact ⟨hB', h_clamp.onDeliverPost_inv hE' ex₁ hpost⟩
  · exact semRecvHook_preserves_clampInv P Dh encPt encT decT lam h_clamp m qep h232
      sC₀ ex₀ Q w false hBase hEx
  · exact semCorrHook_preserves_clampInv P Dh encT h_clamp m sC₀ ex₀ Q hBase hEx

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem fig8GameClampInv_of_fig8GsEnc_eq {L B m : ℕ}
    {g₁ g₂ : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)}
    (h : Fig8GameClampInv L B m g₁)
    (heq : fig8GsEnc (PQ := PQ) (PQC := PQC) g₁ = fig8GsEnc (PQ := PQ) (PQC := PQC) g₂) :
    Fig8GameClampInv L B m g₂ := by
  have hst : ∀ Q : Party, g₂.st Q = g₁.st Q := by
    intro Q
    injection heq with hst_eq _
    injection hst_eq with hA hB
    cases Q
    · exact hA.symm
    · exact hB.symm
  have hmir : fig8MirEnc (PQ := PQ) (PQC := PQC) g₁ =
      fig8MirEnc (PQ := PQ) (PQC := PQC) g₂ := by
    injection heq
  have hep_eq : ∀ R : Party, g₂.epoch R = g₁.epoch R := by
    have h1 : (g₁.epoch .A, g₁.epoch .B) = (g₂.epoch .A, g₂.epoch .B) :=
      congrArg (fun x => x.2.2.1) hmir
    intro R; cases R
    · exact (Prod.mk.inj h1).1.symm
    · exact (Prod.mk.inj h1).2.symm
  have hidx_eq : ∀ R : Party, g₂.idx R = g₁.idx R := by
    have h1 : (g₁.idx .A, g₁.idx .B) = (g₂.idx .A, g₂.idx .B) :=
      congrArg (fun x => x.2.2.2.1) hmir
    intro R; cases R
    · exact (Prod.mk.inj h1).1.symm
    · exact (Prod.mk.inj h1).2.symm
  have htr_eq : g₂.trans = g₁.trans := by
    have h1 :
        (g₁.trans.map fig8RecEnc).map
          (fun rE => (⟨posDec rE.1, rE.2.1, rE.2.2⟩ : Record _ _)) =
        (g₂.trans.map fig8RecEnc).map
          (fun rE => (⟨posDec rE.1, rE.2.1, rE.2.2⟩ : Record _ _)) :=
      congrArg (fun x => x.2.2.2.2.2.1.map
        (fun rE => (⟨posDec rE.1, rE.2.1, rE.2.2⟩ :
          Record (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)))) hmir
    have hid : ∀ rs : List (Record (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)),
        (rs.map fig8RecEnc).map
          (fun rE => (⟨posDec rE.1, rE.2.1, rE.2.2⟩ :
            Record (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))) = rs := by
      intro rs; induction rs with
      | nil => rfl
      | cons r rs ih => cases r; simp [fig8RecEnc, posDec_posEnc, ih]
    rw [hid, hid] at h1
    exact h1.symm
  have hch : g₂.chall.length = g₁.chall.length := by
    have h1 : (g₁.chall.map posEnc).length = (g₂.chall.map posEnc).length :=
      congrArg (fun x => x.2.2.2.2.2.2.1.length) hmir
    simpa using h1.symm
  have hcp_dedup : g₂.comp.dedup = g₁.comp.dedup := by
    have h1 : (g₁.comp.dedup.map posEnc).map posDec = (g₂.comp.dedup.map posEnc).map posDec :=
      congrArg (fun x => x.2.2.2.2.2.2.2.1.map posDec) hmir
    have hid : ∀ ps : List SM.Pos, (ps.map posEnc).map posDec = ps := by
      intro ps; induction ps with
      | nil => rfl
      | cons p ps ih => simp [posDec_posEnc, ih]
    rw [hid, hid] at h1
    exact h1.symm
  have hcp_mem : ∀ p : SM.Pos, p ∈ g₂.comp ↔ p ∈ g₁.comp := by
    intro p
    rw [← List.mem_dedup, hcp_dedup, List.mem_dedup]
  exact {
    hmB := h.hmB
    hmL := h.hmL
    htcur := fun Q => by rw [hst Q]; exact h.htcur Q
    hvS := fun Q v hv => by rw [hst Q] at hv; exact h.hvS Q v hv
    hFresh := ⟨fun r hr => by
        rw [htr_eq] at hr
        rw [hep_eq, hidx_eq]
        exact h.hFresh.1 r hr,
      fun p hp => by
        rw [hcp_mem] at hp
        rw [hep_eq, hidx_eq]
        exact h.hFresh.2 p hp⟩
    hTrans := by rw [htr_eq]; exact h.hTrans
    hChall := by rw [hch]; exact h.hChall
    hCompU := by
      rcases h.hCompU with ⟨U, hUL, hU1, hU2⟩
      exact ⟨U, hUL, fun p hp => hU1 p ((hcp_mem p).mp hp),
        fun r hr => hU2 r (htr_eq ▸ hr)⟩ }

private def KemExtraClampInv (L B m : ℕ) (ex : KemExtraRaw PQ PQC Pt ℓ) : Prop :=
  ∃ g tr, ex = kemExtraEnc (PQC := PQC) P g tr ∧ Fig8GameClampInv L B m g

private theorem kemFailSemHookClampInv (L qep B : ℕ) :
    SemHookClampInv B (KemExtraClampInv (PQC := PQC) P L B)
      (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins L qep B) where
  mono := by
    rintro m₁ m₂ ex hle ⟨g, tr, rfl, hg⟩
    exact ⟨g, tr, rfl, hg.mono hle⟩
  onSendCoins_inv := by
    rintro m Q rq ex ⟨g, tr, rfl, hg⟩ y hy
    rw [kemFailSemHook_onSendCoins_eq, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨⟨g, _, rfl, hg⟩, ⟨g, _, rfl, hg⟩⟩
  onTr_inv := by
    rintro m Q msg rc ex ⟨g, tr, rfl, hg⟩ ⟨res, ex'⟩ hy
    have ht : (g.st Q).tcur + 1 ≤ B := by have := hg.htcur Q; omega
    rw [kemFailSemHook_onTr_eq P Dh encPt encT decT lam K toKemCoins L qep B Q msg rc g tr
        ht hg.hFresh,
      support_map, Set.mem_image] at hy
    obtain ⟨⟨res', g'⟩, hmem, hEq⟩ := hy
    simp only [Prod.map, id_eq, Prod.mk.injEq] at hEq
    rcases hEq with ⟨rfl, rfl⟩
    obtain ⟨hg', hc⟩ := fig8GameClampInv_transmitImpl P Dh encPt encT lam
      (fun R => if R == Party.A then P.idA else P.idB) L B m qep g g' Q msg rc res' hg hmem
    exact ⟨⟨g', tr, rfl, hg'⟩, hc⟩
  onCh_inv := by
    rintro m Q m₀ m₁ rc ex ⟨g, tr, rfl, hg⟩ ⟨res, ex'⟩ hy
    have ht : (g.st Q).tcur + 1 ≤ B := by have := hg.htcur Q; omega
    rw [kemFailSemHook_onCh_eq P Dh encPt encT decT lam K toKemCoins L qep B Q m₀ m₁ rc g tr
        ht hg.hFresh,
      support_map, Set.mem_image] at hy
    obtain ⟨⟨res', g'⟩, hmem, hEq⟩ := hy
    simp only [Prod.map, id_eq, Prod.mk.injEq] at hEq
    rcases hEq with ⟨rfl, rfl⟩
    obtain ⟨hg', hc⟩ := fig8GameClampInv_challImpl P Dh encPt encT lam
      (fun R => if R == Party.A then P.idA else P.idB) L B m qep SM.Config.h1
      g g' Q m₀ m₁ rc res' hg hmem
    exact ⟨⟨g', tr, rfl, hg'⟩, hc⟩
  onDl_inv := by
    rintro m Q c ex ⟨ht, hi⟩ ⟨g, tr, rfl, hg⟩ ⟨res, ex'⟩ hy
    have hTr : g.trans.length ≤ L := by have := hg.hTrans; omega
    have hCh : g.chall.length ≤ L := by have := hg.hChall; omega
    rw [kemFailSemHook_onDl_eq P Dh encPt encT decT lam K toKemCoins L qep B Q c g tr
      hTr hCh hg.comp_dedup_le ht hi, support_map, Set.mem_image] at hy
    obtain ⟨⟨res', g'⟩, hmem, hEq⟩ := hy
    simp only [Prod.map, id_eq, Prod.mk.injEq] at hEq
    rcases hEq with ⟨rfl, rfl⟩
    obtain ⟨hg', ht'⟩ := fig8GameClampInv_deliverImpl P Dh encPt encT lam
      (fun R => if R == Party.A then P.idA else P.idB) L B m g g' Q c res' hg hmem
    exact ⟨⟨g', tr, rfl, hg'⟩, ht'⟩
  onIj_inv := by
    rintro m Q c ex ⟨ht, hi⟩ ⟨g, tr, rfl, hg⟩ ⟨res, ex'⟩ hy
    have hTr : g.trans.length ≤ L := by have := hg.hTrans; omega
    have hCh : g.chall.length ≤ L := by have := hg.hChall; omega
    rw [kemFailSemHook_onIj_eq P Dh encPt encT decT lam K toKemCoins L qep B Q c g tr
      hTr hCh hg.comp_dedup_le ht hi, support_map, Set.mem_image] at hy
    obtain ⟨⟨res', g'⟩, hmem, hEq⟩ := hy
    simp only [Prod.map, id_eq, Prod.mk.injEq] at hEq
    rcases hEq with ⟨rfl, rfl⟩
    obtain ⟨hg', ht'⟩ := fig8GameClampInv_injectImpl P Dh encPt encT lam
      (fun R => if R == Party.A then P.idA else P.idB) L B m qep g g' Q c res' hg hmem
    exact ⟨⟨g', tr, rfl, hg'⟩, ht'⟩
  onCr_inv := by
    rintro m Q ex ⟨g, tr, rfl, hg⟩ ⟨res, ex'⟩ hy
    have hTr : g.trans.length ≤ L := by have := hg.hTrans; omega
    have hCh : g.chall.length ≤ L := by have := hg.hChall; omega
    rw [kemFailSemHook_onCr_eq P Dh encPt encT decT lam K toKemCoins L qep B Q g tr
      hTr hCh hg.comp_dedup_le hg.comp_u, support_map, Set.mem_image] at hy
    obtain ⟨⟨res', g'⟩, hmem, hEq⟩ := hy
    simp only [Prod.map, id_eq, Prod.mk.injEq] at hEq
    rcases hEq with ⟨rfl, rfl⟩
    exact ⟨g', tr, rfl, fig8GameClampInv_corrImpl L B m g g' Q res' hg hmem⟩
  onProbe_inv := by
    rintro m Q c' ex ⟨g, tr, rfl, hg⟩ ex' hy
    change ex' ∈ support (pure (kemExtraEnc P g tr)) at hy
    rw [support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact ⟨g, tr, rfl, hg.mono (Nat.le_succ m)⟩
  onDeliverPost_inv := by
    rintro m Q j? rr ex ⟨g, tr, rfl, hg⟩ ex' hy
    rw [kemFailSemHook_onDeliverPost_eq] at hy
    rcases rr with _ | (_ | ⟨t, i, pm⟩) <;> rcases j? with _ | j <;>
      (rw [support_pure, Set.mem_singleton_iff] at hy; subst hy; exact ⟨g, _, rfl, hg⟩)

omit [SampleableType PQC] in
private theorem kemFailSimImpl_preserves_clampInv
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (L qep B m : ℕ) (h232 : 2 ^ 32 ≤ B)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool)
    (tr : CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState P.C.F)
    (hInv : SimGameClampInv L B (m + 1) sC gh.1) :
    let idOf0 : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    ∀ r ∈ support (runKemFailM (CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSimImpl
        P K ℓ Dh encPt encT decT idOf0 lam qep (.inr t)) (sC, gh, tr)),
      SimGameClampInv L B m r.2.1 r.2.2.1.1 := by
  rintro idOf0 ⟨resp, sC', gh', tr'⟩ hr
  have hStep := semHandleHook_kemFail_eq P Dh encPt encT decT lam K id rfl L qep B
    t sC gh tr (by omega)
    (fun Q => by have := hInv.1.hep Q; omega)
    (fun Q g hg => by have := hInv.1.hch Q g hg; omega)
    (fun _ => Or.inl h232)
    (fun wc hwc => by obtain ⟨h1, h2⟩ := hInv.1.hhonest wc hwc; exact ⟨by omega, by omega⟩)
    (fun Q => by have := hInv.2.htcur Q; omega)
    hInv.2.hFresh
    (by have := hInv.2.hTrans; omega)
    (by have := hInv.2.hChall; omega)
    hInv.2.comp_dedup_le
    hInv.2.comp_u
  have hmem : (resp, (sC', kemExtraEnc (PQC := BitVec 512) P gh'.1 tr')) ∈
      support (semHandleHook P Dh encPt encT decT lam
        (kemFailSemHook (ℓ := ℓ) P Dh encPt encT decT lam K id L qep B)
        qep B t sC (kemExtraEnc (PQC := BitVec 512) P gh.1 tr)) := by
    rw [hStep, support_map, Set.mem_image]
    exact ⟨(resp, (sC', gh', tr')), hr, rfl⟩
  obtain ⟨hB', g₂, tr₂, hEq, hg₂⟩ :=
    semHandleHook_preserves_clampInv P Dh encPt encT decT lam
      (kemFailSemHookClampInv (PQC := BitVec 512) P Dh encPt encT decT lam K id L qep B)
      m qep h232 t sC (kemExtraEnc (PQC := BitVec 512) P gh.1 tr)
      hInv.1 ⟨gh.1, tr, rfl, hInv.2⟩ _ hmem
  have hgs : fig8GsEnc (PQ := PQ) (PQC := BitVec 512) g₂ =
      fig8GsEnc (PQ := PQ) (PQC := BitVec 512) gh'.1 := by
    injection hEq.symm
  exact ⟨hB', fig8GameClampInv_of_fig8GsEnc_eq hg₂ hgs⟩

omit [SampleableType PQC] in
/-- Distribution equivalence between `redKemFailHiddenSaltClamp` and `Refinement.redKemFailHiddenSalt` when `2 ^ 32 ≤ B`, `q + 3 ≤ B`, and `q ≤ L`. -/
theorem redKemFailHiddenSaltClamp_evalDistEq
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (toKemCoins : BitVec 512 → BitVec 512) (hto : toKemCoins = id)
    (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (L qep B : ℕ) (h232 : 2 ^ 32 ≤ B)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
    (q : ℕ) (hq : SM.MakesAtMostQueries A q) (hqB : q + 3 ≤ B) (hqL : q ≤ L) :
    redKemFailHiddenSaltClamp P Dh encPt encT decT lam K toKemCoins L qep B A =ᵈ
      CryptoGames.LibsignalSM.Proofs.Refinement.redKemFailHiddenSalt
        P K ℓ Dh encPt encT decT idOf lam qep A := by
  subst hto; subst hid
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  have heq : redKemFailHiddenSaltClamp P Dh encPt encT decT lam K id L qep B A =
      (do
        let b ← $ᵗ Bool
        let k1 ← $ᵗ (BitVec 256)
        let k2 ← $ᵗ (BitVec 256)
        let pqrKey ← $ᵗ (BitVec 256)
        let idOf0 : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf0 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let gh₀ := (initState fig (k1, k2) b, false)
        let tr₀ := CryptoGames.LibsignalSM.Proofs.Refinement.initKemFailTrack P.C.F pqrKey
        let (_, (_, _, tr)) ←
          (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSimImpl
            P K ℓ Dh encPt encT decT idOf0 lam qep) A).run (sC₀, gh₀, tr₀)
        return tr.cand.getD (List.Vector.replicate 64 0, List.Vector.replicate 32 0)) := by
    unfold redKemFailHiddenSaltClamp
    refine bind_congr fun b => bind_congr fun k1 => bind_congr fun k2 => bind_congr fun pqrKey => ?_
    let idOf0 : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf0 25000 lam
    let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    let gh₀ : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) × Bool :=
      (initState fig (k1, k2) b, false)
    let tr₀ := CryptoGames.LibsignalSM.Proofs.Refinement.initKemFailTrack P.C.F pqrKey
    have hSim := simulateQ_kemFailOracle_eq_of_inv P Dh encPt encT decT lam K id rfl L qep B
      (by omega) (fun m sC gh _ => SimGameClampInv L B m sC gh.1)
      (fun m sC gh _ hInv Q => by have := hInv.1.hep Q; omega)
      (fun m sC gh _ hInv Q g hg => by have := hInv.1.hch Q g hg; omega)
      (fun _ _ _ _ _ _ => Or.inl h232)
      (fun m sC gh _ hInv wc hwc => by
        obtain ⟨h1, h2⟩ := hInv.1.hhonest wc hwc; exact ⟨by omega, by omega⟩)
      (fun m sC gh _ hInv Q => by have := hInv.2.htcur Q; omega)
      (fun m sC gh _ hInv => hInv.2.hFresh)
      (fun m sC gh _ hInv => by have := hInv.2.hTrans; omega)
      (fun m sC gh _ hInv => by have := hInv.2.hChall; omega)
      (fun m sC gh _ hInv => hInv.2.comp_dedup_le)
      (fun m sC gh _ hInv => hInv.2.comp_u)
      (fun m t sC gh tr hInv =>
        kemFailSimImpl_preserves_clampInv P Dh encPt encT decT lam K L qep B m
          h232 t sC gh tr hInv)
      A q hq' sC₀ gh₀ tr₀
      ⟨simBaseClampInv_init B q _ _ hqB,
       fig8GameClampInv_init P Dh encPt encT lam idOf0 L B q (k1, k2) b hqB hqL⟩
    change ((simulateQ (kemFailOracle P Dh encPt encT decT lam K id L qep B) A).run
      (sC₀, kemExtraEnc (PQC := BitVec 512) P gh₀.1 tr₀) >>= _) = _
    rw [hSim]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rfl
  rw [heq]
  exact evalDistEq_bind_bool_prod (fun b k => do
    let pqrKey ← $ᵗ (BitVec 256)
    let idOf0 : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf0 25000 lam
    let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
      initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    let gh₀ := (initState fig k b, false)
    let tr₀ := CryptoGames.LibsignalSM.Proofs.Refinement.initKemFailTrack P.C.F pqrKey
    let (_, (_, _, tr)) ←
      (simulateQ (CryptoGames.LibsignalSM.Proofs.Refinement.kemFailSimImpl
        P K ℓ Dh encPt encT decT idOf0 lam qep) A).run (sC₀, gh₀, tr₀)
    return tr.cand.getD (List.Vector.replicate 64 0, List.Vector.replicate 32 0))

omit [SampleableType PQC] in
/-- `KemFailFind` advantage equality between `redKemFailHiddenSaltClamp` and `Refinement.redKemFailHiddenSalt` when `2 ^ 32 ≤ B`, `q + 3 ≤ B`, and `q ≤ L`. -/
theorem redKemFailHiddenSaltClamp_advantage_eq
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (toKemCoins : BitVec 512 → BitVec 512) (hto : toKemCoins = id)
    (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (L qep B : ℕ) (h232 : 2 ^ 32 ≤ B)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
    (q : ℕ) (hq : SM.MakesAtMostQueries A q) (hqB : q + 3 ≤ B) (hqL : q ≤ L) :
    K.kemFailFindAdvantage
      (redKemFailHiddenSaltClamp P Dh encPt encT decT lam K toKemCoins L qep B A) =
    K.kemFailFindAdvantage
      (CryptoGames.LibsignalSM.Proofs.Refinement.redKemFailHiddenSalt
        P K ℓ Dh encPt encT decT idOf lam qep A) := by
  unfold CryptoVerification.LibsignalSpqrV1.MlKem.kemFailFindAdvantage
    CryptoVerification.LibsignalSpqrV1.MlKem.kemFailFindGame
  congr 1
  exact ((redKemFailHiddenSaltClamp_evalDistEq P Dh encPt encT decT lam K toKemCoins
    hto idOf hid L qep B h232 A q hq hqB hqL).bind fun _ => EvalDistEq.rfl).evalDist_eq

end EvalAgreement

end CryptoGames.Ratchet.LibsignalSim

