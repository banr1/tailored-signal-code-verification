/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingBase
public import Computational.Proofs.E2E.Dsl.DrSessionSimSend -- proof-setup: allow-public-import

/-!
# Tier-2 SPK Table Bookkeeping Expressions

`ReductionDsl` expressions for `Tier2Gs` ciphertext and `Hop2Aux` table operations, together with
their wire-length and `spkTier2Budget` cost bounds.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping

open ReductionDsl (Ty Env Ops Expr bits atomicSig atomicSessionOps BV256 PtT GhostStT B)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (Pos Record maxN maxN_eval partyEnc posTy posEnc posSender posEpoch posIdx
  pGet pSet letE_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState maxForwardJumps)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes paramsIdsWithSpqr sessionSchemeU spkTier2Budget)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (params_send_wire_length_le)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys (spkMaxWireLen ptKeyVal ptKeyE
  eval_ptKeyE cost_ptKeyE spkWireKeyVal spkWireKeyE eval_spkWireKeyE cost_spkWireKeyE_of_lt)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingPure (dllPushPrev dllPushNext
  dllUnlinkHead dllUnlinkPrev dllUnlinkNext Tier2Gs updParty updTbl1 updPosTbl)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs (hop2TblGet hop2TblSet)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingBase (tbl1GetE eval_tbl1GetE
  cost_tbl1GetE tbl1SetE eval_tbl1SetE cost_tbl1SetE posTblGetE eval_posTblGetE cost_posTblGetE
  posTblSetE eval_posTblSetE cost_posTblSetE tier2RecTy tier2RecEnc tier2RecPos tier2RecCt
  tier2GsTy tier2GsEnc gsStTier2E gsEpochTier2E gsIdxTier2E gsTLTier2E gsMaxAccTier2E
  gsNextIdTier2E gsHeadTblTier2E gsNodeRecTier2E gsNodeKeyTier2E gsNodePrevTier2E gsNodeNextTier2E
  gsPosNodeTier2E gsChallTblTier2E gsChallCountTier2E gsCompTblTier2E gsUncompCountTier2E
  safeChTier2E eval_safeChTier2E cost_safeChTier2E)

private theorem ite_eval {S : ReductionDsl.Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (c : Expr O Γ .bool) (a b : Expr O Γ t) (ρ : Env Γ) :
    (Expr.ite c a b).eval ρ = if c.eval ρ then a.eval ρ else b.eval ρ := rfl

private theorem pair_eval {S : ReductionDsl.Sig} {O : Ops S} {Γ : List (Ty S)} {a b : Ty S}
    (x : Expr O Γ a) (y : Expr O Γ b) (ρ : Env Γ) :
    (Expr.pair x y).eval ρ = (x.eval ρ, y.eval ρ) := rfl

/-! ## Ciphertext deletion and acceptance -/

section DeleteAndAccept

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}

local notation "S" => atomicSig ℓ Pt

@[expose] def deleteCiphertextTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (pos : Expr O Γ posTy) : Expr O Γ (tier2GsTy ℓ Pt) :=
  let Γ₀ : List (Ty S) := .prod (tier2GsTy ℓ Pt) posTy :: Γ
  let Γ₁ : List (Ty S) := .prod .nat (.prod .bool .bool) :: Γ₀
  let Γ₂ : List (Ty S) := .prod .nat (.prod .nat .nat) :: Γ₁
  .letE (.pair s pos)
    (let s0 : Expr O Γ₀ (tier2GsTy ℓ Pt) := .fst .v0
     let pos0 : Expr O Γ₀ posTy := .snd .v0
     .letE (.pair (posTblGetE (gsPosNodeTier2E s0) pos0)
             (.pair (posTblGetE (gsChallTblTier2E s0) pos0)
                    (posTblGetE (gsCompTblTier2E s0) pos0)))
       (let s1 : Expr O Γ₁ (tier2GsTy ℓ Pt) := .fst .v1
        let pos1 : Expr O Γ₁ posTy := .snd .v1
        let sender1 : Expr O Γ₁ .bool := posSender pos1
        let idDel : Expr O Γ₁ .nat := .fst .v0
        let wasChall : Expr O Γ₁ .bool := .fst (.snd .v0)
        let challTbl' := posTblSetE (gsChallTblTier2E s1) pos1 (.bool false)
        let challCount' :=
          Expr.ite wasChall
            (pSet (gsChallCountTier2E s1) sender1
              (.sub (pGet (gsChallCountTier2E s1) sender1) (.nat 1)))
            (gsChallCountTier2E s1)
        let compTbl' := posTblSetE (gsCompTblTier2E s1) pos1 (.bool false)
        .ite (.eqN idDel (.nat 0))
          (.pair (.fst s1)
            (.pair (.fst (.snd s1))
              (.pair (gsPosNodeTier2E s1)
                (.pair (.pair challTbl' challCount')
                       (.pair compTbl' (gsUncompCountTier2E s1))))))
          (.letE (.pair (.tget (gsNodeKeyTier2E s1) idDel)
                   (.pair (.tget (gsNodePrevTier2E s1) idDel)
                          (.tget (gsNodeNextTier2E s1) idDel)))
            (let s2 : Expr O Γ₂ (tier2GsTy ℓ Pt) := .fst .v2
             let pos2 : Expr O Γ₂ posTy := .snd .v2
             let sender2 : Expr O Γ₂ .bool := posSender pos2
             let wasChall2 : Expr O Γ₂ .bool := .fst (.snd .v1)
             let wasComp2 : Expr O Γ₂ .bool := .snd (.snd .v1)
             let kE : Expr O Γ₂ .nat := .fst .v0
             let pE : Expr O Γ₂ .nat := .fst (.snd .v0)
             let nE : Expr O Γ₂ .nat := .snd (.snd .v0)
             let oldHead := tbl1GetE (gsHeadTblTier2E s2) sender2 kE
             let newHead := Expr.ite (.eqN pE (.nat 0)) nE oldHead
             let headTbl' := tbl1SetE (gsHeadTblTier2E s2) sender2 kE newHead
             let prev' := Expr.ite (.eqN nE (.nat 0)) (gsNodePrevTier2E s2)
               (.tset (gsNodePrevTier2E s2) nE pE)
             let next' := Expr.ite (.eqN pE (.nat 0)) (gsNodeNextTier2E s2)
               (.tset (gsNodeNextTier2E s2) pE nE)
             let posNode' := posTblSetE (gsPosNodeTier2E s2) pos2 (.nat 0)
             let challTbl2 := posTblSetE (gsChallTblTier2E s2) pos2 (.bool false)
             let challCount2 :=
               Expr.ite wasChall2
                 (pSet (gsChallCountTier2E s2) sender2
                   (.sub (pGet (gsChallCountTier2E s2) sender2) (.nat 1)))
                 (gsChallCountTier2E s2)
             let compTbl2 := posTblSetE (gsCompTblTier2E s2) pos2 (.bool false)
             let uncompCount2 :=
               Expr.ite wasComp2 (gsUncompCountTier2E s2)
                 (pSet (gsUncompCountTier2E s2) sender2
                   (.sub (pGet (gsUncompCountTier2E s2) sender2) (.nat 1)))
             .pair (.fst s2)
               (.pair
                 (.pair (.pair (gsNextIdTier2E s2) headTbl')
                        (.pair (.fst (.snd (.fst (.snd s2))))
                               (.pair prev' next')))
                 (.pair posNode'
                   (.pair (.pair challTbl2 challCount2)
                          (.pair compTbl2 uncompCount2))))))))

@[simp] theorem eval_deleteCiphertextTier2E {Γ : List (Ty S)}
    (s : Expr O Γ (tier2GsTy ℓ Pt)) (pos : Expr O Γ posTy) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (p0 : Pos)
    (hs : s.eval ρ = tier2GsEnc Pt d) (hpos : pos.eval ρ = posEnc p0) :
    (deleteCiphertextTier2E s pos).eval ρ = tier2GsEnc Pt (d.delete p0) := by
  unfold deleteCiphertextTier2E Tier2Gs.delete
  rw [letE_eval]
  have hp0 : (Expr.pair s pos).eval ρ = (tier2GsEnc Pt d, posEnc p0) := by
    simp [Expr.eval, hs, hpos]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (tier2GsTy ℓ Pt) posTy) (tier2GsEnc Pt d, posEnc p0) ρ
  rw [letE_eval]
  have hget1 : (Expr.pair (O := O) (posTblGetE (gsPosNodeTier2E (.fst .v0)) (.snd .v0))
      (.pair (posTblGetE (gsChallTblTier2E (.fst .v0)) (.snd .v0))
             (posTblGetE (gsCompTblTier2E (.fst .v0)) (.snd .v0)))).eval ρ₁ =
      (d.posNode p0.sender p0.epoch p0.idx,
        (d.challTbl p0.sender p0.epoch p0.idx, d.compTbl p0.sender p0.epoch p0.idx)) := by
    dsimp only [Expr.eval]
    rw [eval_posTblGetE _ _ ρ₁ d.posNode p0 rfl rfl,
        eval_posTblGetE _ _ ρ₁ d.challTbl p0 rfl rfl,
        eval_posTblGetE _ _ ρ₁ d.compTbl p0 rfl rfl]
  rw [hget1]; clear hget1
  set idDel := d.posNode p0.sender p0.epoch p0.idx
  set wasChall := d.challTbl p0.sender p0.epoch p0.idx
  set wasComp := d.compTbl p0.sender p0.epoch p0.idx
  set ρ₂ := Env.cons (t := .prod .nat (.prod .bool .bool)) (idDel, (wasChall, wasComp)) ρ₁
  have hsender1 : (posSender (.snd (Expr.v1 (O := O)))).eval ρ₂ = partyEnc p0.sender := by
    rcases p0 with ⟨_, _, _⟩; rfl
  by_cases hid0 : idDel = 0
  · rw [ite_eval]
    have heq_t : ((Expr.eqN (O := O) (.fst .v0) (.nat 0)).eval ρ₂) = true := by
      dsimp [Expr.eval, Expr.v0, Env.get, ρ₂]
      exact decide_eq_true hid0
    rw [heq_t]
    simp only [hid0, ↓reduceIte]
    simp only [pair_eval, ite_eval,
      eval_posTblSetE (gsChallTblTier2E (.fst (Expr.v1 (O := O)))) (.snd .v1) (.bool false)
        ρ₂ d.challTbl p0 rfl rfl,
      eval_posTblSetE (gsCompTblTier2E (.fst (Expr.v1 (O := O)))) (.snd .v1) (.bool false)
        ρ₂ d.compTbl p0 rfl rfl]
    dsimp only [ρ₂, ρ₁]
    rcases p0 with ⟨ps, pe, pi⟩
    cases ps <;> by_cases hwc : wasChall = true <;>
      simp [hwc, pSet, pGet, posSender, posEnc, updParty, partyEnc, gsPosNodeTier2E,
        gsChallCountTier2E, gsUncompCountTier2E, tier2GsEnc,
        Expr.eval, Expr.v0, Expr.v1]
  · rw [ite_eval]
    have heq_f : ((Expr.eqN (O := O) (.fst .v0) (.nat 0)).eval ρ₂) = false := by
      dsimp [Expr.eval, Expr.v0, Env.get, ρ₂]
      exact decide_eq_false hid0
    rw [heq_f]
    simp only [Bool.false_eq_true, hid0, ↓reduceIte]
    rw [letE_eval]
    set k0 := d.nodeKey idDel
    set pv := d.nodePrev idDel
    set nx := d.nodeNext idDel
    have hget2 : (Expr.pair (O := O) (.tget (gsNodeKeyTier2E (.fst .v1)) (.fst .v0))
        (.pair (.tget (gsNodePrevTier2E (.fst .v1)) (.fst .v0))
               (.tget (gsNodeNextTier2E (.fst .v1)) (.fst .v0)))).eval ρ₂ = (k0, (pv, nx)) := rfl
    rw [hget2]; clear hget2
    set ρ₃ := Env.cons (t := .prod .nat (.prod .nat .nat)) (k0, (pv, nx)) ρ₂
    have hsender2 : (posSender (.snd (Expr.v2 (O := O)))).eval ρ₃ = partyEnc p0.sender := by
      rcases p0 with ⟨_, _, _⟩; rfl
    have holdHd : (tbl1GetE (gsHeadTblTier2E (.fst (Expr.v2 (O := O))))
        (posSender (.snd .v2)) (.fst .v0)).eval ρ₃ = d.headTbl p0.sender k0 :=
      eval_tbl1GetE (gsHeadTblTier2E (.fst (Expr.v2 (O := O)))) (posSender (.snd .v2)) (.fst .v0)
        ρ₃ d.headTbl p0.sender rfl hsender2
    have hnewHd : (Expr.ite (.eqN (.fst (.snd (Expr.v0 (O := O)))) (.nat 0))
        (.snd (.snd .v0))
        (tbl1GetE (gsHeadTblTier2E (.fst .v2)) (posSender (.snd .v2)) (.fst .v0))).eval ρ₃ =
        dllUnlinkHead (d.headTbl p0.sender k0) pv nx := by
      rw [ite_eval, holdHd]
      dsimp [dllUnlinkHead, Expr.eval, Expr.v0, Env.get, ρ₃]
      by_cases hpv : pv = 0 <;> simp [hpv]
    have hhdTbl : (tbl1SetE (gsHeadTblTier2E (.fst (Expr.v2 (O := O)))) (posSender (.snd .v2))
        (.fst .v0)
        (Expr.ite (.eqN (.fst (.snd .v0)) (.nat 0)) (.snd (.snd .v0))
          (tbl1GetE (gsHeadTblTier2E (.fst .v2)) (posSender (.snd .v2)) (.fst .v0)))).eval ρ₃ =
        (updTbl1 d.headTbl p0.sender k0 (dllUnlinkHead (d.headTbl p0.sender k0) pv nx) .A,
         updTbl1 d.headTbl p0.sender k0 (dllUnlinkHead (d.headTbl p0.sender k0) pv nx) .B) := by
      rw [eval_tbl1SetE (gsHeadTblTier2E (.fst (Expr.v2 (O := O)))) (posSender (.snd .v2))
            (.fst .v0) _ ρ₃ d.headTbl p0.sender rfl hsender2, hnewHd]
      rfl
    have hprev : (Expr.ite (.eqN (.snd (.snd (Expr.v0 (O := O)))) (.nat 0))
        (gsNodePrevTier2E (.fst .v2))
        (.tset (gsNodePrevTier2E (.fst .v2)) (.snd (.snd .v0)) (.fst (.snd .v0)))).eval ρ₃ =
        dllUnlinkPrev pv nx d.nodePrev := by
      rw [ite_eval]
      dsimp [dllUnlinkPrev, gsNodePrevTier2E, tier2GsEnc, ρ₃, ρ₂, ρ₁, Expr.eval, Expr.v0, Expr.v2,
        Env.get]
      by_cases hnx : nx = 0
      · simp [hnx]
      · simp only [hnx, ↓reduceIte]
        funext j
        by_cases hj : j = nx <;> simp [hj]
    have hnext : (Expr.ite (.eqN (.fst (.snd (Expr.v0 (O := O)))) (.nat 0))
        (gsNodeNextTier2E (.fst .v2))
        (.tset (gsNodeNextTier2E (.fst .v2)) (.fst (.snd .v0)) (.snd (.snd .v0)))).eval ρ₃ =
        dllUnlinkNext pv nx d.nodeNext := by
      rw [ite_eval]
      dsimp [dllUnlinkNext, gsNodeNextTier2E, tier2GsEnc, ρ₃, ρ₂, ρ₁, Expr.eval, Expr.v0, Expr.v2,
        Env.get]
      by_cases hpv : pv = 0
      · simp [hpv]
      · simp only [hpv, ↓reduceIte]
        funext j
        by_cases hj : j = pv <;> simp [hj]
    simp only [pair_eval, ite_eval, hhdTbl, hprev, hnext,
      eval_posTblSetE (gsPosNodeTier2E (.fst (Expr.v2 (O := O)))) (.snd .v2) (.nat 0)
        ρ₃ d.posNode p0 rfl rfl,
      eval_posTblSetE (gsChallTblTier2E (.fst (Expr.v2 (O := O)))) (.snd .v2) (.bool false)
        ρ₃ d.challTbl p0 rfl rfl,
      eval_posTblSetE (gsCompTblTier2E (.fst (Expr.v2 (O := O)))) (.snd .v2) (.bool false)
        ρ₃ d.compTbl p0 rfl rfl]
    dsimp only [ρ₃, ρ₂, ρ₁]
    rcases p0 with ⟨ps, pe, pi⟩
    cases ps <;> by_cases hwc : wasChall = true <;> by_cases hwcp : wasComp = true <;>
      simp [hwc, hwcp, pSet, pGet, posSender, posEnc, updParty, partyEnc, gsNextIdTier2E,
        gsChallCountTier2E, gsUncompCountTier2E, tier2GsEnc,
        Expr.eval, Expr.v0, Expr.v1, Expr.v2]

theorem cost_deleteCiphertextTier2E {Γ : List (Ty S)}
    (s : Expr O Γ (tier2GsTy ℓ Pt)) (pos : Expr O Γ posTy) :
    (deleteCiphertextTier2E s pos).cost ≤ s.cost + pos.cost + 2800 := by
  let c0 : List (Ty S) := .prod (tier2GsTy ℓ Pt) posTy :: Γ
  let c1 : List (Ty S) := .prod .nat (.prod .bool .bool) :: c0
  let c2 : List (Ty S) := .prod .nat (.prod .nat .nat) :: c1
  have hg1 := cost_posTblGetE (O := O) (Γ := c0) (gsPosNodeTier2E (.fst .v0)) (.snd .v0)
  have hg2 := cost_posTblGetE (O := O) (Γ := c0) (gsChallTblTier2E (.fst .v0)) (.snd .v0)
  have hg3 := cost_posTblGetE (O := O) (Γ := c0) (gsCompTblTier2E (.fst .v0)) (.snd .v0)
  have hs1 := cost_posTblSetE (O := O) (Γ := c1)
    (gsChallTblTier2E (.fst .v1)) (.snd .v1) (.bool false)
  have hs2 := cost_posTblSetE (O := O) (Γ := c1)
    (gsCompTblTier2E (.fst .v1)) (.snd .v1) (.bool false)
  have htg := cost_tbl1GetE (O := O) (Γ := c2)
    (gsHeadTblTier2E (.fst .v2)) (posSender (.snd .v2)) (.fst .v0)
  have hts := cost_tbl1SetE (O := O) (Γ := c2)
    (gsHeadTblTier2E (.fst .v2)) (posSender (.snd .v2)) (.fst .v0)
    (.ite (.eqN (.fst (.snd .v0)) (.nat 0)) (.snd (.snd .v0))
      (tbl1GetE (gsHeadTblTier2E (.fst .v2)) (posSender (.snd .v2)) (.fst .v0)))
  have hp0 := cost_posTblSetE (O := O) (Γ := c2)
    (gsPosNodeTier2E (.fst .v2)) (.snd .v2) (.nat 0)
  have hp1 := cost_posTblSetE (O := O) (Γ := c2)
    (gsChallTblTier2E (.fst .v2)) (.snd .v2) (.bool false)
  have hp2 := cost_posTblSetE (O := O) (Γ := c2)
    (gsCompTblTier2E (.fst .v2)) (.snd .v2) (.bool false)
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  simp only [deleteCiphertextTier2E, pSet, pGet, posSender, gsNextIdTier2E, gsHeadTblTier2E,
    gsNodeKeyTier2E, gsNodePrevTier2E, gsNodeNextTier2E, gsPosNodeTier2E, gsChallTblTier2E,
    gsChallCountTier2E, gsCompTblTier2E, gsUncompCountTier2E,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, hb0, hb1] at hg1 hg2 hg3 hs1 hs2 htg hts hp0 hp1 hp2 ⊢
  omega

@[expose] def acceptCiphertextTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) (st' : Expr O Γ GhostStT) (pos : Expr O Γ posTy) :
    Expr O Γ (tier2GsTy ℓ Pt) :=
  .letE (.pair (deleteCiphertextTier2E s pos) (.pair p (.pair st' pos)))
    (let d1 : Expr O _ (tier2GsTy ℓ Pt) := .fst .v0
     let p0 : Expr O _ .bool := .fst (.snd .v0)
     let st0 : Expr O _ GhostStT := .fst (.snd (.snd .v0))
     let pos0 : Expr O _ posTy := .snd (.snd (.snd .v0))
     let epNew := maxN (pGet (gsEpochTier2E d1) p0) (posEpoch pos0)
     let maOld := tbl1GetE (gsMaxAccTier2E d1) p0 (posEpoch pos0)
     let maNew := maxN maOld (posIdx pos0)
     .pair
       (.pair (.pair (pSet (gsStTier2E d1) p0 st0) (.snd (.fst (.fst d1))))
              (.pair (.pair (pSet (gsEpochTier2E d1) p0 epNew) (gsIdxTier2E d1))
                     (.pair (gsTLTier2E d1)
                            (tbl1SetE (gsMaxAccTier2E d1) p0 (posEpoch pos0) maNew))))
       (.snd d1))

@[simp] theorem eval_acceptCiphertextTier2E {Γ : List (Ty S)}
    (s : Expr O Γ (tier2GsTy ℓ Pt)) (p : Expr O Γ .bool)
    (st' : Expr O Γ GhostStT) (pos : Expr O Γ posTy) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (P : Party) (p0 : Pos)
    (hs : s.eval ρ = tier2GsEnc Pt d) (hp : p.eval ρ = partyEnc P)
    (hpos : pos.eval ρ = posEnc p0) :
    (acceptCiphertextTier2E s p st' pos).eval ρ =
      tier2GsEnc Pt (d.accept P (st'.eval ρ) p0) := by
  unfold acceptCiphertextTier2E Tier2Gs.accept
  rw [letE_eval]
  have hp_in : (Expr.pair (deleteCiphertextTier2E s pos) (.pair p (.pair st' pos))).eval ρ =
      (tier2GsEnc Pt (d.delete p0), (partyEnc P, (st'.eval ρ, posEnc p0))) := by
    simp [Expr.eval, eval_deleteCiphertextTier2E s pos ρ d p0 hs hpos, hp, hpos]
  rw [hp_in]; clear hp_in
  set d1 := d.delete p0
  set ρ₁ := Env.cons (t := .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod GhostStT posTy)))
    (tier2GsEnc Pt d1, (partyEnc P, (st'.eval ρ, posEnc p0))) ρ
  have hma_get : (tbl1GetE (gsMaxAccTier2E (.fst (Expr.v0 (O := O)))) (.fst (.snd .v0))
      (posEpoch (.snd (.snd (.snd .v0))))).eval ρ₁ = d1.maxAcc P p0.epoch := by
    rw [eval_tbl1GetE _ _ _ ρ₁ d1.maxAcc P rfl rfl]
    rcases p0 with ⟨_, _, _⟩; rfl
  have hma_set : (tbl1SetE (gsMaxAccTier2E (.fst (Expr.v0 (O := O)))) (.fst (.snd .v0))
      (posEpoch (.snd (.snd (.snd .v0))))
      (maxN (tbl1GetE (gsMaxAccTier2E (.fst .v0)) (.fst (.snd .v0))
        (posEpoch (.snd (.snd (.snd .v0)))))
        (posIdx (.snd (.snd (.snd .v0)))))).eval ρ₁ =
      (updTbl1 d1.maxAcc P p0.epoch (max (d1.maxAcc P p0.epoch) p0.idx) .A,
       updTbl1 d1.maxAcc P p0.epoch (max (d1.maxAcc P p0.epoch) p0.idx) .B) := by
    rw [eval_tbl1SetE _ _ _ _ ρ₁ d1.maxAcc P rfl rfl, maxN_eval, hma_get]
    rcases p0 with ⟨_, _, _⟩; rfl
  dsimp only [Expr.eval]
  rw [hma_set]
  rcases p0 with ⟨ps, pe, pi⟩
  cases P <;>
    simp [pSet, pGet, maxN_eval, posEpoch, posEnc, updParty, partyEnc,
      gsStTier2E, gsEpochTier2E, gsIdxTier2E, gsTLTier2E, tier2GsEnc, ρ₁,
      Expr.eval, Expr.v0]

theorem cost_acceptCiphertextTier2E {Γ : List (Ty S)}
    (s : Expr O Γ (tier2GsTy ℓ Pt)) (p : Expr O Γ .bool)
    (st' : Expr O Γ GhostStT) (pos : Expr O Γ posTy) :
    (acceptCiphertextTier2E s p st' pos).cost ≤
      s.cost + p.cost + 2 * pos.cost + st'.cost + 3400 := by
  let c0 : List (Ty S) := .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod GhostStT posTy)) :: Γ
  have hdel := cost_deleteCiphertextTier2E s pos
  have htg := cost_tbl1GetE (O := O) (Γ := c0)
    (gsMaxAccTier2E (.fst .v0)) (.fst (.snd .v0)) (posEpoch (.snd (.snd (.snd .v0))))
  have hts := cost_tbl1SetE (O := O) (Γ := c0)
    (gsMaxAccTier2E (.fst .v0)) (.fst (.snd .v0)) (posEpoch (.snd (.snd (.snd .v0))))
    (maxN (tbl1GetE (gsMaxAccTier2E (.fst .v0)) (.fst (.snd .v0))
      (posEpoch (.snd (.snd (.snd .v0)))))
      (posIdx (.snd (.snd (.snd .v0)))))
  simp only [acceptCiphertextTier2E, pSet, pGet, maxN, CryptoGames.SM.leN, posEpoch, posIdx,
    gsStTier2E, gsEpochTier2E, gsIdxTier2E, gsTLTier2E, gsMaxAccTier2E,
    Expr.cost, Expr.v0] at hdel htg hts ⊢
  omega

end DeleteAndAccept

/-! ## In-transit lookup and ciphertext recording -/

section WireAndHop2Ops

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "S" => atomicSig ℓ Pt
local notation "OO" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[expose] def inTransitTier2E {Γ : List (Ty S)} (s : Expr OO Γ (tier2GsTy ℓ Pt))
    (qParty : Expr OO Γ .bool) (c : Expr OO Γ (B 32)) :
    Expr OO Γ (.opt (tier2RecTy ℓ Pt)) :=
  .letE (.pair s (.pair qParty (spkWireKeyE c)))
    (.caseOpt (.snd (.snd .v0))
      .none
      (.tget (gsNodeRecTier2E (.fst .v1))
        (tbl1GetE (gsHeadTblTier2E (.fst .v1)) (.fst (.snd .v1)) .v0)))

private theorem caseOpt_eval {Γ : List (Ty S)} {a b : Ty S}
    (scr : Expr OO Γ (.opt a)) (n : Expr OO Γ b) (sm : Expr OO (a :: Γ) b) (ρ : Env Γ) :
    (Expr.caseOpt scr n sm).eval ρ =
      match scr.eval ρ with
      | none => n.eval ρ
      | some x => sm.eval (.cons x ρ) := by
  dsimp only [Expr.eval]
  cases scr.eval ρ <;> rfl

@[simp] theorem eval_inTransitTier2E {Γ : List (Ty S)}
    (s : Expr OO Γ (tier2GsTy ℓ Pt)) (qParty : Expr OO Γ .bool)
    (c : Expr OO Γ (B 32)) (ρ : Env Γ) (d : Tier2Gs ℓ) (Q : Party)
    (hs : s.eval ρ = tier2GsEnc Pt d) (hq : qParty.eval ρ = partyEnc Q) :
    (inTransitTier2E s qParty c).eval ρ = (d.inTransit Q (c.eval ρ)).map tier2RecEnc := by
  unfold inTransitTier2E Tier2Gs.inTransit
  rw [letE_eval]
  have hwk_ev := eval_spkWireKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) c ρ
  have hp0 : (Expr.pair s (.pair qParty (spkWireKeyE c))).eval ρ =
      (tier2GsEnc Pt d, (partyEnc Q, spkWireKeyVal ℓ (c.eval ρ))) := by
    simp [Expr.eval, hs, hq, hwk_ev]
  rw [hp0]; clear hp0 hwk_ev
  cases hwk : spkWireKeyVal ℓ (c.eval ρ) with
  | none => rfl
  | some k0 =>
    let ρ₁ := Env.cons (t := .prod (tier2GsTy ℓ Pt) (.prod .bool (.opt .nat)))
      (tier2GsEnc Pt d, (partyEnc Q, some k0)) ρ
    let ρ₂ := Env.cons (t := .nat) k0 ρ₁
    rw [caseOpt_eval]
    have hscr : (Expr.snd (.snd (Expr.v0 (O := OO)))).eval ρ₁ = some k0 := rfl
    rw [hscr]
    dsimp only [Expr.eval]
    have hhd : (tbl1GetE (gsHeadTblTier2E (.fst (Expr.v1 (O := OO))))
        (.fst (.snd .v1)) .v0).eval ρ₂ = d.headTbl Q k0 :=
      eval_tbl1GetE (gsHeadTblTier2E (.fst (Expr.v1 (O := OO)))) (.fst (.snd .v1)) .v0
        ρ₂ d.headTbl Q rfl rfl
    rw [hhd]
    rfl

theorem cost_inTransitTier2E {Γ : List (Ty S)} (hℓ : ℓ < 10 ^ 6)
    (s : Expr OO Γ (tier2GsTy ℓ Pt)) (qParty : Expr OO Γ .bool) (c : Expr OO Γ (B 32)) :
    (inTransitTier2E s qParty c).cost ≤
      s.cost + qParty.cost + c.cost + 30 * ℓ + 14300 := by
  let c0 : List (Ty S) := .prod (tier2GsTy ℓ Pt) (.prod .bool (.opt .nat)) :: Γ
  let c1 : List (Ty S) := .nat :: c0
  have hwk := cost_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) hℓ c
  have htg := cost_tbl1GetE (O := OO) (Γ := c1)
    (gsHeadTblTier2E (.fst .v1)) (.fst (.snd .v1)) .v0
  simp only [inTransitTier2E, gsNodeRecTier2E, gsHeadTblTier2E,
    Expr.cost, Expr.v0, Expr.v1] at hwk htg ⊢
  omega

@[expose] def recordCiphertextTier2E {Γ : List (Ty S)} (Δ : ℕ)
    (s : Expr OO Γ (tier2GsTy ℓ Pt)) (p : Expr OO Γ .bool)
    (st' : Expr OO Γ GhostStT) (recE : Expr OO Γ (tier2RecTy ℓ Pt))
    (isChall : Expr OO Γ .bool) : Expr OO Γ (tier2GsTy ℓ Pt) :=
  .letE (.pair s (.pair p (.pair st' (.pair recE isChall))))
    (let s0 : Expr OO _ (tier2GsTy ℓ Pt) := .fst .v0
     let r0 : Expr OO _ (tier2RecTy ℓ Pt) := .fst (.snd (.snd (.snd .v0)))
     .caseOpt (spkWireKeyE (tier2RecCt r0))
       s0
       (let s1 : Expr OO _ (tier2GsTy ℓ Pt) := .fst .v1
        let p1 : Expr OO _ .bool := .fst (.snd .v1)
        let st1 : Expr OO _ GhostStT := .fst (.snd (.snd .v1))
        let r1 : Expr OO _ (tier2RecTy ℓ Pt) := .fst (.snd (.snd (.snd .v1)))
        let ch1 : Expr OO _ .bool := .snd (.snd (.snd (.snd .v1)))
        let k0 : Expr OO _ .nat := .v0
        let rPos := tier2RecPos r1
        let safe := safeChTier2E Δ s1 p1
        let idNew := gsNextIdTier2E s1
        let oldHead := tbl1GetE (gsHeadTblTier2E s1) p1 k0
        let prev1 := Expr.tset (gsNodePrevTier2E s1) idNew (.nat 0)
        let prev' := Expr.ite (.eqN oldHead (.nat 0)) prev1 (.tset prev1 oldHead idNew)
        let next' := Expr.tset (gsNodeNextTier2E s1) idNew oldHead
        let nodeRec' := Expr.tset (gsNodeRecTier2E s1) idNew (.some r1)
        let nodeKey' := Expr.tset (gsNodeKeyTier2E s1) idNew k0
        let headTbl' := tbl1SetE (gsHeadTblTier2E s1) p1 k0 idNew
        let posNode' := posTblSetE (gsPosNodeTier2E s1) rPos idNew
        let challTbl' :=
          Expr.ite ch1 (posTblSetE (gsChallTblTier2E s1) rPos (.bool true)) (gsChallTblTier2E s1)
        let challCount' :=
          Expr.ite ch1
            (pSet (gsChallCountTier2E s1) p1 (.add (pGet (gsChallCountTier2E s1) p1) (.nat 1)))
            (gsChallCountTier2E s1)
        let compTbl' :=
          Expr.ite safe (gsCompTblTier2E s1) (posTblSetE (gsCompTblTier2E s1) rPos (.bool true))
        let uncompCount' :=
          Expr.ite safe
            (pSet (gsUncompCountTier2E s1) p1 (.add (pGet (gsUncompCountTier2E s1) p1) (.nat 1)))
            (gsUncompCountTier2E s1)
        .pair
          (.pair (.pair (pSet (gsStTier2E s1) p1 st1) (.snd (.fst (.fst s1))))
                 (.pair (.pair (gsEpochTier2E s1) (pSet (gsIdxTier2E s1) p1 (posIdx rPos)))
                        (.snd (.snd (.fst s1)))))
          (.pair
            (.pair (.pair (.add idNew (.nat 1)) headTbl')
                   (.pair (.pair nodeRec' nodeKey') (.pair prev' next')))
            (.pair posNode'
              (.pair (.pair challTbl' challCount') (.pair compTbl' uncompCount'))))))

@[simp] theorem eval_recordCiphertextTier2E {Γ : List (Ty S)} (Δ : ℕ)
    (s : Expr OO Γ (tier2GsTy ℓ Pt)) (p : Expr OO Γ .bool)
    (st' : Expr OO Γ GhostStT) (recE : Expr OO Γ (tier2RecTy ℓ Pt))
    (isChall : Expr OO Γ .bool) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (P : Party) (r : Record (Plain ℓ) Bytes)
    (hs : s.eval ρ = tier2GsEnc Pt d) (hp : p.eval ρ = partyEnc P)
    (hrec : recE.eval ρ = tier2RecEnc r) :
    (recordCiphertextTier2E Δ s p st' recE isChall).eval ρ =
      tier2GsEnc Pt (d.record Δ P (st'.eval ρ) r (isChall.eval ρ)) := by
  unfold recordCiphertextTier2E Tier2Gs.record
  generalize hch : isChall.eval ρ = ch
  rw [letE_eval]
  have hp0 : (Expr.pair s (.pair p (.pair st' (.pair recE isChall)))).eval ρ =
      (tier2GsEnc Pt d, (partyEnc P, (st'.eval ρ, (tier2RecEnc r, ch)))) := by
    simp [Expr.eval, hs, hp, hrec, hch]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons
    (t := .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod GhostStT (.prod (tier2RecTy ℓ Pt) .bool))))
    (tier2GsEnc Pt d, (partyEnc P, (st'.eval ρ, (tier2RecEnc r, ch)))) ρ
  have hwk_ev := eval_spkWireKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (tier2RecCt (.fst (.snd (.snd (.snd .v0))))) ρ₁
  have hct_ev : (tier2RecCt (.fst (.snd (.snd (.snd (Expr.v0 (O := OO))))))).eval ρ₁ = r.ct := rfl
  rw [hct_ev] at hwk_ev
  rw [caseOpt_eval, hwk_ev]; clear hwk_ev hct_ev
  cases hwk : spkWireKeyVal ℓ r.ct with
  | none => rfl
  | some k0 =>
    dsimp only
    set ρ₂ := Env.cons (t := .nat) k0 ρ₁
    have hrPos : (tier2RecPos (.fst (.snd (.snd (.snd (Expr.v1 (O := OO))))))).eval ρ₂ =
        posEnc r.pos := rfl
    have hsc : (safeChTier2E Δ (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1))).eval ρ₂ =
        d.safeCh Δ P := eval_safeChTier2E Δ _ _ ρ₂ d P rfl rfl
    have holdHd : (tbl1GetE (gsHeadTblTier2E (.fst (Expr.v1 (O := OO))))
        (.fst (.snd .v1)) .v0).eval ρ₂ = d.headTbl P k0 :=
      eval_tbl1GetE (gsHeadTblTier2E (.fst (Expr.v1 (O := OO)))) (.fst (.snd .v1)) .v0
        ρ₂ d.headTbl P rfl rfl
    have hhdTbl : (tbl1SetE (gsHeadTblTier2E (.fst (Expr.v1 (O := OO)))) (.fst (.snd .v1))
        .v0 (gsNextIdTier2E (.fst .v1))).eval ρ₂ =
        (updTbl1 d.headTbl P k0 d.nextId .A, updTbl1 d.headTbl P k0 d.nextId .B) :=
      eval_tbl1SetE (gsHeadTblTier2E (.fst (Expr.v1 (O := OO)))) (.fst (.snd .v1))
        .v0 (gsNextIdTier2E (.fst .v1)) ρ₂ d.headTbl P rfl rfl
    have hposN : (posTblSetE (gsPosNodeTier2E (.fst (Expr.v1 (O := OO))))
        (tier2RecPos (.fst (.snd (.snd (.snd .v1))))) (gsNextIdTier2E (.fst .v1))).eval ρ₂ =
        (updPosTbl d.posNode r.pos d.nextId .A, updPosTbl d.posNode r.pos d.nextId .B) :=
      eval_posTblSetE (gsPosNodeTier2E (.fst (Expr.v1 (O := OO))))
        (tier2RecPos (.fst (.snd (.snd (.snd .v1))))) (gsNextIdTier2E (.fst .v1))
        ρ₂ d.posNode r.pos rfl hrPos
    have hchSet : (posTblSetE (gsChallTblTier2E (.fst (Expr.v1 (O := OO))))
        (tier2RecPos (.fst (.snd (.snd (.snd .v1))))) (.bool true)).eval ρ₂ =
        (updPosTbl d.challTbl r.pos true .A, updPosTbl d.challTbl r.pos true .B) :=
      eval_posTblSetE (gsChallTblTier2E (.fst (Expr.v1 (O := OO))))
        (tier2RecPos (.fst (.snd (.snd (.snd .v1))))) (.bool true)
        ρ₂ d.challTbl r.pos rfl hrPos
    have hcpSet : (posTblSetE (gsCompTblTier2E (.fst (Expr.v1 (O := OO))))
        (tier2RecPos (.fst (.snd (.snd (.snd .v1))))) (.bool true)).eval ρ₂ =
        (updPosTbl d.compTbl r.pos true .A, updPosTbl d.compTbl r.pos true .B) :=
      eval_posTblSetE (gsCompTblTier2E (.fst (Expr.v1 (O := OO))))
        (tier2RecPos (.fst (.snd (.snd (.snd .v1))))) (.bool true)
        ρ₂ d.compTbl r.pos rfl hrPos
    have hprev : (Expr.ite (.eqN (tbl1GetE (gsHeadTblTier2E (.fst (Expr.v1 (O := OO))))
          (.fst (.snd .v1)) .v0) (.nat 0))
        (.tset (gsNodePrevTier2E (.fst .v1)) (gsNextIdTier2E (.fst .v1)) (.nat 0))
        (.tset (.tset (gsNodePrevTier2E (.fst .v1)) (gsNextIdTier2E (.fst .v1)) (.nat 0))
          (tbl1GetE (gsHeadTblTier2E (.fst .v1)) (.fst (.snd .v1)) .v0)
          (gsNextIdTier2E (.fst .v1)))).eval ρ₂ =
        dllPushPrev (d.headTbl P k0) d.nextId d.nodePrev := by
      rw [ite_eval]
      by_cases hhd0 : d.headTbl P k0 = 0
      · have heq_t : ((Expr.eqN (tbl1GetE (gsHeadTblTier2E (.fst (Expr.v1 (O := OO))))
            (.fst (.snd .v1)) .v0) (.nat 0)).eval ρ₂) = true := by
          dsimp only [Expr.eval]
          rw [holdHd]
          exact decide_eq_true hhd0
        rw [heq_t]
        simp only [↓reduceIte]
        dsimp [dllPushPrev, gsNodePrevTier2E, gsNextIdTier2E, tier2GsEnc, ρ₂, ρ₁, Expr.eval,
          Expr.v1, Env.get]
        funext j
        by_cases hj : j = d.nextId <;> simp [hhd0, hj]
      · have heq_f : ((Expr.eqN (tbl1GetE (gsHeadTblTier2E (.fst (Expr.v1 (O := OO))))
            (.fst (.snd .v1)) .v0) (.nat 0)).eval ρ₂) = false := by
          dsimp only [Expr.eval]
          rw [holdHd]
          exact decide_eq_false hhd0
        rw [heq_f]
        simp only [Bool.false_eq_true, ↓reduceIte]
        dsimp only [Expr.eval]
        rw [holdHd]
        dsimp [dllPushPrev, gsNodePrevTier2E, gsNextIdTier2E, tier2GsEnc, ρ₂, ρ₁, Expr.eval,
          Expr.v1, Env.get]
        funext j
        by_cases hjh : j = d.headTbl P k0
        · simp [hhd0, hjh]
        · simp only [hhd0, hjh, ↓reduceIte]
          by_cases hjn : j = d.nextId <;> simp [hjn]
    have hnext : (Expr.tset (gsNodeNextTier2E (.fst (Expr.v1 (O := OO))))
        (gsNextIdTier2E (.fst .v1))
        (tbl1GetE (gsHeadTblTier2E (.fst .v1)) (.fst (.snd .v1)) .v0)).eval ρ₂ =
        dllPushNext (d.headTbl P k0) d.nextId d.nodeNext := by
      dsimp only [Expr.eval, dllPushNext]
      rw [holdHd]
      rfl
    have hnodeRec : (Expr.tset (gsNodeRecTier2E (.fst (Expr.v1 (O := OO))))
        (gsNextIdTier2E (.fst .v1))
        (.some (.fst (.snd (.snd (.snd .v1)))))).eval ρ₂ =
        (fun j => (if j = d.nextId then some r else d.nodeRec j).map tier2RecEnc) := by
      dsimp [gsNodeRecTier2E, gsNextIdTier2E, tier2GsEnc, ρ₂, ρ₁, Expr.eval, Expr.v1, Env.get]
      funext j
      by_cases hj : j = d.nextId <;> simp [hj]
    have hnodeKey : (Expr.tset (gsNodeKeyTier2E (.fst (Expr.v1 (O := OO))))
        (gsNextIdTier2E (.fst .v1)) .v0).eval ρ₂ =
        (fun j => if j = d.nextId then k0 else d.nodeKey j) := by
      dsimp [gsNodeKeyTier2E, gsNextIdTier2E, tier2GsEnc, ρ₂, ρ₁, Expr.eval, Expr.v0, Expr.v1,
        Env.get]
      funext j
      by_cases hj : j = d.nextId <;> simp [hj]
    simp only [pair_eval, ite_eval, hsc, hhdTbl, hposN, hchSet, hcpSet, hprev, hnext, hnodeRec,
      hnodeKey]
    rcases r with ⟨⟨rs, rep, ridx⟩, rmsg, rct⟩
    dsimp only [ρ₂, ρ₁]
    cases P <;> cases ch <;> cases d.safeCh Δ .A <;> cases d.safeCh Δ .B <;>
      simp [pSet, pGet, posIdx, posEnc, tier2RecPos, tier2RecEnc, updParty, partyEnc,
        gsStTier2E, gsEpochTier2E, gsIdxTier2E, gsNextIdTier2E, gsChallTblTier2E,
        gsChallCountTier2E, gsCompTblTier2E, gsUncompCountTier2E, tier2GsEnc,
        Expr.eval, Expr.v0, Expr.v1]

private theorem cost_recordCiphertextTier2E_two_bits {Γ : List (Ty S)} (hℓ : ℓ < 10 ^ 6) (Δ : ℕ)
    (s : Expr OO Γ (tier2GsTy ℓ Pt)) (p : Expr OO Γ .bool)
    (st' : Expr OO Γ GhostStT) (recE : Expr OO Γ (tier2RecTy ℓ Pt))
    (isChall : Expr OO Γ .bool) :
    (recordCiphertextTier2E Δ s p st' recE isChall).cost ≤
      s.cost + p.cost + st'.cost + recE.cost + isChall.cost + 2 * bits Δ + 30 * ℓ + 17000 := by
  let tIn : Ty S :=
    .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod GhostStT (.prod (tier2RecTy ℓ Pt) .bool)))
  let c0 : List (Ty S) := tIn :: Γ
  let c1 : List (Ty S) := .nat :: c0
  have hwk := cost_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := c0) hℓ
    (tier2RecCt (.fst (.snd (.snd (.snd .v0)))))
  have hsc := cost_safeChTier2E (ℓ := ℓ) (Pt := Pt) (O := OO) (Γ := c1) Δ
    (.fst .v1) (.fst (.snd .v1))
  have htg := cost_tbl1GetE (O := OO) (Γ := c1)
    (gsHeadTblTier2E (.fst .v1)) (.fst (.snd .v1)) .v0
  have hts := cost_tbl1SetE (O := OO) (Γ := c1)
    (gsHeadTblTier2E (.fst .v1)) (.fst (.snd .v1)) .v0 (gsNextIdTier2E (.fst .v1))
  have hp0 := cost_posTblSetE (O := OO) (Γ := c1)
    (gsPosNodeTier2E (.fst .v1)) (tier2RecPos (.fst (.snd (.snd (.snd .v1)))))
    (gsNextIdTier2E (.fst .v1))
  have hp1 := cost_posTblSetE (O := OO) (Γ := c1)
    (gsChallTblTier2E (.fst .v1)) (tier2RecPos (.fst (.snd (.snd (.snd .v1))))) (.bool true)
  have hp2 := cost_posTblSetE (O := OO) (Γ := c1)
    (gsCompTblTier2E (.fst .v1)) (tier2RecPos (.fst (.snd (.snd (.snd .v1))))) (.bool true)
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  simp only [recordCiphertextTier2E, pSet, pGet, posIdx, tier2RecPos, tier2RecCt,
    gsStTier2E, gsEpochTier2E, gsIdxTier2E, gsNextIdTier2E, gsHeadTblTier2E, gsNodeRecTier2E,
    gsNodeKeyTier2E, gsNodePrevTier2E, gsNodeNextTier2E, gsPosNodeTier2E, gsChallTblTier2E,
    gsChallCountTier2E, gsCompTblTier2E, gsUncompCountTier2E,
    Expr.cost, Expr.v0, Expr.v1, hb0, hb1] at hwk hsc htg hts hp0 hp1 hp2 ⊢
  omega

theorem cost_recordCiphertextTier2E {Γ : List (Ty S)} (hℓ : ℓ < 10 ^ 6) (Δ : ℕ)
    (s : Expr OO Γ (tier2GsTy ℓ Pt)) (p : Expr OO Γ .bool)
    (st' : Expr OO Γ GhostStT) (recE : Expr OO Γ (tier2RecTy ℓ Pt))
    (isChall : Expr OO Γ .bool) :
    (recordCiphertextTier2E Δ s p st' recE isChall).cost ≤
      s.cost + p.cost + st'.cost + recE.cost + isChall.cost + 2 * bits Δ + 30 * ℓ + 17000 :=
  cost_recordCiphertextTier2E_two_bits hℓ Δ s p st' recE isChall

/-! ## `Hop2Aux` table operations -/

/-- `ReductionDsl` table type for `Hop2Aux.lazy` and `Hop2Aux.made`. -/
@[expose, reducible] def hop2TblTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .tbl (.tbl (.opt BV256))

@[expose] def hop2TblInitE {Γ : List (Ty S)} : Expr OO Γ (hop2TblTy ℓ Pt) :=
  .tconst (.tconst .none)

@[simp] theorem eval_hop2TblInitE {Γ : List (Ty S)} (ρ : Env Γ) :
    (hop2TblInitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)).eval ρ = (fun _ _ => none) := rfl

@[simp] theorem cost_hop2TblInitE {Γ : List (Ty S)} :
    (hop2TblInitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).cost = 3 := rfl

@[expose] def hop2TblGetE {Γ : List (Ty S)} (tblE : Expr OO Γ (hop2TblTy ℓ Pt))
    (tE : Expr OO Γ .nat) (qE : Expr OO Γ (ReductionDsl.PtT (ℓ := ℓ) (Pt := Pt))) :
    Expr OO Γ (.opt BV256) :=
  .tget (.tget tblE tE) (ptKeyE qE)

@[simp] theorem eval_hop2TblGetE {Γ : List (Ty S)} (tblE : Expr OO Γ (hop2TblTy ℓ Pt))
    (tE : Expr OO Γ .nat) (qE : Expr OO Γ (ReductionDsl.PtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) :
    (hop2TblGetE tblE tE qE).eval ρ =
      hop2TblGet encT (tblE.eval ρ) (tE.eval ρ) (qE.eval ρ) := by
  simp [hop2TblGetE, hop2TblGet, eval_ptKeyE, Expr.eval]

theorem cost_hop2TblGetE {Γ : List (Ty S)} (tblE : Expr OO Γ (hop2TblTy ℓ Pt))
    (tE : Expr OO Γ .nat) (qE : Expr OO Γ (ReductionDsl.PtT (ℓ := ℓ) (Pt := Pt))) :
    (hop2TblGetE tblE tE qE).cost ≤ tblE.cost + tE.cost + qE.cost + 1300 := by
  have hp := cost_ptKeyE qE
  simp only [hop2TblGetE, Expr.cost] at hp ⊢
  omega

@[expose] def hop2TblSetE {Γ : List (Ty S)} (tblE : Expr OO Γ (hop2TblTy ℓ Pt))
    (tE : Expr OO Γ .nat) (qE : Expr OO Γ (ReductionDsl.PtT (ℓ := ℓ) (Pt := Pt)))
    (vE : Expr OO Γ BV256) : Expr OO Γ (hop2TblTy ℓ Pt) :=
  .letE (.pair tblE (.pair tE (.pair (ptKeyE qE) vE)))
    (let tbl0 : Expr OO _ (hop2TblTy ℓ Pt) := .fst .v0
     let t0 : Expr OO _ .nat := .fst (.snd .v0)
     let k0 : Expr OO _ .nat := .fst (.snd (.snd .v0))
     let v0 : Expr OO _ BV256 := .snd (.snd (.snd .v0))
     .tset tbl0 t0 (.tset (.tget tbl0 t0) k0 (.some v0)))

@[simp] theorem eval_hop2TblSetE {Γ : List (Ty S)} (tblE : Expr OO Γ (hop2TblTy ℓ Pt))
    (tE : Expr OO Γ .nat) (qE : Expr OO Γ (ReductionDsl.PtT (ℓ := ℓ) (Pt := Pt)))
    (vE : Expr OO Γ BV256) (ρ : Env Γ) :
    (hop2TblSetE tblE tE qE vE).eval ρ =
      hop2TblSet encT (tblE.eval ρ) (tE.eval ρ) (qE.eval ρ) (vE.eval ρ) := by
  unfold hop2TblSetE hop2TblSet
  rw [letE_eval]
  have hp0 : (Expr.pair tblE (.pair tE (.pair (ptKeyE qE) vE))).eval ρ =
      (tblE.eval ρ, (tE.eval ρ, (ptKeyVal encT (qE.eval ρ), vE.eval ρ))) := by
    simp [Expr.eval, eval_ptKeyE]
  rw [hp0]; clear hp0
  dsimp only [Expr.eval, Expr.v0, Env.get]
  funext t k
  by_cases ht : t = tE.eval ρ
  · subst ht
    simp only [↓reduceIte]
    by_cases hk : k = ptKeyVal encT (qE.eval ρ) <;> simp [hk]
  · simp [ht]

theorem cost_hop2TblSetE {Γ : List (Ty S)} (tblE : Expr OO Γ (hop2TblTy ℓ Pt))
    (tE : Expr OO Γ .nat) (qE : Expr OO Γ (ReductionDsl.PtT (ℓ := ℓ) (Pt := Pt)))
    (vE : Expr OO Γ BV256) :
    (hop2TblSetE tblE tE qE vE).cost ≤ tblE.cost + tE.cost + qE.cost + vE.cost + 1550 := by
  have hp := cost_ptKeyE qE
  simp only [hop2TblSetE, Expr.cost, Expr.v0] at hp ⊢
  omega

end WireAndHop2Ops

/-! ## Wire-length and budget bounds -/

theorem sessionSchemeU_send_wire_length_le {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (g : GhostState Bytes) (m : Plain ℓ) (r : BitVec 512) :
    ((sessionSchemeU (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ).send
      g m r).2.length ≤ spkMaxWireLen ℓ :=
  params_send_wire_length_le C K idA idB g m r

theorem spk_totalCost_le_spkTier2Budget (q qep ℓ initCost finishCost stepBound : ℕ)
    (hinit : initCost + finishCost ≤ 2 ^ 9 * maxForwardJumps + 64 * 512)
    (hstep : 16 + stepBound ≤
      64 * (ℓ + 512) + 64 * bits (q + 1) + 64 * bits qep + 2 ^ 9 * maxForwardJumps) :
    initCost + finishCost + q * (16 + stepBound) ≤ spkTier2Budget q qep ℓ := by
  have h1 : initCost + finishCost ≤
      1 * (64 * (ℓ + 512) + 64 * bits (q + 1) + 64 * bits qep + 2 ^ 9 * maxForwardJumps) := by
    omega
  have hq : q * (16 + stepBound) ≤
      q * (64 * (ℓ + 512) + 64 * bits (q + 1) + 64 * bits qep + 2 ^ 9 * maxForwardJumps) :=
    Nat.mul_le_mul_left q hstep
  have hsum : initCost + finishCost + q * (16 + stepBound) ≤
      (q + 1) * (64 * (ℓ + 512) + 64 * bits (q + 1) + 64 * bits qep +
        2 ^ 9 * maxForwardJumps) := by
    calc initCost + finishCost + q * (16 + stepBound)
        ≤ 1 * (64 * (ℓ + 512) + 64 * bits (q + 1) + 64 * bits qep + 2 ^ 9 * maxForwardJumps) +
          q * (64 * (ℓ + 512) + 64 * bits (q + 1) + 64 * bits qep + 2 ^ 9 * maxForwardJumps) :=
          Nat.add_le_add h1 hq
      _ = (q + 1) * (64 * (ℓ + 512) + 64 * bits (q + 1) + 64 * bits qep +
            2 ^ 9 * maxForwardJumps) := by ring
  simpa only [spkTier2Budget] using hsum

end Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping
