/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit

/-!
# Cost and Description-Size Bounds for `KemFailRedInit`

Proves static `.queries`, `.cost`, and `descBits` bounds for `kemFailStateT`, `kemFailMkInitE`,
`kemFailInitC`, and `kemFailFinishOptE`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost

open _root_.ReductionDsl (Ty Expr bits atomicSig atomicSessionOps
  B PB U8 U32 U64 BV128 BV256 BV512 PlainT PtT PK GhostStT
  lpubT fig8CtT fig8HdrT fig8StT fsSendStT fsRecvStT ckaStT lctT wireSaltCtT
  AtomicPureOp AtomicSpqrKemOp)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (posTy)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (
  sessPureOp sessSpqrKemOp)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State (
  bits_zero bits_eq_of_bounds cost_eLet descBits_eLet
  atomicTyDescBits_posTy)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost (
  simRecT ghostChainT simFullT initSimCE initSimMirE keptUnknownE
  cost_initSimCE simFullT_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept (fig8InitAtomicE_cost
  fig8InitAtomicE_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost (
  kemFailInitCoinsC_queries_zero kemFailInitCoinsC_cost kemFailInitCoinsC_descBits_le
  atomicSortDescBits atomicTyDescBits varIdx atomicPureOpDescBits
  atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit (
  fig8RecT fig8MirT fig8GsT kemCoinsT kemSentEntryT kemTrackT kemFailStateT
  initSimCAtomicE initFig8MirAtomicE initFig8GsAtomicE initV1BraidStAtomicE
  initKemTrackAtomicE kemFailMkInitE kemFailInitC kemFailFinishOptE)

section CostAndDescBounds

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

theorem kemFailInitC_queries_zero (idA idB : IdentityKey) (w : Empty → ℕ) :
    (kemFailInitC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB).queries w (fun _ => 0) = 0 :=
  kemFailInitCoinsC_queries_zero (kemFailMkInitE idA idB) w

omit [SampleableType Pt] in
theorem initSimCAtomicE_cost {Γ : List (Ty ASig)} (pqrKeyE : Expr AOps Γ BV256) :
    (initSimCAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) pqrKeyE).cost ≤ pqrKeyE.cost + 520 := by
  let pqA : Expr AOps (BV256 :: Γ) (B 32) :=
    sessSpqrKemOp .spqrV1InitOp (.pair (.bool true) (.var .zero))
  let pqB : Expr AOps (BV256 :: Γ) (B 32) :=
    sessSpqrKemOp .spqrV1InitOp (.pair (.bool false) (.var .zero))
  have hc := cost_initSimCE pqA pqB
  have hcA : pqA.cost = 213 := rfl
  have hcB : pqB.cost = 213 := rfl
  dsimp only [initSimCAtomicE]
  rw [cost_eLet]
  dsimp only [pqA, pqB] at hc hcA hcB
  omega

omit [SampleableType Pt] in
theorem initFig8GsAtomicE_cost (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (bE : Expr AOps Γ .bool) (k1E k2E : Expr AOps Γ BV256) :
    (initFig8GsAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB bE k1E k2E).cost ≤
    bE.cost + k1E.cost + k2E.cost + 1100 := by
  have hfig := fig8InitAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (.pair k1E k2E)
  have hb0 : bits 0 = 1 := bits_zero
  simp only [initFig8GsAtomicE, initFig8MirAtomicE, Expr.cost, hb0] at hfig ⊢
  omega

omit [SampleableType Pt] in
theorem initKemTrackAtomicE_cost {Γ : List (Ty ASig)} (pqrKeyE : Expr AOps Γ BV256) :
    (initKemTrackAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) pqrKeyE).cost ≤ pqrKeyE.cost + 3500 := by
  have hb0 : bits 0 = 1 := bits_zero
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have h_pure (o : AtomicPureOp) :
      (AOps).cost (Sum.inl (Sum.inl (Sum.inl (Sum.inl o)))) = o.cost ℓ := rfl
  have h_spqr (o : AtomicSpqrKemOp) : (AOps).cost (Sum.inr o) = o.cost := rfl
  dsimp only [initKemTrackAtomicE, initV1BraidStAtomicE]
  rw [cost_eLet]
  simp only [Expr.cost, h_pure, h_spqr, AtomicPureOp.cost, AtomicSpqrKemOp.cost,
    hb0, h32, List.length_nil]
  omega

omit [SampleableType Pt] in
theorem kemFailMkInitE_cost_le (idA idB : IdentityKey) :
    (kemFailMkInitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB).cost + 40 ≤ 6000 := by
  let Γ0 : List (Ty ASig) := [BV256, BV256, BV256, .bool, .unit]
  have h1 := initSimCAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0) (.var .zero)
  have h2 := initFig8GsAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ0)
    (.var (.succ (.succ (.succ .zero)))) (.var (.succ (.succ .zero))) (.var (.succ .zero))
  have h3 := initKemTrackAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0) (.var .zero)
  dsimp only [kemFailMkInitE, Γ0, Expr.cost] at h1 h2 h3 ⊢
  omega

theorem kemFailInitC_cost_le (idA idB : IdentityKey) :
    (kemFailInitC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB).cost ≤ 6000 :=
  le_trans (kemFailInitCoinsC_cost (kemFailMkInitE idA idB)) (kemFailMkInitE_cost_le idA idB)

theorem kemFailInitC_cost_le_bundle (idA idB : IdentityKey) :
    (kemFailInitC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB).cost ≤ 50000000 :=
  le_trans (kemFailInitC_cost_le idA idB) (by omega)

omit [SampleableType Pt] in
theorem kemFailFinishOptE_cost_le :
    (kemFailFinishOptE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)).cost + 13 ≤ 32 := by
  dsimp only [kemFailFinishOptE, Expr.cost]
  omega

private theorem hb1_bits : bits 1 = 1 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)

private theorem hb2_bits : bits 2 = 2 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)

private theorem hb3_bits : bits 3 = 2 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)

private theorem hb32_pnat : bits ((32 : ℕ+) : ℕ) = 6 := by
  change bits 32 = 6
  exact bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)

private theorem hb64_pnat : bits ((64 : ℕ+) : ℕ) = 7 := by
  change bits 64 = 7
  exact bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem atomicTyDescBits_fig8RecT :
    atomicTyDescBits (fig8RecT ℓ Pt) ≤ 230 := by
  dsimp only [fig8RecT, posTy, lpubT, PlainT, fig8CtT, fig8HdrT, lctT, wireSaltCtT,
    B, PB, U32, U64, BV256, PtT, atomicTyDescBits, atomicSortDescBits]
  rw [hb32_pnat]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem atomicTyDescBits_kemSentEntryT :
    atomicTyDescBits (kemSentEntryT ℓ Pt) ≤ 50 := by
  dsimp only [kemSentEntryT, U64, B, U32, atomicTyDescBits, atomicSortDescBits]
  rw [hb64_pnat]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem atomicTyDescBits_kemFailStateT :
    atomicTyDescBits (kemFailStateT ℓ Pt) ≤ 4000 := by
  have hsim := simFullT_descBits_le ℓ Pt
  have hrec := atomicTyDescBits_fig8RecT (ℓ := ℓ) (Pt := Pt)
  have hsent := atomicTyDescBits_kemSentEntryT (ℓ := ℓ) (Pt := Pt)
  dsimp only [kemFailStateT, fig8GsT, fig8MirT, kemTrackT, kemCoinsT]
  generalize simFullT ℓ Pt = tSim at hsim ⊢
  generalize fig8RecT ℓ Pt = tRec at hrec ⊢
  generalize kemSentEntryT ℓ Pt = tSent at hsent ⊢
  dsimp only [fig8StT, fsSendStT, fsRecvStT, ckaStT, posTy,
    U64, B, BV512, BV256, PtT, atomicTyDescBits, atomicSortDescBits]
  rw [hb32_pnat]
  omega

omit [SampleableType Pt] in
private theorem initSimCAtomicE_descBits_le {Γ : List (Ty ASig)} (pqrKeyE : Expr AOps Γ BV256) :
    atomicExprDescBits atomicSessionOpDescBits
      (initSimCAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) pqrKeyE) ≤
      atomicExprDescBits atomicSessionOpDescBits pqrKeyE + 2000 := by
  dsimp only [initSimCAtomicE]
  rw [descBits_eLet]
  dsimp only [initSimCE, initSimMirE, keptUnknownE, sessPureOp, sessSpqrKemOp,
    simRecT, ghostChainT, posTy, PlainT, PK, B, PB, fig8CtT, fig8HdrT, fsRecvStT,
    lctT, wireSaltCtT, BV128, U64, BV256, PtT, varIdx,
    atomicExprDescBits, atomicSessionOpDescBits, atomicPureOpDescBits,
    atomicTyDescBits, atomicSortDescBits]
  rw [bits_zero, hb32_pnat]
  omega

omit [SampleableType Pt] in
private theorem initFig8GsAtomicE_descBits_le (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (bE : Expr AOps Γ .bool) (k1E k2E : Expr AOps Γ BV256) :
    atomicExprDescBits atomicSessionOpDescBits
      (initFig8GsAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) idA idB bE k1E k2E) ≤
      atomicExprDescBits atomicSessionOpDescBits bE +
      atomicExprDescBits atomicSessionOpDescBits k1E +
      atomicExprDescBits atomicSessionOpDescBits k2E + 501000 := by
  have hfig := fig8InitAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (.pair k1E k2E)
  have hrec := atomicTyDescBits_fig8RecT (ℓ := ℓ) (Pt := Pt)
  have hpos := atomicTyDescBits_posTy (ℓ := ℓ) (Pt := Pt)
  dsimp only [initFig8GsAtomicE, initFig8MirAtomicE]
  generalize SimFig8Kept.fig8InitAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (.pair k1E k2E) = eFig at hfig ⊢
  dsimp only [atomicExprDescBits] at hfig ⊢
  generalize atomicTyDescBits (fig8RecT ℓ Pt) = nRec at hrec ⊢
  generalize atomicTyDescBits (posTy : Ty ASig) = nPos at hpos ⊢
  dsimp only [atomicTyDescBits]
  rw [bits_zero]
  omega

omit [SampleableType Pt] in
private theorem initKemTrackAtomicE_descBits_le {Γ : List (Ty ASig)} (pqrKeyE : Expr AOps Γ BV256) :
    atomicExprDescBits atomicSessionOpDescBits
      (initKemTrackAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) pqrKeyE) ≤
      atomicExprDescBits atomicSessionOpDescBits pqrKeyE + 1000 := by
  have hsent := atomicTyDescBits_kemSentEntryT (ℓ := ℓ) (Pt := Pt)
  dsimp only [initKemTrackAtomicE, initV1BraidStAtomicE]
  rw [descBits_eLet]
  dsimp only [sessPureOp, sessSpqrKemOp, varIdx,
    atomicExprDescBits, atomicSessionOpDescBits, atomicPureOpDescBits, List.length_nil]
  generalize atomicTyDescBits (kemSentEntryT ℓ Pt) = nSent at hsent ⊢
  simp only [BV256, atomicTyDescBits, atomicSortDescBits, bits_zero, hb32_pnat]
  omega

omit [SampleableType Pt] in
theorem kemFailMkInitE_descBits_le (idA idB : IdentityKey) :
    atomicExprDescBits atomicSessionOpDescBits
      (kemFailMkInitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) idA idB) ≤ 550000 := by
  let Γ0 : List (Ty ASig) := [BV256, BV256, BV256, .bool, .unit]
  have h1 := initSimCAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0) (.var .zero)
  have h2 := initFig8GsAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ0)
    (.var (.succ (.succ (.succ .zero)))) (.var (.succ (.succ .zero))) (.var (.succ .zero))
  have h3 := initKemTrackAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0) (.var .zero)
  dsimp only [kemFailMkInitE, Γ0] at h1 h2 h3 ⊢
  generalize initSimCAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.var .zero) = e1 at h1 ⊢
  generalize initFig8GsAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB _ _ _ = e2 at h2 ⊢
  generalize initKemTrackAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.var .zero) = e3 at h3 ⊢
  simp only [atomicExprDescBits, varIdx, Nat.reduceAdd,
    bits_zero, hb1_bits, hb2_bits, hb3_bits] at h1 h2 h3 ⊢
  omega

theorem kemFailInitC_descBits_le (idA idB : IdentityKey) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
      (kemFailInitC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) idA idB) ≤ 550500 := by
  have h2 := kemFailMkInitE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB
  refine le_trans (kemFailInitCoinsC_descBits_le (kemFailMkInitE idA idB)) ?_
  omega

omit [SampleableType Pt] in
theorem kemFailFinishOptE_descBits_le :
    atomicExprDescBits atomicSessionOpDescBits
      (kemFailFinishOptE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)) ≤ 200 := by
  dsimp only [kemFailFinishOptE, atomicExprDescBits, varIdx]
  rw [bits_zero]
  omega

end CostAndDescBounds

end Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost
