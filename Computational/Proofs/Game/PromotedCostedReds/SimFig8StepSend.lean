/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling

/-!
# Atomic Send and Challenge Step Program for `SimFig8`

Defines and verifies the single-query `Comp` over `atomicSessionOps` and `fig8SmIface` handling the
transmit and challenge branches (`semSendHook`) of `simFig8OracleSan`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8StepSend

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp handlerImpl bits
  atomicSig atomicSessionOps fig8SmIface e2eSessionCodec GhostStT smQT smRT
  B U32 BV256 BV512 PlainT SMTag UniformSamplerTag AtomicPureOp
  partyToBool boolToParty lpubT lpubV lpubOfV fig8CtT fig8CtV fig8CtOfV
  fig8StT fig8StV fig8StOfV fsSendStT fsSendStV fsSendStOfV)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFig8)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimState SimCStateBounded mkPub toWire
  scPostSendPure semDrawSendCoins semSendHook)
open CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState)
open CryptoGames.SM (Pos Record GameState partyEnc partyDec posTy posEnc posDec
  noBobSendInEpoch0 orE isSomeE sendsInE pGet pSet
  ite_eval orE_eval isSomeE_eval sendsInE_eval pGet_eval pSet_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle (simFig8OracleSan)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SanSnapExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost (simFullT simFullEnc
  simFullDec simFullDec_simFullEnc simBaseT simBaseEnc simBaseDec simMirT simMirEnc simMirDec
  simRecT simRecEnc simRecDec ghostChainT ghostChainEnc ghostChainDec honestPairEnc honestPairDec
  keptT keptEnc keptDec snapT snapEnc snapDec sentEntryT sentEntryEnc sentEntryDec fig8IdSemHook)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (figS fig8San)
open Computational.Proofs.ReductionDsl.Fig8Atomic (salt32V_salt32OfV lpubOfV_lpubV
  ckaSendExpr prngUpExpr defaultEExpr fsSendExpr)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State (eLet eval_eLet cost_eLet
  descBits_eLet sOpPure eval_sOpPure cost_sOpPure descBits_sOpPure runFig8WithIds
  descBits_runFig8WithIds mWin mEpoch mIdx mSafeChE mSafeChE_eval cost_mSafeChE
  mSafeChE_descBits_le mEpMgmtE mEpMgmtE_eval cost_mEpMgmtE mEpMgmtE_descBits_le mRecordE
  mRecordE_eval cost_mRecordE mRecordE_descBits_le mNoBobEpoch0E mNoBobEpoch0E_eval
  cost_mNoBobEpoch0E mNoBobEpoch0E_descBits_le ssMir ssPq ssPn ssUnackA ssHonest ssChains ssAmb
  ssStopped ssMk scBase scKept scSent scSnaps scMk bits_zero bits_eq_of_bounds bits_le_of_lt_pow
  atomicTyDescBits_posTy atomicTyDescBits_simRecT atomicTyDescBits_simMirT atomicTyDescBits_fig8CtT
  atomicTyDescBits_fsSendStT atomicTyDescBits_fig8StT atomicTyDescBits_simBaseT
  atomicTyDescBits_keptT atomicTyDescBits_sentEntryT atomicTyDescBits_simFullT)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc (prngUpExpr_descBits_le
  ckaSendExpr_descBits_le defaultEExpr_descBits_le fsSendExpr_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto (toWireAtomicE toWireAtomicE_eval
  toWireAtomicE_cost toWireAtomicE_descBits_le mkPubAtomicC mkPubAtomicC_eval mkPubAtomicC_queries
  mkPubAtomicC_cost mkPubAtomicC_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept (f8Id f8Root f8VS f8VR f8Gamma f8Cur
  f8Tcur f8Mk defaultMcAtomicE defaultMcAtomicE_descBits_le fig8SendStepAtomicE keptSendAtomicE
  keptSendAtomicE_eval keptSendAtomicE_cost)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost (atomicSortDescBits
  atomicTyDescBits varIdx atomicPureOpDescBits atomicSessionOpDescBits atomicExprDescBits
  atomicCompDescBits)

/-! ## State round-trip and `Kept.send` equivalence -/

section RoundTrip

variable {ℓ : ℕ} {Pt : Type}

private theorem fig8CtV_fig8CtOfV (v : (fig8CtT (ℓ := ℓ) (Pt := Pt)).denote) :
    fig8CtV (ℓ := ℓ) (Pt := Pt) (fig8CtOfV v) = v := by
  rcases v with ⟨h, n, ws, sv⟩
  simp [fig8CtV, fig8CtOfV, ReductionDsl.lctV, ReductionDsl.lctOfV,
    ReductionDsl.wireSaltCtV, ReductionDsl.wireSaltCtOfV, salt32V_salt32OfV]

private theorem fig8StV_fig8StOfV (v : (fig8StT (ℓ := ℓ) (Pt := Pt)).denote) :
    fig8StV (ℓ := ℓ) (Pt := Pt) (fig8StOfV v) = v := by
  rcases v with ⟨p, rk, vs?, vrTbl, γv, cur?, tc⟩
  simp only [fig8StV, fig8StOfV]
  have hp : partyToBool (boolToParty p) = p := by cases p <;> rfl
  have hvs : (vs?.map (ReductionDsl.fsSendStOfV (ℓ := ℓ) (Pt := Pt))).map
      ReductionDsl.fsSendStV = vs? := by
    rcases vs? with _ | ⟨ck, li⟩ <;> rfl
  have hvr : (fun t => ((vrTbl t).map (ReductionDsl.fsRecvStOfV (ℓ := ℓ) (Pt := Pt))).map
      ReductionDsl.fsRecvStV) = vrTbl := by
    funext t; rcases vrTbl t with _ | ⟨ck, li, sk⟩ <;> rfl
  have hγ : ReductionDsl.ckaStV (ℓ := ℓ) (Pt := Pt) (ReductionDsl.ckaStOfV γv) = γv := by
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

private theorem kept_send_figS_eq [Zero Pt] (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (k : Kept Pt) :
    Kept.send (ℓ := ℓ)
      (fig := figS (ℓ := ℓ) (paramsV1 C K idA idB) Dh encPt encT lam 0) k =
    Kept.send (ℓ := ℓ)
      (fig := lFig8 Dh encPt C protoSignalCodec ℓ encT
        (fun R => if R == Party.A then idA else idB) 25000 lam) k := by
  unfold Kept.send figS fig8San
  have h1 : (paramsV1 C K idA idB).C = C := rfl
  have h2 : (paramsV1 C K idA idB).codec = protoSignalCodec := rfl
  have h3 : (paramsV1 C K idA idB).idA = idA := rfl
  have h4 : (paramsV1 C K idA idB).idB = idB := rfl
  rw [h1, h2, h3, h4]

end RoundTrip

/-! ## Post-send state update -/

section PostSend

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ADesc" => atomicSessionOpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
  (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)

@[local simp] private theorem sb_c0 : bits 0 = 1 := bits_zero
@[local simp] private theorem sb_c1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem sb_c2 : bits 2 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem sb_c3 : bits 3 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem sb_c4 : bits 4 = 3 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem sb_c32 : bits 32 = 6 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem sb_p32 : bits ((32 : ℕ+) : ℕ) = 6 := sb_c32

private theorem fig8SendStepAtomicE_descBits_tight (idA idB : IdentityKey) (B_cl : ℕ)
    {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (mcOptE : Expr AOps Γ (.opt (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256))) :
    atomicExprDescBits ADesc
      (fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB B_cl stE mcOptE) ≤
      atomicExprDescBits ADesc stE + atomicExprDescBits ADesc mcOptE +
        8 * bits B_cl + 25000 := by
  have hdef := defaultMcAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  let t0 := Ty.prod (fig8StT (ℓ := ℓ) (Pt := Pt))
    (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256)
  let Γ1 := t0 :: Γ
  let Γ2 := Ty.prod (_root_.ReductionDsl.ckaStT (ℓ := ℓ) (Pt := Pt))
    (.prod (_root_.ReductionDsl.PtT (ℓ := ℓ) (Pt := Pt)) (_root_.ReductionDsl.PtT (ℓ := ℓ) (Pt := Pt))) :: Γ1
  let Γ3 := Ty.prod .bool
    (.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT)) :: Γ1
  let Γ4 := fsSendStT (ℓ := ℓ) (Pt := Pt) :: Γ3
  have hcka := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ1)
    (ckaSendExpr ℓ Pt C Dh encPt encT lam) (.pair (f8Gamma (.fst .v0)) (.snd (.snd .v0)))
  have hup := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ2)
    (prngUpExpr ℓ Pt C Dh encPt encT lam) (.pair (f8Root (.fst .v1)) (.snd (.snd .v0)))
  have hdefE := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ3)
    (defaultEExpr ℓ Pt C Dh encPt encT lam) .unit
  have hfs := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ4)
    (fsSendExpr ℓ Pt C Dh encPt encT lam)
    (.pair .v0 (.pair (.pair (f8Tcur (.fst (.snd .v1))) (f8Cur (.fst (.snd .v1))))
      (.snd (.snd .v1))))
  have hd_cka := ckaSendExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  have hd_up := prngUpExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  have hd_defE := defaultEExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  have hd_fs := fsSendExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  dsimp only [fig8SendStepAtomicE, f8Mk, f8Id, f8Root, f8VS, f8VR, f8Gamma, f8Cur, f8Tcur,
    sendsInE, Expr.v0, Expr.v1, Expr.v2] at hcka hup hdefE hfs ⊢
  generalize defaultMcAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) = e_def at hdef ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ1) (ckaSendExpr ℓ Pt C Dh encPt encT lam)
    _ = e_rcka at hcka ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (prngUpExpr ℓ Pt C Dh encPt encT lam)
    _ = e_rup at hup ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ3) (defaultEExpr ℓ Pt C Dh encPt encT lam)
    .unit = e_rdefE at hdefE ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ4) (fsSendExpr ℓ Pt C Dh encPt encT lam)
    _ = e_rfs at hfs ⊢
  simp only [descBits_eLet, varIdx, atomicExprDescBits, Nat.reduceAdd,
    sb_c0, sb_c1, sb_c2] at hcka hup hdefE hfs ⊢
  omega

private theorem keptSendAtomicE_descBits_tight (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt)) :
    atomicExprDescBits ADesc
      (keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB kE) ≤
      atomicExprDescBits ADesc kE + 30000 := by
  let Γ1 := fig8StT (ℓ := ℓ) (Pt := Pt) :: keptT ℓ Pt :: Γ
  have hstep := fig8SendStepAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB 0 (Γ := Γ1) .v0 .none
  have ht_f8 := atomicTyDescBits_fig8StT (ℓ := ℓ) (Pt := Pt)
  dsimp only [keptSendAtomicE, sendsInE, f8Id, f8Tcur, f8VR, Expr.v0, Expr.v1] at hstep ⊢
  generalize fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB 0 (Γ := Γ1) _ _ = e_s at hstep ⊢
  simp only [descBits_eLet, BV256, varIdx,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd,
    sb_c0, sb_c1, sb_c2, sb_p32] at hstep ⊢
  omega

def scPostSendAtomicE (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (s1E : Expr AOps Γ (simMirT ℓ Pt))
    (qBE : Expr AOps Γ .bool) (m0E : Expr AOps Γ PlainT) (chBE : Expr AOps Γ .bool)
    (pq'E : Expr AOps Γ (B 32)) (pnE : Expr AOps Γ U32)
    (cVE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (.prod (B 32) (simFullT ℓ Pt)) :=
  eLet (.pair sCE (.pair s1E (.pair qBE (.pair m0E (.pair chBE (.pair pq'E (.pair pnE cVE)))))))
    (eLet (toWireAtomicE (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
      (eLet (keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) idA idB
          (pGet (scKept (.fst .v1)) (.fst (.snd (.snd .v1)))))
        (let ks0 : Expr AOps _ (keptT ℓ Pt) := .v0
         let w0  : Expr AOps _ (B 32) := .v1
         let sC2 : Expr AOps _ (simFullT ℓ Pt) := .fst .v2
         let s12 : Expr AOps _ (simMirT ℓ Pt) := .fst (.snd .v2)
         let q2  : Expr AOps _ .bool := .fst (.snd (.snd .v2))
         let m2  : Expr AOps _ PlainT := .fst (.snd (.snd (.snd .v2)))
         let ch2 : Expr AOps _ .bool := .fst (.snd (.snd (.snd (.snd .v2))))
         let pq2 : Expr AOps _ (B 32) := .fst (.snd (.snd (.snd (.snd (.snd .v2)))))
         let pn2 : Expr AOps _ U32 := .fst (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
         let c2  : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) :=
           .snd (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
         let b2  := scBase sC2
         let posE : Expr AOps _ (posTy (S' := ASig)) :=
           .pair q2 (.pair (pGet (mEpoch s12) q2) (.add (pGet (mIdx s12) q2) (.nat 1)))
         let recE : Expr AOps _ (simRecT ℓ Pt) := .pair posE (.pair m2 w0)
         let mir'E := mRecordE s12 q2 recE ch2
         let base'E := ssMk mir'E
           (pSet (ssPq b2) q2 pq2)
           (pSet (ssPn b2) q2 pn2)
           (ssUnackA b2)
           (.cons (.pair w0 c2) (ssHonest b2))
           (ssChains b2)
           (ssAmb b2)
           (ssStopped b2)
         let kept'E := pSet (scKept sC2) q2 ks0
         let sent'E : Expr AOps _ (.list (sentEntryT ℓ Pt)) :=
           .caseOpt (.fst (pGet (scKept sC2) q2))
             (scSent sC2)
             (.ite (sendsInE (f8Id .v0) (.add (f8Tcur .v0) (.nat 1)))
               (scSent (.fst .v3))
               (.caseOpt (f8VS .v0)
                 (scSent (.fst .v3))
                 (.cons (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4))))))) .v0)
                   (scSent (.fst .v4)))))
         .pair w0 (scMk base'E kept'E sent'E (scSnaps sC2)))))

theorem scPostSendAtomicE_eval (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (s1E : Expr AOps Γ (simMirT ℓ Pt))
    (qBE : Expr AOps Γ .bool) (m0E : Expr AOps Γ PlainT) (chBE : Expr AOps Γ .bool)
    (pq'E : Expr AOps Γ (B 32)) (pnE : Expr AOps Γ U32)
    (cVE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (s₁ : GameState Unit (Plain ℓ) Bytes) (Q : Party) (m₀ : Plain ℓ) (chB : Bool)
    (pq' : Bytes) (pn : BitVec 32) (c : Fig8C Pt)
    (hsC : sCE.eval ρ = simFullEnc sC) (hs1 : s1E.eval ρ = simMirEnc s₁)
    (hq : qBE.eval ρ = partyEnc Q) (hm0 : m0E.eval ρ = m₀) (hch : chBE.eval ρ = chB)
    (hpq : pq'E.eval ρ = pq') (hpn : pnE.eval ρ = pn)
    (hc : cVE.eval ρ = fig8CtV (ℓ := ℓ) (Pt := Pt) c) :
    (scPostSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB sCE s1E qBE m0E chBE pq'E pnE cVE).eval ρ =
      (toWire c,
        simFullEnc (scPostSendPure (paramsV1 C K idA idB) Dh encPt encT lam
          sC s₁ Q m₀ chB pq' pn c)) := by
  dsimp only [scPostSendAtomicE]
  rw [eval_eLet, eval_eLet, eval_eLet]
  let tupT : Ty ASig := .prod (simFullT ℓ Pt) (.prod (simMirT ℓ Pt)
    (.prod .bool (.prod PlainT (.prod .bool (.prod (B 32) (.prod U32 (fig8CtT (ℓ := ℓ) (Pt := Pt))))))))
  let tup : tupT.denote := (simFullEnc sC, (simMirEnc (Pt := Pt) s₁, (partyEnc Q,
    (m₀, (chB, (pq', (pn, fig8CtV (ℓ := ℓ) (Pt := Pt) c)))))))
  have htup : (Expr.pair sCE (.pair s1E (.pair qBE (.pair m0E (.pair chBE (.pair pq'E (.pair pnE cVE))))))).eval ρ = tup := by
    simp [tup, Expr.eval, hsC, hs1, hq, hm0, hch, hpq, hpn, hc]
  rw [htup]
  let ρ1 := Env.cons (t := tupT) tup ρ
  have hw : (toWireAtomicE (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))) :
      Expr AOps _ (B 32)).eval ρ1 = toWire c :=
    toWireAtomicE_eval _ ρ1 c rfl
  rw [hw]
  let ρ2 := Env.cons (t := B 32) (toWire c) ρ1
  have hkQ : (pGet (scKept (.fst .v1)) (.fst (.snd (.snd .v1))) :
      Expr AOps _ (keptT ℓ Pt)).eval ρ2 = keptEnc (ℓ := ℓ) (sC.kept Q) := by
    cases Q <;> rfl
  have hks : (keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB
      (pGet (scKept (.fst .v1)) (.fst (.snd (.snd .v1))))).eval ρ2 =
      keptEnc (ℓ := ℓ) (Kept.send (ℓ := ℓ)
        (fig := lFig8 Dh encPt C protoSignalCodec ℓ encT
          (fun R => if R == Party.A then idA else idB) 25000 lam) (sC.kept Q)) := by
    rw [keptSendAtomicE_eval idA idB 0 _ ρ2 (sC.kept Q) hkQ, kept_send_figS_eq]
  rw [hks]
  let ksVal := Kept.send (ℓ := ℓ)
    (fig := lFig8 Dh encPt C protoSignalCodec ℓ encT
      (fun R => if R == Party.A then idA else idB) 25000 lam) (sC.kept Q)
  let ρ3 := Env.cons (t := keptT ℓ Pt) (keptEnc (ℓ := ℓ) ksVal) ρ2
  have hmir' : (mRecordE (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))
      (.pair (.pair (.fst (.snd (.snd .v2)))
        (.pair (pGet (mEpoch (.fst (.snd .v2))) (.fst (.snd (.snd .v2))))
          (.add (pGet (mIdx (.fst (.snd .v2))) (.fst (.snd (.snd .v2)))) (.nat 1))))
        (.pair (.fst (.snd (.snd (.snd .v2)))) .v1))
      (.fst (.snd (.snd (.snd (.snd .v2))))) : Expr AOps _ (simMirT ℓ Pt)).eval ρ3 =
      simMirEnc (Pt := Pt) (s₁.record 3 Q () ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, toWire c⟩ chB) := by
    refine mRecordE_eval _ _ _ _ ρ3 s₁ Q ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, toWire c⟩ rfl rfl ?_
    cases Q <;> rfl
  have hsent' : (Expr.caseOpt (.fst (pGet (scKept (.fst .v2)) (.fst (.snd (.snd .v2)))))
      (scSent (.fst .v2))
      (.ite (sendsInE (f8Id .v0) (.add (f8Tcur .v0) (.nat 1)))
        (scSent (.fst .v3))
        (.caseOpt (f8VS .v0)
          (scSent (.fst .v3))
          (.cons (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4))))))) .v0)
            (scSent (.fst .v4))))) : Expr AOps _ (.list (sentEntryT ℓ Pt))).eval ρ3 =
      (match (sC.kept Q).full with
       | some st =>
         if st.id.sendsIn (st.tcur + 1) then sC.sent
         else match st.vS with
           | some v => (c, v) :: sC.sent
           | none => sC.sent
       | none => sC.sent).map sentEntryEnc := by
    have hkQ3 : (pGet (scKept (.fst .v2)) (.fst (.snd (.snd .v2))) :
        Expr AOps _ (keptT ℓ Pt)).eval ρ3 = keptEnc (ℓ := ℓ) (sC.kept Q) := by
      cases Q <;> rfl
    have hsc2 : (scSent (.fst .v2) : Expr AOps _ (.list (sentEntryT ℓ Pt))).eval ρ3 =
        sC.sent.map sentEntryEnc := rfl
    dsimp only [Expr.eval]
    rw [hkQ3]
    dsimp only [keptEnc]
    rcases hfull : (sC.kept Q).full with _ | st
    · exact hsc2
    · dsimp only [Option.map]
      let ρ4 := Env.cons (t := fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8StV (ℓ := ℓ) (Pt := Pt) st) ρ3
      have hsn : (sendsInE (f8Id .v0) (.add (f8Tcur .v0) (.nat 1)) :
          Expr AOps _ .bool).eval ρ4 = st.id.sendsIn (st.tcur + 1) := by
        have hid : (f8Id .v0 : Expr AOps _ .bool).eval ρ4 = partyEnc st.id := by
          show partyToBool st.id = partyEnc st.id
          cases st.id <;> rfl
        rw [sendsInE_eval _ _ _ st.id hid]
        rfl
      change (if (sendsInE (f8Id .v0) (.add (f8Tcur .v0) (.nat 1)) :
          Expr AOps _ .bool).eval ρ4 then _ else _) = _
      rw [hsn]
      cases hs : st.id.sendsIn (st.tcur + 1)
      · rcases st with ⟨id_, rk, _ | v, vr, γ, cur, tc⟩ <;> rfl
      · rfl
  have hparams : (lFig8 Dh encPt (paramsV1 C K idA idB).C (paramsV1 C K idA idB).codec ℓ encT
      (fun R => if R == Party.A then (paramsV1 C K idA idB).idA else (paramsV1 C K idA idB).idB)
      25000 lam) =
    (lFig8 Dh encPt C protoSignalCodec ℓ encT
      (fun R => if R == Party.A then idA else idB) 25000 lam) := rfl
  change (Expr.v1.eval ρ3,
    ((ssMk _ _ _ _ _ _ _ _).eval ρ3,
     ((pSet (scKept (.fst .v2)) (.fst (.snd (.snd .v2))) .v0).eval ρ3,
      ((Expr.caseOpt _ _ _).eval ρ3, (scSnaps (.fst .v2)).eval ρ3)))) = _
  rw [hsent']
  dsimp only [scPostSendPure]
  rw [hparams]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl rfl)))
  · dsimp only [ssMk, Expr.eval]
    rw [hmir']
    cases Q <;> rfl
  · cases Q <;> rfl

theorem scPostSendAtomicE_cost (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (s1E : Expr AOps Γ (simMirT ℓ Pt))
    (qBE : Expr AOps Γ .bool) (m0E : Expr AOps Γ PlainT) (chBE : Expr AOps Γ .bool)
    (pq'E : Expr AOps Γ (B 32)) (pnE : Expr AOps Γ U32)
    (cVE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (scPostSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB sCE s1E qBE m0E chBE pq'E pnE cVE).cost ≤
      sCE.cost + s1E.cost + qBE.cost + m0E.cost + chBE.cost + pq'E.cost + pnE.cost + cVE.cost +
        13 * (ℓ / 32) + 241000 := by
  let tupT : Ty ASig := .prod (simFullT ℓ Pt) (.prod (simMirT ℓ Pt)
    (.prod .bool (.prod PlainT (.prod .bool (.prod (B 32) (.prod U32 (fig8CtT (ℓ := ℓ) (Pt := Pt))))))))
  let Γ1 := tupT :: Γ
  let Γ2 := B 32 :: Γ1
  let Γ3 := keptT ℓ Pt :: Γ2
  have hw := toWireAtomicE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1)
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
  have hks := keptSendAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2)
    (pGet (scKept (.fst .v1)) (.fst (.snd (.snd .v1))))
  have hrec := cost_mRecordE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ3)
    (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))
    (.pair (.pair (.fst (.snd (.snd .v2)))
      (.pair (pGet (mEpoch (.fst (.snd .v2))) (.fst (.snd (.snd .v2))))
        (.add (pGet (mIdx (.fst (.snd .v2))) (.fst (.snd (.snd .v2)))) (.nat 1))))
      (.pair (.fst (.snd (.snd (.snd .v2)))) .v1))
    (.fst (.snd (.snd (.snd (.snd .v2)))))
  dsimp only [scPostSendAtomicE]
  generalize toWireAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) _ = ew at hw ⊢
  generalize keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) _ = eks at hks ⊢
  generalize mRecordE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ3) _ _ _ _ = erec at hrec ⊢
  have hb2 : bits 2 ≤ 2 := bits_le_of_lt_pow (by omega) (by omega)
  dsimp only [cost_eLet, pGet, pSet, sendsInE, scMk, ssMk, scBase, scKept, scSent, scSnaps,
    ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped, mEpoch, mIdx,
    f8Id, f8Tcur, f8VS, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.cost] at hw hks hrec ⊢
  simp only [sb_c0, sb_c1] at hrec ⊢
  omega

theorem scPostSendAtomicE_descBits_le (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (s1E : Expr AOps Γ (simMirT ℓ Pt))
    (qBE : Expr AOps Γ .bool) (m0E : Expr AOps Γ PlainT) (chBE : Expr AOps Γ .bool)
    (pq'E : Expr AOps Γ (B 32)) (pnE : Expr AOps Γ U32)
    (cVE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc
      (scPostSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB sCE s1E qBE m0E chBE pq'E pnE cVE) ≤
      atomicExprDescBits ADesc sCE + atomicExprDescBits ADesc s1E +
      atomicExprDescBits ADesc qBE + atomicExprDescBits ADesc m0E +
      atomicExprDescBits ADesc chBE + atomicExprDescBits ADesc pq'E +
      atomicExprDescBits ADesc pnE + atomicExprDescBits ADesc cVE + 40000 := by
  let tupT : Ty ASig := .prod (simFullT ℓ Pt) (.prod (simMirT ℓ Pt)
    (.prod .bool (.prod PlainT (.prod .bool (.prod (B 32) (.prod U32 (fig8CtT (ℓ := ℓ) (Pt := Pt))))))))
  let Γ1 := tupT :: Γ
  let Γ2 := B 32 :: Γ1
  let Γ3 := keptT ℓ Pt :: Γ2
  have hw := toWireAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1)
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
  have hks := keptSendAtomicE_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ2)
    (pGet (scKept (.fst .v1)) (.fst (.snd (.snd .v1))))
  have hrec := mRecordE_descBits_le (ℓ := ℓ) (Pt := Pt) ADesc (Γ := Γ3)
    (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))
    (.pair (.pair (.fst (.snd (.snd .v2)))
      (.pair (pGet (mEpoch (.fst (.snd .v2))) (.fst (.snd (.snd .v2))))
        (.add (pGet (mIdx (.fst (.snd .v2))) (.fst (.snd (.snd .v2)))) (.nat 1))))
      (.pair (.fst (.snd (.snd (.snd .v2)))) .v1))
    (.fst (.snd (.snd (.snd (.snd .v2)))))
  dsimp only [scPostSendAtomicE]
  generalize toWireAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) _ = ew at hw ⊢
  generalize keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) _ = eks at hks ⊢
  generalize mRecordE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ3) _ _ _ _ = erec at hrec ⊢
  simp only [descBits_eLet, tupT, PlainT, B, U32,
    pGet, pSet, sendsInE, scMk, ssMk, scBase, scKept, scSent, scSnaps,
    ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped, mEpoch, mIdx,
    f8Id, f8Tcur, f8VS, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    varIdx, atomicExprDescBits, Nat.reduceAdd,
    sb_c0, sb_c1, sb_c2, sb_c3, sb_c4] at hw hks hrec ⊢
  omega

end PostSend

/-! ## Coin sampling and target query -/

section CoinsAndQuery

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ADesc" => atomicSessionOpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
  (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)

@[local simp] private theorem cq_c0 : bits 0 = 1 := bits_zero
@[local simp] private theorem cq_c1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem cq_c2 : bits 2 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)

omit [DecidableEq Pt] [Zero Pt] in
@[local simp] private theorem liftP_fig8SmIface_eq_liftM {α : Type} (p : ProbComp α) :
    (fig8SmIface ℓ Pt).liftP p =
      (liftM p : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) α) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [Iface.liftP]
  | query_bind n mx ih =>
    dsimp only [Iface.liftP, fig8SmIface] at ih ⊢
    rw [simulateQ_bind, simulateQ_query]
    exact congrArg (Bind.bind _) (funext ih)

def simDrawSendCoinsC {Γ : List (Ty ASig)} (rE : Expr AOps Γ (.opt BV512)) :
    Comp AOps (fig8SmIface ℓ Pt) Γ (.prod BV512 (.opt BV256)) :=
  .caseOpt rE
    (.bind (Comp.sample (I := fig8SmIface ℓ Pt) (UniformSamplerTag.base .bv512) .unit)
      (.ret (.pair .v0 .none)))
    (.bind (Comp.sample (I := fig8SmIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit)
      (.ret (.pair .v1 (.some .v0))))

@[simp] theorem simDrawSendCoinsC_queries {Γ : List (Ty ASig)} (rE : Expr AOps Γ (.opt BV512))
    (w : SMTag → ℕ) :
    (simDrawSendCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) rE).queries w (fun _ => 0) = 0 := rfl

theorem simDrawSendCoinsC_cost {Γ : List (Ty ASig)} (rE : Expr AOps Γ (.opt BV512)) :
    (simDrawSendCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) rE).cost ≤ rE.cost + 16 := by
  dsimp only [simDrawSendCoinsC, Comp.cost, Expr.cost, Expr.v0, Expr.v1, fig8SmIface,
    _root_.ReductionDsl.atomicSamplers, _root_.ReductionDsl.unifSamplers,
    _root_.ReductionDsl.AtomicUnifBase.cost]
  omega

theorem simDrawSendCoinsC_descBits_le {Γ : List (Ty ASig)} (rE : Expr AOps Γ (.opt BV512)) :
    atomicCompDescBits ADesc (fun _ => 8) (fun _ => 8)
      (simDrawSendCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) rE) ≤
      atomicExprDescBits ADesc rE + 150 := by
  simp only [simDrawSendCoinsC, BV256, Expr.v0, Expr.v1, varIdx,
    atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    Nat.reduceAdd, cq_c0, cq_c1]
  omega

theorem simDrawSendCoinsC_eval {Γ : List (Ty ASig)} (rE : Expr AOps Γ (.opt BV512)) (ρ : Env Γ) :
    (simDrawSendCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) rE).eval ρ =
      semDrawSendCoins (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
        (rE.eval ρ) := by
  rcases hr : rE.eval ρ with _ | rq <;>
    simp only [simDrawSendCoinsC, semDrawSendCoins, fig8IdSemHook,
      Comp.eval, Expr.eval, Expr.v0, Expr.v1, Env.get, hr, liftP_fig8SmIface_eq_liftM] <;>
    rfl

def simSendQueryC {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (pubVE : Expr AOps Γ (lpubT (ℓ := ℓ) (Pt := Pt)))
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rcOptE : Expr AOps Γ (.opt BV256)) :
    Comp AOps (fig8SmIface ℓ Pt) Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) :=
  .bind (.ret (.pair chalE (.pair qBE (.pair pubVE (.pair m0E rcOptE)))))
    (.caseOpt (.fst .v0)
      (Comp.query (I := fig8SmIface ℓ Pt) SMTag.tr
        (let r := Expr.snd .v0
         .pair (.fst r) (.pair (.pair (.fst (.snd r)) (.fst (.snd (.snd r))))
           (.snd (.snd (.snd r))))))
      (Comp.query (I := fig8SmIface ℓ Pt) SMTag.ch
        (let r := Expr.snd .v1
         .pair (.fst r)
           (.pair (.pair (.fst (.snd r)) (.fst (.snd (.snd r))))
             (.pair (.pair (.fst (.snd r)) .v0) (.snd (.snd (.snd r))))))))

@[simp] theorem simSendQueryC_queries {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (pubVE : Expr AOps Γ (lpubT (ℓ := ℓ) (Pt := Pt)))
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rcOptE : Expr AOps Γ (.opt BV256)) :
    (simSendQueryC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) qBE pubVE m0E chalE rcOptE).queries
      (fun _ => 1) (fun _ => 0) = 1 := rfl

theorem simSendQueryC_cost {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (pubVE : Expr AOps Γ (lpubT (ℓ := ℓ) (Pt := Pt)))
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rcOptE : Expr AOps Γ (.opt BV256)) :
    (simSendQueryC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) qBE pubVE m0E chalE rcOptE).cost ≤
      qBE.cost + pubVE.cost + m0E.cost + chalE.cost + rcOptE.cost +
        3 * (ℓ / 32) + 80 := by
  dsimp only [simSendQueryC, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
  omega

theorem simSendQueryC_descBits_le {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (pubVE : Expr AOps Γ (lpubT (ℓ := ℓ) (Pt := Pt)))
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rcOptE : Expr AOps Γ (.opt BV256)) :
    atomicCompDescBits ADesc (fun _ => 8) (fun _ => 8)
      (simSendQueryC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) qBE pubVE m0E chalE rcOptE) ≤
      atomicExprDescBits ADesc qBE + atomicExprDescBits ADesc pubVE +
      atomicExprDescBits ADesc m0E + atomicExprDescBits ADesc chalE +
      atomicExprDescBits ADesc rcOptE + 500 := by
  simp only [simSendQueryC, Expr.v0, Expr.v1, varIdx,
    atomicCompDescBits, atomicExprDescBits, Nat.reduceAdd, cq_c0, cq_c1]
  omega

theorem simSendQueryC_eval {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (pubVE : Expr AOps Γ (lpubT (ℓ := ℓ) (Pt := Pt)))
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rcOptE : Expr AOps Γ (.opt BV256)) (ρ : Env Γ)
    (Q : Party) (pub : LibsignalMsgPublicPart) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (rc : Option (BitVec 256))
    (hq : qBE.eval ρ = partyEnc Q) (hpub : pubVE.eval ρ = lpubV (ℓ := ℓ) (Pt := Pt) pub)
    (hm0 : m0E.eval ρ = m₀) (hch : chalE.eval ρ = chal) (hrc : rcOptE.eval ρ = rc) :
    (simSendQueryC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) qBE pubVE m0E chalE rcOptE).eval ρ =
      (fun p => p.1.map (fig8CtV (ℓ := ℓ) (Pt := Pt))) <$>
        (match chal with
         | none => (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none).onTr Q (pub, m₀) rc ()
         | some m₁ =>
           (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none).onCh Q (pub, m₀) (pub, m₁) rc ()) := by
  have hpQ : boolToParty (partyEnc Q) = Q := by cases Q <;> rfl
  rcases chal with _ | m₁
  · simp only [simSendQueryC, Comp.eval, Expr.eval, Expr.v0,
      hq, hpub, hm0, hch, hrc, fig8SmIface, fig8IdSemHook, CryptoGames.SM.transmitQuery,
      pure_bind, bind_pure_comp, Functor.map_map]
    rw [_root_.ReductionDsl.Env.get_cons_zero, hpQ, lpubOfV_lpubV]
    rfl
  · simp only [simSendQueryC, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
      hq, hpub, hm0, hch, hrc, fig8SmIface, fig8IdSemHook, CryptoGames.SM.challQuery,
      pure_bind, bind_pure_comp, Functor.map_map]
    rw [_root_.ReductionDsl.Env.get_cons_zero]
    dsimp only
    rw [_root_.ReductionDsl.Env.get_cons_succ, _root_.ReductionDsl.Env.get_cons_zero,
      hpQ, lpubOfV_lpubV]
    rfl

end CoinsAndQuery

/-! ## Send/challenge hook and step specification -/

section SendStep

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ADesc" => atomicSessionOpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
  (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)

@[local simp] private theorem sh_c0 : bits 0 = 1 := bits_zero
@[local simp] private theorem sh_c1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem sh_c2 : bits 2 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem sh_c3 : bits 3 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem sh_c4 : bits 4 = 3 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem sh_c5 : bits 5 = 3 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem sh_c6 : bits 6 = 3 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem sh_c7 : bits 7 = 3 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem sh_c32 : bits 32 = 6 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem sh_p32 : bits ((32 : ℕ+) : ℕ) = 6 := sh_c32

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem bits_mono_le {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

abbrev sendInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt) (.prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))))

/-- Atomic `Comp` implementing `semSendHook` for transmit and challenge queries. -/
def simFig8SendHookC (idA idB : IdentityKey) (qep : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) :
    Comp AOps (fig8SmIface ℓ Pt) Γ (.prod (.opt (B 32)) (simFullT ℓ Pt)) :=
  .bind (.ret (.pair sCE (.pair qBE (.pair m0E (.pair chalE rE)))))
    (let s0   : Expr AOps _ (simFullT ℓ Pt) := .fst .v0
     let b0   := scBase s0
     let mir0 := ssMir b0
     let q0   : Expr AOps _ .bool := .fst (.snd .v0)
     let r0   : Expr AOps _ (.opt BV512) := .snd (.snd (.snd (.snd .v0)))
     .ite (orE (orE (ssStopped b0) (mWin mir0)) (.not (mNoBobEpoch0E mir0 q0)))
       (.ret (.pair .none s0))
       (.caseOpt (mEpMgmtE qep mir0 q0 (isSomeE r0))
         (.ret (.pair .none s0))
         (.ite (.and (isSomeE (.fst (.snd (.snd (.snd .v1)))))
             (.not (mSafeChE .v0 (.fst (.snd .v1)))))
           (.ret (.pair .none (.fst .v1)))
           (.bind (simDrawSendCoinsC (.snd (.snd (.snd (.snd .v1)))))
             (.bind (.ret
                 (let b2   := scBase (.fst .v2)
                  let mir2 := ssMir b2
                  let q2   : Expr AOps _ .bool := .fst (.snd .v2)
                  Expr.ite (.not (.eqN (pGet (mEpoch .v1) q2) (pGet (mEpoch mir2) q2)))
                    (sOpPure .u32OfNat (.sub (pGet (mIdx mir2) q2) (.nat 1)))
                    (pGet (ssPn b2) q2)))
               (.bind
                 (mkPubAtomicC (fig8SmIface ℓ Pt) idA idB
                   (scBase (.fst .v3)) (.fst (.snd .v3)) (.fst .v1) .v0)
                 (.caseOpt .v0
                   (.ret (.pair .none (.fst .v4)))
                   (.bind
                     (simSendQueryC (.fst (.snd .v5)) (.snd .v0) (.fst (.snd (.snd .v5)))
                       (.fst (.snd (.snd (.snd .v5)))) (.snd .v3))
                     (.caseOpt .v0
                       (.ret (.pair .none (.fst .v6)))
                       (let v7 : Expr AOps _ (sendInpT ℓ Pt) :=
                          .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
                        .ret (eLet
                          (scPostSendAtomicE idA idB (.fst v7) .v6 (.fst (.snd v7))
                            (.fst (.snd (.snd v7)))
                            (isSomeE (.fst (.snd (.snd (.snd v7)))))
                            (.fst .v2) .v4 .v0)
                          (.pair (.some (.fst .v0)) (.snd .v0)))))))))))))

theorem simFig8SendHookC_queries (idA idB : IdentityKey) (qep : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) :
    (simFig8SendHookC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB qep sCE qBE m0E chalE rE).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  simp [simFig8SendHookC, Comp.queries]

theorem simFig8SendHookC_cost (idA idB : IdentityKey) (qep : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) :
    (simFig8SendHookC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB qep sCE qBE m0E chalE rE).cost ≤
      sCE.cost + qBE.cost + m0E.cost + chalE.cost + rE.cost +
        16 * (ℓ / 32) + 2 * bits qep + 2400000 := by
  let Γ1 := sendInpT ℓ Pt :: Γ; let Γ2 := simMirT ℓ Pt :: Γ1
  let Γ3 := Ty.prod BV512 (.opt BV256) :: Γ2; let Γ4 := U32 :: Γ3
  let Γ5 := Ty.opt (.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt))) :: Γ4
  let Γ6 := Ty.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt)) :: Γ5
  let Γ7 := Ty.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ6
  let Γ8 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ7
  have hnb := cost_mNoBobEpoch0E (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1)
    (ssMir (scBase (.fst .v0))) (.fst (.snd .v0))
  have hep := cost_mEpMgmtE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) qep
    (ssMir (scBase (.fst .v0))) (.fst (.snd .v0)) (isSomeE (.snd (.snd (.snd (.snd .v0)))))
  have hsf := cost_mSafeChE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ2) .v0 (.fst (.snd .v1))
  have hdc := simDrawSendCoinsC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.snd (.snd (.snd (.snd .v1))))
  have hmk := mkPubAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB (Γ := Γ4)
    (scBase (.fst .v3)) (.fst (.snd .v3)) (.fst .v1) .v0
  have hsq := simSendQueryC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ6)
    (.fst (.snd .v5)) (.snd .v0) (.fst (.snd (.snd .v5))) (.fst (.snd (.snd (.snd .v5)))) (.snd .v3)
  let v7 : Expr AOps Γ8 (sendInpT ℓ Pt) := .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
  have hps := scPostSendAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ8) (.fst v7) .v6 (.fst (.snd v7))
    (.fst (.snd (.snd v7))) (isSomeE (.fst (.snd (.snd (.snd v7))))) (.fst .v2) .v4 .v0
  dsimp only [simFig8SendHookC]
  generalize mNoBobEpoch0E (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) _ _ = enb at hnb ⊢
  generalize mEpMgmtE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) qep _ _ _ = eep at hep ⊢
  generalize mSafeChE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ2) _ _ = esf at hsf ⊢
  generalize simDrawSendCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) _ = cdc at hdc ⊢
  generalize mkPubAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB (Γ := Γ4) _ _ _ _ = cmk at hmk ⊢
  generalize simSendQueryC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ6) _ _ _ _ _ = csq at hsq ⊢
  generalize scPostSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ8) _ _ _ _ _ _ _ _ = eps at hps ⊢
  dsimp only [v7, Comp.cost, Expr.cost, cost_eLet, cost_sOpPure, AtomicPureOp.cost,
    orE, isSomeE, pGet, scBase, ssMir, ssStopped, ssPn, mWin, mEpoch, mIdx,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6] at hnb hep hsf hdc hmk hsq hps ⊢
  simp only [sh_c1]; omega

theorem simFig8SendHookC_descBits_le (idA idB : IdentityKey) (qep : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) :
    atomicCompDescBits ADesc (fun _ => 8) (fun _ => 8)
      (simFig8SendHookC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB qep sCE qBE m0E chalE rE) ≤
      atomicExprDescBits ADesc sCE + atomicExprDescBits ADesc qBE +
      atomicExprDescBits ADesc m0E + atomicExprDescBits ADesc chalE +
      atomicExprDescBits ADesc rE + 4 * bits qep + 80000 := by
  let Γ1 := sendInpT ℓ Pt :: Γ; let Γ2 := simMirT ℓ Pt :: Γ1
  let Γ3 := Ty.prod BV512 (.opt BV256) :: Γ2; let Γ4 := U32 :: Γ3
  let Γ5 := Ty.opt (.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt))) :: Γ4
  let Γ6 := Ty.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt)) :: Γ5
  let Γ7 := Ty.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ6
  let Γ8 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ7
  have hnb := mNoBobEpoch0E_descBits_le (ℓ := ℓ) (Pt := Pt) ADesc (Γ := Γ1)
    (ssMir (scBase (.fst .v0))) (.fst (.snd .v0))
  have hep := mEpMgmtE_descBits_le (ℓ := ℓ) (Pt := Pt) ADesc qep (Γ := Γ1)
    (ssMir (scBase (.fst .v0))) (.fst (.snd .v0)) (isSomeE (.snd (.snd (.snd (.snd .v0)))))
  have hsf := mSafeChE_descBits_le (ℓ := ℓ) (Pt := Pt) ADesc (Γ := Γ2) .v0 (.fst (.snd .v1))
  have hdc := simDrawSendCoinsC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.snd (.snd (.snd (.snd .v1))))
  have hmk := mkPubAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB (fun _ => 8) (fun _ => 8) (Γ := Γ4)
    (scBase (.fst .v3)) (.fst (.snd .v3)) (.fst .v1) .v0
  have hsq := simSendQueryC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ6)
    (.fst (.snd .v5)) (.snd .v0) (.fst (.snd (.snd .v5))) (.fst (.snd (.snd (.snd .v5)))) (.snd .v3)
  let v7 : Expr AOps Γ8 (sendInpT ℓ Pt) := .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
  have hps := scPostSendAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ8) (.fst v7) .v6 (.fst (.snd v7))
    (.fst (.snd (.snd v7))) (isSomeE (.fst (.snd (.snd (.snd v7))))) (.fst .v2) .v4 .v0
  dsimp only [simFig8SendHookC]
  generalize mNoBobEpoch0E (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) _ _ = enb at hnb ⊢
  generalize mEpMgmtE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) qep _ _ _ = eep at hep ⊢
  generalize mSafeChE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ2) _ _ = esf at hsf ⊢
  generalize simDrawSendCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) _ = cdc at hdc ⊢
  generalize mkPubAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB (Γ := Γ4) _ _ _ _ = cmk at hmk ⊢
  generalize simSendQueryC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ6) _ _ _ _ _ = csq at hsq ⊢
  generalize scPostSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ8) _ _ _ _ _ _ _ _ = eps at hps ⊢
  simp only [v7, atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    descBits_eLet, descBits_sOpPure, atomicPureOpDescBits, B,
    orE, isSomeE, pGet, scBase, ssMir, ssStopped, ssPn, mWin, mEpoch, mIdx,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, varIdx, Nat.reduceAdd,
    sh_c0, sh_c1, sh_c2, sh_c3, sh_c4, sh_c5, sh_c6, sh_c7, sh_p32] at hnb hep hsf hdc hmk hsq hps ⊢
  omega

theorem simFig8SendHookC_eval (idA idB : IdentityKey) (qep : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (hsC : sCE.eval ρ = simFullEnc sC) (hq : qBE.eval ρ = partyEnc Q)
    (hm0 : m0E.eval ρ = m₀) (hch : chalE.eval ρ = chal) (hr : rE.eval ρ = r)
    (htight : CryptoVerification.SpqrV1Sync.SendTotal.TopStateTight C.F K (sC.base.pq Q)) :
    (simFig8SendHookC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB qep sCE qBE m0E chalE rE).eval ρ =
      (fun z => (z.1, simFullEnc z.2.1)) <$>
        semSendHook (paramsV1 C K idA idB) Dh encPt encT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
          qep sC () Q m₀ chal r := by
  dsimp only [simFig8SendHookC, semSendHook, Comp.eval]
  let inp : (sendInpT ℓ Pt).denote := (simFullEnc sC, (partyEnc Q, (m₀, (chal, r))))
  have hinp : (Expr.pair sCE (.pair qBE (.pair m0E (.pair chalE rE)))).eval ρ = inp := by
    simp [inp, Expr.eval, hsC, hq, hm0, hch, hr]
  rw [hinp, pure_bind]
  let ρ1 := Env.cons (t := sendInpT ℓ Pt) inp ρ
  have hg1 : (orE (orE (ssStopped (scBase (.fst .v0))) (mWin (ssMir (scBase (.fst .v0)))))
      (.not (mNoBobEpoch0E (ssMir (scBase (.fst .v0))) (.fst (.snd .v0)))) :
      Expr AOps _ .bool).eval ρ1 =
      (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) := by
    have hs1 : (ssStopped (scBase (.fst .v0)) : Expr AOps _ .bool).eval ρ1 = sC.base.stopped := rfl
    have hw1 : (mWin (ssMir (scBase (.fst .v0))) : Expr AOps _ .bool).eval ρ1 = sC.base.mir.win := rfl
    have hnb : (mNoBobEpoch0E (ssMir (scBase (.fst .v0))) (.fst (.snd .v0)) :
        Expr AOps _ .bool).eval ρ1 = noBobSendInEpoch0 sC.base.mir Q :=
      mNoBobEpoch0E_eval _ _ ρ1 sC.base.mir Q rfl rfl
    rw [orE_eval, orE_eval, hs1, hw1]
    dsimp only [Expr.eval]
    rw [hnb]
  rw [hg1]
  cases hstop : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hep : (mEpMgmtE qep (ssMir (scBase (.fst .v0))) (.fst (.snd .v0))
        (isSomeE (.snd (.snd (.snd (.snd .v0))))) :
        Expr AOps _ (.opt (simMirT ℓ Pt))).eval ρ1 =
        (sC.base.mir.epMgmt 3 qep Q r.isSome).map (simMirEnc (Pt := Pt)) := by
      rw [mEpMgmtE_eval qep _ _ _ ρ1 sC.base.mir Q rfl rfl, isSomeE_eval]; rfl
    rw [hep]
    rcases hep_res : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · simp only [map_pure]; rfl
    · dsimp only [Option.map]
      let ρ2 := Env.cons (t := simMirT ℓ Pt) (simMirEnc (Pt := Pt) s₁) ρ1
      have hg2 : (Expr.and (isSomeE (.fst (.snd (.snd (.snd .v1)))))
          (.not (mSafeChE .v0 (.fst (.snd .v1)))) : Expr AOps _ .bool).eval ρ2 =
          (chal.isSome && !(s₁.safeCh 3 Q)) := by
        have his : (isSomeE (.fst (.snd (.snd (.snd .v1)))) : Expr AOps _ .bool).eval ρ2 =
            chal.isSome := isSomeE_eval _ ρ2
        have hsf : (mSafeChE .v0 (.fst (.snd .v1)) : Expr AOps _ .bool).eval ρ2 =
            s₁.safeCh 3 Q := mSafeChE_eval _ _ ρ2 s₁ Q rfl rfl
        dsimp only [Expr.eval]; rw [his, hsf]
      rw [hg2]
      cases hsf_guard : (chal.isSome && !(s₁.safeCh 3 Q))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hdc : (simDrawSendCoinsC (.snd (.snd (.snd (.snd .v1)))) :
            Comp AOps _ _ _).eval ρ2 =
            semDrawSendCoins (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none) r :=
          simDrawSendCoinsC_eval _ ρ2
        rw [hdc]
        simp only [fig8IdSemHook, pure_bind, map_bind]
        refine bind_congr fun ⟨rq, rc⟩ => ?_
        let ρ3 := Env.cons (t := .prod BV512 (.opt BV256)) (rq, rc) ρ2
        let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then
          BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
        have hpn : (Expr.ite (.not (.eqN (pGet (mEpoch .v1) (.fst (.snd .v2)))
              (pGet (mEpoch (ssMir (scBase (.fst .v2)))) (.fst (.snd .v2)))))
            (sOpPure .u32OfNat (.sub (pGet (mIdx (ssMir (scBase (.fst .v2)))) (.fst (.snd .v2))) (.nat 1)))
            (pGet (ssPn (scBase (.fst .v2))) (.fst (.snd .v2))) : Expr AOps _ U32).eval ρ3 = pn := by
          have hep1 : (pGet (mEpoch .v1) (.fst (.snd .v2)) : Expr AOps _ .nat).eval ρ3 =
              s₁.epoch Q := by cases Q <;> rfl
          have hep0 : (pGet (mEpoch (ssMir (scBase (.fst .v2)))) (.fst (.snd .v2)) :
              Expr AOps _ .nat).eval ρ3 = sC.base.mir.epoch Q := by cases Q <;> rfl
          have hidx0 : (pGet (mIdx (ssMir (scBase (.fst .v2)))) (.fst (.snd .v2)) :
              Expr AOps _ .nat).eval ρ3 = sC.base.mir.idx Q := by cases Q <;> rfl
          have hpn0 : (pGet (ssPn (scBase (.fst .v2))) (.fst (.snd .v2)) :
              Expr AOps _ U32).eval ρ3 = sC.base.pn Q := by cases Q <;> rfl
          dsimp only [pn]; rw [ite_eval]
          simp only [Expr.eval, eval_sOpPure, AtomicPureOp.eval, hep1, hep0, hidx0, hpn0]
          by_cases heq : s₁.epoch Q = sC.base.mir.epoch Q <;> simp [heq]
        rw [hpn]
        let ρ4 := Env.cons (t := U32) pn ρ3
        have hpQ_dec : partyDec (partyEnc Q) = Q := by cases Q <;> rfl
        have hmk : (mkPubAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB
            (scBase (.fst .v3)) (.fst (.snd .v3)) (.fst .v1) .v0).eval ρ4 =
            pure ((mkPub (P := paramsV1 C K idA idB) sC.base Q rq pn).map
              fun (pq', pub) => (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub)) := by
          rw [mkPubAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB _ _ _ _ ρ4
            sC.base (partyEnc Q) rq pn rfl rfl rfl rfl (hpQ_dec.symm ▸ htight), hpQ_dec]
        rw [hmk, pure_bind]
        let mkOpt := (mkPub (P := paramsV1 C K idA idB) sC.base Q rq pn).map
          fun (pq', pub) => (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub)
        let ρ5 := Env.cons (t := .opt (.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt)))) mkOpt ρ4
        have hv0_mk : (Expr.v0 : Expr AOps _ _).eval ρ5 = mkOpt := rfl
        rw [hv0_mk]
        rcases hmk_res : mkPub (P := paramsV1 C K idA idB) sC.base Q rq pn with _ | ⟨pq', pub⟩
        · dsimp only [mkOpt]; rw [hmk_res]; simp only [map_pure]; rfl
        · dsimp only [mkOpt]; rw [hmk_res]; dsimp only [Option.map]
          let ρ5' := Env.cons (t := .opt (.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt))))
            (some (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub)) ρ4
          let ρ6 := Env.cons (t := .prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt)))
            (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub) ρ5'
          have hsq := simSendQueryC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) (Γ := _)
            (.fst (.snd .v5)) (.snd .v0) (.fst (.snd (.snd .v5)))
            (.fst (.snd (.snd (.snd .v5)))) (.snd .v3) ρ6 Q pub m₀ chal rc rfl rfl rfl rfl rfl
          rw [hsq, bind_map_left, map_bind]
          refine bind_congr fun ⟨res, ex₂⟩ => ?_
          have hv0_ct : (Expr.v0 : Expr AOps _ _).eval
              (Env.cons (t := .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))
                (res.map (fig8CtV (ℓ := ℓ) (Pt := Pt))) ρ6) =
              res.map (fig8CtV (ℓ := ℓ) (Pt := Pt)) := rfl
          rw [hv0_ct]
          rcases res with _ | c
          · dsimp only [Option.map]; simp only [map_pure]; rfl
          · dsimp only [Option.map]
            let ρ7 := Env.cons (t := .opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (some (fig8CtV c)) ρ6
            let ρ8 := Env.cons (t := fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtV c) ρ7
            let Γ8 : List (Ty ASig) := fig8CtT (ℓ := ℓ) (Pt := Pt) :: .opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) ::
              .prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt)) :: .opt (.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt))) ::
              U32 :: .prod BV512 (.opt BV256) :: simMirT ℓ Pt :: sendInpT ℓ Pt :: Γ
            let v7 : Expr AOps Γ8 (sendInpT ℓ Pt) := .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
            have hpost := scPostSendAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam) idA idB
              (.fst v7) .v6 (.fst (.snd v7)) (.fst (.snd (.snd v7)))
              (isSomeE (.fst (.snd (.snd (.snd v7))))) (.fst .v2) .v4 .v0 ρ8
              sC s₁ Q m₀ chal.isSome pq' pn c rfl rfl rfl rfl
              (isSomeE_eval _ ρ8) rfl rfl rfl
            rw [eval_eLet, hpost]; simp only [map_pure]; rfl
      · rfl
  · rfl

def unpackSendQE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (qE : Expr O' Γ (smQT (ℓ := ℓ) (Pt := Pt))) :
    Expr O' Γ (.opt (.prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))))) :=
  .caseSum qE
    (.some (.pair (.fst .v0) (.pair (.fst (.snd .v0)) (.pair .none (.snd (.snd .v0))))))
    (.caseSum .v0
      (.some (.pair (.fst .v0) (.pair (.fst (.snd .v0))
        (.pair (.some (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))))))
      .none)

/-- Single-query `Comp` over `[simFullT ℓ Pt, smQT]` handling both send and challenge. -/
def simFig8StepSendC (idA idB : IdentityKey) (qep : ℕ) :
    Comp AOps (fig8SmIface ℓ Pt) [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)) :=
  .caseOpt (unpackSendQE .v1) (.ret (.pair (.pair .none (.pair .none .none)) .v0))
    (.bind (simFig8SendHookC idA idB qep .v1 (.fst .v0) (.fst (.snd .v0))
        (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))))
      (.ret (.pair (.pair (.fst .v0) (.pair .none .none)) (.snd .v0))))

end SendStep

/-- Specification bundle for the send/challenge atomic `Comp` branch of `simFig8OracleSan`. -/
structure SimFig8SendStepSpec (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) where
  step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
    [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
    (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt))
  hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1
  hstep_c : ℓ < 10 ^ 6 →
    step.cost ≤ 60000000 + 30000000 * q + 1024 * bits (qep + 1)
  hstep_d : ℓ < 10 ^ 6 →
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
      2 ^ 20 + 2 ^ 11 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))
  hstep_tr : ℓ < 10 ^ 6 →
    ∀ (P : CryptoGames.Party) (m : CryptoGames.CBC.Plain ℓ) (r : Option (BitVec 512))
      (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded q (simFullDec s_raw) →
      SanSnapExtra C K (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step
          (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run s_raw)) =
      ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep
        (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q)
        (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (simFullDec s_raw))
  hstep_ch : ℓ < 10 ^ 6 →
    ∀ (P : CryptoGames.Party) (m₀ m₁ : CryptoGames.CBC.Plain ℓ) (r : Option (BitVec 512))
      (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded q (simFullDec s_raw) →
      SanSnapExtra C K (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step
          (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run s_raw)) =
      ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep
        (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q)
        (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (simFullDec s_raw))

/-- Constructive send/challenge atomic step bundle for `simFig8`. -/
def simFig8SendStepSpec {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    SimFig8SendStepSpec Pt ℓ C K idA idB Dh encPt encT decT lam qep q where
  step := simFig8StepSendC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep
  hstep_q := by
    let Γ0 := [Ty.prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))),
      simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
    have h := simFig8SendHookC_queries (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep (Γ := Γ0)
      .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
    dsimp only [simFig8StepSendC]
    generalize simFig8SendHookC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep (Γ := Γ0)
      _ _ _ _ _ = ch at h ⊢
    dsimp only [Comp.queries] at h ⊢
    omega
  hstep_c hℓ := by
    let Γ0 := [Ty.prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))),
      simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
    have h := simFig8SendHookC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep (Γ := Γ0)
      .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
    have hb : bits qep ≤ bits (qep + 1) := bits_mono_le (by omega)
    dsimp only [simFig8StepSendC]
    generalize simFig8SendHookC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep (Γ := Γ0)
      _ _ _ _ _ = ch at h ⊢
    dsimp only [unpackSendQE, Comp.cost, Expr.cost, Expr.v0, Expr.v1] at h ⊢
    omega
  hstep_d _ := by
    let Γ0 := [Ty.prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))),
      simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
    have h := simFig8SendHookC_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep (Γ := Γ0)
      .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
    have hb : bits qep ≤ bits (ratchetCostBudget q (qep + 1) + (qep + 1)) :=
      bits_mono_le (by omega)
    dsimp only [simFig8StepSendC]
    generalize simFig8SendHookC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep (Γ := Γ0)
      _ _ _ _ _ = ch at h ⊢
    simp only [unpackSendQE, PlainT, BV512, B,
      Expr.v0, Expr.v1, varIdx, atomicCompDescBits, atomicExprDescBits,
      atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd,
      sh_c0, sh_c1, sh_p32] at h ⊢
    omega
  hstep_tr _ P m r s_raw _ hExtra := by
    let sC := simFullDec s_raw
    have hs_raw : s_raw = simFullEnc sC := (simFullEnc_simFullDec s_raw).symm
    have hpP : partyToBool P = partyEnc P := by cases P <;> rfl
    let qEnc : (smQT (ℓ := ℓ) (Pt := Pt)).denote := Sum.inl (partyToBool P, (m, r))
    let ρ0 := Env.cons (t := .prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))))
      (partyToBool P, (m, (none, r))) (.cons s_raw (.cons qEnc .nil))
    have hunp : (unpackSendQE (ℓ := ℓ) (Pt := Pt)
        (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (Γ := [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]) .v1).eval
        (.cons s_raw (.cons qEnc .nil)) = some (partyToBool P, (m, (none, r))) := rfl
    have hh := simFig8SendHookC_eval (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep
      .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))) ρ0
      sC P m none r hs_raw hpP rfl rfl rfl (hExtra.1 P)
    have hrun : (handlerImpl (C := e2eSessionCodec ℓ Pt)
          (simFig8StepSendC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
            (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep)
          (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run s_raw =
        (simFig8SendHookC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep
          .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
          (.snd (.snd (.snd .v0)))).eval ρ0 := by
      dsimp only [handlerImpl, e2eSessionCodec, _root_.ReductionDsl.smQenc, _root_.ReductionDsl.smRdec]
      rw [StateT.run_mk]
      dsimp only [simFig8StepSendC, Comp.eval]
      rw [hunp]
      change ((simFig8SendHookC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep
          .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
          (.snd (.snd (.snd .v0)))).eval ρ0 >>=
          fun x => pure ((x.1, (none, none)), x.2)) >>= (fun p => pure (p.1.1, p.2)) = _
      simp only [bind_assoc, pure_bind, Prod.mk.eta, bind_pure]
    rw [hrun, hh]
    simp only [simFig8OracleSan, StateT.run_mk,
      Computational.Proofs.Game.PromotedCostedReds.SanOracleCore.semHandleHookDedupS, Functor.map_map]
    congr 1; funext ⟨res, sC', _⟩; simp [Prod.map]
  hstep_ch _ P m₀ m₁ r s_raw _ hExtra := by
    let sC := simFullDec s_raw
    have hs_raw : s_raw = simFullEnc sC := (simFullEnc_simFullDec s_raw).symm
    have hpP : partyToBool P = partyEnc P := by cases P <;> rfl
    let qEnc : (smQT (ℓ := ℓ) (Pt := Pt)).denote := Sum.inr (Sum.inl (partyToBool P, (m₀, (m₁, r))))
    let ρ0 := Env.cons (t := .prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))))
      (partyToBool P, (m₀, (some m₁, r))) (.cons s_raw (.cons qEnc .nil))
    have hunp : (unpackSendQE (ℓ := ℓ) (Pt := Pt)
        (O' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (Γ := [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]) .v1).eval
        (.cons s_raw (.cons qEnc .nil)) = some (partyToBool P, (m₀, (some m₁, r))) := rfl
    have hh := simFig8SendHookC_eval (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep
      .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))) ρ0
      sC P m₀ (some m₁) r hs_raw hpP rfl rfl rfl (hExtra.1 P)
    have hrun : (handlerImpl (C := e2eSessionCodec ℓ Pt)
          (simFig8StepSendC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
            (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep)
          (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run s_raw =
        (simFig8SendHookC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep
          .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
          (.snd (.snd (.snd .v0)))).eval ρ0 := by
      dsimp only [handlerImpl, e2eSessionCodec, _root_.ReductionDsl.smQenc, _root_.ReductionDsl.smRdec]
      rw [StateT.run_mk]
      dsimp only [simFig8StepSendC, Comp.eval]
      rw [hunp]
      change ((simFig8SendHookC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep
          .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
          (.snd (.snd (.snd .v0)))).eval ρ0 >>=
          fun x => pure ((x.1, (none, none)), x.2)) >>= (fun p => pure (p.1.1, p.2)) = _
      simp only [bind_assoc, pure_bind, Prod.mk.eta, bind_pure]
    rw [hrun, hh]
    simp only [simFig8OracleSan, StateT.run_mk,
      Computational.Proofs.Game.PromotedCostedReds.SanOracleCore.semHandleHookDedupS, Functor.map_map]
    congr 1; funext ⟨res, sC', _⟩; simp [Prod.map]

theorem simFig8SendStepSpec_nonempty {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    Nonempty (SimFig8SendStepSpec Pt ℓ C K idA idB Dh encPt encT decT lam qep q) :=
  ⟨simFig8SendStepSpec ℓ C K idA idB Dh encPt encT decT lam qep q⟩

end Computational.Proofs.Game.PromotedCostedReds.SimFig8StepSend
