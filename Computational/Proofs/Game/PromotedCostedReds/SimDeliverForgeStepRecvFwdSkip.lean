/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdCost

/-!
# Guard, Probe, and Resync Evaluation Lemmas for `SimDeliverForge`

Proves semantic `.eval` lemmas for the pure expression helpers, probe/resync computations, and
early-reject guard branches of `fwdRecvNewC`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdSkip

open _root_.ReductionDsl (Ty Expr Comp Env SMTagDF atomicSig atomicSessionOps fig8SmIfaceDF
  B PK PlainT PtT lpubV lctT lctV fig8CtT fig8CtV fig8CtOfV fig8StT fig8StV fig8StOfV
  fsSendStV fsSendStOfV smRrT smRrEnc smRrDec partyToBool boolToParty)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (Fig8C SimFig8St SimState SimStateBounded SimCStateBounded
  GhostChain pushChain inReceiveOnlyEpoch onAcceptPure deliverForgeSemHook fig8Clamp fsClampSim
  toWire)
open CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState predictReceive)
open CryptoGames.LibsignalSM.Proofs.Refinement (sameWireFig8)
open CryptoGames.SM (Pos RecvResult partyEnc partyDec posTy posEnc posDec
  ite_eval orE orE_eval boolEq boolEq_eval pGet pSet)
open CryptoGames.SM.Construction.DeliverForge (deliverQueryDF deliverForgeQuery)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.ReductionDsl.Fig8Atomic (salt32V_salt32OfV lpubOfV_lpubV)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (figS fsS evalCKS semResyncHookS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SanSnapExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simMirT simMirEnc simMirDec simRecT simRecEnc simRecDec ghostChainT ghostChainEnc ghostChainDec
   honestPairEnc honestPairDec keptT keptEnc keptDec sentEntryEnc sentEntryDec snapEnc snapDec
   simBaseT simFullT simBaseEnc simBaseDec simFullEnc simFullDec
   fig8CtOfV_fig8CtV simBaseDec_simBaseEnc simFullDec_simFullEnc)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (eLet eval_eLet sOpPure eval_sOpPure srecPos mWin mEpoch
   mSafeInjE mSafeInjE_eval mInTransitE mInTransitE_eval mAcceptE mAcceptE_eval
   mChallContainsE mChallContainsE_eval mTrivialE mTrivialE_eval mInWinE mInWinE_eval
   ssMir ssPq ssPn ssUnackA ssHonest ssChains ssAmb ssStopped ssMk
   ssSetAmb eval_ssSetAmb ssSetMirWin eval_ssSetMirWin
   scBase scKept scSent scSnaps scMk scSetBase eval_scSetBase
   ghostAcceptC ghostAcceptC_eval pushChainE eval_pushChainE
   modifyChainAcceptC modifyChainAcceptC_eval anyChainKeyNoneE eval_anyChainKeyNoneE)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
  (kDecOutT kDecOutV parseOutV knownSeedDecryptAtomicFastC knownSeedDecryptAtomicFastC_eval_snapEnc
   lctSaltEqOfLctAtomicE lctSaltEqOfLctAtomicE_eval injOKAtomicE injOKAtomicE_eval
   toWireAtomicE toWireAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
  (sameWireFig8AtomicE sameWireFig8AtomicE_eval eqFig8CAtomicE eqFig8CAtomicE_eval
   keptRecvAtomicE keptRecvAtomicE_eval keptEvalAtomicE keptEvalAtomicE_eval
   sentEvalAtomicE sentEvalAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdCost
  (dfStepT dfStepDec dfStepEnc dfRecvOutT dfRecvOutDec
   fwdOrElseOptE fwdNoneOutE fwdRejOutE fwdAccRrE fwdOnAcceptFinishE
   fwdInTE fwdScAcceptUpdateE fwdMkCE fwdEvictedE fwdSaltEqE
   fwdAmbCondE fwdScAmbE fwdNewGuardRejectE fwdRefuseE fwdHonestCE
   fwdOnAcceptC fwdProbeC fwdEvalCKSC fwdResyncC)

noncomputable section

section Codecs

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
      (simRecT ℓ Pt).denote → (simRecT ℓ Pt).denote) = id := by
    funext ⟨⟨p, e, i⟩, m, c⟩; cases p <;> rfl
  have hpos : (posEnc ∘ posDec :
      (posTy (S' := atomicSig ℓ Pt)).denote → (posTy (S' := atomicSig ℓ Pt)).denote) = id := by
    funext ⟨p, e, i⟩; cases p <;> rfl
  have hcor : ((fun pe : Party × ℕ => (partyEnc pe.1, pe.2)) ∘
      (fun pe : Bool × ℕ => (partyDec pe.1, pe.2))) = id := by
    funext ⟨p, e⟩; cases p <;> rfl
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

theorem dfStepEnc_dfStepDec (v : (dfStepT ℓ Pt).denote) :
    dfStepEnc (dfStepDec v) = v := by
  rcases v with ⟨sCv, exv⟩
  simp [dfStepEnc, simFullEnc_simFullDec, List.map_map, Function.comp_def,
    fig8CtV_fig8CtOfV]

@[simp] theorem dfStepDec_dfStepEnc
    (st : LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)) :
    dfStepDec (ℓ := ℓ) (Pt := Pt) (dfStepEnc st) = st := by
  rcases st with ⟨sC, ex⟩
  simp [dfStepDec, dfStepEnc, simFullDec_simFullEnc, List.map_map, Function.comp_def,
    fig8CtOfV_fig8CtV]

end Codecs

section SkipAndGuardEval

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
  (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

private theorem not_partyEnc_eq_other (Q : Party) : (!partyEnc Q) = partyEnc Q.other := by
  cases Q <;> rfl

theorem fwdOrElseOptE_eval {Γ : List (Ty ASig)} {a : Ty ASig}
    (e1 e2 : Expr AOps Γ (.opt a)) (ρ : Env Γ) :
    (fwdOrElseOptE C K Dh encPt encT decT lam e1 e2).eval ρ =
      (e1.eval ρ).orElse (fun _ => e2.eval ρ) := by
  let _ := ‹SampleableType Pt›
  dsimp only [fwdOrElseOptE, eLet, Expr.eval]
  cases e1.eval ρ <;> rfl

theorem fwdNoneOutE_eval {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (ρ : Env Γ) :
    dfRecvOutDec ((fwdNoneOutE C K Dh encPt encT decT lam stE).eval ρ) =
      (none, dfStepDec (stE.eval ρ)) := by
  let _ := ‹SampleableType Pt›
  rfl

theorem fwdRejOutE_eval {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (ρ : Env Γ) :
    dfRecvOutDec ((fwdRejOutE C K Dh encPt encT decT lam stE).eval ρ) =
      (some .rejected, dfStepDec (stE.eval ρ)) := by
  let _ := ‹SampleableType Pt›
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem any_and_wire_eq_local {α β : Type} [DecidableEq β]
    (l : List (α × β)) (c₀ : β) (p : α → Bool) (f : β → α)
    (h : ∀ wc ∈ l, wc.1 = f wc.2) :
    ((l.any fun wc => decide (wc.2 = c₀)) && p (f c₀)) =
      (l.any fun wc => decide (wc.2 = c₀) && p wc.1) := by
  induction l with
  | nil => rfl
  | cons wc tl ih =>
    have hwc : (decide (wc.2 = c₀) && p wc.1) = (decide (wc.2 = c₀) && p (f c₀)) := by
      by_cases heq : wc.2 = c₀
      · rw [decide_eq_true heq, h wc (.head _), heq]
      · simp [heq]
    have htl := ih (fun x hx => h x (.tail _ hx))
    simp only [List.any_cons, hwc, ← htl]
    cases decide (wc.2 = c₀) <;> cases (tl.any fun x => decide (x.2 = c₀)) <;> cases p (f c₀) <;> rfl

theorem fwdInTE_eval (Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (s : SimState Bytes Pt ℓ) (Q : Party) (c' : Fig8C Pt)
    (hs : sE.eval ρ = simBaseEnc s) (hq : qBE.eval ρ = partyEnc Q)
    (hc' : c'E.eval ρ = fig8CtV c')
    (hHon : s.honest.length ≤ Lq) (hTr : s.mir.trans.length ≤ Lq)
    (hHonWire : ∀ wc ∈ s.honest, wc.1 = toWire wc.2) :
    (fwdInTE C K Dh encPt encT decT lam Lq sE qBE c'E).eval ρ =
      (s.honest.any fun wc =>
        decide (wc.2 = c') && (s.mir.inTransit Q.other wc.1).isSome) := by
  let _ := ‹SampleableType Pt›
  rw [← any_and_wire_eq_local s.honest c'
    (fun w => (s.mir.inTransit Q.other w).isSome) toWire hHonWire]
  dsimp only [fwdInTE, eLet, Expr.eval]
  rw [hs, hq, hc']
  let tupIn := Ty.prod (simBaseT ℓ Pt) (.prod .bool (fig8CtT (ℓ := ℓ) (Pt := Pt)))
  let ρi : Env (tupIn :: Γ) := .cons (simBaseEnc s, (partyEnc Q, fig8CtV c')) ρ
  have hany :
      (((ssHonest (O' := AOps) (.fst .v0)).eval ρi).take Lq).any
        (fun x => (eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) (.snd .v0) (.snd (.snd .v1))).eval (.cons x ρi)) =
      (s.honest.any fun wc => decide (wc.2 = c')) := by
    have hhon_val : (ssHonest (O' := AOps) (.fst .v0)).eval ρi = s.honest.map honestPairEnc := rfl
    rw [hhon_val, List.take_of_length_le (by simpa using hHon), List.any_map]
    congr 1; funext wc
    dsimp only [Function.comp_def]
    exact eqFig8CAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.snd .v0) (.snd (.snd .v1))
      (.cons (t := .prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt))) (honestPairEnc wc) ρi)
      wc.2 c' rfl rfl
  have htw := toWireAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.snd (.snd .v0)) ρi c' rfl
  have htr := mInTransitE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) Lq (ssMir (.fst .v0)) (.not (.fst (.snd .v0)))
    (toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.snd (.snd .v0)))
    ρi s.mir Q.other hTr rfl (not_partyEnc_eq_other Q)
  rw [htw] at htr
  dsimp only [ρi] at hany htr
  rw [hany, htr]
  cases s.mir.inTransit Q.other (toWire c') <;> rfl

theorem fwdScAcceptUpdateE_eval (T : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (base'E : Expr AOps Γ (simBaseT ℓ Pt))
    (qBE : Expr AOps Γ .bool) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (base' : SimState Bytes Pt ℓ) (Q : Party) (c : Fig8C Pt)
    (hsC : sCE.eval ρ = simFullEnc sC) (hb : base'E.eval ρ = simBaseEnc base')
    (hq : qBE.eval ρ = partyEnc Q) (hc : cE.eval ρ = fig8CtV c) :
    simFullDec ((fwdScAcceptUpdateE C K idA idB Dh encPt encT decT lam T
      sCE base'E qBE cE).eval ρ) =
      { sC with
        base := base'
        kept := Function.update sC.kept Q
          (Kept.recv (ℓ := ℓ)
            (fig := figS (ℓ := ℓ) (paramsV1 C K idA idB) Dh encPt encT lam T)
            (fs := fsS (ℓ := ℓ) (paramsV1 C K idA idB) encT T)
            c (sC.kept Q)) } := by
  suffices h : (fwdScAcceptUpdateE C K idA idB Dh encPt encT decT lam T
      sCE base'E qBE cE).eval ρ = simFullEnc
      { sC with
        base := base'
        kept := Function.update sC.kept Q
          (Kept.recv (ℓ := ℓ)
            (fig := figS (ℓ := ℓ) (paramsV1 C K idA idB) Dh encPt encT lam T)
            (fs := fsS (ℓ := ℓ) (paramsV1 C K idA idB) encT T)
            c (sC.kept Q)) } by
    let _ := ‹SampleableType Pt›
    rw [h, simFullDec_simFullEnc]
  dsimp only [fwdScAcceptUpdateE, eLet, Expr.eval]
  rw [hsC, hb, hq, hc]
  let tupSc := Ty.prod (simFullT ℓ Pt)
    (.prod (simBaseT ℓ Pt) (.prod .bool (fig8CtT (ℓ := ℓ) (Pt := Pt))))
  let ρ1 : Env (tupSc :: Γ) := .cons (simFullEnc sC,
    (simBaseEnc base', (partyEnc Q, fig8CtV c))) ρ
  have hk : (pGet (O' := AOps) (scKept (.fst .v0)) (.fst (.snd (.snd .v0)))).eval ρ1 =
      keptEnc (sC.kept Q) := by
    cases Q <;> rfl
  have hkr := keptRecvAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB T
    (pGet (scKept (.fst .v0)) (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0))) ρ1
    (sC.kept Q) c hk rfl
  change (scMk (.fst (.snd .v0))
    (pSet (scKept (.fst .v0)) (.fst (.snd (.snd .v0)))
      (keptRecvAtomicE idA idB T (pGet (scKept (.fst .v0)) (.fst (.snd (.snd .v0))))
        (.snd (.snd (.snd .v0)))))
    (scSent (.fst .v0)) (scSnaps (.fst .v0))).eval ρ1 = _
  dsimp only [scMk, pSet, Expr.eval]
  rw [hkr]
  dsimp only [scKept, scSent, scSnaps, Expr.eval]
  cases Q <;> simp [simFullEnc, partyEnc, Function.update, Expr.eval, Expr.v0, ρ1]

theorem fwdMkCE_eval {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (tE : Expr AOps Γ .nat) (T?E : Expr AOps Γ (.opt PtT))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (honestC : Option (Fig8C Pt)) (t : ℕ) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (hhc : honestCE.eval ρ = honestC.map fig8CtV) (ht : tE.eval ρ = t)
    (hT : T?E.eval ρ = T?) (hlct : lctE.eval ρ = lctV lct) :
    (fwdMkCE C K Dh encPt encT decT lam honestCE tE T?E lctE).eval ρ =
      fig8CtV (match honestC with
        | some c => if c.2.2.2 = lct.2.2 then c else ((t, T?), lct)
        | none => ((t, T?), lct)) := by
  let _ := ‹SampleableType Pt›
  unfold fwdMkCE
  rw [eval_eLet]
  have hp : (Expr.pair honestCE (.pair tE (.pair T?E lctE))).eval ρ =
      (honestC.map fig8CtV, (t, (T?, lctV lct))) := by
    simp [Expr.eval, hhc, ht, hT, hlct]
  rw [hp]
  cases honestC with
  | none => rfl
  | some c =>
    dsimp only [Option.map, Expr.eval]
    let tupMk := Ty.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))
      (.prod .nat (.prod (.opt PtT) (lctT (ℓ := ℓ) (Pt := Pt))))
    let ρm : Env (fig8CtT (ℓ := ℓ) (Pt := Pt) :: tupMk :: Γ) :=
      .cons (fig8CtV c) (.cons (some (fig8CtV c), (t, (T?, lctV lct))) ρ)
    have hfst : ((Expr.v0 (O := AOps)).eval
        (Env.cons (t := tupMk) (some (fig8CtV c), (t, (T?, lctV lct))) ρ)).1 = some (fig8CtV c) := rfl
    rw [hfst]
    dsimp only
    rw [lctSaltEqOfLctAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .v0 (.snd (.snd (.snd .v1))) ρm c lct rfl rfl]
    by_cases h : c.2.2.2 = lct.2.2 <;> simp [h, fig8CtV, Expr.eval, Expr.v0, Expr.v1]

theorem fwdEvictedE_eval {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool) (ρ : Env Γ)
    (honestC : Option (Fig8C Pt)) (s : SimState Bytes Pt ℓ) (Q : Party)
    (hhc : honestCE.eval ρ = honestC.map fig8CtV)
    (hs : sE.eval ρ = simBaseEnc s) (hq : qBE.eval ρ = partyEnc Q) :
    (fwdEvictedE C K Dh encPt encT decT lam honestCE sE qBE).eval ρ =
      ((honestC.map fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) := by
  let _ := ‹SampleableType Pt›
  dsimp only [fwdEvictedE, eLet, Expr.eval]
  rw [hhc, hs, hq]
  cases honestC with
  | none => rfl
  | some c =>
    cases Q with
    | A =>
      by_cases h : c.1.1 = s.mir.epoch .A + 1 <;>
        simp [pGet, mEpoch, ssMir, simBaseEnc, simMirEnc, partyEnc, fig8CtV,
          Expr.eval, Expr.v0, Expr.v1, h]
    | B =>
      by_cases h : c.1.1 = s.mir.epoch .B + 1 <;>
        simp [pGet, mEpoch, ssMir, simBaseEnc, simMirEnc, partyEnc, fig8CtV,
          Expr.eval, Expr.v0, Expr.v1, h]

theorem fwdSaltEqE_eval {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (honestC : Option (Fig8C Pt)) (lct : ℕ × LibsignalCiphertextWithSalt32)
    (hhc : honestCE.eval ρ = honestC.map fig8CtV) (hlct : lctE.eval ρ = lctV lct) :
    (fwdSaltEqE C K Dh encPt encT decT lam honestCE lctE).eval ρ =
      ((honestC.map fun c => decide (c.2.2.2 = lct.2.2)) == some true) := by
  let _ := ‹SampleableType Pt›
  unfold fwdSaltEqE
  rw [eval_eLet]
  have hp : (Expr.pair honestCE lctE).eval ρ = (honestC.map fig8CtV, lctV lct) := by
    simp [Expr.eval, hhc, hlct]
  rw [hp]
  cases honestC with
  | none => rfl
  | some c =>
    dsimp only [Option.map, Expr.eval]
    let tupS := Ty.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (lctT (ℓ := ℓ) (Pt := Pt))
    let ρs : Env (fig8CtT (ℓ := ℓ) (Pt := Pt) :: tupS :: Γ) :=
      .cons (fig8CtV c) (.cons (some (fig8CtV c), lctV lct) ρ)
    have hfst : ((Expr.v0 (O := AOps)).eval
        (Env.cons (t := tupS) (some (fig8CtV c), lctV lct) ρ)).1 = some (fig8CtV c) := rfl
    rw [hfst]
    dsimp only
    rw [lctSaltEqOfLctAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .v0 (.snd .v1) ρs c lct rfl rfl]
    by_cases h : c.2.2.2 = lct.2.2 <;> simp [h]

theorem fwdAmbCondE_eval {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool) (ρ : Env Γ)
    (s : SimState Bytes Pt ℓ) (Q : Party)
    (hs : sE.eval ρ = simBaseEnc s) (hq : qBE.eval ρ = partyEnc Q)
    (hCs : (s.chains Q).length ≤ 5) :
    (fwdAmbCondE C K Dh encPt encT decT lam sE qBE).eval ρ =
      (inReceiveOnlyEpoch s.mir Q ||
        (Q == Party.A && (s.chains Q).any (·.key.isNone))) := by
  let _ := ‹SampleableType Pt›
  dsimp only [fwdAmbCondE, eLet, Expr.eval]
  rw [hs, hq]
  let ρ1 : Env (Ty.prod (simBaseT ℓ Pt) .bool :: Γ) := .cons (simBaseEnc s, partyEnc Q) ρ
  change (orE (mInWinE (ssMir (.fst .v0)) (.snd .v0))
    (.and (.not (.snd .v0))
      (anyChainKeyNoneE (pGet (ssChains (.fst .v0)) (.snd .v0))))).eval ρ1 = _
  rw [orE_eval, mInWinE_eval _ _ ρ1 s.mir Q rfl rfl]
  have hcsQ : (pGet (O' := AOps) (ssChains (.fst .v0)) (.snd .v0)).eval ρ1 =
      (s.chains Q).map ghostChainEnc := by
    cases Q <;> rfl
  have hany := eval_anyChainKeyNoneE (pGet (O' := AOps) (ssChains (.fst .v0)) (.snd .v0)) ρ1
    (s.chains Q) hcsQ hCs
  dsimp only [Expr.eval]
  rw [hany]
  cases Q <;> rfl

theorem fwdScAmbE_eval {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) (ρ : Env Γ)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (Q : Party)
    (hsC : sCE.eval ρ = simFullEnc sC) (hq : qBE.eval ρ = partyEnc Q)
    (hCs : (sC.base.chains Q).length ≤ 5) :
    (fwdScAmbE C K Dh encPt encT decT lam sCE qBE).eval ρ =
      simFullEnc
        (let amb := inReceiveOnlyEpoch sC.base.mir Q ||
           (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
         { sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }) := by
  let _ := ‹SampleableType Pt›
  unfold fwdScAmbE
  rw [eval_eLet]
  have hp : (Expr.pair sCE qBE).eval ρ = (simFullEnc sC, partyEnc Q) := by
    simp [Expr.eval, hsC, hq]
  rw [hp]
  let ρ1 : Env (Ty.prod (simFullT ℓ Pt) .bool :: Γ) := .cons (simFullEnc sC, partyEnc Q) ρ
  have hamb := fwdAmbCondE_eval C K Dh encPt encT decT lam
    (scBase (.fst .v0)) (.snd .v0) ρ1 sC.base Q rfl rfl hCs
  change (Expr.ite (fwdAmbCondE C K Dh encPt encT decT lam (scBase (.fst .v0)) (.snd .v0))
    (scSetBase (.fst .v0) (ssSetAmb (scBase (.fst .v0)) (.add (ssAmb (scBase (.fst .v0))) (.nat 1))))
    (.fst .v0)).eval ρ1 = _
  dsimp only [Expr.eval]
  rw [hamb]
  cases inReceiveOnlyEpoch sC.base.mir Q ||
      (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) with
  | false => rfl
  | true =>
    have hb : (ssSetAmb (O' := AOps) (scBase (.fst .v0))
        (.add (ssAmb (scBase (.fst .v0))) (.nat 1))).eval ρ1 =
        simBaseEnc { sC.base with amb := sC.base.amb + 1 } :=
      eval_ssSetAmb (scBase (.fst .v0)) (.add (ssAmb (scBase (.fst .v0))) (.nat 1)) ρ1 sC.base rfl
    exact eval_scSetBase (.fst .v0) _ ρ1 sC _ rfl hb

theorem fwdNewGuardRejectE_eval {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (iE : Expr AOps Γ .nat) (ρ : Env Γ)
    (s : SimState Bytes Pt ℓ) (Q : Party) (i : ℕ)
    (hs : sE.eval ρ = simBaseEnc s) (hq : qBE.eval ρ = partyEnc Q) (hi : iE.eval ρ = i) :
    (fwdNewGuardRejectE C K Dh encPt encT decT lam sE qBE iE).eval ρ =
      (inReceiveOnlyEpoch s.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) := by
  let _ := ‹SampleableType Pt›
  unfold fwdNewGuardRejectE
  rw [eval_eLet]
  have hp : (Expr.pair sE (.pair qBE iE)).eval ρ = (simBaseEnc s, (partyEnc Q, i)) := by
    simp [Expr.eval, hs, hq, hi]
  rw [hp]
  let ρ1 : Env (Ty.prod (simBaseT ℓ Pt) (.prod .bool .nat) :: Γ) :=
    .cons (simBaseEnc s, (partyEnc Q, i)) ρ
  rw [orE_eval, orE_eval, mInWinE_eval _ _ ρ1 s.mir Q rfl rfl]
  simp only [Expr.eval, Expr.v0, Env.get]
  have hlt : (!decide (i < 4294967296)) = decide (2 ^ 32 ≤ i) := by
    rw [← decide_not]
    exact decide_eq_decide.mpr (by omega)
  have hlt2 : (!decide (i < 2 ^ 32)) = decide (2 ^ 32 ≤ i) := by
    rw [← decide_not]
    exact decide_eq_decide.mpr (by omega)
  first | rw [hlt] | rw [hlt2]

theorem fwdRefuseE_eval (Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool) (ρ : Env Γ)
    (s : SimState Bytes Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool)
    (hs : sE.eval ρ = simBaseEnc s) (hq : qBE.eval ρ = partyEnc Q)
    (hw : wE.eval ρ = w) (hd : isDelE.eval ρ = isDel)
    (hTr : s.mir.trans.length ≤ Lq) :
    (fwdRefuseE C K Dh encPt encT decT lam Lq sE qBE wE isDelE).eval ρ =
      (s.stopped || s.mir.win ||
        (isDel && (s.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT w)))) := by
  let _ := ‹SampleableType Pt›
  dsimp only [fwdRefuseE, eLet, Expr.eval]
  rw [hs, hq, hw, hd]
  let tupR := Ty.prod (simBaseT ℓ Pt) (.prod .bool (.prod (B 32) .bool))
  let ρ1 : Env (tupR :: Γ) := .cons (simBaseEnc s, (partyEnc Q, (w, isDel))) ρ
  have htr := mInTransitE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) Lq (ssMir (.fst .v0)) (.not (.fst (.snd .v0)))
    (.fst (.snd (.snd .v0))) ρ1 s.mir Q.other hTr rfl (not_partyEnc_eq_other Q)
  have hsi := mSafeInjE_eval (ssMir (O' := AOps) (.fst .v0)) ρ1 s.mir rfl
  have hinj := injOKAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (.fst (.snd (.snd .v0))) ρ1
  have hw1 : (Expr.fst (O := AOps) (.snd (.snd .v0))).eval ρ1 = w := rfl
  rw [hw1] at htr hinj
  change (orE _ _).eval ρ1 = _
  simp only [orE_eval, Expr.eval, htr, hsi, hinj]
  cases s.mir.inTransit Q.other w <;>
    simp [ssStopped, mWin, ssMir, simBaseEnc, simMirEnc, Expr.eval, Expr.v0, ρ1, Bool.or_assoc]

theorem party_senderOf_beq_other (t : ℕ) (Q : Party) :
    (Party.senderOf t == Q.other) = (decide (t % 2 = 0) == !(partyEnc Q)) := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;>
    cases Q <;> simp [Party.senderOf, Party.other, partyEnc, h]

theorem fwdHonestCE_eval (Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) (ρ : Env Γ)
    (s : SimState Bytes Pt ℓ) (Q : Party) (w : Bytes)
    (hs : sE.eval ρ = simBaseEnc s) (hq : qBE.eval ρ = partyEnc Q)
    (hw : wE.eval ρ = w) (hHon : s.honest.length ≤ Lq) :
    (fwdHonestCE C K Dh encPt encT decT lam Lq sE qBE wE).eval ρ =
      ((s.honest.find? fun wc =>
        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map fig8CtV := by
  let _ := ‹SampleableType Pt›
  unfold fwdHonestCE
  rw [eval_eLet]
  have hp : (Expr.pair sE (.pair qBE wE)).eval ρ = (simBaseEnc s, (partyEnc Q, w)) := by
    simp [Expr.eval, hs, hq, hw]
  rw [hp]
  let tupH := Ty.prod (simBaseT ℓ Pt) (.prod .bool (B 32))
  dsimp only [Expr.eval]
  have hhon_val : (ssHonest (O' := AOps) (.fst .v0)).eval
      (Env.cons (t := tupH) (simBaseEnc s, (partyEnc Q, w)) ρ) =
      s.honest.map honestPairEnc := rfl
  have htake : (s.honest.map (honestPairEnc (ℓ := ℓ) (Pt := Pt))).take Lq =
      s.honest.map honestPairEnc :=
    List.take_of_length_le (by simpa using hHon)
  have hfind :
      ((s.honest.map (honestPairEnc (ℓ := ℓ) (Pt := Pt))).find? fun x =>
        (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) (.bytesEq 32 32) (.pair (.fst .v0) (.snd (.snd .v1)))).eval
          (Env.cons x (Env.cons (t := tupH) (simBaseEnc s, (partyEnc Q, w)) ρ)) &&
        (boolEq (O' := AOps) (.eqN (.modK 2 (.fst (.fst (.snd .v0)))) (.nat 0))
          (.not (.fst (.snd .v1)))).eval
          (Env.cons x (Env.cons (t := tupH) (simBaseEnc s, (partyEnc Q, w)) ρ))) =
      (s.honest.find? fun wc =>
        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map honestPairEnc := by
    rw [List.find?_map]
    congr 1; congr 1; funext wc
    dsimp only [Function.comp_def]
    rw [party_senderOf_beq_other wc.2.1.1 Q]
    by_cases h0 : wc.2.1.1 % 2 = 0 <;>
      simp [Expr.eval, eval_sOpPure, ReductionDsl.AtomicPureOp.eval,
        boolEq_eval, honestPairEnc, fig8CtV, Expr.v0, Expr.v1, h0]
  rw [hhon_val, htake, hfind]
  rcases hf : (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with _ | wc <;>
    (rw [hf]; rfl)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem smRrDec_id_smRrEnc_id (rr : RecvResult (Plain ℓ)) :
    smRrDec (ℓ := ℓ) (Pt := Pt) id
      (smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id rr) = rr := by
  rcases rr with _ | ⟨t, i, _ | m⟩ <;> rfl

omit [SampleableType Pt] in
private theorem fwdOnAcceptFinishE_eval (qep Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt))
    (csE : Expr AOps Γ (.list (ghostChainT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool)
    (tE iE : Expr AOps Γ .nat) (mE : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (pq'E : Expr AOps Γ (B 32))
    (ρ : Env Γ) (s : SimState Bytes Pt ℓ) (cs : List GhostChain)
    (Q : Party) (w : Bytes) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (pq' : Bytes)
    (hs : sE.eval ρ = simBaseEnc s) (hcs : csE.eval ρ = cs.map ghostChainEnc)
    (hq : qBE.eval ρ = partyEnc Q) (hw : wE.eval ρ = w) (hisDel : isDelE.eval ρ = isDel)
    (ht : tE.eval ρ = t) (hi : iE.eval ρ = i) (hm : mE.eval ρ = m) (hpq : pq'E.eval ρ = pq')
    (htrans : s.mir.trans.length ≤ Lq) (hchall : s.mir.chall.length ≤ Lq)
    (hcomp : s.mir.comp.length ≤ Lq) :
    (fwdOnAcceptFinishE C K Dh encPt encT decT lam qep Lq
      sE csE qBE wE isDelE tE iE mE pq'E).eval ρ =
      (let s' : SimState Bytes Pt ℓ :=
         { s with
           chains := Function.update s.chains Q cs
           pq := Function.update s.pq Q pq'
           unackA := s.unackA && Q != Party.A }
       let out : Option (RecvResult (Plain ℓ)) × SimState Bytes Pt ℓ :=
         if isDel then
           match s.mir.inTransit Q.other w with
           | none => (none, s)
           | some r =>
             (some (.accepted t i (if s.mir.chall.contains r.pos then none else some m)),
               { s' with mir := s.mir.accept Q () r.pos })
         else if qep + 1 < t then (some .rejected, s)
         else
           let pos : Pos := ⟨Q.other, t, i⟩
           if s.mir.trivial 3 pos then
             (some (.accepted t i (some m)), { s' with mir := s.mir.accept Q () pos })
           else
             (some .rejected, { s with mir := { s.mir with win := true } })
       (out.1.map (smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id),
        simBaseEnc out.2)) := by
  unfold fwdOnAcceptFinishE
  rw [eval_eLet]
  have hp : (Expr.pair sE (.pair csE (.pair qBE (.pair wE (.pair isDelE
      (.pair tE (.pair iE (.pair mE pq'E)))))))).eval ρ =
      (simBaseEnc s, (cs.map ghostChainEnc,
        (partyEnc Q, (w, (isDel, (t, (i, (m, pq')))))))) := by
    simp [Expr.eval, hs, hcs, hq, hw, hisDel, ht, hi, hm, hpq]
  rw [hp]
  let tupF := Ty.prod (simBaseT ℓ Pt) (.prod (.list (ghostChainT ℓ Pt))
    (.prod .bool (.prod (B 32) (.prod .bool (.prod .nat (.prod .nat
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (B 32))))))))
  let ρ1 : Env (tupF :: Γ) := .cons (simBaseEnc s, (cs.map ghostChainEnc,
    (partyEnc Q, (w, (isDel, (t, (i, (m, pq')))))))) ρ
  rw [ite_eval]
  have his : (Expr.fst (O := AOps) (.snd (.snd (.snd (.snd .v0))))).eval ρ1 = isDel := rfl
  rw [his]
  cases isDel with
  | true =>
    simp only [ite_true]
    dsimp only [Expr.eval]
    have htr := mInTransitE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) Lq (ssMir (.fst .v0)) (.not (.fst (.snd (.snd .v0))))
      (.fst (.snd (.snd (.snd .v0)))) ρ1 s.mir Q.other htrans rfl (not_partyEnc_eq_other Q)
    have hw0 : (Expr.fst (O := AOps) (.snd (.snd (.snd .v0)))).eval ρ1 = w := rfl
    rw [htr, hw0]
    cases s.mir.inTransit Q.other w with
    | none => rfl
    | some r =>
      dsimp only [Option.map, Expr.eval]
      let ρ2 : Env (simRecT ℓ Pt :: tupF :: Γ) := .cons (simRecEnc r) ρ1
      have hch := mChallContainsE_eval Lq (ssMir (O' := AOps) (.fst .v1))
        (srecPos (O' := AOps) .v0) ρ2 s.mir r.pos hchall rfl rfl
      have hacc := mAcceptE_eval Lq (ssMir (O' := AOps) (.fst .v1))
        (.fst (.snd (.snd .v1))) (srecPos (O' := AOps) .v0) ρ2
        s.mir Q r.pos htrans hchall hcomp rfl rfl rfl
      dsimp only [fwdAccRrE, ssMk, Expr.eval]
      rw [hch, hacc]
      cases s.mir.chall.contains r.pos <;>
        cases Q <;>
        simp [pSet, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped,
          simBaseEnc, partyEnc, Function.update, smRrEnc, Expr.eval, Expr.v0, Expr.v1]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [ite_eval]
    have hltE : (Expr.lt (O := AOps) (.nat (qep + 1))
        (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))).eval ρ1 = decide (qep + 1 < t) := rfl
    rw [hltE]
    by_cases hlt : qep + 1 < t
    · simp [hlt, smRrEnc, Expr.eval, Expr.v0]
    · simp only [hlt, decide_false, Bool.false_eq_true, ite_false]
      rw [ite_eval]
      have hpos : (Expr.pair (O := AOps) (.not (.fst (.snd (.snd .v0))))
          (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
            (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))).eval ρ1 =
          posEnc ⟨Q.other, t, i⟩ := by
        cases Q <;> rfl
      have htriv := mTrivialE_eval Lq (ssMir (.fst .v0)) _ ρ1 s.mir ⟨Q.other, t, i⟩
        htrans hcomp rfl hpos
      rw [htriv]
      by_cases ht3 : s.mir.trivial 3 ⟨Q.other, t, i⟩
      · simp only [ht3, ite_true]
        have hacc := mAcceptE_eval Lq (ssMir (.fst .v0)) (.fst (.snd (.snd .v0))) _ ρ1
          s.mir Q ⟨Q.other, t, i⟩ htrans hchall hcomp rfl rfl hpos
        dsimp only [fwdAccRrE, ssMk, Expr.eval]
        rw [hacc]
        cases Q <;>
          simp [pSet, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped,
            simBaseEnc, partyEnc, Function.update, smRrEnc, Expr.eval, Expr.v0]
      · simp only [ht3, Bool.false_eq_true, ite_false]
        dsimp only [Expr.eval]
        rw [eval_ssSetMirWin (O' := AOps) (.fst .v0) ρ1 s rfl]
        rfl

private theorem fwdOnAcceptC_eval_enc (qep Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt))
    (ci?E : Expr AOps Γ (.opt .nat)) (pkE : Expr AOps Γ PK)
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool)
    (tE iE : Expr AOps Γ .nat) (mE : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (pq'E : Expr AOps Γ (B 32))
    (ρ : Env Γ) (s : SimState Bytes Pt ℓ) (ci? : Option ℕ) (pk : PublicKey)
    (Q : Party) (w : Bytes) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (pq' : Bytes)
    (hs : sE.eval ρ = simBaseEnc s) (hci : ci?E.eval ρ = ci?) (hpk : pkE.eval ρ = pk)
    (hq : qBE.eval ρ = partyEnc Q) (hw : wE.eval ρ = w) (hd : isDelE.eval ρ = isDel)
    (ht : tE.eval ρ = t) (hi : iE.eval ρ = i) (hm : mE.eval ρ = m) (hpq : pq'E.eval ρ = pq')
    (hbnd : CryptoGames.Ratchet.LibsignalSim.SimStateBounded Lq s)
    (hCs : (s.chains Q).length ≤ 5) (hSk : ∀ g ∈ s.chains Q, g.skipped.length ≤ 2000) :
    (fwdOnAcceptC C K Dh encPt encT decT lam qep Lq
      sE ci?E pkE qBE wE isDelE tE iE mE pq'E).eval ρ =
      pure (let (rr, base') := onAcceptPure qep Q w isDel t i m ci? pk pq' s
            (rr.map (smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id),
             simBaseEnc base')) := by
  dsimp only [fwdOnAcceptC, Comp.eval, Expr.eval]
  rw [hs, hci, hpk, hq, hw, hd, ht, hi, hm, hpq, pure_bind]
  let tupA := Ty.prod (simBaseT ℓ Pt) (.prod (.opt .nat) (.prod PK
    (.prod .bool (.prod (B 32) (.prod .bool (.prod .nat (.prod .nat
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (B 32)))))))))
  have hcsQ : ∀ {Δ} (x : Expr AOps Δ (simBaseT ℓ Pt))
      (qx : Expr AOps Δ .bool) (ρx : Env Δ),
      x.eval ρx = simBaseEnc s → qx.eval ρx = partyEnc Q →
      (pGet (ssChains x) qx).eval ρx = (s.chains Q).map ghostChainEnc := by
    intro Δ x qx ρx hx hqx
    cases Q <;> simp [pGet, ssChains, hx, hqx, simBaseEnc, partyEnc, Expr.eval, Expr.v0]
  cases ci? with
  | none =>
    let ρ1n : Env (tupA :: Γ) := .cons (simBaseEnc s, (none, (pk,
      (partyEnc Q, (w, (isDel, (t, (i, (m, pq'))))))))) ρ
    have hci0 : ((Expr.v0 (O := AOps)).eval ρ1n).2.1 = none := rfl
    rw [hci0]
    dsimp only
    have hga := ghostAcceptC_eval (ℓ := ℓ) (Pt := Pt) (O' := AOps) (fig8SmIfaceDF ℓ Pt)
      (.pair (.some (.fst (.snd (.snd .v0))))
        (.pair (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))) (.pair (.nat 0) .nil)))
      (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))) ρ1n
      ⟨some pk, t, 0, []⟩
      (by simp [ghostChainEnc, Expr.eval, Expr.v0, ρ1n]) (by simp)
    have hi0 : (Expr.fst (O := AOps)
        (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))).eval ρ1n = i := rfl
    rw [hi0] at hga
    rw [hga, pure_bind, pure_bind]
    have hpush := eval_pushChainE (ℓ := ℓ) (Pt := Pt)
      (pGet (ssChains (.fst .v1)) (.fst (.snd (.snd (.snd .v1))))) .v0
      (.cons (ghostChainEnc (GhostChain.accept ⟨some pk, t, 0, []⟩ i)) ρ1n)
      (s.chains Q) (GhostChain.accept ⟨some pk, t, 0, []⟩ i)
      (hcsQ (.fst .v1) (.fst (.snd (.snd (.snd .v1)))) _ rfl rfl) hCs rfl
    rw [hpush, fwdOnAcceptFinishE_eval C K Dh encPt encT decT lam qep Lq
      (.fst .v1) .v0 (.fst (.snd (.snd (.snd .v1))))
      (.fst (.snd (.snd (.snd (.snd .v1)))))
      (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))
      (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
      (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
      (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))))
      (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))))
      _ s (pushChain (s.chains Q) (GhostChain.accept ⟨some pk, t, 0, []⟩ i))
      Q w isDel t i m pq' rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hbnd.trans_le hbnd.chall_le hbnd.comp_le]
    rfl
  | some ci =>
    let ρ1s : Env (tupA :: Γ) := .cons (simBaseEnc s, (some ci, (pk,
      (partyEnc Q, (w, (isDel, (t, (i, (m, pq'))))))))) ρ
    have hci1 : ((Expr.v0 (O := AOps)).eval ρ1s).2.1 = some ci := rfl
    rw [hci1]
    dsimp only
    have hmod := modifyChainAcceptC_eval (ℓ := ℓ) (Pt := Pt) (fig8SmIfaceDF ℓ Pt)
      (pGet (ssChains (.fst .v1)) (.fst (.snd (.snd (.snd .v1))))) .v0
      (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
      (.cons ci ρ1s) (s.chains Q)
      (hcsQ (.fst .v1) (.fst (.snd (.snd (.snd .v1)))) _ rfl rfl) hCs hSk
    rw [hmod, pure_bind]
    dsimp only [Expr.eval]
    rw [fwdOnAcceptFinishE_eval C K Dh encPt encT decT lam qep Lq
      (.fst .v1) .v0 (.fst (.snd (.snd (.snd .v1))))
      (.fst (.snd (.snd (.snd (.snd .v1)))))
      (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))
      (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
      (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
      (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))))
      (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))))
      _ s ((s.chains Q).modify ci (·.accept i))
      Q w isDel t i m pq' rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hbnd.trans_le hbnd.chall_le hbnd.comp_le]
    rfl

theorem fwdOnAcceptC_eval (qep Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt))
    (ci?E : Expr AOps Γ (.opt .nat)) (pkE : Expr AOps Γ PK)
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool)
    (tE iE : Expr AOps Γ .nat) (mE : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (pq'E : Expr AOps Γ (B 32))
    (ρ : Env Γ) (s : SimState Bytes Pt ℓ) (ci? : Option ℕ) (pk : PublicKey)
    (Q : Party) (w : Bytes) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (pq' : Bytes)
    (hs : sE.eval ρ = simBaseEnc s) (hci : ci?E.eval ρ = ci?) (hpk : pkE.eval ρ = pk)
    (hq : qBE.eval ρ = partyEnc Q) (hw : wE.eval ρ = w) (hd : isDelE.eval ρ = isDel)
    (ht : tE.eval ρ = t) (hi : iE.eval ρ = i) (hm : mE.eval ρ = m) (hpq : pq'E.eval ρ = pq')
    (hbnd : CryptoGames.Ratchet.LibsignalSim.SimStateBounded Lq s)
    (hCs : (s.chains Q).length ≤ 5) (hSk : ∀ g ∈ s.chains Q, g.skipped.length ≤ 2000) :
    (Prod.map (Option.map (smRrDec id)) simBaseDec <$>
      (fwdOnAcceptC C K Dh encPt encT decT lam qep Lq
        sE ci?E pkE qBE wE isDelE tE iE mE pq'E).eval ρ) =
    pure (onAcceptPure qep Q w isDel t i m ci? pk pq' s) := by
  rw [fwdOnAcceptC_eval_enc C K Dh encPt encT decT lam qep Lq
    sE ci?E pkE qBE wE isDelE tE iE mE pq'E ρ s ci? pk Q w isDel t i m pq'
    hs hci hpk hq hw hd ht hi hm hpq hbnd hCs hSk]
  rcases onAcceptPure qep Q w isDel t i m ci? pk pq' s with ⟨rr, base'⟩
  rcases rr with _ | rr
  · simp [Prod.map, simBaseDec_simBaseEnc]
  · simp only [map_pure, Prod.map, Option.map]
    rw [smRrDec_id_smRrEnc_id, simBaseDec_simBaseEnc]

theorem fwdProbeC_eval (Lq : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool)
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (exE : Expr AOps Γ (.list (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (ρ : Env Γ) (Q : Party) (c' : Fig8C Pt) (ex : List (Fig8C Pt))
    (hq : qBE.eval ρ = partyEnc Q) (hc' : c'E.eval ρ = fig8CtV c')
    (hex : exE.eval ρ = ex.map fig8CtV) (hlen : ex.length ≤ Lq) :
    (List.map fig8CtOfV <$>
      (fwdProbeC C K Dh encPt encT decT lam Lq qBE c'E exE).eval ρ) =
    (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)).onProbe Q c' ex := by
  let _ := ‹SampleableType Pt›
  have hpQ : boolToParty (partyEnc Q) = Q := by cases Q <;> rfl
  unfold fwdProbeC
  dsimp only [Comp.eval, Expr.eval, deliverForgeSemHook]
  rw [hq, hc', hex, pure_bind]
  let t0 := Ty.prod .bool (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (.list (fig8CtT (ℓ := ℓ) (Pt := Pt))))
  let ρ1 : Env (t0 :: Γ) :=
    .cons (partyEnc Q, (fig8CtV (ℓ := ℓ) (Pt := Pt) c', ex.map (fig8CtV (ℓ := ℓ) (Pt := Pt)))) ρ
  have htake : (ex.map (fig8CtV (ℓ := ℓ) (Pt := Pt))).take Lq = ex.map fig8CtV :=
    List.take_of_length_le (by simpa using hlen)
  have hfind :
      ((ex.map (fig8CtV (ℓ := ℓ) (Pt := Pt))).find? fun cv =>
        (sameWireFig8AtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .v0 (.fst (.snd .v1))).eval (.cons cv ρ1)) =
      (ex.find? fun c => sameWireFig8 c c').map fig8CtV := by
    rw [List.find?_map]
    congr 1; congr 1; funext x
    dsimp only [Function.comp_def]
    rw [sameWireFig8AtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .v0 (.fst (.snd .v1))
      (.cons (fig8CtV (ℓ := ℓ) (Pt := Pt) x) ρ1) x c' rfl rfl]
    apply Bool.eq_iff_iff.mpr
    simp [sameWireFig8]
  have hex0 : ((Expr.v0 (O := AOps)).eval ρ1).2.2 =
      ex.map (fig8CtV (ℓ := ℓ) (Pt := Pt)) := rfl
  rw [hex0, htake, hfind]
  rcases ex.find? fun c => sameWireFig8 c c' with _ | c
  · simp [List.map_map, Function.comp_def, fig8CtOfV_fig8CtV]
  · dsimp only [Option.map]
    simp only [Function.comp_def,
      Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get,
      map_eq_bind_pure_comp, bind_assoc, pure_bind]
    simp [deliverForgeQuery, List.map_map, Function.comp_def, fig8CtOfV_fig8CtV]
    rw [hpQ, fig8CtOfV_fig8CtV, fig8CtOfV_fig8CtV]

theorem fwdEvalCKSC_eval (Lq T Kc B_cap : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (cE c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ)
    (Q : Party) (w : Bytes) (c c' : Fig8C Pt)
    (hsC : sCE.eval ρ = simFullEnc sC) (hq : qBE.eval ρ = partyEnc Q)
    (hw : wE.eval ρ = w) (hc : cE.eval ρ = fig8CtV c) (hc' : c'E.eval ρ = fig8CtV c')
    (hbnd : SimCStateBounded Lq sC) (hextra : SanSnapExtra C K sC) :
    (fwdEvalCKSC C K idA idB Dh encPt encT decT lam Lq T Kc B_cap
      sCE qBE wE cE c'E).eval ρ =
    pure ((evalCKS (paramsV1 C K idA idB) Dh encPt encT lam T Kc B_cap
      sC Q w c c').map (Option.map kDecOutV)) := by
  let _ := hℓ
  dsimp only [fwdEvalCKSC, Comp.eval, Expr.eval]
  rw [hsC, hq, hw, hc, hc', pure_bind]
  let tupCK := Ty.prod (simFullT ℓ Pt)
    (.prod .bool (.prod (B 32) (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
  let ρ1 : Env (tupCK :: Γ) := .cons (simFullEnc sC,
    (partyEnc Q, (w, (fig8CtV c, fig8CtV c')))) ρ
  have hk : (pGet (O' := AOps) (scKept (.fst .v0)) (.fst (.snd .v0))).eval ρ1 =
      keptEnc (sC.kept Q) := by
    cases Q <;> rfl
  have hke := keptEvalAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB T B_cap
    (pGet (scKept (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))) ρ1
    (sC.kept Q) c' hk rfl
  have hse := sentEvalAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB Lq T B_cap
    (scSent (.fst .v0)) (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0)))) ρ1
    sC.sent c c' rfl rfl rfl hbnd.sent_le
  have hpred : (fwdOrElseOptE C K Dh encPt encT decT lam
      (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB T B_cap
        (pGet (scKept (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))
      (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB Lq B_cap
        (scSent (.fst .v0)) (.fst (.snd (.snd (.snd .v0))))
        (.snd (.snd (.snd (.snd .v0)))))).eval ρ1 =
      (predictReceive
        (fig := fig8Clamp B_cap (figS (ℓ := ℓ) (paramsV1 C K idA idB) Dh encPt encT lam T))
        (fs := fsClampSim B_cap (fsS (ℓ := ℓ) (paramsV1 C K idA idB) encT T))
        sC Q c c').map (Option.map (kDecOutV (ℓ := ℓ) (Pt := Pt))) := by
    rw [fwdOrElseOptE_eval, hke, hse]
    unfold predictReceive
    cases Kept.eval (ℓ := ℓ)
      (fig := fig8Clamp B_cap (figS (ℓ := ℓ) (paramsV1 C K idA idB) Dh encPt encT lam T))
      (fs := fsClampSim B_cap (fsS (ℓ := ℓ) (paramsV1 C K idA idB) encT T))
      c' (sC.kept Q) <;> rfl
  rw [hpred]
  unfold evalCKS
  cases predictReceive
    (fig := fig8Clamp B_cap (figS (ℓ := ℓ) (paramsV1 C K idA idB) Dh encPt encT lam T))
    (fs := fsClampSim B_cap (fsS (ℓ := ℓ) (paramsV1 C K idA idB) encT T))
    sC Q c c' with
  | some r => rfl
  | none =>
    dsimp only [Option.orElse]
    exact knownSeedDecryptAtomicFastC_eval_snapEnc (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB Lq Kc B_cap (fig8SmIfaceDF ℓ Pt)
      (scSnaps (.fst .v0)) (.fst (.snd .v0)) (.fst (.fst (.fst (.snd (.snd (.snd .v0))))))
      (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))) ρ1
      sC.snaps Q c.1.1 w c' rfl hbnd.snaps_le rfl rfl rfl rfl (by unfold SanSnapExtra at hextra; tauto)

theorem fwdResyncC_eval (qep Lq T : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (ci?E : Expr AOps Γ (.opt .nat)) (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (rE : Expr AOps Γ (.opt (kDecOutT ℓ Pt)))
    (ρ : Env Γ) (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (ci? : Option ℕ) (pk : PublicKey) (pq' : Bytes)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hst : stE.eval ρ = dfStepEnc (sC, ex)) (hq : qBE.eval ρ = partyEnc Q)
    (hw : wE.eval ρ = w) (hci : ci?E.eval ρ = ci?) (hpk : pkE.eval ρ = pk)
    (hpq : pq'E.eval ρ = pq') (hc : cE.eval ρ = fig8CtV c)
    (hr : rE.eval ρ = r.map kDecOutV)
    (hbnd : SimCStateBounded Lq sC) (hextra : SanSnapExtra C K sC) :
    (dfRecvOutDec <$>
      (fwdResyncC C K idA idB Dh encPt encT decT lam qep Lq T
        stE qBE wE ci?E pkE pq'E cE rE).eval ρ) =
    semResyncHookS (paramsV1 C K idA idB) Dh encPt encT lam T
      (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ))
      qep sC ex Q w ci? pk pq' c r := by
  let _ := hℓ
  have hCh : ∀ R, (sC.base.chains R).length ≤ 5 ∧ ∀ g ∈ sC.base.chains R, g.skipped.length ≤ 2000 :=
    hextra.2.1
  have hpQ : boolToParty (partyEnc Q) = Q := by cases Q <;> rfl
  let tupT := Ty.prod (dfStepT ℓ Pt) (.prod .bool (.prod (B 32)
    (.prod (.opt .nat) (.prod PK (.prod (B 32)
      (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (.opt (kDecOutT ℓ Pt))))))))
  rcases r with _ | ⟨t, i, pub, m'⟩
  · simp only [Option.map] at hr
    unfold fwdResyncC
    dsimp only [Comp.eval, Expr.eval, semResyncHookS]
    rw [hst, hq, hw, hci, hpk, hpq, hc, hr, pure_bind]
    let ρ0 : Env (tupT :: Γ) :=
      .cons (dfStepEnc (sC, ex), (partyEnc Q, (w, (ci?, (pk, (pq', (fig8CtV c, none))))))) ρ
    have hnone : ((Expr.v0 (O := AOps)).eval ρ0).2.2.2.2.2.2.2 = none := rfl
    rw [hnone]
    dsimp only
    rw [map_pure, fwdRejOutE_eval]
    simp [dfStepEnc, simFullDec_simFullEnc, List.map_map, Function.comp_def,
      fig8CtOfV_fig8CtV, Expr.eval, Expr.v0]
  · simp only [Option.map] at hr
    unfold fwdResyncC
    dsimp only [Comp.eval, Expr.eval, semResyncHookS, deliverForgeSemHook]
    rw [hst, hq, hw, hci, hpk, hpq, hc, hr, pure_bind]
    let ρ1 : Env (tupT :: Γ) :=
      .cons (dfStepEnc (sC, ex),
        (partyEnc Q, (w, (ci?, (pk, (pq', (fig8CtV c, some (kDecOutV (t, i, pub, m'))))))))) ρ
    have hsome : ((Expr.v0 (O := AOps)).eval ρ1).2.2.2.2.2.2.2 =
        some (kDecOutV (t, i, pub, m')) := rfl
    rw [hsome]
    dsimp only
    let ρ2 : Env (kDecOutT ℓ Pt :: tupT :: Γ) := .cons (kDecOutV (t, i, pub, m')) ρ1
    have hp1 : ((Expr.v1 (O := AOps)).eval ρ2).2.1 = partyEnc Q := rfl
    have hc1 : ((Expr.v1 (O := AOps)).eval ρ2).2.2.2.2.2.2.1 = fig8CtV c := rfl
    rw [hp1, hc1, hpQ, fig8CtOfV_fig8CtV]
    simp only [deliverQueryDF, bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
    congr 1; funext res
    let rrDlT := smRrT (ℓ := ℓ) (Pt := Pt)
      (.prod (ReductionDsl.lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt)))
    let accT : Ty ASig := .prod .nat (.prod .nat (.opt (.prod (ReductionDsl.lpubT (ℓ := ℓ) (Pt := Pt))
      (PlainT (ℓ := ℓ) (Pt := Pt)))))
    let outAccT : Ty ASig := .prod
      (.opt (smRrT (ℓ := ℓ) (Pt := Pt) (PlainT (ℓ := ℓ) (Pt := Pt)))) (simBaseT ℓ Pt)
    rcases res with _ | (_ | ⟨tr, ir, _ | ⟨pr, mr⟩⟩)
    · dsimp only [Option.map]
      let ρ3 : Env (.opt rrDlT :: kDecOutT ℓ Pt :: tupT :: Γ) := .cons none ρ2
      have hm0 : (Expr.v0 (O := AOps)).eval ρ3 = none := rfl
      rw [hm0]
      dsimp only
      rw [pure_bind, fwdRejOutE_eval]
      simp [dfStepEnc, simFullDec_simFullEnc, List.map_map, Function.comp_def,
        fig8CtOfV_fig8CtV, Expr.eval, Expr.v2]
    · dsimp only [Option.map, smRrEnc]
      let ρ3 : Env (.opt rrDlT :: kDecOutT ℓ Pt :: tupT :: Γ) := .cons (some (.inl ())) ρ2
      have hm1 : (Expr.v0 (O := AOps)).eval ρ3 = some (.inl ()) := rfl
      rw [hm1]
      dsimp only
      let ρ4 : Env (rrDlT :: .opt rrDlT :: kDecOutT ℓ Pt :: tupT :: Γ) := .cons (.inl ()) ρ3
      have hm2 : (Expr.v0 (O := AOps)).eval ρ4 = .inl () := rfl
      rw [hm2]
      dsimp only
      rw [pure_bind, fwdRejOutE_eval]
      simp [dfStepEnc, simFullDec_simFullEnc, List.map_map, Function.comp_def,
        fig8CtOfV_fig8CtV, Expr.eval, Expr.v4]
    · dsimp only [Option.map, smRrEnc]
      let vAcc : accT.denote := (tr, (ir, none))
      let ρ3 : Env (.opt rrDlT :: kDecOutT ℓ Pt :: tupT :: Γ) := .cons (some (.inr vAcc)) ρ2
      have hm1 : (Expr.v0 (O := AOps)).eval ρ3 = some (.inr vAcc) := rfl
      rw [hm1]
      dsimp only
      let ρ4 : Env (rrDlT :: .opt rrDlT :: kDecOutT ℓ Pt :: tupT :: Γ) := .cons (.inr vAcc) ρ3
      have hm2 : (Expr.v0 (O := AOps)).eval ρ4 = .inr vAcc := rfl
      rw [hm2]
      dsimp only
      let ρ5 : Env (accT :: rrDlT :: .opt rrDlT :: kDecOutT ℓ Pt :: tupT :: Γ) := .cons vAcc ρ4
      have hacc := fwdOnAcceptC_eval_enc C K Dh encPt encT decT lam qep Lq
        (scBase (.fst (.fst .v4)))
        (.fst (.snd (.snd (.snd .v4))))
        (.fst (.snd (.snd (.snd (.snd .v4)))))
        (.fst (.snd .v4))
        (.fst (.snd (.snd .v4)))
        (.bool true)
        (.fst .v3) (.fst (.snd .v3)) (.snd (.snd (.snd .v3)))
        (.fst (.snd (.snd (.snd (.snd (.snd .v4))))))
        ρ5 sC.base ci? pk Q w true t i m' pq'
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        hbnd.base (hCh Q).1 (hCh Q).2
      rw [hacc, pure_bind, pure_bind]
      rcases hon : onAcceptPure qep Q w true t i m' ci? pk pq' sC.base with ⟨rr, base'⟩
      dsimp only [Expr.eval]
      let ρ6 : Env (outAccT :: accT :: rrDlT :: .opt rrDlT :: kDecOutT ℓ Pt :: tupT :: Γ) :=
        .cons (rr.map (smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id),
          simBaseEnc base') ρ5
      have hr6 : ((Expr.v0 (O := AOps)).eval ρ6).1 =
          rr.map (smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id) := rfl
      have hex6 : ((Expr.v5 (O := AOps)).eval ρ6).1.2 =
          ex.map (fig8CtV (ℓ := ℓ) (Pt := Pt)) := rfl
      have hupd := fwdScAcceptUpdateE_eval C K idA idB Dh encPt encT decT lam T
        (.fst (.fst .v5)) (.snd .v0) (.fst (.snd .v5))
        (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v5)))))))
        ρ6 sC base' Q c rfl rfl rfl rfl
      dsimp only [dfRecvOutDec, dfStepDec]
      rw [hr6, hupd, hex6]
      rcases rr with _ | rr
      · simp [List.map_map, Function.comp_def, fig8CtOfV_fig8CtV]
      · dsimp only [Option.map]
        rw [smRrDec_id_smRrEnc_id]
        simp [List.map_map, Function.comp_def, fig8CtOfV_fig8CtV]
    · dsimp only [Option.map, smRrEnc]
      let vAcc : accT.denote := (tr, (ir, some (lpubV pr, mr)))
      let ρ3 : Env (.opt rrDlT :: kDecOutT ℓ Pt :: tupT :: Γ) := .cons (some (.inr vAcc)) ρ2
      have hm1 : (Expr.v0 (O := AOps)).eval ρ3 = some (.inr vAcc) := rfl
      rw [hm1]
      dsimp only
      let ρ4 : Env (rrDlT :: .opt rrDlT :: kDecOutT ℓ Pt :: tupT :: Γ) := .cons (.inr vAcc) ρ3
      have hm2 : (Expr.v0 (O := AOps)).eval ρ4 = .inr vAcc := rfl
      rw [hm2]
      dsimp only
      let ρ5 : Env (accT :: rrDlT :: .opt rrDlT :: kDecOutT ℓ Pt :: tupT :: Γ) := .cons vAcc ρ4
      have hacc := fwdOnAcceptC_eval_enc C K Dh encPt encT decT lam qep Lq
        (scBase (.fst (.fst .v4)))
        (.fst (.snd (.snd (.snd .v4))))
        (.fst (.snd (.snd (.snd (.snd .v4)))))
        (.fst (.snd .v4))
        (.fst (.snd (.snd .v4)))
        (.bool true)
        (.fst .v3) (.fst (.snd .v3)) (.snd (.snd (.snd .v3)))
        (.fst (.snd (.snd (.snd (.snd (.snd .v4))))))
        ρ5 sC.base ci? pk Q w true t i m' pq'
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        hbnd.base (hCh Q).1 (hCh Q).2
      rw [hacc, pure_bind, pure_bind]
      rcases hon : onAcceptPure qep Q w true t i m' ci? pk pq' sC.base with ⟨rr, base'⟩
      dsimp only [Expr.eval]
      let ρ6 : Env (outAccT :: accT :: rrDlT :: .opt rrDlT :: kDecOutT ℓ Pt :: tupT :: Γ) :=
        .cons (rr.map (smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id),
          simBaseEnc base') ρ5
      have hr6 : ((Expr.v0 (O := AOps)).eval ρ6).1 =
          rr.map (smRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := PlainT (ℓ := ℓ) (Pt := Pt)) id) := rfl
      have hex6 : ((Expr.v5 (O := AOps)).eval ρ6).1.2 =
          ex.map (fig8CtV (ℓ := ℓ) (Pt := Pt)) := rfl
      have hupd := fwdScAcceptUpdateE_eval C K idA idB Dh encPt encT decT lam T
        (.fst (.fst .v5)) (.snd .v0) (.fst (.snd .v5))
        (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v5)))))))
        ρ6 sC base' Q c rfl rfl rfl rfl
      dsimp only [dfRecvOutDec, dfStepDec]
      rw [hr6, hupd, hex6]
      rcases rr with _ | rr
      · simp [List.map_map, Function.comp_def, fig8CtOfV_fig8CtV]
      · dsimp only [Option.map]
        rw [smRrDec_id_smRrEnc_id]
        simp [List.map_map, Function.comp_def, fig8CtOfV_fig8CtV]

end SkipAndGuardEval

end

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdSkip
