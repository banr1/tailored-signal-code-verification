/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.CostedTables
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimShallow
public import Computational.Proofs.ReductionDsl.Soundness
public import Computational.Proofs.SpecLemmas.Session.ACD19.SM.CostedTables
public import Computational.Proofs.GameHop.CompDedup
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.SM.GameCosted
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.ReductionDsl.Tables
import Computational.Proofs.ReductionDsl.Notation

/-!
# Costed `LibsignalSim` Reduction

Defines the costed `ReductionDsl.CostedReduction` programs `simRunProg` and `simProg` for
`LibsignalSim.simRun` and `Refine.sim` over `simSig`, `simCodec`, `simOps`, and `simIface`.
Establishes size honesty, evaluation agreement under `SimStateBounded K` for adversaries making at
most `q ≤ K` queries, target query bounds, and static cost bounds.
-/

@[expose] public section

namespace CryptoGames.Ratchet.LibsignalSim

set_option exponentiation.threshold 1024

open ReductionDsl OracleSpec OracleComp
open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA LibsignalSession LibsignalInst
open Computational.Proofs.GameHop.CompDedup
  (CountLe countLe_nil countLe_cons_cons countLe_cons_right countLe_filter_left
   countLe_length_le countLe_dedupPrepend foldr_dedup_map_eq afterCorrDedup canonComp
   canonComp_idem canonComp_trivial canonComp_corrAllowed canonComp_epMgmt canonComp_record
   canonComp_accept canonComp_afterCorr canonComp_afterCorrDedup run'_simulateQ_eq_of_idem_proj)
open scoped Computational.Proofs.ReductionDsl.Notation

local macro_rules
  | `(rdsl_pat| .transmit $p:term)  => `(rdsl_pat| .inl (.inl (.inl (.inl $p))))
  | `(rdsl_pat| .challenge $p:term) => `(rdsl_pat| .inl (.inl (.inl (.inr $p))))
  | `(rdsl_pat| .deliver $p:term)   => `(rdsl_pat| .inl (.inl (.inr $p)))
  | `(rdsl_pat| .inject $p:term)    => `(rdsl_pat| .inl (.inr $p))
  | `(rdsl_pat| .corrupt $p:term)   => `(rdsl_pat| .inr $p)

/-! ## Size honesty -/

section SizeHonesty

theorem simParamOps_sizeHonest {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) (toKemCoins : PQC → BitVec 512)
    (cSpqrInit cSpqrSend cSpqrRecv cSpqrRecvPanics cSplitWireTag cParseWire cU32ToNat cToWire
      cEqWire cEqFig8C cInjOK cDh cEncT cDecT cIsZeroPt cKeyPairGen
      cFig8Init cFig8Send cFig8Recv cFsRecv cSentEval cSameWireFig8 cSnapSeed cKDecrypt
      cKemInit cKemSend cKemDeliver : ℕ) :
    OpsSizeHonest (simParamOps (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins
      cSpqrInit cSpqrSend cSpqrRecv cSpqrRecvPanics cSplitWireTag cParseWire cU32ToNat cToWire
      cEqWire cEqFig8C cInjOK cDh cEncT cDecT cIsZeroPt cKeyPairGen
      cFig8Init cFig8Send cFig8Recv cFsRecv cSentEval cSameWireFig8 cSnapSeed cKDecrypt
      cKemInit cKemSend cKemDeliver) := by
  intro o x B hx
  cases o with
  | spqrInitA | spqrInitB | zeroU32 | natToU32 | defaultPlain | emptyLPub | effectiveHkdfSalt32
  | toWire | dh | dhBase | encT | keyPairGen | emptyChainSt | chainAccept | fig8Root
  | mkSenderChain | mkRecvChain | fig8Init | senderToFreshVr | initKemFailTrack =>
    simp only [simOpCost, Ty.Fits] at hx ⊢
    omega
  | mkLPub =>
    rcases x with ⟨pn, pqm, s, a⟩
    simp only [simOpCost, Ty.Fits] at hx ⊢
    omega
  | mkLCt =>
    rcases x with ⟨c, ⟨ser, tag⟩, s⟩
    simp only [simOpCost, Ty.Fits] at hx ⊢
    omega
  | mkGhostState =>
    rcases x with ⟨qB, rk, pn, sc, rcs, ppk, pq, ep, eps⟩
    simp only [simOpCost, Ty.Fits] at hx ⊢
    omega
  | addrAB =>
    simp only [simOpCost, Ty.Fits] at hx ⊢
    rcases P.addrAB with _ | a
    · trivial
    · simp only [Ty.Fits]; omega
  | spqrSend =>
    rcases x with ⟨pq, rq⟩
    simp only [simOpCost, Ty.Fits] at hx ⊢
    rcases P.spqr.send pq rq with _ | ⟨pq', _ | s, pqm⟩
    · trivial
    · simp only [Ty.Fits]; exact ⟨by omega, trivial, by omega⟩
    · simp only [Ty.Fits]; exact ⟨by omega, by omega, by omega⟩
  | spqrRecv =>
    rcases x with ⟨pq, pqm⟩
    simp only [simOpCost, Ty.Fits] at hx ⊢
    rcases (P.spqr.recv pq pqm).toOption with _ | ⟨pq', _ | s⟩
    · trivial
    · simp only [Ty.Fits]; exact ⟨by omega, trivial⟩
    · simp only [Ty.Fits]; exact ⟨by omega, by omega⟩
  | u32IncToNat B_idx =>
    simp only [simOpCost, Ty.Fits] at hx ⊢
    have hb : bits (min (x.toNat + 1) B_idx) ≤ bits B_idx :=
      bits_mono (Nat.min_le_right _ _)
    omega
  | splitWireTag =>
    simp only [simOpCost, Ty.Fits] at hx ⊢
    rcases simSplitWireTag x with _ | ⟨ser, tag⟩
    · trivial
    · simp only [Ty.Fits]; exact ⟨by omega, by omega⟩
  | parseWire =>
    simp only [simOpCost, Ty.Fits] at hx ⊢
    rcases simParseWire P.codec x with _ | ⟨srk, cnt, pqm, _ | addrs⟩
    · trivial
    · simp only [Ty.Fits]; exact ⟨by omega, by omega, by omega, trivial⟩
    · simp only [Ty.Fits]; exact ⟨by omega, by omega, by omega, by omega⟩
  | decT =>
    simp only [simOpCost, Ty.Fits] at hx ⊢
    rcases decT x with _ | pt
    · trivial
    · simp only [Ty.Fits]; omega
  | fig8GammaExp =>
    simp only [simOpCost, Ty.Fits] at hx ⊢
    rcases x.γ with _ | exp
    · trivial
    · simp only [Ty.Fits]; omega
  | fig8VS =>
    simp only [simOpCost, Ty.Fits] at hx ⊢
    rcases x.vS with _ | v
    · trivial
    · simp only [Ty.Fits]; omega
  | fig8VR =>
    rcases x with ⟨st, ep⟩
    simp only [simOpCost, Ty.Fits] at hx ⊢
    rcases st.vR ep with _ | v
    · trivial
    · simp only [Ty.Fits]; omega
  | fig8SendStep B_idx =>
    rcases x with ⟨st, mc?⟩
    simp only [simOpCost, Ty.Fits] at hx ⊢
    refine ⟨trivial, by omega, ⟨Nat.le_trans (bits_mono (Nat.min_le_right _ B_idx)) (by omega), ?_⟩,
      by omega⟩
    rcases ((lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam).send st
          (mc?.getD ((⟨0, [], effectiveHkdfSalt32 none, none⟩, default), 0)).1
          (mc?.getD ((⟨0, [], effectiveHkdfSalt32 none, none⟩, default), 0)).2).2.1.2 with _ | pt
    · trivial
    · simp only [Ty.Fits]; omega
  | fig8Receive B_idx =>
    rcases x with ⟨st, c⟩
    simp only [simParamOps, simOpCost, Ty.Fits] at hx ⊢
    rcases (lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam).receive st c
      with _ | ⟨st', t, i, pm⟩
    · trivial
    · simp only [Option.map_some, Ty.Fits]
      have ht : bits (min t B_idx) ≤ bits B_idx := bits_mono (Nat.min_le_right _ _)
      have hi : bits (min i B_idx) ≤ bits B_idx := bits_mono (Nat.min_le_right _ _)
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  | fsReceive B_idx =>
    rcases x with ⟨v, c⟩
    simp only [simParamOps, simOpCost, Ty.Fits] at hx ⊢
    rcases (lFS P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000).receive v c.1 c.2
      with _ | ⟨v', i, pm⟩
    · trivial
    · simp only [Option.map_some, Ty.Fits]
      have hi : bits (min i B_idx) ≤ bits B_idx := bits_mono (Nat.min_le_right _ _)
      exact ⟨by omega, by omega, by omega, by omega⟩
  | snapSeed =>
    rcases x with ⟨branch, qB, w, t, e, ePrev?⟩
    simp only [simParamOps, simOpCost, Ty.Fits] at hx ⊢
    rcases simSnapSeed P branch qB w t e ePrev? with _ | seed
    · trivial
    · simp only [Ty.Fits]; omega
  | kDecryptFig8 B_idx =>
    rcases x with ⟨qB, w, c', seed⟩
    simp only [simParamOps, simOpCost, simKDecryptFig8, Ty.Fits] at hx ⊢
    split
    · simp only [Ty.Fits]
      have ht : bits (min c'.1.1 B_idx) ≤ bits B_idx := bits_mono (Nat.min_le_right _ _)
      have hi : bits (min c'.2.1 B_idx) ≤ bits B_idx := bits_mono (Nat.min_le_right _ _)
      exact ⟨by omega, by omega, by omega, by omega⟩
    · trivial
  | stepKemFailSend =>
    rcases x with ⟨⟨F, tr⟩, qB, rq⟩
    simp only [simOpCost, Ty.Fits] at hx ⊢
    exact ⟨by omega, by omega, by omega⟩
  | stepKemFailDeliver =>
    rcases x with ⟨⟨F, tr⟩, qB, j⟩
    simp only [simOpCost, Ty.Fits] at hx ⊢
    omega
  | addrsOkA | addrsOkB | eqWire | eqFig8C | lctSaltEq | injOK | eqPk | isZeroPt | chainRejects
  | spqrRecvPanics | sameWireFig8 =>
    trivial

theorem simOpsWithFig_sizeHonest {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) (toKemCoins : PQC → BitVec 512) :
    OpsSizeHonest (simOpsUnitCost (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins) :=
  simParamOps_sizeHonest P Dh encPt encT decT lam K toKemCoins
    1 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1

theorem simOps_sizeHonest {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) :
    OpsSizeHonest (simOps (ℓ := ℓ) P Dh encT decT) :=
  simOpsWithFig_sizeHonest P Dh (fun T => (encT T).1.toList) encT decT (0 : Pt)
    simDummyMlKem (fun _ => 0)

theorem simParamSamplers_sizeHonest (PQ PQC Pt : Type) [SampleableType PQC] (ℓ : ℕ)
    (cSampBv256 cSampPqc : ℕ) (hbv : 1 ≤ cSampBv256) (hpqc : 1 ≤ cSampPqc) :
    SampSizeHonest (simParamSamplers PQ PQC Pt ℓ cSampBv256 cSampPqc) :=
  SampSizeHonest.unifSamplers (S := simSig PQ PQC Pt ℓ) simBaseSampSort
    (simBaseSampCost cSampBv256 cSampPqc)
    (fun b _ => by cases b <;> dsimp [simSig, simBaseSampCost] <;> omega)

theorem simSamplers_sizeHonest (PQ PQC Pt : Type) [SampleableType PQC] (ℓ : ℕ) :
    SampSizeHonest (simSamplers PQ PQC Pt ℓ) :=
  simParamSamplers_sizeHonest PQ PQC Pt ℓ 1 1 (by decide) (by decide)

end SizeHonesty

/-! ## `SimState` representation and pure mirror bookkeeping -/

section StateAndBookkeeping

variable {PQ PQC Pt : Type} {ℓ : ℕ}

local notation "S" => simSig PQ PQC Pt ℓ

def ghostChainEnc (g : GhostChain) : Option PublicKey × (ℕ × (ℕ × List ℕ)) :=
  (g.key, (g.epoch, (g.last, g.skipped)))

def ghostChainDec (v : Option PublicKey × (ℕ × (ℕ × List ℕ))) : GhostChain :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2⟩

@[simp] theorem ghostChainDec_ghostChainEnc (g : GhostChain) :
    ghostChainDec (ghostChainEnc g) = g := by
  cases g; rfl

@[simp] theorem ghostChainEnc_ghostChainDec (v : Option PublicKey × (ℕ × (ℕ × List ℕ))) :
    ghostChainEnc (ghostChainDec v) = v := by
  rcases v with ⟨k, ep, last, sk⟩; rfl

def simRecEnc (r : Record (Plain ℓ) (List (BitVec 8))) :
    (Bool × ℕ × ℕ) × Plain ℓ × List (BitVec 8) :=
  (posEnc r.pos, r.msg, r.ct)

def simRecDec (v : (Bool × ℕ × ℕ) × Plain ℓ × List (BitVec 8)) :
    Record (Plain ℓ) (List (BitVec 8)) :=
  ⟨posDec v.1, v.2.1, v.2.2⟩

@[simp] theorem simRecDec_simRecEnc (r : Record (Plain ℓ) (List (BitVec 8))) :
    simRecDec (simRecEnc r) = r := by
  cases r; simp [simRecEnc, simRecDec]

@[simp] theorem simRecEnc_simRecDec (v : (Bool × ℕ × ℕ) × Plain ℓ × List (BitVec 8)) :
    simRecEnc (simRecDec v) = v := by
  rcases v with ⟨p, m, c⟩; simp [simRecEnc, simRecDec]

def simMirEnc (s : GameState Unit (Plain ℓ) (List (BitVec 8))) :
    (@simMirTy PQ PQC Pt ℓ).denote :=
  (s.b,
   (s.win,
    ((s.epoch .A, s.epoch .B),
     ((s.idx .A, s.idx .B),
      (s.tL,
       (s.trans.map simRecEnc,
        (s.chall.map posEnc,
         (s.comp.map posEnc,
          ((s.maxAcc .A, s.maxAcc .B),
           (s.leaks,
            s.corrs.map (fun pe => (partyEnc pe.1, pe.2))))))))))))

def simMirDec (v : (@simMirTy PQ PQC Pt ℓ).denote) :
    GameState Unit (Plain ℓ) (List (BitVec 8)) :=
  let (b, (win, (epAB, (idxAB, (tL, (trs, (chall, (comp, (maAB, (leaks, corrs)))))))))) := v
  { st := fun _ => ()
    epoch := fun | .A => epAB.1 | .B => epAB.2
    idx := fun | .A => idxAB.1 | .B => idxAB.2
    tL := tL
    trans := trs.map simRecDec
    chall := chall.map posDec
    comp := comp.map posDec
    maxAcc := fun | .A => maAB.1 | .B => maAB.2
    b := b
    win := win
    leaks := leaks
    corrs := corrs.map (fun pe => (partyDec pe.1, pe.2)) }

@[simp] theorem simMirDec_simMirEnc (s : GameState Unit (Plain ℓ) (List (BitVec 8))) :
    simMirDec (PQ := PQ) (PQC := PQC) (Pt := Pt) (simMirEnc s) = s := by
  cases s
  simp only [simMirEnc, simMirDec, List.map_map]
  congr 1
  · funext p; cases p <;> rfl
  · funext p; cases p <;> rfl
  · rw [show (simRecDec ∘ simRecEnc :
        Record (Plain ℓ) (List (BitVec 8)) → Record (Plain ℓ) (List (BitVec 8))) = id by
      funext r; simp, List.map_id]
  · rw [show (posDec ∘ posEnc : Pos → Pos) = id by funext p; simp, List.map_id]
  · rw [show (posDec ∘ posEnc : Pos → Pos) = id by funext p; simp, List.map_id]
  · funext p; cases p <;> rfl
  · rw [show ((fun pe : Bool × ℕ => (partyDec pe.1, pe.2)) ∘
        (fun pe : Party × ℕ => (partyEnc pe.1, pe.2))) = id by
      funext ⟨p, e⟩; simp, List.map_id]

@[simp] theorem simMirEnc_simMirDec (v : (@simMirTy PQ PQC Pt ℓ).denote) :
    simMirEnc (PQ := PQ) (PQC := PQC) (Pt := Pt) (simMirDec v) = v := by
  rcases v with ⟨b, win, ⟨epA, epB⟩, ⟨idxA, idxB⟩, tL, trs, chall, comp,
    ⟨maA, maB⟩, leaks, corrs⟩
  simp [simMirEnc, simMirDec, List.map_map, Function.comp_def]

def simStateEnc (s : SimState PQ Pt ℓ) : (@simStateTy PQ PQC Pt ℓ).denote :=
  (simMirEnc s.mir,
   ((s.pq .A, s.pq .B),
    ((s.pn .A, s.pn .B),
     (s.unackA,
      (s.honest,
       (((s.chains .A).map ghostChainEnc, (s.chains .B).map ghostChainEnc),
        (s.amb, s.stopped)))))))

def simStateDec (v : (@simStateTy PQ PQC Pt ℓ).denote) : SimState PQ Pt ℓ :=
  let (mir, (pqAB, (pnAB, (unackA, (honest, (chainsAB, (amb, stopped))))))) := v
  { mir := simMirDec mir
    pq := fun | .A => pqAB.1 | .B => pqAB.2
    pn := fun | .A => pnAB.1 | .B => pnAB.2
    unackA := unackA
    honest := honest
    chains := fun
      | .A => chainsAB.1.map ghostChainDec
      | .B => chainsAB.2.map ghostChainDec
    amb := amb
    stopped := stopped }

@[simp] theorem simStateDec_simStateEnc (s : SimState PQ Pt ℓ) :
    simStateDec (PQC := PQC) (simStateEnc s) = s := by
  cases s
  simp only [simStateEnc, simStateDec, simMirDec_simMirEnc, List.map_map]
  congr 1
  · funext p; cases p <;> rfl
  · funext p; cases p <;> rfl
  · funext p; cases p <;>
    simp [show (ghostChainDec ∘ ghostChainEnc : GhostChain → GhostChain) = id by
      funext g; simp]

@[simp] theorem simStateEnc_simStateDec (v : (@simStateTy PQ PQC Pt ℓ).denote) :
    simStateEnc (PQC := PQC) (simStateDec v) = v := by
  rcases v with ⟨mir, ⟨pqA, pqB⟩, ⟨pnA, pnB⟩, unackA, honest, ⟨csA, csB⟩, amb, stopped⟩
  simp [simStateEnc, simStateDec, List.map_map, Function.comp_def]

variable {P : Params PQ PQC} {Dh : DHFun (BitVec 256) Pt}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt}

local notation "OO" => simOps (ℓ := ℓ) P Dh encT decT

def mInTransitE [DecidableEq Pt] [Zero Pt] {Γ} (K : ℕ) (s : Expr OO Γ simMirTy)
    (qParty : Expr OO Γ .bool) (w : Expr OO Γ (.base .wire)) : Expr OO Γ (.opt simRecTy) :=
  rdslExpr =>
    letE (s, (qParty, w)) fun (s0, (qp0, w0)) =>
      findB K (mTrans s0) fun recElem =>
        boolEq (posSender (srecPos recElem)) qp0 &&
          Expr.op (O := OO) SimOp.eqWire (srecCt recElem, w0)

@[simp] theorem mSafeChE_eval {O' : Ops S} {Γ} (s : Expr O' Γ simMirTy) (p : Expr O' Γ .bool)
    (ρ : Env Γ) (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mSafeChE s p).eval ρ = st.safeCh 3 Q := by
  simp only [mSafeChE, Expr.eval, hs, hp, healedByE_eval]
  cases Q <;> simp [GameState.safeCh, mTL, mEpoch, pGet, Expr.eval, Expr.v0, simMirEnc, partyEnc]

@[simp] theorem mSafeInjE_eval {O' : Ops S} {Γ} (s : Expr O' Γ simMirTy)
    (ρ : Env Γ) (st : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (hs : s.eval ρ = simMirEnc st) :
    (mSafeInjE s).eval ρ = st.safeInj 3 := by
  simp only [mSafeInjE, Expr.eval, hs, healedByE_eval, minN_eval]
  simp [GameState.safeInj, mTL, mEpoch, Expr.eval, Expr.v0, simMirEnc]

@[simp] theorem mLeakE_eval {O' : Ops S} {Γ} (s : Expr O' Γ simMirTy) (l : Expr O' Γ .nat)
    (ρ : Env Γ) (st : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (hs : s.eval ρ = simMirEnc st) :
    (mLeakE s l).eval ρ = simMirEnc (st.leak (l.eval ρ)) := by
  simp only [mLeakE, mMk, Expr.eval, hs, maxOptE_eval]
  simp [GameState.leak, mB, mWin, mEpoch, mIdx, mTL, mTrans, mChall,
    mComp, mMaxAcc, mLeaks, mCorrs, Expr.eval, Expr.v0, simMirEnc]

@[simp] theorem mEpMgmtE_eval {O' : Ops S} {Γ} (qep : ℕ) (s : Expr O' Γ simMirTy)
    (p : Expr O' Γ .bool) (bad : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mEpMgmtE qep s p bad).eval ρ = (st.epMgmt 3 qep Q (bad.eval ρ)).map simMirEnc := by
  unfold mEpMgmtE GameState.epMgmt
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair p bad)).eval ρ = (simMirEnc st, partyEnc Q, bad.eval ρ) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod simMirTy (.prod .bool .bool))
    (simMirEnc st, partyEnc Q, bad.eval ρ) ρ
  rw [ite_eval]
  have hSends : (sendsInE (.fst (.snd (Expr.v0 (O := O'))))
      (.add (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
        (.nat 1))).eval ρ₁ = Q.sendsIn (st.epoch Q + 1) := by
    rw [sendsInE_eval _ _ ρ₁ Q rfl]
    congr 1
    cases Q <;> simp [ρ₁, pGet, mEpoch, simMirEnc, partyEnc, Expr.eval, Expr.v0]
  rw [hSends]
  by_cases h1 : Q.sendsIn (st.epoch Q + 1)
  · simp only [h1, ↓reduceIte]
    rw [ite_eval]
    have hlt1 : (Expr.lt (.nat qep) (.add (pGet (mEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O'))))) (.nat 1))).eval ρ₁ =
        decide (qep < st.epoch Q + 1) := by
      cases Q <;> simp [ρ₁, pGet, mEpoch, simMirEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt1]
    by_cases h2 : qep < st.epoch Q + 1
    · simp [h2, Expr.eval]
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte, Option.map_some]
      rw [letE_eval, ite_eval]
      have hCond : (Expr.and (.snd (.snd (Expr.v0 (O := O'))))
          (.not (mSafeChE (.fst (Expr.v0 (O := O')))
            (.fst (.snd (Expr.v0 (O := O'))))))).eval ρ₁ =
          (bad.eval ρ && !(st.safeCh 3 Q)) := by
        have hsafe := mSafeChE_eval (.fst (Expr.v0 (O := O')))
          (.fst (.snd (Expr.v0 (O := O')))) ρ₁ st Q rfl rfl
        simp only [Expr.eval, hsafe]
        rfl
      have hLeak : (mLeakE (.fst (Expr.v0 (O := O')))
          (.add (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
            (.nat 1))).eval ρ₁ = simMirEnc (st.leak (st.epoch Q + 1)) := by
        rw [mLeakE_eval (.fst (Expr.v0 (O := O'))) _ ρ₁ st rfl]
        congr 2
        cases Q <;> simp [ρ₁, pGet, mEpoch, simMirEnc, partyEnc, Expr.eval, Expr.v0]
      have hBase : (Expr.fst (Expr.v0 (O := O'))).eval ρ₁ = simMirEnc st := rfl
      rw [hCond, hLeak, hBase]
      set st₁ := if (bad.eval ρ && !(st.safeCh 3 Q)) = true then st.leak (st.epoch Q + 1) else st
      have hst₁ : (if (bad.eval ρ && !(st.safeCh 3 Q)) = true
          then (simMirEnc (st.leak (st.epoch Q + 1)) : (@simMirTy PQ PQC Pt ℓ).denote)
          else simMirEnc st) = simMirEnc st₁ := by
        dsimp only [st₁]; split_ifs <;> rfl
      rw [hst₁]
      cases Q <;>
        simp [ρ₁, mMk, mB, mWin, mEpoch, mIdx, mTL, mTrans, mChall, mComp,
          mMaxAcc, mLeaks, mCorrs, pGet, pSet, simMirEnc, partyEnc, Function.update,
          Expr.eval, Expr.v0, Expr.v1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [ite_eval]
    have hlt2 : (Expr.lt (.nat qep) (pGet (mEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O')))))).eval ρ₁ = decide (qep < st.epoch Q) := by
      cases Q <;> simp [ρ₁, pGet, mEpoch, simMirEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt2]
    by_cases h2 : qep < st.epoch Q <;> simp [ρ₁, h2, Expr.eval, Expr.v0]

@[simp] theorem mRecordE_eval {O' : Ops S} {Γ} (s : Expr O' Γ simMirTy) (p : Expr O' Γ .bool)
    (r : Expr O' Γ simRecTy) (isChall : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (rec_ : Record (Plain ℓ) (List (BitVec 8)))
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) (hr : r.eval ρ = simRecEnc rec_) :
    (mRecordE s p r isChall).eval ρ =
      simMirEnc (st.record 3 Q () rec_ (isChall.eval ρ)) := by
  unfold mRecordE
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair p (.pair r isChall))).eval ρ =
      (simMirEnc st, partyEnc Q, simRecEnc rec_, isChall.eval ρ) := by
    simp [Expr.eval, hs, hp, hr]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod simMirTy (.prod .bool (.prod simRecTy .bool)))
    (simMirEnc st, partyEnc Q, simRecEnc rec_, isChall.eval ρ) ρ
  have hSafe : (mSafeChE (.fst (Expr.v0 (O := O'))) (.fst (.snd (Expr.v0 (O := O'))))).eval ρ₁ =
      st.safeCh 3 Q :=
    mSafeChE_eval (.fst .v0) (.fst (.snd .v0)) ρ₁ st Q rfl rfl
  simp only [mMk, Expr.eval, hSafe]
  cases Q <;> cases hch : isChall.eval ρ <;>
  by_cases hsafeA : st.safeCh 3 .A <;> by_cases hsafeB : st.safeCh 3 .B <;>
  simp [ρ₁, GameState.record, mB, mWin, mEpoch, mIdx, mTL, mTrans,
    mChall, mComp, mMaxAcc, mLeaks, mCorrs, posIdx, pSet,
    hch, hsafeA, hsafeB, simMirEnc, simRecEnc, posEnc, partyEnc, Function.update,
    Expr.eval, Expr.v0]

@[simp] theorem mInTransitE_eval [DecidableEq Pt] [Zero Pt] {Γ} (K : ℕ) (s : Expr OO Γ simMirTy)
    (qParty : Expr OO Γ .bool) (w : Expr OO Γ (.base .wire)) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (hK : st.trans.length ≤ K)
    (hs : s.eval ρ = simMirEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (mInTransitE K s qParty w).eval ρ = (st.inTransit Q (w.eval ρ)).map simRecEnc := by
  have htake : ((st.trans.map simRecEnc).take K) = st.trans.map simRecEnc :=
    List.take_of_length_le (by simpa using hK)
  simp only [mInTransitE, GameState.inTransit, mTrans, srecPos, posSender, srecCt,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    boolEq_eval, simOps, hs, hq, simMirEnc, htake]
  rw [find?_map_eq]
  congr 2
  funext ⟨⟨sender, ep, idx⟩, msg, ct⟩
  cases sender <;> cases Q <;> by_cases h : ct = w.eval ρ <;>
    simp [simRecEnc, posEnc, partyEnc, h]

@[simp] theorem mDeleteE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ simMirTy)
    (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (p : Pos)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K)
    (hComp : st.comp.length ≤ K)
    (hs : s.eval ρ = simMirEnc st) (hp : pos.eval ρ = posEnc p) :
    (mDeleteE K s pos).eval ρ = simMirEnc (st.delete p) := by
  have ht1 : (st.trans.map simRecEnc).take K = st.trans.map simRecEnc :=
    List.take_of_length_le (by simpa using hTrans)
  have ht2 : (st.chall.map posEnc).take K = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have ht3 : (st.comp.map posEnc).take K = st.comp.map posEnc :=
    List.take_of_length_le (by simpa using hComp)
  simp only [mDeleteE, GameState.delete, mMk, mB, mWin, mEpoch, mIdx, mTL, mTrans,
    mChall, mComp, mMaxAcc, mLeaks, mCorrs, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hp, simMirEnc, ht1, ht2, ht3]
  rw [foldr_filter_map, foldr_filter_map, foldr_filter_map]
  simp [simRecEnc, posDec_posEnc, bne]

@[simp] theorem mAcceptE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ simMirTy)
    (p : Expr O' Γ .bool) (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party) (pos₀ : Pos)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K)
    (hComp : st.comp.length ≤ K)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q)
    (hpos : pos.eval ρ = posEnc pos₀) :
    (mAcceptE K s p pos).eval ρ = simMirEnc (st.accept Q () pos₀) := by
  have hdel := mDeleteE_eval K s pos ρ st pos₀ hTrans hChall hComp hs hpos
  simp only [mAcceptE, mMk, Expr.eval, hdel, hp, hpos]
  cases Q <;>
  · simp [GameState.accept, mB, mWin, mEpoch, mIdx, mTL, mTrans,
      mChall, mComp, mMaxAcc, mLeaks, mCorrs, posEpoch, posIdx, pGet, pSet,
      maxAccGet, maxAccSet, maxN_eval, simMirEnc, posEnc, partyEnc,
      Function.update, Expr.eval, Expr.v0]
    funext j; split_ifs with hj <;> simp [hj]

@[simp] theorem mCompContainsE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ simMirTy)
    (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (pos₀ : Pos)
    (hComp : st.comp.length ≤ K)
    (hs : s.eval ρ = simMirEnc st) (hpos : pos.eval ρ = posEnc pos₀) :
    (mCompContainsE K s pos).eval ρ = st.comp.contains pos₀ := by
  have ht : (st.comp.map posEnc).take K = st.comp.map posEnc :=
    List.take_of_length_le (by simpa using hComp)
  simp only [mCompContainsE, mComp, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hpos, simMirEnc, ht]
  rw [any_map_eq]
  simp only [posDec_posEnc]
  exact any_beq_eq_contains pos₀ st.comp

@[simp] theorem mChallContainsE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ simMirTy)
    (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (pos₀ : Pos)
    (hChall : st.chall.length ≤ K)
    (hs : s.eval ρ = simMirEnc st) (hpos : pos.eval ρ = posEnc pos₀) :
    (mChallContainsE K s pos).eval ρ = st.chall.contains pos₀ := by
  have ht : (st.chall.map posEnc).take K = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  simp only [mChallContainsE, mChall, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hpos, simMirEnc, ht]
  rw [any_map_eq]
  simp only [posDec_posEnc]
  exact any_beq_eq_contains pos₀ st.chall

@[simp] theorem mTrivialE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ simMirTy)
    (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (pos₀ : Pos)
    (hTrans : st.trans.length ≤ K) (hComp : st.comp.length ≤ K)
    (hs : s.eval ρ = simMirEnc st) (hpos : pos.eval ρ = posEnc pos₀) :
    (mTrivialE K s pos).eval ρ = st.trivial 3 pos₀ := by
  have ht : (st.trans.map simRecEnc).take K = st.trans.map simRecEnc :=
    List.take_of_length_le (by simpa using hTrans)
  simp only [mTrivialE, Expr.eval, hs, hpos, orE_eval, healedByE_eval]
  rw [mCompContainsE_eval K _ _ _ st pos₀ hComp rfl rfl]
  simp only [GameState.trivial, mTrans, mTL, posEpoch,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    posEq_eval, simMirEnc, ht]
  rw [any_map_eq]
  simp [simRecEnc, posEnc, posDec]

@[simp] theorem mCorrAllowedE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ simMirTy)
    (p : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K)
    (hComp : st.comp.length ≤ K)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mCorrAllowedE K s p).eval ρ = st.corrAllowed Q := by
  unfold mCorrAllowedE GameState.corrAllowed
  rw [letE_eval]
  have h0 : (Expr.pair s p).eval ρ = (simMirEnc st, partyEnc Q) := by simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod simMirTy .bool) (simMirEnc st, partyEnc Q) ρ
  have htCh : (st.chall.map posEnc).take K = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have htTr : (st.trans.map simRecEnc).take K = st.trans.map simRecEnc :=
    List.take_of_length_le (by simpa using hTrans)
  have hCh0 : (mChall (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.chall.map posEnc := rfl
  have hTr0 : (mTrans (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.trans.map simRecEnc := rfl
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
    have hcomp := mCompContainsE_eval (O' := O') K (.fst .v1) (srecPos .v0)
      (Env.cons (t := simRecTy) (simRecEnc r) ρ₁) st r.pos hComp rfl rfl
    dsimp only [srecPos] at hcomp
    rw [hcomp]
    simp [ρ₁, posSender, otherE, simRecEnc, posEnc, ← partyEnc_other, partyEnc_beq,
      Expr.eval, Expr.v0, Expr.v1]

@[simp] theorem mAfterCorrE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ simMirTy)
    (p : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (hTrans : st.trans.length ≤ K)
    (hCompU : ∃ U : List Pos, U.length ≤ K ∧ CountLe st.comp U ∧ ∀ r ∈ st.trans, r.pos ∈ U)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mAfterCorrE K s p).eval ρ = simMirEnc (afterCorrDedup st Q) := by
  rcases hCompU with ⟨U, hUK, haccU, htransU⟩
  simp only [mAfterCorrE, mLeakE, maxOptE, mMk, mB, mWin, mEpoch, mIdx, mTL,
    mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs, posSender, otherE,
    Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ,
    boolEq_eval, posEq_eval, maxN_eval, hs, hp, simMirEnc]
  have hfold := foldr_dedup_map_eq (K := K) (encR := simRecEnc) (encP := posEnc)
    (posOf := Record.pos)
    (keep := fun r : Record (Plain ℓ) (List (BitVec 8)) => r.pos.sender == Q.other)
    (keepE := fun rE => rE.1.1 == !partyEnc Q)
    (posE := fun rE => rE.1)
    (eqP := fun p₁ p₂ => posDec p₁ == posDec p₂)
    (rs := st.trans) (acc := st.comp) (U := U)
    (by intro r; simp [simRecEnc, posEnc, ← partyEnc_other, partyEnc_beq])
    (by intro r; rfl)
    (by intro p₁ p₂; simp [posDec_posEnc])
    hTrans hUK haccU (fun r hr _ => htransU r hr)
  rw [hfold]
  cases Q <;>
  · simp only [afterCorrDedup, GameState.leak, maxOpt, pGet, partyEnc,
      Expr.eval, Expr.v0, Env.get_cons_zero]
    cases st.tL <;> rfl

@[simp] theorem mInWinE_eval {O' : Ops S} {Γ} (s : Expr O' Γ simMirTy) (p : Expr O' Γ .bool)
    (ρ : Env Γ) (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mInWinE s p).eval ρ = inReceiveOnlyEpoch st Q := by
  cases Q <;> simp [mInWinE, inReceiveOnlyEpoch, sendsInE, pGet, mEpoch, hs, hp, simMirEnc, partyEnc,
    Party.sendsIn, BEq.beq, Expr.eval, Expr.v0]

@[simp] theorem mNoBobEpoch0E_eval {O' : Ops S} {Γ} (s : Expr O' Γ simMirTy) (p : Expr O' Γ .bool)
    (ρ : Env Γ) (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mNoBobEpoch0E s p).eval ρ = noBobSendInEpoch0 st Q := by
  cases Q <;> simp [mNoBobEpoch0E, noBobSendInEpoch0, mEpoch, hs, hp, simMirEnc, partyEnc,
    BEq.beq, Expr.eval, Expr.v0]

@[simp] theorem mNoSpkCorrE_eval {O' : Ops S} {Γ} (s : Expr O' Γ simMirTy) (p : Expr O' Γ .bool)
    (ρ : Env Γ) (st : GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mNoSpkCorrE s p).eval ρ = noAliceCorrWhileAliceBelowEpoch10 st Q := by
  cases Q <;> simp [mNoSpkCorrE, noAliceCorrWhileAliceBelowEpoch10, mEpoch, hs, hp, simMirEnc, partyEnc,
    BEq.beq, Expr.eval, Expr.v0]

end StateAndBookkeeping

/-! ## Costed `LibsignalSim` handlers and reductions -/

section HandlersAndProg

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)

local notation "S" => simSig PQ PQC Pt ℓ
local notation "OO" => simOps (ℓ := ℓ) P Dh encT decT
local notation "SIface" => simIface PQ PQC Pt ℓ

def simFindChain (cs : List (Option PublicKey × (ℕ × (ℕ × List ℕ)))) (pk : PublicKey) :
    Option (ℕ × (Option PublicKey × (ℕ × (ℕ × List ℕ)))) :=
  match cs.findIdx? (fun g => g.1 == some pk) with
  | some ci => some (ci, cs.getD ci (none, (0, (0, []))))
  | none => none

def simModifyChainAccept (cs : List (Option PublicKey × (ℕ × (ℕ × List ℕ)))) (ci i : ℕ) :
    List (Option PublicKey × (ℕ × (ℕ × List ℕ))) :=
  cs.modify ci (fun g => (g.1, (g.2.1, simChainAccept g.2.2 i)))

def simPushChain (cs : List (Option PublicKey × (ℕ × (ℕ × List ℕ))))
    (T : PublicKey) (t i : ℕ) : List (Option PublicKey × (ℕ × (ℕ × List ℕ))) :=
  let g := (some T, (t, simChainAccept (0, []) i))
  let cs' := cs ++ [g]
  cs'.drop (cs'.length - 5)

def simRevealSpkChains {Pt : Type} (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (csA : List (Option PublicKey × (ℕ × (ℕ × List ℕ)))) (st : SimFig8St Pt) :
    List (Option PublicKey × (ℕ × (ℕ × List ℕ))) :=
  match st.γ with
  | .exp x =>
    csA.map fun g =>
      if g.1.isNone then (some (encT (Dh.dh x Dh.base)), g.2) else g
  | _ => csA

def simToGhost {PQ PQC Pt : Type} (P : Params PQ PQC) (qB : Bool) (st : SimFig8St Pt)
    (pn : BitVec 32) (cs : List (Option PublicKey × (ℕ × (ℕ × List ℕ))))
    (unackA : Bool) (pq : PQ) (ep : ℕ) : GhostState PQ :=
  let Q := partyDec qB
  let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let sender : Option SenderChain :=
    match st.γ, st.vS with
    | .exp x, some v => some ⟨KeyPair.generate P.C x, ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩⟩
    | _, _ => none
  let recv : (Option PublicKey × (ℕ × (ℕ × List ℕ))) → ReceiverChain := fun g =>
    simMkRecvChain g.1 g.2.2 (st.vR g.2.1)
  ⟨Q, { sessionVersion := BitVec.ofNat 32 currentVersion.toNat, localIdentity := idOf Q,
        remoteIdentity := some (idOf Q.other), rootKey := st.root, previousCounter := pn,
        senderChain := sender, receiverChains := cs.map recv,
        pendingPreKey := Q == Party.A && unackA, pqRatchetState := pq },
    ep, cs.map (·.2.1)⟩

def simSpqrSendPub {PQ PQC : Type} (P : Params PQ PQC) (qB unackA : Bool)
    (pq : PQ) (rq : PQC) (pn : BitVec 32) : Option (PQ × LibsignalMsgPublicPart) :=
  let Q := partyDec qB
  (P.spqr.send pq rq).map fun x =>
    (x.1, ⟨pn, x.2.2, effectiveHkdfSalt32 x.2.1, if Q == Party.A && unackA then P.addrAB else none⟩)

def simParseRecv {PQ PQC Pt : Type} (P : Params PQ PQC) (decT : PublicKey → Option Pt)
    (B : ℕ) (qB : Bool) (pq : PQ) (w : List (BitVec 8)) :
    Option (PQ × (ℕ × (PublicKey × (Option Pt × (ℕ × LibsignalCiphertextWithSalt32))))) :=
  let Q := partyDec qB
  if w.length < 9 then none
  else
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    match (signalWireCodec P.codec).parse ser with
    | none => none
    | some (h, _) =>
      if !(addressCheckPasses h.addresses (P.expectedAddrs Q)) then none
      else
        match P.spqr.recv pq h.pqRatchet with
        | .error _ => none
        | .ok (pq', salt) =>
          let i := h.counter.toNat + 1
          some (pq', (min i B, (h.senderRatchetKey,
            (decT h.senderRatchetKey, (i, ((ser, tag), effectiveHkdfSalt32 salt))))))

def initChainAE {Γ} : Expr OO Γ (ghostChainTy PQ PQC Pt ℓ) :=
  .pair .none (.pair (.nat 0) (Expr.op (O := OO) SimOp.emptyChainSt .unit))

def hasUnknownKeyE {Γ}
    (cs : Expr OO Γ (.list (ghostChainTy PQ PQC Pt ℓ))) : Expr OO Γ .bool :=
  rdslExpr =>
    anyB 5 cs fun (optPk, _) =>
      match optPk with
      | none => true
      | some _ => false

def findChainE {Γ}
    (arg : Expr OO Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.base .pk))) :
    Expr OO Γ (.opt (.prod .nat (ghostChainTy PQ PQC Pt ℓ))) :=
  rdslExpr =>
    letE arg fun (cs, pk) =>
      foldrB 5 cs none fun g@(optPk, _) acc =>
        if (match optPk with
            | none => false
            | some gPk => Expr.op (O := OO) SimOp.eqPk (gPk, pk)) then
          some (0, g)
        else
          match acc with
          | none => none
          | some (idx, found) => some (idx + 1, found)

def modifyChainAcceptE {Γ}
    (arg : Expr OO Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.prod .nat .nat))) :
    Expr OO Γ (.list (ghostChainTy PQ PQC Pt ℓ)) :=
  rdslExpr =>
    letE arg fun (cs, (ci, i)) =>
      foldrB 5 cs [] fun g@(optPk, (ep, chSt)) acc =>
        cons
          (if len acc + (ci + 1) == len cs then
             (optPk, (ep, Expr.op (O := OO) SimOp.chainAccept (chSt, i)))
           else
             g)
          acc

def pushChainE {Γ}
    (arg : Expr OO Γ
      (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.prod (.base .pk) (.prod .nat .nat)))) :
    Expr OO Γ (.list (ghostChainTy PQ PQC Pt ℓ)) :=
  rdslExpr =>
    letE arg fun (cs0, (T0, (t0, i0))) =>
      let g :=
        (some T0,
          (t0,
            Expr.op (O := OO) SimOp.chainAccept
              (Expr.op (O := OO) SimOp.emptyChainSt (), i0)))
      foldrB 5 cs0 [g] fun elem acc =>
        if len acc < 5 then cons elem acc else acc

def revealSpkChainsE {Γ}
    (arg : Expr OO Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.base .fig8st))) :
    Expr OO Γ (.list (ghostChainTy PQ PQC Pt ℓ)) :=
  rdslExpr =>
    letE arg fun (csA, fig8st) =>
      match Expr.op (O := OO) SimOp.fig8GammaExp fig8st with
      | none => csA
      | some x =>
        mapB 5 csA fun g@(optPk, rest) =>
          match optPk with
          | none =>
            (some
              (Expr.op (O := OO) SimOp.encT
                (Expr.op (O := OO) SimOp.dh
                  (x, Expr.op (O := OO) SimOp.dhBase ()))),
             rest)
          | some _ => g

def spqrSendPubE {Γ}
    (arg : Expr OO Γ
      (.prod .bool (.prod .bool (.prod (.base .pq) (.prod (.base .pqc) (.base .u32)))))) :
    Expr OO Γ (.opt (.prod (.base .pq) (.base .lpub))) :=
  rdslExpr =>
    letE arg fun (qB, (unackA, (pq, (rq, pn)))) =>
      match Expr.op (O := OO) SimOp.spqrSend (pq, rq) with
      | none => none
      | some (pq', (salt?, pqm)) =>
        let addr := if (!qB) && unackA then Expr.op (O := OO) SimOp.addrAB () else none
        some
          (pq',
            Expr.op (O := OO) SimOp.mkLPub
              (pn, (pqm, (Expr.op (O := OO) SimOp.effectiveHkdfSalt32 salt?, addr))))

def parseRecvE (B : ℕ) {Γ}
    (arg : Expr OO Γ (.prod .bool (.prod (.base .pq) (.base .wire)))) :
    Expr OO Γ
      (.opt (.prod (.base .pq)
        (.prod .nat (.prod (.base .pk) (.prod (.opt (.base .pt)) (.base .lct)))))) :=
  rdslExpr =>
    letE arg fun (qB, (pq, wire)) =>
      match Expr.op (O := OO) SimOp.splitWireTag wire with
      | none => none
      | some serTag@(ser, _tag) =>
        match Expr.op (O := OO) SimOp.parseWire ser with
        | none => none
        | some (srk, (cnt, (pqm, addrs))) =>
          if (if qB then
                Expr.op (O := OO) SimOp.addrsOkB addrs
              else
                Expr.op (O := OO) SimOp.addrsOkA addrs) then
            match Expr.op (O := OO) SimOp.spqrRecv (pq, pqm) with
            | none => none
            | some (pq', salt?) =>
              some
                (pq',
                  (Expr.op (O := OO) (raw (SimOp.u32IncToNat B)) cnt,
                    (srk,
                      (Expr.op (O := OO) SimOp.decT srk,
                        Expr.op (O := OO) SimOp.mkLCt
                          (cnt, (serTag, Expr.op (O := OO) SimOp.effectiveHkdfSalt32 salt?))))))
          else
            none

def toGhostE {Γ}
    (arg : Expr OO Γ
      (.prod .bool
        (.prod (.base .fig8st)
          (.prod (.base .u32)
            (.prod (.list (ghostChainTy PQ PQC Pt ℓ))
              (.prod .bool (.prod (.base .pq) .nat))))))) :
    Expr OO Γ (.base .ghostSt) :=
  rdslExpr =>
    letE arg fun (qB, (st, (pn, (cs, (unackA, (pq, ep)))))) =>
      let sender :=
        match Expr.op (O := OO) SimOp.fig8GammaExp st with
        | none => none
        | some x =>
          match Expr.op (O := OO) SimOp.fig8VS st with
          | none => none
          | some vs =>
            some (Expr.op (O := OO) SimOp.mkSenderChain (Expr.op (O := OO) SimOp.keyPairGen x, vs))
      let rcs :=
        mapB 5 cs fun (optPk, (epG, chSt)) =>
          Expr.op (O := OO) SimOp.mkRecvChain
            (optPk, (chSt, Expr.op (O := OO) SimOp.fig8VR (st, epG)))
      let eps := mapB 5 cs fun (_, (epG, _)) => epG
      Expr.op (O := OO) SimOp.mkGhostState
        (qB,
          (Expr.op (O := OO) SimOp.fig8Root st,
            (pn, (sender, (rcs, (((!qB) && unackA), (pq, (ep, eps))))))))

def guardC {Γ t} (s : Expr OO Γ simStateTy)
    (body : Comp OO SIface Γ (.prod (.opt t) simStateTy)) :
    Comp OO SIface Γ (.prod (.opt t) simStateTy) :=
  rdsl do
    if ssStopped s then
      return (none, s)
    else
      raw body

def simDrawSendCoinsC {Γ} (r : Expr OO Γ (.opt (.base .pqc))) :
    Comp OO SIface Γ (.prod (.base .pqc) (.opt (.base .bv256))) :=
  rdsl do
    match r with
    | none =>
      rq ← sample (I := SIface) (UniformSamplerTag.base SimBaseSamp.pqc) ()
      return (rq, none)
    | some rq =>
      rc ← sample (I := SIface) (UniformSamplerTag.base SimBaseSamp.bv256) ()
      return (rq, some rc)

def simSendPostQueryC {Γ} :
    Comp OO SIface
      (.opt (fig8CTy PQ PQC Pt ℓ) ::
       .prod (.base .pq) (.base .lpub) ::
       .prod (.base .pqc) (.opt (.base .bv256)) ::
       simMirTy ::
       .prod simStateTy
         (.prod .bool (.prod (.base .plain)
           (.prod (.opt (.base .plain)) (.opt (.base .pqc))))) ::
       Γ)
      (.prod (.opt (.base .wire)) simStateTy) :=
  rdsl [res, (pq', _pub), (_rq, _rc), s1, (s0, (q0, (m0, (chal0, _r0))))] do
    match res with
    | none => return (none, s0)
    | some c =>
      let pn5 :=
        if !(pGet (mEpoch s1) q0 == pGet (mEpoch (ssMir s0)) q0) then
          Expr.op (O := OO) SimOp.natToU32 (pGet (mIdx (ssMir s0)) q0 - 1)
        else
          pGet (ssPn s0) q0
      let w := Expr.op (O := OO) SimOp.toWire c
      let rec' := ((q0, (pGet (mEpoch s1) q0, pGet (mIdx s1) q0 + 1)), (m0, w))
      let mir' := mRecordE s1 q0 rec' (isSomeE chal0)
      let nextSt :=
        ssMk mir'
          (pSet (ssPq s0) q0 pq')
          (pSet (ssPn s0) q0 pn5)
          (ssUnackA s0)
          (cons (w, c) (ssHonest s0))
          (ssChains s0)
          (ssAmb s0)
          (ssStopped s0)
      return (some w, nextSt)

def simSendPostCoinsC {Γ} :
    Comp OO SIface
      (.prod (.base .pqc) (.opt (.base .bv256)) ::
       simMirTy ::
       .prod simStateTy
         (.prod .bool (.prod (.base .plain)
           (.prod (.opt (.base .plain)) (.opt (.base .pqc))))) ::
       Γ)
      (.prod (.opt (.base .wire)) simStateTy) :=
  rdsl [(rq, rc), s1, (s0, (q0, (m0, (chal0, _r0))))] do
    let pn :=
      if !(pGet (mEpoch s1) q0 == pGet (mEpoch (ssMir s0)) q0) then
        Expr.op (O := OO) SimOp.natToU32 (pGet (mIdx (ssMir s0)) q0 - 1)
      else
        pGet (ssPn s0) q0
    match spqrSendPubE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
        (q0, (ssUnackA s0, (pGet (ssPq s0) q0, (rq, pn)))) with
    | none => return (none, s0)
    | some (_pq', pub) =>
      _res ←
        match chal0 with
        | none => query (I := SIface) SM.SMTag.tr (q0, ((pub, m0), rc))
        | some m1 => query (I := SIface) SM.SMTag.ch (q0, ((pub, m0), ((pub, m1), rc)))
      simSendPostQueryC (P := P) (Dh := Dh) (encT := encT) (decT := decT)

/-- `LibsignalSim.simSend` in `ReductionDsl`, handling `transmit` (`chal = .none`) and `challenge`
(`chal = .some m₁`). -/
def simSendC (qep : ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (m₀ : Expr OO Γ (.base .plain)) (chal : Expr OO Γ (.opt (.base .plain)))
    (r : Expr OO Γ (.opt (.base .pqc))) :
    Comp OO SIface Γ (.prod (.opt (.base .wire)) simStateTy) :=
  rdsl do
    (s0, (q0, (_m0, (chal0, r0)))) ← return (s, (qParty, (m₀, (chal, r))))
    let refuse := orE (mWin (ssMir s0)) (!(mNoBobEpoch0E (ssMir s0) q0))
    if refuse then
      return (none, s0)
    else
      match mEpMgmtE qep (ssMir s0) q0 (isSomeE r0) with
      | none => return (none, s0)
      | some s1 =>
        if isSomeE chal0 && !(mSafeChE s1 q0) then
          return (none, s0)
        else
          _coins ← simDrawSendCoinsC (P := P) (Dh := Dh) (encT := encT) (decT := decT) r0
          simSendPostCoinsC (P := P) (Dh := Dh) (encT := encT) (decT := decT)

def inTE (K : ℕ) {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (c : Expr OO Γ (fig8CTy PQ PQC Pt ℓ)) : Expr OO Γ .bool :=
  rdslExpr =>
    letE (s, (qParty, c)) fun (s0, (qp0, c0)) =>
      anyB K (ssHonest s0) fun (wH, cH) =>
        Expr.op (O := OO) SimOp.eqFig8C (cH, c0) &&
          isSomeE (mInTransitE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            K (ssMir s0) (otherE qp0) wH)

def fwdC (K : ℕ) {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (c : Expr OO Γ (fig8CTy PQ PQC Pt ℓ)) :
    Comp OO SIface Γ (.opt (fig8RrTy PQ PQC Pt ℓ)) :=
  rdsl do
    if inTE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s qParty c then
      query (I := SIface) SM.SMTag.dl (qParty, c)
    else
      query (I := SIface) SM.SMTag.ij (qParty, c)

def onAcceptPreE {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (t i : Expr OO Γ .nat) (ciOpt : Expr OO Γ (.opt .nat))
    (T : Expr OO Γ (.base .pk)) (pq' : Expr OO Γ (.base .pq)) :
    Expr OO Γ simStateTy :=
  rdslExpr =>
    letE (s, (qParty, (t, (i, (ciOpt, (T, pq'))))))
      fun (s0, (q0, (t0, (i0, (ci0, (T0, pq0)))))) =>
      let cs :=
        match ci0 with
        | none =>
          pushChainE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (pGet (ssChains s0) q0, (T0, (t0, i0)))
        | some ci =>
          modifyChainAcceptE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (pGet (ssChains s0) q0, (ci, i0))
      ssMk (ssMir s0) (pSet (ssPq s0) q0 pq0) (ssPn s0) (ssUnackA s0 && q0)
        (ssHonest s0) (pSet (ssChains s0) q0 cs) (ssAmb s0) (ssStopped s0)

def onAcceptE (K qep : ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (w : Expr OO Γ (.base .wire)) (isDel : Expr OO Γ .bool)
    (t i : Expr OO Γ .nat) (m : Expr OO Γ (.base .plain))
    (ciOpt : Expr OO Γ (.opt .nat)) (T : Expr OO Γ (.base .pk))
    (pq' : Expr OO Γ (.base .pq)) :
    Expr OO Γ (.prod (.opt (simRrTy PQ PQC Pt ℓ)) simStateTy) :=
  rdslExpr =>
    letE (s, (onAcceptPreE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
        s qParty t i ciOpt T pq',
      (qParty, (w, (isDel, (t, (i, m)))))))
      fun (s0, (s'0, (q0, (w0, (del0, (t0, (i0, m0))))))) =>
      if del0 then
        match mInTransitE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            K (ssMir s0) (otherE q0) w0 with
        | none => (none, s0)
        | some recFound =>
          let rPos := srecPos recFound
          let mOut := if mChallContainsE K (ssMir s0) rPos then none else some m0
          (some (.inr (t0, (i0, mOut))),
            ssSetMir s'0 (mAcceptE K (ssMir s0) q0 rPos))
      else if nat (qep + 1) < t0 then
        (some (.inl ()), s0)
      else
        let pos := (otherE q0, (t0, i0))
        if mTrivialE K (ssMir s0) pos then
          (some (.inr (t0, (i0, some m0))),
            ssSetMir s'0 (mAcceptE K (ssMir s0) q0 pos))
        else
          (some (.inl ()), ssSetMirWin s0)

def onAnswerE (K qep : ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (w : Expr OO Γ (.base .wire)) (isDel : Expr OO Γ .bool)
    (ciOpt : Expr OO Γ (.opt .nat)) (T : Expr OO Γ (.base .pk))
    (pq' : Expr OO Γ (.base .pq))
    (res : Expr OO Γ (.opt (fig8RrTy PQ PQC Pt ℓ))) :
    Expr OO Γ (.prod (.opt (simRrTy PQ PQC Pt ℓ)) simStateTy) :=
  rdslExpr =>
    letE (s, (qParty, (w, (isDel, (ciOpt, (T, (pq', res)))))))
      fun (s0, (q0, (w0, (del0, (ci0, (T0, (pq0, res0))))))) =>
      match res0 with
      | none => (some (.inl ()), s0)
      | some rr =>
        match rr with
        | .inl _ => (some (.inl ()), s0)
        | .inr (t0, (i0, pm)) =>
          let m :=
            match pm with
            | none => Expr.op (O := OO) SimOp.defaultPlain ()
            | some (_pub, plain) => plain
          onAcceptE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K qep
            s0 q0 w0 del0 t0 i0 m ci0 T0 pq0

def honestCE (K : ℕ) {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (w : Expr OO Γ (.base .wire)) : Expr OO Γ (.opt (fig8CTy PQ PQC Pt ℓ)) :=
  rdslExpr =>
    letE (s, (qParty, w)) fun (s0, (qp0, w0)) =>
      match findB K (ssHonest s0) (fun (wH, ((epH, _), _)) =>
          Expr.op (O := OO) SimOp.eqWire (wH, w0) &&
            boolEq (senderOfE epH) (otherE qp0)) with
      | none => none
      | some (_wH, cH) => some cH

def mkCE {Γ} (honestC : Expr OO Γ (.opt (fig8CTy PQ PQC Pt ℓ)))
    (lct : Expr OO Γ (.base .lct)) (t : Expr OO Γ .nat) (T? : Expr OO Γ (.opt (.base .pt))) :
    Expr OO Γ (fig8CTy PQ PQC Pt ℓ) :=
  rdslExpr =>
    letE (honestC, (lct, (t, T?))) fun (hc, (lct0, (t0, T0))) =>
      let dflt := ((t0, T0), lct0)
      match hc with
      | none => dflt
      | some c@(_hdr, cLct) =>
        if Expr.op (O := OO) SimOp.lctSaltEq (cLct, lct0) then c else dflt

def spkAmbE {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool) : Expr OO Γ .bool :=
  .and (.not qParty)
    (hasUnknownKeyE (P := P) (Dh := Dh) (encT := encT) (decT := decT) (pGet (ssChains s) qParty))

def ambCondE {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool) : Expr OO Γ .bool :=
  orE (mInWinE (ssMir s) qParty)
    (spkAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT) s qParty)

def sAmbE {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool) : Expr OO Γ simStateTy :=
  .ite (ambCondE (P := P) (Dh := Dh) (encT := encT) (decT := decT) s qParty)
    (ssSetAmb s (.add (ssAmb s) (.nat 1)))
    s

def evictedHonestE {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (honestC : Expr OO Γ (.opt (fig8CTy PQ PQC Pt ℓ))) : Expr OO Γ .bool :=
  rdslExpr =>
    letE (s, (qParty, honestC)) fun (s0, (qp0, hc0)) =>
      match hc0 with
      | none => false
      | some ((epH, _), _) =>
        !(epH == pGet (mEpoch (ssMir s0)) qp0 + 1)

@[reducible] def parsedRecvTy : Ty S :=
  .prod (.base .pq) (.prod .nat (.prod (.base .pk) (.prod (.opt (.base .pt)) (.base .lct))))

def simRecvNewChainNormalC (K qep : ℕ) {Γ} :
    Comp OO SIface
      (parsedRecvTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) ::
        .prod simStateTy (.prod .bool (.prod (.base .wire) .bool)) :: Γ)
      (.prod (.opt (simRrTy PQ PQC Pt ℓ)) simStateTy) :=
  rdsl [(pq', (i0, (pk, (T?0, lct)))), (s1, (q1, (w1, del1)))] do
    let sAmb := sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT) s1 q1
    if orE (mInWinE (ssMir s1) q1)
        (orE (25000 < i0 - 1) (leN (nat (2 ^ 32)) i0)) then
      return (some (.inl ()), sAmb)
    else
      match T?0 with
      | none => return (some (.inl ()), sAmb)
      | some pt =>
        let hc := honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s1 q1 w1
        let epNext := pGet (mEpoch (ssMir s1)) q1 + 1
        res ← fwdC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s1 q1
          (mkCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) hc lct epNext (some pt))
        return onAnswerE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K qep
          sAmb q1 w1 del1 none pk pq' res

def simRecvNewChainStopC (K : ℕ) {Γ} :
    Comp OO SIface
      (parsedRecvTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) ::
        .prod simStateTy (.prod .bool (.prod (.base .wire) .bool)) :: Γ)
      (.prod (.opt (simRrTy PQ PQC Pt ℓ)) simStateTy) :=
  rdsl [(_pq', (i0, (_pk, (T?0, lct)))), (s1, (q1, (w1, _del1)))] do
    let sStop :=
      ssSetStopped (sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT) s1 q1) true
    if !(mInWinE (ssMir s1) q1) then
      if !(orE (25000 < i0 - 1) (leN (nat (2 ^ 32)) i0)) then
        match T?0 with
        | none => return (none, sStop)
        | some pt =>
          let hc := honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s1 q1 w1
          let epNext := pGet (mEpoch (ssMir s1)) q1 + 1
          _res ← fwdC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s1 q1
            (mkCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) hc lct epNext (some pt))
          return (none, sStop)
      else
        return (none, sStop)
    else
      _tr ← query (I := SIface) SM.SMTag.tr
        (q1, ((Expr.op (O := OO) SimOp.emptyLPub (),
          Expr.op (O := OO) SimOp.defaultPlain ()), none))
      match T?0 with
      | none => return (none, sStop)
      | some pt =>
        let hc := honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s1 q1 w1
        let epPlus2 := pGet (mEpoch (ssMir s1)) q1 + 2
        _res ← fwdC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s1 q1
          (mkCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) hc lct epPlus2 (some pt))
        return (none, sStop)

/-- `LibsignalSim.simRecv` in `ReductionDsl` with list-scan bound `K`; meta-level matching on `k`
keeps static query weight `1` when `k = none`. -/
def simRecvC (K qep : ℕ) (k : Option ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (w : Expr OO Γ (.base .wire)) (isDel : Expr OO Γ .bool) :
    Comp OO SIface Γ (.prod (.opt (simRrTy PQ PQC Pt ℓ)) simStateTy) :=
  let newChainBranch :
      Comp OO SIface
        (parsedRecvTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) ::
          .prod simStateTy (.prod .bool (.prod (.base .wire) .bool)) :: Γ)
        (.prod (.opt (simRrTy PQ PQC Pt ℓ)) simStateTy) :=
    match k with
    | none =>
      simRecvNewChainNormalC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K qep
    | some k₀ =>
      rdsl [_, (s1, (q1, _))] do
        if ambCondE (P := P) (Dh := Dh) (encT := encT) (decT := decT) s1 q1 &&
            ssAmb s1 == nat k₀ then
          simRecvNewChainStopC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
        else
          simRecvNewChainNormalC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K qep
  rdsl do
    (s0, (q0, (w0, del0))) ← return (s, (qParty, (w, isDel)))
    let inTrOpt :=
      mInTransitE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K (ssMir s0) (otherE q0) w0
    let refuse :=
      orE (mWin (ssMir s0))
        (orE (del0 && !(isSomeE inTrOpt))
          ((!del0) &&
            (orE (isSomeE inTrOpt)
              (orE (!(mSafeInjE (ssMir s0)))
                (!(Expr.op (O := OO) SimOp.injOK w0))))))
    if refuse then
      return (none, s0)
    else
      match parseRecvE (P := P) (Dh := Dh) (encT := encT) (decT := decT) (raw (2 ^ 32))
          (q0, (pGet (ssPq s0) q0, w0)) with
      | none => return (some (.inl ()), s0)
      | some (pq', (i1, (pk0, (T?0, lct1)))) =>
        let hc := honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s0 q0 w0
        match findChainE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (pGet (ssChains s0) q0, pk0) with
        | none =>
          if evictedHonestE (P := P) (Dh := Dh) (encT := encT) (decT := decT) s0 q0 hc then
            return (some (.inl ()), s0)
          else if Expr.op (O := OO) SimOp.isZeroPt T?0 then
            return (some (.inl ()), s0)
          else
            raw newChainBranch
        | some (ci1, g0) =>
          if Expr.op (O := OO) SimOp.chainRejects (g0.2.2, i1) then
            return (some (.inl ()), s0)
          else
            res ← fwdC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s0 q0
              (mkCE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
                hc lct1 g0.2.1 T?0)
            return onAnswerE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K qep
              s0 q0 w0 del0 (some ci1) pk0 pq' res

def simCorrC (K : ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool) :
    Comp OO SIface Γ (.prod (.opt (.base .ghostSt)) simStateTy) :=
  rdsl do
    (s0, q0) ← return (s, qParty)
    let refuse :=
      orE (mWin (ssMir s0))
        (orE (!(mCorrAllowedE K (ssMir s0) q0))
          (orE (mInWinE (ssMir s0) q0)
            (!(mNoSpkCorrE (ssMir s0) q0))))
    if refuse then
      return (none, s0)
    else
      crOpt ← query (I := SIface) SM.SMTag.cr q0
      match crOpt with
      | none => return (none, s0)
      | some st =>
        let chains' :=
          if q0 && (mEpoch (ssMir s0)).2 == 0 then
            (revealSpkChainsE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
              ((ssChains s0).1, st),
             (ssChains s0).2)
          else
            ssChains s0
        let nextSt :=
          ssMk (mAfterCorrE K (ssMir s0) q0)
            (ssPq s0) (ssPn s0) (ssUnackA s0) (ssHonest s0) chains'
            (ssAmb s0) (ssStopped s0)
        let ghostOut :=
          toGhostE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (q0,
              (st,
                (pGet (ssPn s0) q0,
                  (pGet chains' q0,
                    (ssUnackA s0,
                      (pGet (ssPq s0) q0,
                        pGet (mEpoch (ssMir s0)) q0))))))
        return (some ghostOut, nextSt)

/-- Combined 5-oracle dispatcher for `LibsignalSim.simImpl` in `ReductionDsl`. -/
def simHandleC (K qep : ℕ) (k : Option ℕ) :
    Comp OO SIface
      [simStateTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ),
       (simCodec PQ PQC Pt ℓ).Q]
      (.prod (simCodec PQ PQC Pt ℓ).R
        (simStateTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ))) :=
  rdsl [s, qry] do
    match qry with
    | .transmit (qp, (m₀, r)) =>
      (out, s') ← guardC (P := P) (Dh := Dh) (encT := encT) (decT := decT) s
        (simSendC (P := P) (Dh := Dh) (encT := encT) (decT := decT) qep s qp m₀ none r)
      return (.inl (.inl (.inl (.inl out))), s')
    | .challenge (qp, (m₀, (m₁, r))) =>
      (out, s') ← guardC (P := P) (Dh := Dh) (encT := encT) (decT := decT) s
        (simSendC (P := P) (Dh := Dh) (encT := encT) (decT := decT) qep s qp m₀ (some m₁) r)
      return (.inl (.inl (.inl (.inr out))), s')
    | .deliver (qp, w) =>
      (out, s') ← guardC (P := P) (Dh := Dh) (encT := encT) (decT := decT) s
        (simRecvC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K qep (raw k) s qp w true)
      return (.inl (.inl (.inr out)), s')
    | .inject (qp, w) =>
      (out, s') ← guardC (P := P) (Dh := Dh) (encT := encT) (decT := decT) s
        (simRecvC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K qep (raw k) s qp w false)
      return (.inl (.inr out), s')
    | .corrupt qp =>
      (out, s') ← guardC (P := P) (Dh := Dh) (encT := encT) (decT := decT) s
        (simCorrC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s qp)
      return (.inr out, s')

def initSimE {Γ} (pqA pqB : Expr OO Γ (.base .pq)) : Expr OO Γ simStateTy :=
  ssMk initSimMirE
    (.pair pqA pqB)
    (.pair (Expr.op (O := OO) SimOp.zeroU32 .unit) (Expr.op (O := OO) SimOp.zeroU32 .unit))
    (.bool true)
    .nil
    (.pair (.cons (initChainAE (P := P) (Dh := Dh) (encT := encT) (decT := decT)) .nil) .nil)
    (.nat 0)
    (.bool false)

def simInitC :
    Comp OO SIface [.unit]
      (.prod .unit (simStateTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ))) :=
  rdsl [_] do
    pqrKey ← sample (I := SIface) (UniformSamplerTag.base SimBaseSamp.bv256) ()
    return ((),
      initSimE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
        (Expr.op (O := OO) SimOp.spqrInitA pqrKey)
        (Expr.op (O := OO) SimOp.spqrInitB pqrKey))

def simFinishC (k : Option ℕ) :
    Comp OO SIface
      [simStateTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ), .bool] .bool :=
  match k with
  | none => rdsl [_, b'] do return b'
  | some _ => rdsl [_, _] do sample (I := SIface) UniformSamplerTag.bool ()

/-- Costed `CostedReduction` for `LibsignalSim.simRun` with list-scan bound `K`. -/
@[reducible] def simRunProg (K qep : ℕ) (k : Option ℕ) :
    CostedReduction OO SIface
      (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (simCodec PQ PQC Pt ℓ) .unit .unit .bool .bool where
  σ := simStateTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ)
  init := simInitC P Dh encT decT
  handle := simHandleC P Dh encT decT K qep k
  finish := simFinishC P Dh encT decT k

/-- Costed `CostedReduction` for `Refine.sim` (`simRunProg` at `k = none`). -/
@[reducible] def simProg (K qep : ℕ) :
    CostedReduction OO SIface
      (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (simCodec PQ PQC Pt ℓ) .unit .unit .bool .bool :=
  simRunProg P Dh encT decT K qep none

end HandlersAndProg

/-! ## Step-level and full reduction evaluation agreement -/

section EvalAgreement

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)

local notation "S" => simSig PQ PQC Pt ℓ
local notation "OO" => simOps (ℓ := ℓ) P Dh encT decT
local notation "SIface" => simIface PQ PQC Pt ℓ

theorem comp_eval_bind_ret {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι} {I : Iface S' T}
    {Γ} {t u : Ty S'} (e : Expr O' Γ t) (k : Comp O' I (t :: Γ) u) (ρ : Env Γ) :
    (Comp.bind (.ret e) k).eval ρ = k.eval (Env.cons (e.eval ρ) ρ) :=
  pure_bind (e.eval ρ) (fun x => k.eval (Env.cons x ρ))

theorem comp_eval_ite {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι} {I : Iface S' T}
    {Γ} {t : Ty S'} (c : Expr O' Γ .bool) (th el : Comp O' I Γ t) (ρ : Env Γ) :
    (Comp.ite c th el).eval ρ = if c.eval ρ then th.eval ρ else el.eval ρ := rfl

theorem comp_eval_bind {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι} {I : Iface S' T}
    {Γ} {t u : Ty S'} (m : Comp O' I Γ t) (k : Comp O' I (t :: Γ) u) (ρ : Env Γ) :
    (Comp.bind m k).eval ρ = (m.eval ρ >>= fun x => k.eval (Env.cons x ρ)) := rfl

theorem comp_eval_caseOpt {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι} {I : Iface S' T}
    {Γ} {t u : Ty S'} (e : Expr O' Γ (.opt t))
    (noneB : Comp O' I Γ u) (someB : Comp O' I (t :: Γ) u) (ρ : Env Γ) :
    (Comp.caseOpt e noneB someB).eval ρ =
      match e.eval ρ with
      | none => noneB.eval ρ
      | some x => someB.eval (Env.cons x ρ) := by
  rcases h : e.eval ρ with _ | x <;> simp [Comp.eval, h]

theorem comp_eval_caseOpt_v0_some {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι}
    {I : Iface S' T} {Γ} {t u : Ty S'} (x : t.denote)
    (noneB : Comp O' I (.opt t :: Γ) u) (someB : Comp O' I (t :: .opt t :: Γ) u) (ρ : Env Γ) :
    (Comp.caseOpt .v0 noneB someB).eval (Env.cons (t := .opt t) (some x) ρ) =
      someB.eval (Env.cons (t := t) x (Env.cons (t := .opt t) (some x) ρ)) := rfl

theorem comp_eval_ret {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι} {I : Iface S' T}
    {Γ} {t : Ty S'} (e : Expr O' Γ t) (ρ : Env Γ) :
    (Comp.ret (I := I) e).eval ρ = pure (e.eval ρ) := rfl

/-- List-length bounds on `SimState PQ Pt ℓ` required for `K`-bounded `LibsignalSim` handlers. -/
structure SimStateBounded (K : ℕ) (s : SimState PQ Pt ℓ) : Prop where
  trans_le : s.mir.trans.length ≤ K
  chall_le : s.mir.chall.length ≤ K
  honest_le : s.honest.length ≤ K
  comp_u : ∃ U : List Pos, U.length ≤ K ∧ CountLe s.mir.comp U ∧ ∀ r ∈ s.mir.trans, r.pos ∈ U
  chainsA_le : (s.chains .A).length ≤ 5
  chainsB_le : (s.chains .B).length ≤ 5

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem SimStateBounded.comp_le {K : ℕ} {s : SimState PQ Pt ℓ}
    (h : SimStateBounded K s) : s.mir.comp.length ≤ K := by
  rcases h.comp_u with ⟨U, hUK, hCU, -⟩
  exact (countLe_length_le hCU).trans hUK

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem SimStateBounded.chains_le {K : ℕ} {s : SimState PQ Pt ℓ}
    (h : SimStateBounded K s) (Q : Party) : (s.chains Q).length ≤ 5 := by
  cases Q
  · exact h.chainsA_le
  · exact h.chainsB_le

/-- Query-budget invariant on `simStateTy.denote` with `m` adversary game queries remaining. -/
def SimBoundInv (K m : ℕ) (v : (@simStateTy PQ PQC Pt ℓ).denote) : Prop :=
  let s := simStateDec v
  s.mir.trans.length + m ≤ K ∧ s.mir.chall.length + m ≤ K ∧
  s.honest.length + m ≤ K ∧
  (∃ U : List Pos, U.length + m ≤ K ∧ CountLe s.mir.comp U ∧ ∀ r ∈ s.mir.trans, r.pos ∈ U) ∧
  (s.chains .A).length ≤ 5 ∧ (s.chains .B).length ≤ 5

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem SimBoundInv.mono {K m₁ m₂ : ℕ} {v : (@simStateTy PQ PQC Pt ℓ).denote}
    (hle : m₁ ≤ m₂) (h : SimBoundInv K m₂ v) : SimBoundInv K m₁ v := by
  rcases h.2.2.2.1 with ⟨U, hUlen, hCU, htrU⟩
  exact ⟨by have := h.1; omega, by have := h.2.1; omega, by have := h.2.2.1; omega,
    ⟨U, by omega, hCU, htrU⟩, h.2.2.2.2.1, h.2.2.2.2.2⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem SimBoundInv.toBounded {K m : ℕ} {v : (@simStateTy PQ PQC Pt ℓ).denote}
    (h : SimBoundInv K m v) : SimStateBounded K (simStateDec v) := by
  rcases h.2.2.2.1 with ⟨U, hUlen, hCU, htrU⟩
  exact ⟨by have := h.1; omega, by have := h.2.1; omega,
    by have := h.2.2.1; omega, ⟨U, by omega, hCU, htrU⟩,
    h.2.2.2.2.1, h.2.2.2.2.2⟩

@[simp] theorem query_tr_eval {Γ}
    (e : Expr OO Γ (.prod .bool (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base .bv256)))))
    (ρ : Env Γ) :
    (Comp.query (I := SIface) SM.SMTag.tr e).eval ρ =
      SM.transmitQuery (St := Fig8St Pt)
        (partyDec (e.eval ρ).1) (e.eval ρ).2.1 (e.eval ρ).2.2 := by
  simp [Comp.eval, simIface, simParamIface, SM.transmitQuery]

@[simp] theorem query_ch_eval {Γ}
    (e : Expr OO Γ (.prod .bool
      (.prod (lpubPlainTy PQ PQC Pt ℓ)
        (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base .bv256))))))
    (ρ : Env Γ) :
    (Comp.query (I := SIface) SM.SMTag.ch e).eval ρ =
      SM.challQuery (St := Fig8St Pt)
        (partyDec (e.eval ρ).1) (e.eval ρ).2.1 (e.eval ρ).2.2.1 (e.eval ρ).2.2.2 := by
  simp [Comp.eval, simIface, simParamIface, SM.challQuery]

@[simp] theorem query_dl_eval {Γ}
    (e : Expr OO Γ (.prod .bool (fig8CTy PQ PQC Pt ℓ))) (ρ : Env Γ) :
    (Comp.query (I := SIface) SM.SMTag.dl e).eval ρ =
      Option.map SM.smRrEnc <$>
        SM.deliverQuery (St := Fig8St Pt) (Coins := BitVec 256)
          (partyDec (e.eval ρ).1) (e.eval ρ).2 := by
  simp [Comp.eval, simIface, simParamIface, SM.deliverQuery]

@[simp] theorem query_ij_eval {Γ}
    (e : Expr OO Γ (.prod .bool (fig8CTy PQ PQC Pt ℓ))) (ρ : Env Γ) :
    (Comp.query (I := SIface) SM.SMTag.ij e).eval ρ =
      Option.map SM.smRrEnc <$>
        SM.injectQuery (St := Fig8St Pt) (Coins := BitVec 256)
          (partyDec (e.eval ρ).1) (e.eval ρ).2 := by
  simp [Comp.eval, simIface, simParamIface, SM.injectQuery]

@[simp] theorem query_cr_eval {Γ}
    (e : Expr OO Γ .bool) (ρ : Env Γ) :
    (Comp.query (I := SIface) SM.SMTag.cr e).eval ρ =
      SM.corrQuery (St := Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt)
        (partyDec (e.eval ρ)) := by
  simp [Comp.eval, simIface, simParamIface, SM.corrQuery]

@[simp] theorem sample_pqc_eval {Γ} (e : Expr OO Γ .unit) (ρ : Env Γ) :
    (Comp.sample (I := SIface) (UniformSamplerTag.base SimBaseSamp.pqc) e).eval ρ =
      (liftM ($ᵗ PQC : ProbComp PQC) : Fig8Comp Pt ℓ PQC) := rfl

@[simp] theorem sample_bv256_eval {Γ} (e : Expr OO Γ .unit) (ρ : Env Γ) :
    (Comp.sample (I := SIface) (UniformSamplerTag.base SimBaseSamp.bv256) e).eval ρ =
      (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256)) := rfl

@[simp] theorem sample_bool_eval {Γ} (e : Expr OO Γ .unit) (ρ : Env Γ) :
    (Comp.sample (I := SIface) UniformSamplerTag.bool e).eval ρ =
      (liftM ($ᵗ Bool : ProbComp Bool) : Fig8Comp Pt ℓ Bool) := rfl

@[simp] theorem stateT_lift_run {m : Type → Type} [Monad m] {σ α : Type}
    (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

@[simp] theorem ghostChainEnc_accept (g : GhostChain) (i : ℕ) :
    ghostChainEnc (g.accept i) =
      ((ghostChainEnc g).1, ((ghostChainEnc g).2.1, simChainAccept (ghostChainEnc g).2.2 i)) := by
  unfold GhostChain.accept simChainAccept ghostChainEnc
  split_ifs <;> rfl

@[simp] theorem simChainRejects_ghostChainEnc (g : GhostChain) (i : ℕ) :
    simChainRejects (ghostChainEnc g).2.2 i = g.rejects i := rfl

private theorem getD_map {α β : Type} (f : α → β) (xs : List α) (i : ℕ) (d : α) :
    (xs.map f).getD i (f d) = f (xs.getD i d) := by
  induction xs generalizing i with
  | nil => rfl
  | cons a as ih =>
    cases i with
    | zero => rfl
    | succ i' => exact ih i'

private theorem findIdx?_map {α β : Type} (f : α → β) (p : β → Bool) (xs : List α) :
    (xs.map f).findIdx? p = xs.findIdx? (fun x => p (f x)) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.findIdx?_cons, ih]

theorem simFindChain_map_ghostChainEnc (cs : List GhostChain) (pk : PublicKey) :
    simFindChain (cs.map ghostChainEnc) pk =
      match cs.findIdx? (fun g => g.key == some pk) with
      | some ci => some (ci, ghostChainEnc (cs.getD ci ⟨none, 0, 0, []⟩))
      | none => none := by
  unfold simFindChain
  rw [findIdx?_map]
  have hfn : (fun x : GhostChain => (ghostChainEnc x).1 == some pk) =
      (fun g : GhostChain => g.key == some pk) := rfl
  rw [hfn]
  cases cs.findIdx? (fun g => g.key == some pk) with
  | none => rfl
  | some ci =>
    exact congrArg (fun x => some (ci, x)) (getD_map ghostChainEnc cs ci ⟨none, 0, 0, []⟩)

private theorem modify_map {α β : Type} (f : α → β) (g : α → α) (h : β → β)
    (hfg : ∀ x, h (f x) = f (g x)) (xs : List α) (ci : ℕ) :
    (xs.map f).modify ci h = (xs.modify ci g).map f := by
  induction xs generalizing ci with
  | nil => simp
  | cons a as ih =>
    cases ci with
    | zero => simp [hfg]
    | succ ci' => simp [ih]

theorem simModifyChainAccept_map_ghostChainEnc (cs : List GhostChain) (ci i : ℕ) :
    simModifyChainAccept (cs.map ghostChainEnc) ci i =
      (cs.modify ci (·.accept i)).map ghostChainEnc :=
  modify_map ghostChainEnc (·.accept i)
    (fun g => (g.1, (g.2.1, simChainAccept g.2.2 i)))
    (fun g => (ghostChainEnc_accept g i).symm) cs ci

theorem simPushChain_map_ghostChainEnc (cs : List GhostChain) (T : PublicKey) (t i : ℕ) :
    simPushChain (cs.map ghostChainEnc) T t i =
      (pushChain cs (GhostChain.accept ⟨some T, t, 0, []⟩ i)).map ghostChainEnc := by
  dsimp only [simPushChain, pushChain]
  have hg : [(some T, (t, simChainAccept (0, []) i))] =
      [GhostChain.accept ⟨some T, t, 0, []⟩ i].map ghostChainEnc :=
    congrArg (· :: []) (ghostChainEnc_accept ⟨some T, t, 0, []⟩ i).symm
  rw [hg, ← List.map_append, ← List.map_drop, List.length_map, List.length_append]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem simRevealSpkChains_map_ghostChainEnc (csA : List GhostChain) (st : Fig8St Pt) :
    simRevealSpkChains Dh encT (csA.map ghostChainEnc) st =
      (match st.γ with
       | .exp x =>
         csA.map fun (g : GhostChain) =>
           if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g
       | _ => csA).map ghostChainEnc := by
  unfold simRevealSpkChains
  rcases st.γ with _ | x
  · rfl
  · simp only [List.map_map, Function.comp_def]
    congr 1; funext g
    rcases g with ⟨_ | k, ep, ls, sk⟩ <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem simToGhost_eq (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt) :
    simToGhost P (partyEnc Q) st (s.pn Q) ((s.chains Q).map ghostChainEnc)
      s.unackA (s.pq Q) (s.mir.epoch Q) =
    toGhost P s Q st := by
  unfold simToGhost toGhost
  simp only [partyDec_partyEnc, List.map_map, Function.comp_def]
  have hfn :
      (fun x : GhostChain =>
        simMkRecvChain (ghostChainEnc x).1 (ghostChainEnc x).2.2
          (st.vR (ghostChainEnc x).2.1)) =
      (fun g : GhostChain =>
        match st.vR g.epoch with
        | some v =>
          ⟨g.key.getD dummyKey, some ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩,
            g.skipped.filterMap fun j =>
              (v.skippedKeys.lookup j).map fun mk =>
                ⟨keyToBytes32 mk, BitVec.ofNat 32 (j - 1)⟩⟩
        | none => ⟨g.key.getD dummyKey, none, []⟩) := by
    funext g; rcases g with ⟨_ | k, ep, ls, sk⟩ <;> rfl
  rw [hfn]; rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem simSpqrSendPub_eq (s : SimState PQ Pt ℓ) (Q : Party) (rq : PQC) (pn : BitVec 32) :
    simSpqrSendPub P (partyEnc Q) s.unackA (s.pq Q) rq pn =
    mkPub P s Q rq pn := by
  simp [simSpqrSendPub, mkPub, partyDec_partyEnc]

omit [SampleableType PQC] in
@[simp] theorem initChainAE_eval {Γ : List (Ty S)} (ρ : Env Γ) :
    (initChainAE (ℓ := ℓ) (P := P) (Dh := Dh) (encT := encT) (decT := decT)).eval ρ =
      ghostChainEnc ⟨none, 0, 0, []⟩ :=
  rfl

omit [SampleableType PQC] in
theorem hasUnknownKeyE_eval {Γ}
    (cs : Expr OO Γ (.list (ghostChainTy PQ PQC Pt ℓ))) (ρ : Env Γ)
    (xs : List GhostChain) (hxs : xs.length ≤ 5)
    (hcs : cs.eval ρ = xs.map ghostChainEnc) :
    (hasUnknownKeyE (P := P) (Dh := Dh) (encT := encT) (decT := decT) cs).eval ρ =
      xs.any (·.key.isNone) := by
  unfold hasUnknownKeyE
  have htake : (xs.map ghostChainEnc).take 5 = xs.map ghostChainEnc :=
    List.take_of_length_le (by simp [hxs])
  simp only [Expr.eval, hcs, htake, List.any_map, Function.comp_def]
  congr 1; funext g
  rcases g with ⟨_ | k, ep, ls, sk⟩ <;> rfl

private theorem foldr_findChain (cs : List (Option PublicKey × (ℕ × (ℕ × List ℕ))))
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
theorem findChainE_eval {Γ}
    (arg : Expr OO Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.base .pk))) (ρ : Env Γ)
    (cs : List (Option PublicKey × (ℕ × (ℕ × List ℕ)))) (pk : PublicKey)
    (hcs : cs.length ≤ 5) (harg : arg.eval ρ = (cs, pk)) :
    (findChainE (P := P) (Dh := Dh) (encT := encT) (decT := decT) arg).eval ρ =
      simFindChain cs pk := by
  unfold findChainE
  rw [letE_eval, harg]
  have htake : cs.take 5 = cs := List.take_of_length_le hcs
  simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v3, Env.get, htake, simOps]
  rw [← foldr_findChain cs pk]
  congr 1; funext x acc
  rcases x with ⟨_ | k, rest⟩ <;> rcases acc with _ | ⟨ci, g⟩ <;> rfl

private theorem foldr_modify_noop {α : Type} (f : α → α) (xs : List α) (c L : ℕ)
    (hle : xs.length + c ≤ L) :
    xs.foldr
      (fun x acc => (if decide (acc.length + c = L) then f x else x) :: acc)
      [] = xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.length_cons] at hle
    have htail := ih (by omega)
    simp only [List.foldr_cons, htail]
    have hne : ¬ (as.length + c = L) := by omega
    simp [hne]

private theorem foldr_modify {α : Type} (f : α → α) (xs : List α) (ci : ℕ) :
    xs.foldr
      (fun x acc => (if decide (acc.length + (ci + 1) = xs.length) then f x else x) :: acc)
      [] =
    xs.modify ci f := by
  induction xs generalizing ci with
  | nil => simp
  | cons a as ih =>
    cases ci with
    | zero =>
      simp only [List.foldr_cons, List.length_cons, Nat.zero_add, List.modify_cons]
      have htail := foldr_modify_noop f as 1 (as.length + 1) (by omega)
      rw [htail]
      simp
    | succ ci' =>
      simp only [List.foldr_cons, List.length_cons]
      have hstep :
          (fun x (acc : List α) =>
            (if decide (acc.length + (ci' + 1 + 1) = as.length + 1) then f x else x) :: acc) =
          (fun x (acc : List α) =>
            (if decide (acc.length + (ci' + 1) = as.length) then f x else x) :: acc) := by
        funext x acc
        have heq : decide (acc.length + (ci' + 1 + 1) = as.length + 1) =
            decide (acc.length + (ci' + 1) = as.length) := by
          simp only [decide_eq_decide]; omega
        rw [heq]
      rw [hstep, ih ci']
      have hne : ¬ ((as.modify ci' f).length + (ci' + 1 + 1) = as.length + 1) := by
        rw [List.length_modify]; omega
      simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte]
      rfl

omit [SampleableType PQC] in
theorem modifyChainAcceptE_eval {Γ}
    (arg : Expr OO Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.prod .nat .nat)))
    (ρ : Env Γ)
    (cs : List (Option PublicKey × (ℕ × (ℕ × List ℕ)))) (ci i : ℕ)
    (hcs : cs.length ≤ 5) (harg : arg.eval ρ = (cs, (ci, i))) :
    (modifyChainAcceptE (P := P) (Dh := Dh) (encT := encT) (decT := decT) arg).eval ρ =
      simModifyChainAccept cs ci i := by
  unfold modifyChainAcceptE simModifyChainAccept
  rw [letE_eval, harg]
  have htake : cs.take 5 = cs := List.take_of_length_le hcs
  simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, htake, simOps]
  exact foldr_modify (fun g => (g.1, (g.2.1, simChainAccept g.2.2 i))) cs ci

private theorem foldr_pushChain {α : Type} (cs : List α) (g : α) (hcs : cs.length ≤ 5) :
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
theorem pushChainE_eval {Γ}
    (arg : Expr OO Γ
      (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.prod (.base .pk) (.prod .nat .nat))))
    (ρ : Env Γ)
    (cs : List (Option PublicKey × (ℕ × (ℕ × List ℕ)))) (T : PublicKey) (t i : ℕ)
    (hcs : cs.length ≤ 5) (harg : arg.eval ρ = (cs, (T, (t, i)))) :
    (pushChainE (P := P) (Dh := Dh) (encT := encT) (decT := decT) arg).eval ρ =
      simPushChain cs T t i := by
  unfold pushChainE simPushChain
  rw [letE_eval, harg]
  have htake : cs.take 5 = cs := List.take_of_length_le hcs
  simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, htake, simOps]
  exact foldr_pushChain cs (some T, (t, simChainAccept (0, []) i)) hcs

omit [SampleableType PQC] in
theorem revealSpkChainsE_eval {Γ}
    (arg : Expr OO Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.base .fig8st))) (ρ : Env Γ)
    (csA : List (Option PublicKey × (ℕ × (ℕ × List ℕ)))) (st : SimFig8St Pt)
    (hcsA : csA.length ≤ 5) (harg : arg.eval ρ = (csA, st)) :
    (revealSpkChainsE (P := P) (Dh := Dh) (encT := encT) (decT := decT) arg).eval ρ =
      simRevealSpkChains Dh encT csA st := by
  unfold revealSpkChainsE simRevealSpkChains
  rw [letE_eval, harg]
  have htake : csA.take 5 = csA := List.take_of_length_le hcsA
  simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, simOps]
  rcases st.γ with _ | x
  · rfl
  · simp only [htake]
    congr 1; funext g
    rcases g with ⟨_ | k, rest⟩ <;> rfl

omit [SampleableType PQC] in
theorem spqrSendPubE_eval {Γ}
    (arg : Expr OO Γ
      (.prod .bool (.prod .bool (.prod (.base .pq) (.prod (.base .pqc) (.base .u32))))))
    (ρ : Env Γ)
    (qB unackA : Bool) (pq : PQ) (rq : PQC) (pn : BitVec 32)
    (harg : arg.eval ρ = (qB, (unackA, (pq, (rq, pn))))) :
    (spqrSendPubE (P := P) (Dh := Dh) (encT := encT) (decT := decT) arg).eval ρ =
      simSpqrSendPub P qB unackA pq rq pn := by
  unfold spqrSendPubE simSpqrSendPub
  rw [letE_eval, harg]
  simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, simOps]
  rcases P.spqr.send pq rq with _ | ⟨pq', salt?, pqm⟩
  · rfl
  · cases qB <;> cases unackA <;> rfl

omit [SampleableType PQC] in
theorem parseRecvE_eval (B : ℕ) {Γ}
    (arg : Expr OO Γ (.prod .bool (.prod (.base .pq) (.base .wire)))) (ρ : Env Γ)
    (qB : Bool) (pq : PQ) (w : List (BitVec 8))
    (harg : arg.eval ρ = (qB, (pq, w))) :
    (parseRecvE (P := P) (Dh := Dh) (encT := encT) (decT := decT) B arg).eval ρ =
      simParseRecv P decT B qB pq w := by
  unfold parseRecvE simParseRecv
  rw [letE_eval, harg]
  simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, simOps,
    simSplitWireTag, simParseWire]
  by_cases hlen : w.length < 9
  · simp [hlen]
  · simp only [hlen, ↓reduceIte]
    rcases hwire : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, rest⟩
    · rfl
    · cases qB
      · by_cases hok : addressCheckPasses h.addresses (P.expectedAddrs .A) = true
        · simp only [hok, partyDec, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.map]
          rcases P.spqr.recv pq h.pqRatchet with err | ⟨pq', salt⟩ <;> rfl
        · simp [hok, partyDec]
      · by_cases hok : addressCheckPasses h.addresses (P.expectedAddrs .B) = true
        · simp only [hok, partyDec, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.map]
          rcases P.spqr.recv pq h.pqRatchet with err | ⟨pq', salt⟩ <;> rfl
        · simp [hok, partyDec]

omit [SampleableType PQC] in
theorem toGhostE_eval {Γ}
    (arg : Expr OO Γ
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
    (toGhostE (P := P) (Dh := Dh) (encT := encT) (decT := decT) arg).eval ρ =
      simToGhost P qB st pn cs unackA pq ep := by
  unfold toGhostE simToGhost
  rw [letE_eval, harg]
  have htake : cs.take 5 = cs := List.take_of_length_le hcs
  simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, htake, simOps,
    simMkGhostState, simMkSenderChain]
  rcases st.γ with _ | x <;> rcases st.vS with _ | v <;> cases qB <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem pGet_eval {S' : Sig} {O' : Ops S'} {Γ} {t : Ty S'}
    (pr : Expr O' Γ (.prod t t)) (p : Expr O' Γ .bool) (ρ : Env Γ) :
    (pGet pr p).eval ρ = if p.eval ρ then (pr.eval ρ).2 else (pr.eval ρ).1 := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem pSet_eval {S' : Sig} {O' : Ops S'} {Γ} {t : Ty S'}
    (pr : Expr O' Γ (.prod t t)) (p : Expr O' Γ .bool) (v : Expr O' Γ t) (ρ : Env Γ) :
    (pSet pr p v).eval ρ =
      if p.eval ρ then ((pr.eval ρ).1, v.eval ρ) else (v.eval ρ, (pr.eval ρ).2) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem expr_caseOpt_eval {S' : Sig} {O' : Ops S'} {Γ} {t u : Ty S'}
    (e : Expr O' Γ (.opt t)) (noneB : Expr O' Γ u) (someB : Expr O' (t :: Γ) u) (ρ : Env Γ) :
    (Expr.caseOpt e noneB someB).eval ρ =
      match e.eval ρ with
      | none => noneB.eval ρ
      | some x => someB.eval (Env.cons x ρ) := by
  rcases h : e.eval ρ with _ | x <;> simp [Expr.eval, h]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem expr_pair_eval {S' : Sig} {O' : Ops S'} {Γ} {t u : Ty S'}
    (a : Expr O' Γ t) (b : Expr O' Γ u) (ρ : Env Γ) :
    (Expr.pair a b).eval ρ = (a.eval ρ, b.eval ρ) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem expr_some_eval {S' : Sig} {O' : Ops S'} {Γ} {t : Ty S'}
    (a : Expr O' Γ t) (ρ : Env Γ) :
    (Expr.some a).eval ρ = some (a.eval ρ) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp] theorem ssSetMir_eval {O' : Ops S} {Γ}
    (s : Expr O' Γ simStateTy) (m : Expr O' Γ simMirTy) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (mir' : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (hs : s.eval ρ = simStateEnc st) (hm : m.eval ρ = simMirEnc mir') :
    (ssSetMir s m).eval ρ = simStateEnc { st with mir := mir' } := by
  simp [ssSetMir, ssMk, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped,
    hs, hm, simStateEnc, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp] theorem ssSetAmb_eval {O' : Ops S} {Γ}
    (s : Expr O' Γ simStateTy) (a : Expr O' Γ .nat) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (hs : s.eval ρ = simStateEnc st) :
    (ssSetAmb s a).eval ρ = simStateEnc { st with amb := a.eval ρ } := by
  simp [ssSetAmb, ssMk, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssStopped,
    hs, simStateEnc, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp] theorem ssSetStopped_eval {O' : Ops S} {Γ}
    (s : Expr O' Γ simStateTy) (stp : Expr O' Γ .bool) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (hs : s.eval ρ = simStateEnc st) :
    (ssSetStopped s stp).eval ρ = simStateEnc { st with stopped := stp.eval ρ } := by
  simp [ssSetStopped, ssMk, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb,
    hs, simStateEnc, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp] theorem ssSetMirWin_eval {O' : Ops S} {Γ}
    (s : Expr O' Γ simStateTy) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (hs : s.eval ρ = simStateEnc st) :
    (ssSetMirWin s).eval ρ = simStateEnc { st with mir := { st.mir with win := true } } := by
  simp [ssSetMirWin, mSetWin, ssMk, mMk, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains,
    ssAmb, ssStopped, mB, mEpoch, mIdx, mTL, mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs,
    hs, simStateEnc, simMirEnc, Expr.eval, Expr.v0]

theorem guardC_eval {Γ t} (s : Expr OO Γ simStateTy)
    (body : Comp OO SIface Γ (.prod (.opt t) simStateTy))
    (ρ : Env Γ) (st : SimState PQ Pt ℓ) {α : Type}
    (f : Option α → Option t.denote)
    (m : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α))
    (hs : s.eval ρ = simStateEnc st)
    (hf : f none = none)
    (hbody : body.eval ρ = Prod.map f simStateEnc <$> m.run st) :
    (guardC (P := P) (Dh := Dh) (encT := encT) (decT := decT) s body).eval ρ =
      Prod.map f simStateEnc <$> ((«guard» m).run st) := by
  unfold guardC «guard»
  rw [comp_eval_ite]
  have hstp : (ssStopped s).eval ρ = st.stopped := by
    simp [ssStopped, Expr.eval, hs, simStateEnc]
  rw [hstp]
  cases h : st.stopped
  · simp [h, hbody, StateT.run_bind, StateT.run_get]
  · simp [h, comp_eval_ret, hs, hf, StateT.run_bind, StateT.run_get, StateT.run_pure,
      Prod.map, Expr.eval]

theorem simDrawSendCoinsC_eval {Γ} (r : Expr OO Γ (.opt (.base .pqc))) (ρ : Env Γ) :
    (simDrawSendCoinsC (P := P) (Dh := Dh) (encT := encT) (decT := decT) r).eval ρ =
      (match r.eval ρ with
       | none => do
         let rq ← (liftM ($ᵗ PQC : ProbComp PQC) : Fig8Comp Pt ℓ PQC)
         pure (rq, none)
       | some rq => do
         let c ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
         pure (rq, some c)) := by
  unfold simDrawSendCoinsC
  rw [comp_eval_caseOpt]
  rcases r.eval ρ with _ | rq <;>
    (simp [comp_eval_bind, comp_eval_ret, map_eq_bind_pure_comp, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, Env.get_cons_succ]; rfl)

theorem simSendPostQueryC_eval {Γ}
    (ρ : Env Γ) (st : SimState PQ Pt ℓ) (Q : Party)
    (m₀ : Plain ℓ) (chal₀ : Option (Plain ℓ)) (r₀ : Option PQC)
    (s₁ : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (rq : PQC) (rc : Option (BitVec 256)) (pq' : PQ) (pub : LibsignalMsgPublicPart)
    (res : Option (Fig8C Pt)) :
    (simSendPostQueryC (P := P) (Dh := Dh) (encT := encT) (decT := decT)).eval
      (Env.cons (t := .opt (fig8CTy PQ PQC Pt ℓ)) res
        (Env.cons (t := .prod (.base SimSort.pq) (.base SimSort.lpub)) (pq', pub)
          (Env.cons (t := .prod (.base SimSort.pqc) (.opt (.base SimSort.bv256))) (rq, rc)
            (Env.cons (t := simMirTy) (simMirEnc s₁)
              (Env.cons
                (t := .prod simStateTy
                  (.prod .bool (.prod (.base SimSort.plain)
                    (.prod (.opt (.base SimSort.plain)) (.opt (.base SimSort.pqc))))))
                (simStateEnc st, partyEnc Q, m₀, chal₀, r₀) ρ))))) =
      Prod.map id simStateEnc <$>
        ((match res with
          | none => return none
          | some c =>
            let pn := if s₁.epoch Q ≠ st.mir.epoch Q then
              BitVec.ofNat 32 (st.mir.idx Q - 1) else st.pn Q
            let w := toWire c
            let rec' : Record (Plain ℓ) (List (BitVec 8)) :=
              ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
            let mir' := s₁.record 3 Q () rec' chal₀.isSome
            do
              putS { st with mir := mir', pq := Function.update st.pq Q pq',
                             pn := Function.update st.pn Q pn,
                             honest := (w, c) :: st.honest }
              return some w).run st) := by
  set ρ₁ := Env.cons
    (t := .prod simStateTy
      (.prod .bool (.prod (.base SimSort.plain)
        (.prod (.opt (.base SimSort.plain)) (.opt (.base SimSort.pqc))))))
    (simStateEnc st, partyEnc Q, m₀, chal₀, r₀) ρ
  set ρ₂ := Env.cons (t := simMirTy) (simMirEnc s₁) ρ₁
  set ρ₃ := Env.cons (t := .prod (.base SimSort.pqc) (.opt (.base SimSort.bv256))) (rq, rc) ρ₂
  set ρ₄ := Env.cons (t := .prod (.base SimSort.pq) (.base SimSort.lpub)) (pq', pub) ρ₃
  unfold simSendPostQueryC
  rcases res with _ | c
  · simp [ρ₄, ρ₃, ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval,
      Expr.v0, Expr.v4]
  · rw [comp_eval_caseOpt_v0_some]
    set ρ₅ := Env.cons (t := fig8CTy PQ PQC Pt ℓ) c
      (Env.cons (t := .opt (fig8CTy PQ PQC Pt ℓ)) (some c) ρ₄)
    simp only [comp_eval_ret, putS, StateT.run_bind, StateT.run_set, StateT.run_pure,
      pure_bind, map_pure, Prod.map]
    have hpn5 : (Expr.ite
        (.not (.eqN (pGet (mEpoch (Expr.v4 (O := OO))) (.fst (.snd .v5)))
          (pGet (mEpoch (ssMir (.fst .v5))) (.fst (.snd .v5)))))
        (Expr.op (O := OO) SimOp.natToU32
          (.sub (pGet (mIdx (ssMir (.fst .v5))) (.fst (.snd .v5))) (.nat 1)))
        (pGet (ssPn (.fst .v5)) (.fst (.snd .v5)))).eval ρ₅ =
        (if s₁.epoch Q ≠ st.mir.epoch Q then
          BitVec.ofNat 32 (st.mir.idx Q - 1) else st.pn Q) := by
      cases Q <;>
        (by_cases heq : s₁.epoch .A = st.mir.epoch .A <;>
         by_cases heqB : s₁.epoch .B = st.mir.epoch .B <;>
         simp [ρ₅, ρ₄, ρ₃, ρ₂, ρ₁, heq, heqB, mEpoch, mIdx, ssMir, ssPn, pGet_eval,
           simOps, simStateEnc, simMirEnc, partyEnc,
           Expr.eval, Expr.v4, Expr.v5])
    have hch5 : (isSomeE (.fst (.snd (.snd (.snd (Expr.v5 (O := OO))))))).eval ρ₅ =
        chal₀.isSome := by
      cases chal₀ <;> rfl
    have hrec : (mRecordE (Expr.v4 (O := OO)) (.fst (.snd .v5))
        (.pair
          (.pair (.fst (.snd .v5))
            (.pair (pGet (mEpoch .v4) (.fst (.snd .v5)))
              (.add (pGet (mIdx .v4) (.fst (.snd .v5))) (.nat 1))))
          (.pair (.fst (.snd (.snd .v5))) (Expr.op (O := OO) SimOp.toWire .v0)))
        (isSomeE (.fst (.snd (.snd (.snd .v5)))))).eval ρ₅ =
        simMirEnc (s₁.record 3 Q ()
          ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, toWire c⟩
          chal₀.isSome) := by
      rw [← hch5]
      refine mRecordE_eval (Expr.v4 (O := OO)) (.fst (.snd .v5)) _ _ ρ₅ s₁ Q
        ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, toWire c⟩ rfl rfl ?_
      cases Q <;>
        simp [ρ₅, ρ₄, ρ₃, ρ₂, ρ₁, mEpoch, mIdx, pGet_eval, simOps,
          simToWire, toWire, simTagBytes, tagBytes, simMirEnc, simRecEnc, posEnc,
          partyEnc, Expr.eval, Expr.v0, Expr.v4, Expr.v5]
    simp only [ssMk, expr_pair_eval, expr_some_eval, pSet_eval, hpn5, hrec]
    cases Q <;>
      simp [ρ₅, ρ₄, ρ₃, ρ₂, ρ₁, ssPq, ssPn, ssUnackA, ssHonest, ssChains,
        ssAmb, ssStopped, simOps, simToWire, toWire, simTagBytes,
        tagBytes, simStateEnc, partyEnc, Function.update, Expr.eval,
        Expr.v0, Expr.v2, Expr.v5]

theorem simSendPostCoinsC_eval {Γ}
    (ρ : Env Γ) (st : SimState PQ Pt ℓ) (Q : Party)
    (m₀ : Plain ℓ) (chal₀ : Option (Plain ℓ)) (r₀ : Option PQC)
    (s₁ : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (rq : PQC) (rc : Option (BitVec 256)) :
    (simSendPostCoinsC (P := P) (Dh := Dh) (encT := encT) (decT := decT)).eval
      (Env.cons (t := .prod (.base SimSort.pqc) (.opt (.base SimSort.bv256))) (rq, rc)
        (Env.cons (t := simMirTy) (simMirEnc s₁)
          (Env.cons
            (t := .prod simStateTy
              (.prod .bool (.prod (.base SimSort.plain)
                (.prod (.opt (.base SimSort.plain)) (.opt (.base SimSort.pqc))))))
            (simStateEnc st, partyEnc Q, m₀, chal₀, r₀) ρ))) =
      Prod.map id simStateEnc <$>
        ((let pn := if s₁.epoch Q ≠ st.mir.epoch Q then
            BitVec.ofNat 32 (st.mir.idx Q - 1) else st.pn Q
          match mkPub (P := P) st Q rq pn with
          | none => return none
          | some (pq', pub) => do
            let res ← match chal₀ with
              | none => liftQ (SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc)
              | some m₁ =>
                liftQ (SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc)
            match res with
            | none => return none
            | some c =>
              let w := toWire c
              let rec' : Record (Plain ℓ) (List (BitVec 8)) :=
                ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
              let mir' := s₁.record 3 Q () rec' chal₀.isSome
              putS { st with mir := mir', pq := Function.update st.pq Q pq',
                             pn := Function.update st.pn Q pn,
                             honest := (w, c) :: st.honest }
              return some w).run st) := by
  dsimp only []
  set ρ₁ := Env.cons
    (t := .prod simStateTy
      (.prod .bool (.prod (.base SimSort.plain)
        (.prod (.opt (.base SimSort.plain)) (.opt (.base SimSort.pqc))))))
    (simStateEnc st, partyEnc Q, m₀, chal₀, r₀) ρ
  set ρ₂ := Env.cons (t := simMirTy) (simMirEnc s₁) ρ₁
  set ρ₃ := Env.cons (t := .prod (.base SimSort.pqc) (.opt (.base SimSort.bv256)))
    (rq, rc) ρ₂
  set pn₀ := if s₁.epoch Q ≠ st.mir.epoch Q then
    BitVec.ofNat 32 (st.mir.idx Q - 1) else st.pn Q
  unfold simSendPostCoinsC
  rw [comp_eval_caseOpt]
  have hpn3 : (Expr.ite
      (.not (.eqN (pGet (mEpoch (Expr.v1 (O := OO))) (.fst (.snd .v2)))
        (pGet (mEpoch (ssMir (.fst .v2))) (.fst (.snd .v2)))))
      (Expr.op (O := OO) SimOp.natToU32
        (.sub (pGet (mIdx (ssMir (.fst .v2))) (.fst (.snd .v2))) (.nat 1)))
      (pGet (ssPn (.fst .v2)) (.fst (.snd .v2)))).eval ρ₃ = pn₀ := by
    cases Q <;>
      (dsimp only [pn₀];
       by_cases heq : s₁.epoch .A = st.mir.epoch .A <;>
       by_cases heqB : s₁.epoch .B = st.mir.epoch .B <;>
       simp [ρ₃, ρ₂, ρ₁, heq, heqB, mEpoch, mIdx, ssMir, ssPn, pGet,
         simOps, simStateEnc, simMirEnc, partyEnc,
         Expr.eval, Expr.v0, Expr.v1, Expr.v2])
  have hspqr : (spqrSendPubE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
      (.pair (.fst (.snd .v2)) (.pair (ssUnackA (.fst .v2))
        (.pair (pGet (ssPq (.fst .v2)) (.fst (.snd .v2)))
          (.pair (.fst .v0)
            (.ite (.not (.eqN (pGet (mEpoch .v1) (.fst (.snd .v2)))
                (pGet (mEpoch (ssMir (.fst .v2))) (.fst (.snd .v2)))))
              (Expr.op (O := OO) SimOp.natToU32
                (.sub (pGet (mIdx (ssMir (.fst .v2))) (.fst (.snd .v2))) (.nat 1)))
              (pGet (ssPn (.fst .v2)) (.fst (.snd .v2))))))))).eval ρ₃ =
      mkPub P st Q rq pn₀ := by
    rw [← simSpqrSendPub_eq P st Q rq pn₀]
    refine spqrSendPubE_eval P Dh encT decT _ ρ₃ (partyEnc Q) st.unackA (st.pq Q) rq pn₀ ?_
    simp only [expr_pair_eval, hpn3]
    cases Q <;>
      simp [ρ₃, ρ₂, ρ₁, ssUnackA, ssPq, pGet, simStateEnc, partyEnc,
        Expr.eval, Expr.v0, Expr.v2]
  rw [hspqr]
  rcases mkPub P st Q rq pn₀ with _ | ⟨pq', pub⟩
  · simp [ρ₃, ρ₂, ρ₁, comp_eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v2]
  · dsimp only []
    set ρ₄ := Env.cons (t := .prod (.base SimSort.pq) (.base SimSort.lpub)) (pq', pub) ρ₃
    have hq_chal :
        (Comp.caseOpt (.fst (.snd (.snd (.snd (Expr.v3 (O := OO))))))
          (Comp.query (I := SIface) SM.SMTag.tr
            (.pair (.fst (.snd .v3))
              (.pair (.pair (.snd .v0) (.fst (.snd (.snd .v3)))) (.snd .v1))))
          (Comp.query (I := SIface) SM.SMTag.ch
            (.pair (.fst (.snd .v4))
              (.pair (.pair (.snd .v1) (.fst (.snd (.snd .v4))))
                (.pair (.pair (.snd .v1) .v0) (.snd .v2)))))).eval ρ₄ =
        (match chal₀ with
         | none => SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc
         | some m₁ =>
           SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc) := by
      rw [comp_eval_caseOpt]
      have hch3 : (Expr.fst (.snd (.snd (.snd (Expr.v3 (O := OO)))))).eval ρ₄ =
          chal₀ := rfl
      rw [hch3]
      rcases chal₀ with _ | m₁
      · dsimp only []
        rw [query_tr_eval]
        simp [ρ₄, ρ₃, ρ₂, ρ₁, partyDec_partyEnc, Expr.eval,
          Expr.v0, Expr.v1, Expr.v3]
      · dsimp only []
        rw [query_ch_eval]
        simp [ρ₄, ρ₃, ρ₂, ρ₁, partyDec_partyEnc, Expr.eval,
          Expr.v0, Expr.v1, Expr.v2, Expr.v4]
    rw [comp_eval_bind, hq_chal]
    rcases chal₀ with _ | m₁ <;>
      (dsimp only [];
       simp only [StateT.run_bind, liftQ, stateT_lift_run, bind_assoc,
         pure_bind, map_bind];
       exact bind_congr (simSendPostQueryC_eval P Dh encT decT ρ st Q m₀ _ r₀ s₁ rq rc pq' pub))

theorem simSendC_eval (qep : ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (m₀ : Expr OO Γ (.base .plain)) (chal : Expr OO Γ (.opt (.base .plain)))
    (r : Expr OO Γ (.opt (.base .pqc))) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (simSendC P Dh encT decT qep s qParty m₀ chal r).eval ρ =
      Prod.map id simStateEnc <$>
        ((simSend P qep Q (m₀.eval ρ) (chal.eval ρ) (r.eval ρ)).run st) := by
  unfold simSendC simSend
  rw [comp_eval_bind_ret]
  have h0 : (Expr.pair s (.pair qParty (.pair m₀ (.pair chal r)))).eval ρ =
      (simStateEnc st, partyEnc Q, m₀.eval ρ, chal.eval ρ, r.eval ρ) := by
    simp [Expr.eval, hs, hq]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod simStateTy
      (.prod .bool (.prod (.base SimSort.plain)
        (.prod (.opt (.base SimSort.plain)) (.opt (.base SimSort.pqc))))))
    (simStateEnc st, partyEnc Q, m₀.eval ρ, chal.eval ρ, r.eval ρ) ρ
  rw [comp_eval_ite]
  have href : (orE (mWin (ssMir (.fst (Expr.v0 (O := OO)))))
      (.not (mNoBobEpoch0E (ssMir (.fst .v0)) (.fst (.snd .v0))))).eval ρ₁ =
      (st.mir.win || !(noBobSendInEpoch0 st.mir Q)) := by
    have hnb := mNoBobEpoch0E_eval (O' := OO) (ssMir (.fst .v0)) (.fst (.snd .v0))
      ρ₁ st.mir Q rfl rfl
    rw [orE_eval]
    dsimp only [Expr.eval]
    rw [hnb]
    rfl
  rw [href]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases h1 : (st.mir.win || !(noBobSendInEpoch0 st.mir Q)) = true
  · simp [ρ₁, h1, comp_eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [comp_eval_caseOpt]
    have hep : (mEpMgmtE qep (ssMir (.fst (Expr.v0 (O := OO)))) (.fst (.snd .v0))
        (isSomeE (.snd (.snd (.snd (.snd .v0)))))).eval ρ₁ =
        (st.mir.epMgmt 3 qep Q (r.eval ρ).isSome).map simMirEnc := by
      rw [mEpMgmtE_eval qep (ssMir (.fst .v0)) (.fst (.snd .v0))
        (isSomeE (.snd (.snd (.snd (.snd .v0))))) ρ₁ st.mir Q rfl rfl]
      simp [ρ₁, isSomeE_eval, Expr.eval, Expr.v0]
    rw [hep]
    rcases st.mir.epMgmt 3 qep Q (r.eval ρ).isSome with _ | s₁
    · simp [ρ₁, comp_eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp only [Option.map_some]
      set ρ₂ := Env.cons (t := simMirTy) (simMirEnc s₁) ρ₁
      rw [comp_eval_ite]
      have hsc : (Expr.and (isSomeE (.fst (.snd (.snd (.snd (Expr.v1 (O := OO)))))))
          (.not (mSafeChE .v0 (.fst (.snd .v1))))).eval ρ₂ =
          ((chal.eval ρ).isSome && !(s₁.safeCh 3 Q)) := by
        have hs' := mSafeChE_eval (O' := OO) .v0 (.fst (.snd .v1)) ρ₂ s₁ Q rfl rfl
        dsimp only [Expr.eval]
        rw [isSomeE_eval, hs']
        rfl
      rw [hsc]
      by_cases h2 : ((chal.eval ρ).isSome && !(s₁.safeCh 3 Q)) = true
      · simp [ρ₂, ρ₁, h2, comp_eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
      · simp only [h2, Bool.false_eq_true, ↓reduceIte, comp_eval_bind]
        rw [simDrawSendCoinsC_eval]
        have hr0 : (Expr.snd (.snd (.snd (.snd (Expr.v1 (O := OO)))))).eval ρ₂ = r.eval ρ := rfl
        rw [hr0]
        rcases r.eval ρ with _ | rq₀
        · dsimp only []
          simp only [bind_assoc, pure_bind, StateT.run_bind,
            coin, liftQ, stateT_lift_run, map_bind]
          refine bind_congr fun rq => ?_
          exact simSendPostCoinsC_eval P Dh encT decT ρ st Q (m₀.eval ρ) (chal.eval ρ) _ s₁
            rq none
        · dsimp only []
          simp only [bind_assoc, pure_bind, StateT.run_bind,
            coin, liftQ, stateT_lift_run, bind_map_left, map_bind]
          refine bind_congr fun c => ?_
          exact simSendPostCoinsC_eval P Dh encT decT ρ st Q (m₀.eval ρ) (chal.eval ρ) _ s₁
            rq₀ (some c)

omit [SampleableType PQC] in
theorem inTE_eval (K : ℕ) {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (c : Expr OO Γ (fig8CTy PQ PQC Pt ℓ)) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party) (c₀ : Fig8C Pt)
    (hTrans : st.mir.trans.length ≤ K) (hHonest : st.honest.length ≤ K)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q)
    (hc : c.eval ρ = c₀) :
    (inTE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s qParty c).eval ρ =
      (st.honest.any fun wc =>
        decide (wc.2 = c₀) && (st.mir.inTransit Q.other wc.1).isSome) := by
  unfold inTE
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair qParty c)).eval ρ = (simStateEnc st, partyEnc Q, c₀) := by
    simp [Expr.eval, hs, hq, hc]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod simStateTy (.prod .bool (fig8CTy PQ PQC Pt ℓ)))
    (simStateEnc st, partyEnc Q, c₀) ρ
  have ht : st.honest.take K = st.honest := List.take_of_length_le hHonest
  have hHon : (ssHonest (.fst (Expr.v0 (O := OO)))).eval ρ₁ = st.honest := rfl
  simp only [Expr.eval, hHon, ht]
  congr 1; funext wc
  have htr := mInTransitE_eval (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
    (ssMir (.fst .v1)) (otherE (.fst (.snd .v1))) (.fst .v0)
    (Env.cons (t := .prod (.base SimSort.wire) (fig8CTy PQ PQC Pt ℓ)) wc ρ₁)
    st.mir Q.other hTrans rfl
    (by simp [ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ])
  have his := isSomeE_eval
    (mInTransitE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
      (ssMir (.fst .v1)) (otherE (.fst (.snd .v1))) (.fst .v0))
    (Env.cons (t := .prod (.base SimSort.wire) (fig8CTy PQ PQC Pt ℓ)) wc ρ₁)
  rw [his, htr]
  simp [ρ₁, simOps, Expr.eval, Expr.v0, Expr.v1]

theorem fwdC_eval (K : ℕ) {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (c : Expr OO Γ (fig8CTy PQ PQC Pt ℓ)) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party) (c₀ : Fig8C Pt)
    (hTrans : st.mir.trans.length ≤ K) (hHonest : st.honest.length ≤ K)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q)
    (hc : c.eval ρ = c₀) :
    (fwdC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s qParty c).eval ρ =
      (let inT := st.honest.any fun wc =>
          decide (wc.2 = c₀) && (st.mir.inTransit Q.other wc.1).isSome
       if inT then Option.map SM.smRrEnc <$> SM.deliverQuery (St := Fig8St Pt) Q c₀
       else Option.map SM.smRrEnc <$> SM.injectQuery (St := Fig8St Pt) Q c₀) := by
  unfold fwdC
  rw [comp_eval_ite, inTE_eval P Dh encT decT K s qParty c ρ st Q c₀ hTrans hHonest hs hq hc]
  by_cases hin : (st.honest.any fun wc =>
      decide (wc.2 = c₀) && (st.mir.inTransit Q.other wc.1).isSome) = true
  · simp [hin, query_dl_eval, Expr.eval, hq, hc, partyDec_partyEnc]
  · simp [hin, query_ij_eval, Expr.eval, hq, hc, partyDec_partyEnc]

omit [SampleableType PQC] in
theorem onAcceptPreE_eval {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (t i : Expr OO Γ .nat) (ciOpt : Expr OO Γ (.opt .nat))
    (T : Expr OO Γ (.base .pk)) (pq' : Expr OO Γ (.base .pq)) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hChains : (st.chains Q).length ≤ 5)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (onAcceptPreE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
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
  unfold onAcceptPreE
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
      (Expr.caseOpt (.fst (.snd (.snd (.snd (.snd (Expr.v0 (O := OO)))))))
        (pushChainE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
          (.pair (pGet (ssChains (.fst .v0)) (.fst (.snd .v0)))
            (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
              (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))))))
        (modifyChainAcceptE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
          (.pair (pGet (ssChains (.fst .v1)) (.fst (.snd .v1)))
            (.pair .v0 (.fst (.snd (.snd (.snd .v1)))))))).eval ρ₁ =
      (match ciOpt.eval ρ with
       | some ci => (st.chains Q).modify ci (·.accept (i.eval ρ))
       | none => pushChain (st.chains Q)
           (GhostChain.accept ⟨some (T.eval ρ), t.eval ρ, 0, []⟩
             (i.eval ρ))).map ghostChainEnc := by
    rw [expr_caseOpt_eval]
    have hci : (Expr.fst (.snd (.snd (.snd (.snd (Expr.v0 (O := OO))))))).eval ρ₁ =
        ciOpt.eval ρ := rfl
    rw [hci]
    rcases ciOpt.eval ρ with _ | ci
    · rw [← simPushChain_map_ghostChainEnc]
      refine pushChainE_eval P Dh encT decT _ ρ₁ ((st.chains Q).map ghostChainEnc)
        (T.eval ρ) (t.eval ρ) (i.eval ρ) (by simp [hChains]) ?_
      cases Q <;>
        simp [ρ₁, ssChains, pGet_eval, simStateEnc, partyEnc, Expr.eval, Expr.v0]
    · rw [← simModifyChainAccept_map_ghostChainEnc]
      refine modifyChainAcceptE_eval P Dh encT decT _ _ ((st.chains Q).map ghostChainEnc)
        ci (i.eval ρ) (by simp [hChains]) ?_
      cases Q <;>
        simp [ρ₁, ssChains, pGet_eval, simStateEnc, partyEnc, Expr.eval, Expr.v0, Expr.v1]
  simp only [ssMk, expr_pair_eval, pSet_eval, hcs]
  cases Q <;>
    simp [ρ₁, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped,
      simStateEnc, partyEnc, Function.update, bne, Expr.eval, Expr.v0]

omit [SampleableType PQC] in
theorem onAcceptE_eval (K qep : ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (w : Expr OO Γ (.base .wire)) (isDel : Expr OO Γ .bool)
    (t i : Expr OO Γ .nat) (m : Expr OO Γ (.base .plain))
    (ciOpt : Expr OO Γ (.opt .nat)) (T : Expr OO Γ (.base .pk))
    (pq' : Expr OO Γ (.base .pq)) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hBound : SimStateBounded K st)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (pure ((onAcceptE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K qep
      s qParty w isDel t i m ciOpt T pq').eval ρ) :
        Fig8Comp Pt ℓ (Option (@simRrTy PQ PQC Pt ℓ).denote × (@simStateTy PQ PQC Pt ℓ).denote)) =
    Prod.map (Option.map SM.smRrEnc) simStateEnc <$>
      ((onAccept qep Q (w.eval ρ) (isDel.eval ρ) (t.eval ρ) (i.eval ρ) (m.eval ρ)
        (ciOpt.eval ρ) (T.eval ρ) (pq'.eval ρ)).run st) := by
  unfold onAcceptE onAccept
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
  have hpre := onAcceptPreE_eval P Dh encT decT s qParty t i ciOpt T pq' ρ st Q
    (hBound.chains_le Q) hs hq
  have h0 :
      (Expr.pair s (.pair (onAcceptPreE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
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
  have hdel0 : (Expr.fst (.snd (.snd (.snd (.snd (Expr.v0 (O := OO))))))).eval ρ₁ =
      isDel.eval ρ := rfl
  rw [hdel0]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hdel : isDel.eval ρ = true
  · simp only [hdel, ↓reduceIte]
    rw [expr_caseOpt_eval]
    have hinTr := mInTransitE_eval (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
      (ssMir (.fst .v0)) (otherE (.fst (.snd (.snd .v0)))) (.fst (.snd (.snd (.snd .v0))))
      ρ₁ st.mir Q.other hBound.trans_le rfl
      (by simp [ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v0])
    have hw0 : (Expr.fst (.snd (.snd (.snd (Expr.v0 (O := OO)))))).eval ρ₁ = w.eval ρ := rfl
    rw [hw0] at hinTr
    rw [hinTr]
    rcases st.mir.inTransit Q.other (w.eval ρ) with _ | r
    · simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · dsimp only [Option.map_some]
      set ρ₂ := Env.cons (t := simRecTy) (simRecEnc r) ρ₁
      have hch := mChallContainsE_eval (O' := OO) K (ssMir (.fst .v1)) (srecPos .v0)
        ρ₂ st.mir r.pos hBound.chall_le rfl rfl
      have hacc := mAcceptE_eval (O' := OO) K (ssMir (.fst .v1)) (.fst (.snd (.snd .v1)))
        (srecPos .v0) ρ₂ st.mir Q r.pos
        hBound.trans_le hBound.chall_le hBound.comp_le rfl rfl rfl
      have hset := ssSetMir_eval (O' := OO) (.fst (.snd .v1))
        (mAcceptE (O' := OO) K (ssMir (.fst .v1)) (.fst (.snd (.snd .v1))) (srecPos .v0))
        ρ₂ s' (st.mir.accept Q () r.pos) rfl hacc
      have hfst :
          (Expr.some (.inr (t := .unit)
            (.pair (.fst (.snd (.snd (.snd (.snd (.snd (Expr.v1 (O := OO))))))))
              (.pair (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
                (.ite (mChallContainsE K (ssMir (.fst .v1)) (srecPos .v0))
                  .none (.some (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))))))).eval ρ₂ =
          some (SM.smRrEnc (.accepted (t.eval ρ) (i.eval ρ)
            (if st.mir.chall.contains r.pos then none else some (m.eval ρ)))) := by
        change some (Sum.inr (t.eval ρ, i.eval ρ,
          (Expr.ite (mChallContainsE K (ssMir (.fst (Expr.v1 (O := OO)))) (srecPos .v0))
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
        (.fst (.snd (.snd (.snd (.snd (.snd (Expr.v0 (O := OO))))))))).eval ρ₁ =
        decide (qep + 1 < t.eval ρ) := rfl
    rw [hlt]
    by_cases h1 : qep + 1 < t.eval ρ
    · simp [ρ₁, h1, SM.smRrEnc, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [ite_eval]
      have hpos : (Expr.pair (otherE (.fst (.snd (.snd (Expr.v0 (O := OO))))))
          (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
            (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))).eval ρ₁ =
          posEnc ⟨Q.other, t.eval ρ, i.eval ρ⟩ := by
        simp [ρ₁, otherE, posEnc, partyEnc_other, Expr.eval, Expr.v0]
      have htriv := mTrivialE_eval (O' := OO) K (ssMir (.fst .v0))
        (.pair (otherE (.fst (.snd (.snd .v0))))
          (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
            (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))))
        ρ₁ st.mir ⟨Q.other, t.eval ρ, i.eval ρ⟩ hBound.trans_le hBound.comp_le rfl hpos
      rw [htriv]
      by_cases h2 : (st.mir.trivial 3 ⟨Q.other, t.eval ρ, i.eval ρ⟩) = true
      · simp only [h2, ↓reduceIte]
        have hacc := mAcceptE_eval (O' := OO) K (ssMir (.fst .v0)) (.fst (.snd (.snd .v0)))
          (.pair (otherE (.fst (.snd (.snd .v0))))
            (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
              (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))))
          ρ₁ st.mir Q ⟨Q.other, t.eval ρ, i.eval ρ⟩
          hBound.trans_le hBound.chall_le hBound.comp_le rfl rfl hpos
        have hset := ssSetMir_eval (O' := OO) (.fst (.snd .v0))
          (mAcceptE (O' := OO) K (ssMir (.fst .v0)) (.fst (.snd (.snd .v0)))
            (.pair (otherE (.fst (.snd (.snd .v0))))
              (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))))
          ρ₁ s' (st.mir.accept Q () ⟨Q.other, t.eval ρ, i.eval ρ⟩) rfl hacc
        rw [expr_pair_eval, hset]
        simp only [putS, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, map_pure, Prod.map, Option.map, s']
        cases ciOpt.eval ρ <;> rfl
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        have hwin := ssSetMirWin_eval (O' := OO) (.fst .v0) ρ₁ st rfl
        rw [expr_pair_eval, hwin]
        simp only [putS, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, map_pure, Prod.map, Option.map]
        rfl

theorem ret_onAnswerE_eval (K qep : ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (w : Expr OO Γ (.base .wire)) (isDel : Expr OO Γ .bool)
    (ciOpt : Expr OO Γ (.opt .nat)) (T : Expr OO Γ (.base .pk))
    (pq' : Expr OO Γ (.base .pq))
    (resE : Expr OO Γ (.opt (fig8RrTy PQ PQC Pt ℓ))) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hBound : SimStateBounded K st)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q)
    (hres : resE.eval ρ = res.map SM.smRrEnc) :
    (Comp.ret (I := SIface)
      (onAnswerE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K qep
        s qParty w isDel ciOpt T pq' resE)).eval ρ =
    Prod.map (Option.map SM.smRrEnc) simStateEnc <$>
      ((onAnswer qep Q (w.eval ρ) (isDel.eval ρ) (ciOpt.eval ρ) (T.eval ρ) (pq'.eval ρ)
        res).run st) := by
  rw [comp_eval_ret]
  unfold onAnswerE onAnswer
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
    change pure ((onAcceptE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K qep
        (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2))) (.fst (.snd (.snd (.snd .v2))))
        (.fst .v0) (.fst (.snd .v0))
        (.caseOpt (.snd (.snd .v0)) (Expr.op (O := OO) SimOp.defaultPlain .unit) (.snd .v0))
        (.fst (.snd (.snd (.snd (.snd .v2)))))
        (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v2)))))))).eval ρ₂) = _
    have hm : (Expr.caseOpt (.snd (.snd (Expr.v0 (O := OO))))
        (Expr.op (O := OO) SimOp.defaultPlain .unit) (.snd .v0)).eval ρ₂ =
        (pm.map (·.2)).getD default := by
      rcases pm with _ | ⟨pub, plain⟩ <;>
        simp [ρ₂, simOps, Expr.eval, Expr.v0]
    have hacc := onAcceptE_eval P Dh encT decT K qep
        (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2))) (.fst (.snd (.snd (.snd .v2))))
        (.fst .v0) (.fst (.snd .v0))
        (.caseOpt (.snd (.snd .v0)) (Expr.op (O := OO) SimOp.defaultPlain .unit) (.snd .v0))
        (.fst (.snd (.snd (.snd (.snd .v2)))))
        (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v2)))))))
        ρ₂ st Q hBound rfl rfl
    rw [hacc, hm]
    rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
/-- Deduplicated `corr-P` mirror counterpart of `simCorr`, using `afterCorrDedup` so `mAfterCorrE`
evaluates directly to `simCorrDedup`. -/
def simCorrDedup (Q : Party) : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option (GhostState PQ)) := do
  let s ← get
  if s.mir.win || !(s.mir.corrAllowed Q) || inReceiveOnlyEpoch s.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 s.mir Q) then return none
  let res ← liftQ (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q)
  match res with
  | none => return none
  | some st =>
    let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
        match st.γ with
        | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
            if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
        | _ => s.chains
      else s.chains
    putS { s with mir := afterCorrDedup s.mir Q, chains }
    return some (toGhost (P := P) { s with chains } Q st)

theorem simCorrC_eval (K : ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hBound : SimStateBounded K st)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (simCorrC P Dh encT decT K s qParty).eval ρ =
      Prod.map id simStateEnc <$> ((simCorrDedup P Dh encT Q).run st) := by
  unfold simCorrC simCorrDedup
  rw [comp_eval_bind_ret]
  have h0 : (Expr.pair s qParty).eval ρ = (simStateEnc st, partyEnc Q) := by
    simp [Expr.eval, hs, hq]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod simStateTy .bool) (simStateEnc st, partyEnc Q) ρ
  rw [comp_eval_ite]
  have href : (orE (mWin (ssMir (.fst (Expr.v0 (O := OO)))))
      (orE (.not (mCorrAllowedE K (ssMir (.fst .v0)) (.snd .v0)))
        (orE (mInWinE (ssMir (.fst .v0)) (.snd .v0))
          (.not (mNoSpkCorrE (ssMir (.fst .v0)) (.snd .v0)))))).eval ρ₁ =
      (st.mir.win || !(st.mir.corrAllowed Q) || inReceiveOnlyEpoch st.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 st.mir Q)) := by
    have hca := mCorrAllowedE_eval (O' := OO) K (ssMir (.fst .v0)) (.snd .v0) ρ₁ st.mir Q
      hBound.trans_le hBound.chall_le hBound.comp_le rfl rfl
    have hinw := mInWinE_eval (O' := OO) (ssMir (.fst .v0)) (.snd .v0) ρ₁ st.mir Q rfl rfl
    have hnspk := mNoSpkCorrE_eval (O' := OO) (ssMir (.fst .v0)) (.snd .v0) ρ₁ st.mir Q rfl rfl
    rw [orE_eval, orE_eval, orE_eval]
    dsimp only [Expr.eval]
    rw [hca, hinw, hnspk, Bool.or_assoc, Bool.or_assoc]
    rfl
  rw [href]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases h1 :
      (st.mir.win || !(st.mir.corrAllowed Q) || inReceiveOnlyEpoch st.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 st.mir Q)) = true
  · simp [ρ₁, h1, comp_eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, comp_eval_bind]
    have hcr : (Comp.query (I := SIface) SM.SMTag.cr (.snd (Expr.v0 (O := OO)))).eval ρ₁ =
        SM.corrQuery (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
          (C := Fig8C Pt) Q := by
      rw [query_cr_eval]
      simp [ρ₁, partyDec_partyEnc, Expr.eval, Expr.v0]
    rw [hcr]
    simp only [StateT.run_bind, liftQ, stateT_lift_run, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    rcases res with _ | fig8st
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · rw [comp_eval_caseOpt_v0_some]
      set ρ₂ := Env.cons (t := .base SimSort.fig8st) fig8st
        (Env.cons (t := .opt (.base SimSort.fig8st)) (some fig8st) ρ₁)
      rw [comp_eval_ret]
      set chains' : Party → List GhostChain :=
        if Q == Party.B && st.mir.epoch Party.B == 0 then
          match fig8st.γ with
          | .exp x => Function.update st.chains Party.A ((st.chains Party.A).map fun g =>
              if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => st.chains
        else st.chains
      have hchains :
          (Expr.ite (.and (.snd (Expr.v2 (O := OO)))
              (.eqN (.snd (mEpoch (ssMir (.fst .v2)))) (.nat 0)))
            (.pair
              (revealSpkChainsE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
                (.pair (.fst (ssChains (.fst .v2))) .v0))
              (.snd (ssChains (.fst .v2))))
            (ssChains (.fst .v2))).eval ρ₂ =
          ((chains' .A).map ghostChainEnc, (chains' .B).map ghostChainEnc) := by
        rw [ite_eval]
        have hcond : (Expr.and (.snd (Expr.v2 (O := OO)))
            (.eqN (.snd (mEpoch (ssMir (.fst .v2)))) (.nat 0))).eval ρ₂ =
            (Q == Party.B && st.mir.epoch Party.B == 0) := by
          cases Q <;>
            simp [ρ₂, ρ₁, mEpoch, ssMir, simStateEnc, simMirEnc, partyEnc, BEq.beq,
              Expr.eval, Expr.v2]
        rw [hcond]
        by_cases hc : (Q == Party.B && st.mir.epoch Party.B == 0) = true
        · simp only [hc, ↓reduceIte, chains', expr_pair_eval]
          have hA : ((ssChains (.fst (Expr.v2 (O := OO)))).eval ρ₂).1 =
              (st.chains .A).map ghostChainEnc := rfl
          have hB : ((ssChains (.fst (Expr.v2 (O := OO)))).eval ρ₂).2 =
              (st.chains .B).map ghostChainEnc := rfl
          have h0' : (Expr.v0 (O := OO)).eval ρ₂ = fig8st := rfl
          have hrev := revealSpkChainsE_eval P Dh encT decT
            (.pair (.fst (ssChains (.fst .v2))) .v0) ρ₂
            ((st.chains .A).map ghostChainEnc) fig8st
            (by rw [List.length_map]; exact hBound.chainsA_le)
            (by rw [expr_pair_eval, Expr.eval, hA, h0'])
          rw [hrev, Expr.eval, hB, simRevealSpkChains_map_ghostChainEnc]
          rcases fig8st.γ with _ | x <;> simp [Function.update]
        · simp [ρ₂, ρ₁, hc, chains', ssChains, simStateEnc, Expr.eval, Expr.v2]
      have hafc := mAfterCorrE_eval (O' := OO) K (ssMir (.fst .v2)) (.snd .v2) ρ₂ st.mir Q
        hBound.trans_le hBound.comp_u rfl rfl
      have hpchains :
          (pGet
            (.ite (.and (.snd (Expr.v2 (O := OO)))
                (.eqN (.snd (mEpoch (ssMir (.fst .v2)))) (.nat 0)))
              (.pair
                (revealSpkChainsE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
                  (.pair (.fst (ssChains (.fst .v2))) .v0))
                (.snd (ssChains (.fst .v2))))
              (ssChains (.fst .v2)))
            (.snd .v2)).eval ρ₂ =
          (chains' Q).map ghostChainEnc := by
        rw [pGet_eval, hchains]
        cases Q <;> simp [ρ₂, ρ₁, partyEnc, Expr.eval, Expr.v2]
      have hchains'_le : (chains' Q).length ≤ 5 := by
        dsimp only [chains']
        split_ifs
        · rcases fig8st.γ with _ | x
          · exact hBound.chains_le Q
          · cases Q <;> simp [Function.update, hBound.chainsA_le, hBound.chainsB_le]
        · exact hBound.chains_le Q
      have hghost :
          (toGhostE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (.pair (.snd .v2)
              (.pair .v0
                (.pair (pGet (ssPn (.fst .v2)) (.snd .v2))
                  (.pair
                    (pGet
                      (.ite (.and (.snd .v2) (.eqN (.snd (mEpoch (ssMir (.fst .v2)))) (.nat 0)))
                        (.pair
                          (revealSpkChainsE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
                            (.pair (.fst (ssChains (.fst .v2))) .v0))
                          (.snd (ssChains (.fst .v2))))
                        (ssChains (.fst .v2)))
                      (.snd .v2))
                    (.pair (ssUnackA (.fst .v2))
                      (.pair (pGet (ssPq (.fst .v2)) (.snd .v2))
                        (pGet (mEpoch (ssMir (.fst .v2))) (.snd .v2))))))))).eval ρ₂ =
          toGhost P { st with chains := chains' } Q fig8st := by
        rw [← simToGhost_eq P { st with chains := chains' } Q fig8st]
        refine toGhostE_eval P Dh encT decT _ ρ₂
          (partyEnc Q) fig8st (st.pn Q) ((chains' Q).map ghostChainEnc)
          st.unackA (st.pq Q) (st.mir.epoch Q)
          (by rw [List.length_map]; exact hchains'_le) ?_
        simp only [expr_pair_eval, hpchains]
        cases Q <;>
          simp [ρ₂, ρ₁, pGet_eval, ssPn, ssUnackA, ssPq, mEpoch, ssMir,
            simStateEnc, simMirEnc, partyEnc, Expr.eval, Expr.v0, Expr.v2]
      simp only [putS, StateT.run_bind, StateT.run_set, StateT.run_pure,
        pure_bind, map_pure, Prod.map]
      simp only [ssMk, expr_pair_eval, expr_some_eval, hghost, hafc, hchains]
      simp [ρ₂, ρ₁, chains', ssPq, ssPn, ssUnackA, ssHonest, ssAmb, ssStopped,
        simStateEnc, Expr.eval, Expr.v2]
      exact ⟨rfl, rfl, rfl⟩

omit [SampleableType PQC] in
theorem honestCE_eval (K : ℕ) {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (w : Expr OO Γ (.base .wire)) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party) (w₀ : List (BitVec 8))
    (hHonest : st.honest.length ≤ K)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q)
    (hw : w.eval ρ = w₀) :
    (honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s qParty w).eval ρ =
      (st.honest.find? fun wc =>
        wc.1 == w₀ && Party.senderOf wc.2.1.1 == Q.other).map (·.2) := by
  unfold honestCE
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair qParty w)).eval ρ = (simStateEnc st, partyEnc Q, w₀) := by
    simp [Expr.eval, hs, hq, hw]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod simStateTy (.prod .bool (.base SimSort.wire)))
    (simStateEnc st, partyEnc Q, w₀) ρ
  have ht : st.honest.take K = st.honest := List.take_of_length_le hHonest
  have hfind :
      (Expr.findB K (ssHonest (.fst (Expr.v0 (O := OO))))
        (.and
          (Expr.op (O := OO) SimOp.eqWire (.pair (.fst .v0) (.snd (.snd .v1))))
          (boolEq (senderOfE (.fst (.fst (.snd .v0)))) (otherE (.fst (.snd .v1)))))).eval ρ₁ =
      st.honest.find? fun wc => wc.1 == w₀ && Party.senderOf wc.2.1.1 == Q.other := by
    have hHon : (ssHonest (.fst (Expr.v0 (O := OO)))).eval ρ₁ = st.honest := rfl
    simp only [Expr.eval, hHon, ht]
    congr 1; funext wc
    let ρ₂ := Env.cons (t := .prod (.base SimSort.wire) (fig8CTy PQ PQC Pt ℓ)) wc ρ₁
    have hsnd : (senderOfE (O' := OO) (.fst (.fst (.snd .v0)))).eval ρ₂ =
        partyEnc (Party.senderOf wc.2.1.1) :=
      senderOfE_eval (O' := OO) (.fst (.fst (.snd .v0))) ρ₂
    have hoth : (otherE (O' := OO) (.fst (.snd .v1))).eval ρ₂ = partyEnc Q.other := by
      simp [ρ₂, ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v1]
    have hbeq := boolEq_eval (O' := OO)
      (senderOfE (.fst (.fst (.snd .v0)))) (otherE (.fst (.snd .v1))) ρ₂
    rw [hbeq, hsnd, hoth, partyEnc_beq]
    rfl
  rw [expr_caseOpt_eval, hfind]
  rcases h : st.honest.find? (fun wc => wc.1 == w₀ && Party.senderOf wc.2.1.1 == Q.other) with
    _ | wc <;> simp [h, Expr.eval, Expr.v0]

omit [SampleableType PQC] in
theorem mkCE_eval {Γ} (honestC : Expr OO Γ (.opt (fig8CTy PQ PQC Pt ℓ)))
    (lct : Expr OO Γ (.base .lct)) (t : Expr OO Γ .nat) (T? : Expr OO Γ (.opt (.base .pt)))
    (ρ : Env Γ) :
    (mkCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) honestC lct t T?).eval ρ =
      match honestC.eval ρ with
      | some c => if c.2.2.2 = (lct.eval ρ).2.2 then c else ((t.eval ρ, T?.eval ρ), lct.eval ρ)
      | none => ((t.eval ρ, T?.eval ρ), lct.eval ρ) := by
  unfold mkCE
  rw [letE_eval]
  rcases h : honestC.eval ρ with _ | c
  · simp [h, Expr.eval, Expr.v0]
  · simp [h, simOps, Expr.eval, Expr.v0, Expr.v1]

omit [SampleableType PQC] in
theorem spkAmbE_eval {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hChains : (st.chains Q).length ≤ 5)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (spkAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT) s qParty).eval ρ =
      (Q == Party.A && (st.chains Q).any (·.key.isNone)) := by
  unfold spkAmbE
  have hp : (pGet (ssChains s) qParty).eval ρ = (st.chains Q).map ghostChainEnc := by
    rw [pGet_eval]
    cases Q <;> simp [ssChains, hs, hq, simStateEnc, partyEnc, Expr.eval]
  have hhas := hasUnknownKeyE_eval P Dh encT decT
    (pGet (ssChains s) qParty) ρ (st.chains Q) hChains hp
  dsimp only [Expr.eval]
  rw [hhas, hq]
  cases Q <;> rfl

omit [SampleableType PQC] in
theorem ambCondE_eval {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hChains : (st.chains Q).length ≤ 5)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (ambCondE (P := P) (Dh := Dh) (encT := encT) (decT := decT) s qParty).eval ρ =
      (inReceiveOnlyEpoch st.mir Q || (Q == Party.A && (st.chains Q).any (·.key.isNone))) := by
  unfold ambCondE
  rw [orE_eval,
    mInWinE_eval (O' := OO) (ssMir s) qParty ρ st.mir Q
      (by simp [ssMir, Expr.eval, hs, simStateEnc]) hq,
    spkAmbE_eval P Dh encT decT s qParty ρ st Q hChains hs hq]

omit [SampleableType PQC] in
theorem sAmbE_eval {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hChains : (st.chains Q).length ≤ 5)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT) s qParty).eval ρ =
      simStateEnc
        (if inReceiveOnlyEpoch st.mir Q || (Q == Party.A && (st.chains Q).any (·.key.isNone))
         then { st with amb := st.amb + 1 }
         else st) := by
  unfold sAmbE
  rw [ite_eval, ambCondE_eval P Dh encT decT s qParty ρ st Q hChains hs hq]
  split_ifs
  · rw [ssSetAmb_eval s (.add (ssAmb s) (.nat 1)) ρ st hs]
    simp [ssAmb, hs, simStateEnc, Expr.eval]
  · exact hs

omit [SampleableType PQC] in
theorem evictedHonestE_eval {Γ} (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (honestC : Expr OO Γ (.opt (fig8CTy PQ PQC Pt ℓ))) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (evictedHonestE (P := P) (Dh := Dh) (encT := encT) (decT := decT) s qParty honestC).eval ρ =
      ((honestC.eval ρ).map (fun c => decide (c.1.1 ≠ st.mir.epoch Q + 1)) == some true) := by
  unfold evictedHonestE
  rw [letE_eval, expr_caseOpt_eval]
  rcases h : honestC.eval ρ with _ | c
  · simp [h, Expr.eval]; rfl
  · cases Q <;>
      simp [h, hs, hq, mEpoch, ssMir, pGet_eval, simStateEnc, simMirEnc, partyEnc,
        Option.some_beq_some, decide_not, Expr.eval, Expr.v0, Expr.v1]

omit [Zero Pt] [SampleableType PQC] in
theorem fwd_run_eq (Q : Party) (c₀ : Fig8C Pt) (st : SimState PQ Pt ℓ) :
    (fwd Q c₀).run st =
      ((if (st.honest.any fun wc => decide (wc.2 = c₀) && (st.mir.inTransit Q.other wc.1).isSome)
        then SM.deliverQuery (St := Fig8St Pt) Q c₀
        else SM.injectQuery (St := Fig8St Pt) Q c₀) >>= fun res => pure (res, st)) := by
  unfold fwd
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs <;> rfl

theorem bind_fwdC_eval (K : ℕ) {Γ u}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (c : Expr OO Γ (fig8CTy PQ PQC Pt ℓ))
    (k : Comp OO SIface (.opt (fig8RrTy PQ PQC Pt ℓ) :: Γ) u)
    (ρ : Env Γ) (st : SimState PQ Pt ℓ) (Q : Party) (c₀ : Fig8C Pt)
    (hTrans : st.mir.trans.length ≤ K) (hHonest : st.honest.length ≤ K)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q)
    (hc : c.eval ρ = c₀) :
    (Comp.bind (fwdC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s qParty c) k).eval ρ =
      ((if (st.honest.any fun wc => decide (wc.2 = c₀) && (st.mir.inTransit Q.other wc.1).isSome)
        then SM.deliverQuery (St := Fig8St Pt) Q c₀
        else SM.injectQuery (St := Fig8St Pt) Q c₀) >>= fun res =>
          k.eval (Env.cons (t := .opt (fig8RrTy PQ PQC Pt ℓ)) (res.map SM.smRrEnc) ρ)) := by
  rw [comp_eval_bind, fwdC_eval P Dh encT decT K s qParty c ρ st Q c₀ hTrans hHonest hs hq hc]
  by_cases hin : (st.honest.any fun wc =>
      decide (wc.2 = c₀) && (st.mir.inTransit Q.other wc.1).isSome) = true <;>
    simp [hin, bind_map_left]

private theorem min_counter_add_one (c : BitVec 32) :
    min (c.toNat + 1) (2 ^ 32) = c.toNat + 1 :=
  Nat.min_eq_left (by have := c.isLt; omega)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem ite_putS_bind_run (cond : Bool) (s₁ s₀ : SimState PQ Pt ℓ) {α : Type}
    (m : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) :
    (if cond = true then do putS s₁; m else m).run s₀ =
      m.run (if cond then s₁ else s₀) := by
  cases cond <;> rfl

theorem simRecvNewChainNormalC_eval (K qep : ℕ) {Γ}
    (ρ : Env Γ) (st : SimState PQ Pt ℓ) (Q : Party)
    (w₀ : List (BitVec 8)) (isDel₀ : Bool)
    (pq' : PQ) (i : ℕ) (pk : PublicKey) (T? : Option Pt) (lct : ℕ × LibsignalCiphertextWithSalt32)
    (hBound : SimStateBounded K st) :
    let ρ₁ := Env.cons (t := .prod simStateTy (.prod .bool (.prod (.base SimSort.wire) .bool)))
      (simStateEnc st, partyEnc Q, w₀, isDel₀) ρ
    let ρ₂ := Env.cons (t := parsedRecvTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
      (pq', i, pk, T?, lct) ρ₁
    let honestC := (st.honest.find? fun wc =>
      wc.1 == w₀ && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    let mkC (t : ℕ) (T : Option Pt) : Fig8C Pt :=
      match honestC with
      | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
      | none => ((t, T), lct)
    let spkAmb := Q == Party.A && (st.chains Q).any (·.key.isNone)
    let amb := inReceiveOnlyEpoch st.mir Q || spkAmb
    let stAmb := if amb then { st with amb := st.amb + 1 } else st
    (simRecvNewChainNormalC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K qep).eval ρ₂ =
      Prod.map (Option.map SM.smRrEnc) simStateEnc <$>
        ((if inReceiveOnlyEpoch st.mir Q || 25000 < i - 1 || 2 ^ 32 ≤ i then
            pure (some RecvResult.rejected)
          else
            match T? with
            | none => pure (some RecvResult.rejected)
            | some T => do
              let res ← fwd Q (mkC (st.mir.epoch Q + 1) (some T))
              onAnswer qep Q w₀ isDel₀ none pk pq' res).run stAmb) := by
  intro ρ₁ ρ₂ honestC mkC spkAmb amb stAmb
  have hBoundAmb : SimStateBounded K stAmb := by
    dsimp only [stAmb]
    split_ifs
    · exact ⟨hBound.1, hBound.2, hBound.3, hBound.4, hBound.5, hBound.6⟩
    · exact hBound
  have hsAmb2 :
      (sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
        (.fst .v1) (.fst (.snd .v1))).eval ρ₂ = simStateEnc stAmb :=
    sAmbE_eval P Dh encT decT (.fst .v1) (.fst (.snd .v1)) ρ₂ st Q (hBound.chains_le Q) rfl rfl
  unfold simRecvNewChainNormalC
  rw [comp_eval_ite]
  have hcond :
      (orE (mInWinE (ssMir (.fst (Expr.v1 (O := OO)))) (.fst (.snd .v1)))
        (orE (.lt (.nat 25000) (.sub (.fst (.snd .v0)) (.nat 1)))
          (leN (.nat (2 ^ 32)) (.fst (.snd .v0))))).eval ρ₂ =
      (inReceiveOnlyEpoch st.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) := by
    rw [orE_eval, orE_eval, mInWinE_eval (O' := OO) (ssMir (.fst .v1)) (.fst (.snd .v1))
      ρ₂ st.mir Q rfl rfl, leN_eval, Bool.or_assoc]
    rfl
  rw [hcond]
  by_cases h1 : (inReceiveOnlyEpoch st.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
  · simp only [h1, ↓reduceIte, comp_eval_ret, StateT.run_pure]
    simp [hsAmb2, SM.smRrEnc, Prod.map, Expr.eval]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [comp_eval_caseOpt]
    have hT0 : (Expr.fst (.snd (.snd (.snd (Expr.v0 (O := OO)))))).eval ρ₂ = T? := rfl
    rw [hT0]
    rcases T? with _ | T
    · simp [comp_eval_ret, hsAmb2, SM.smRrEnc, StateT.run_pure, Prod.map, Expr.eval]
    · dsimp only []
      let ρ₃ := Env.cons (t := .base SimSort.pt) T ρ₂
      have hmk :
          (mkCE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
              (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2))))
            (.snd (.snd (.snd (.snd .v1))))
            (.add (pGet (mEpoch (ssMir (.fst .v2))) (.fst (.snd .v2))) (.nat 1))
            (.some .v0)).eval ρ₃ =
          mkC (st.mir.epoch Q + 1) (some T) := by
        have hhc :
            (honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
              (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))).eval ρ₃ = honestC :=
          honestCE_eval P Dh encT decT K (.fst .v2) (.fst (.snd .v2))
            (.fst (.snd (.snd .v2))) ρ₃ st Q w₀ hBound.honest_le rfl rfl rfl
        have hep : (Expr.add (pGet (mEpoch (ssMir (.fst (Expr.v2 (O := OO)))))
            (.fst (.snd .v2))) (.nat 1)).eval ρ₃ = st.mir.epoch Q + 1 := by
          cases Q <;>
            simp [ρ₃, ρ₂, ρ₁, pGet_eval, mEpoch, ssMir, simStateEnc, simMirEnc, partyEnc,
              Expr.eval, Expr.v2]
        have hlct : (Expr.snd (.snd (.snd (.snd (Expr.v1 (O := OO)))))).eval ρ₃ = lct := rfl
        have hT : (Expr.some (Expr.v0 (O := OO))).eval ρ₃ = some T := rfl
        rw [mkCE_eval, hhc, hep, hlct, hT]
        dsimp only [mkC]
        generalize honestC = hc
        cases hc <;> rfl
      rw [bind_fwdC_eval P Dh encT decT K (.fst .v2) (.fst (.snd .v2)) _ _
        ρ₃ st Q (mkC (st.mir.epoch Q + 1) (some T))
        hBound.trans_le hBound.honest_le rfl rfl hmk]
      have hHonEq : stAmb.honest = st.honest := by dsimp only [stAmb]; split_ifs <;> rfl
      have hMirEq : stAmb.mir = st.mir := by dsimp only [stAmb]; split_ifs <;> rfl
      simp only [StateT.run_bind, fwd_run_eq, hHonEq, hMirEq, bind_assoc, pure_bind, map_bind]
      refine bind_congr fun res => ?_
      let ρ₄ := Env.cons (t := .opt (fig8RrTy PQ PQC Pt ℓ)) (res.map SM.smRrEnc) ρ₃
      have hsAmb4 :
          (sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (.fst .v3) (.fst (.snd .v3))).eval ρ₄ = simStateEnc stAmb :=
        sAmbE_eval P Dh encT decT (.fst .v3) (.fst (.snd .v3)) ρ₄ st Q (hBound.chains_le Q) rfl rfl
      exact ret_onAnswerE_eval P Dh encT decT K qep
        (sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT) (.fst .v3) (.fst (.snd .v3)))
        (.fst (.snd .v3))
        (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))
        .none (.fst (.snd (.snd .v2))) (.fst .v2) .v0
        ρ₄ stAmb Q res hBoundAmb hsAmb4 rfl rfl

theorem simRecvNewChainStopC_eval (K : ℕ) {Γ}
    (ρ : Env Γ) (st : SimState PQ Pt ℓ) (Q : Party)
    (w₀ : List (BitVec 8)) (isDel₀ : Bool)
    (pq' : PQ) (i : ℕ) (pk : PublicKey) (T? : Option Pt) (lct : ℕ × LibsignalCiphertextWithSalt32)
    (hBound : SimStateBounded K st) :
    let ρ₁ := Env.cons (t := .prod simStateTy (.prod .bool (.prod (.base SimSort.wire) .bool)))
      (simStateEnc st, partyEnc Q, w₀, isDel₀) ρ
    let ρ₂ := Env.cons (t := parsedRecvTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
      (pq', i, pk, T?, lct) ρ₁
    let honestC := (st.honest.find? fun wc =>
      wc.1 == w₀ && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    let mkC (t : ℕ) (T : Option Pt) : Fig8C Pt :=
      match honestC with
      | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
      | none => ((t, T), lct)
    let spkAmb := Q == Party.A && (st.chains Q).any (·.key.isNone)
    let amb := inReceiveOnlyEpoch st.mir Q || spkAmb
    let stAmb := if amb then { st with amb := st.amb + 1 } else st
    (simRecvNewChainStopC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K).eval ρ₂ =
      Prod.map (Option.map SM.smRrEnc) simStateEnc <$>
        ((if !(inReceiveOnlyEpoch st.mir Q) then do
            if !(25000 < i - 1 || 2 ^ 32 ≤ i) then
              match T? with
              | none => pure ()
              | some T => let _ ← fwd Q (mkC (st.mir.epoch Q + 1) (some T))
            modify fun s' : SimState PQ Pt ℓ => { s' with stopped := true }
            return none
          else do
            let _ ← liftQ (SM.transmitQuery (St := Fig8St Pt) Q
              (⟨0, [], effectiveHkdfSalt32 none, none⟩, default) none)
            match T? with
            | none => pure ()
            | some T => let _ ← fwd Q (mkC (st.mir.epoch Q + 2) (some T))
            modify fun s' : SimState PQ Pt ℓ => { s' with stopped := true }
            return none).run stAmb) := by
  intro ρ₁ ρ₂ honestC mkC spkAmb amb stAmb
  have hsAmb2 :
      (sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
        (.fst .v1) (.fst (.snd .v1))).eval ρ₂ = simStateEnc stAmb :=
    sAmbE_eval P Dh encT decT (.fst .v1) (.fst (.snd .v1)) ρ₂ st Q (hBound.chains_le Q) rfl rfl
  have hsStop2 :
      (ssSetStopped (sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
        (.fst .v1) (.fst (.snd .v1))) (.bool true)).eval ρ₂ =
      simStateEnc { stAmb with stopped := true } :=
    ssSetStopped_eval _ (.bool true) ρ₂ stAmb hsAmb2
  have hHonEq : stAmb.honest = st.honest := by dsimp only [stAmb]; split_ifs <;> rfl
  have hMirEq : stAmb.mir = st.mir := by dsimp only [stAmb]; split_ifs <;> rfl
  unfold simRecvNewChainStopC
  rw [comp_eval_ite]
  have hInw : (Expr.not (mInWinE (ssMir (.fst (Expr.v1 (O := OO)))) (.fst (.snd .v1)))).eval ρ₂ =
      !(inReceiveOnlyEpoch st.mir Q) := by
    simp only [Expr.eval,
      mInWinE_eval (O' := OO) (ssMir (.fst .v1)) (.fst (.snd .v1)) ρ₂ st.mir Q rfl rfl]
  rw [hInw]
  by_cases h1 : (!(inReceiveOnlyEpoch st.mir Q)) = true
  · simp only [h1, ↓reduceIte]
    rw [comp_eval_ite]
    have hcond :
        (Expr.not (orE (.lt (.nat 25000) (.sub (.fst (.snd (Expr.v0 (O := OO)))) (.nat 1)))
          (leN (.nat (2 ^ 32)) (.fst (.snd .v0))))).eval ρ₂ =
        !(decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) := by
      rw [Expr.eval, orE_eval, leN_eval]; rfl
    rw [hcond]
    by_cases h2 : (!(decide (25000 < i - 1) || decide (2 ^ 32 ≤ i))) = true
    · simp only [h2, ↓reduceIte]
      rw [comp_eval_caseOpt]
      have hT0 : (Expr.fst (.snd (.snd (.snd (Expr.v0 (O := OO)))))).eval ρ₂ = T? := rfl
      rw [hT0]
      rcases T? with _ | T
      · simp [comp_eval_ret, StateT.run_modify, Prod.map, Expr.eval]
        exact hsStop2
      · dsimp only []
        let ρ₃ := Env.cons (t := .base SimSort.pt) T ρ₂
        have hmk :
            (mkCE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
              (honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
                (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2))))
              (.snd (.snd (.snd (.snd .v1))))
              (.add (pGet (mEpoch (ssMir (.fst .v2))) (.fst (.snd .v2))) (.nat 1))
              (.some .v0)).eval ρ₃ =
            mkC (st.mir.epoch Q + 1) (some T) := by
          have hhc :
              (honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
                (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))).eval ρ₃ = honestC :=
            honestCE_eval P Dh encT decT K (.fst .v2) (.fst (.snd .v2))
              (.fst (.snd (.snd .v2))) ρ₃ st Q w₀ hBound.honest_le rfl rfl rfl
          have hep : (Expr.add (pGet (mEpoch (ssMir (.fst (Expr.v2 (O := OO)))))
              (.fst (.snd .v2))) (.nat 1)).eval ρ₃ = st.mir.epoch Q + 1 := by
            cases Q <;>
              simp [ρ₃, ρ₂, ρ₁, pGet_eval, mEpoch, ssMir, simStateEnc, simMirEnc, partyEnc,
                Expr.eval, Expr.v2]
          have hlct : (Expr.snd (.snd (.snd (.snd (Expr.v1 (O := OO)))))).eval ρ₃ = lct := rfl
          have hT : (Expr.some (Expr.v0 (O := OO))).eval ρ₃ = some T := rfl
          rw [mkCE_eval, hhc, hep, hlct, hT]
          dsimp only [mkC]
          generalize honestC = hc
          cases hc <;> rfl
        rw [bind_fwdC_eval P Dh encT decT K (.fst .v2) (.fst (.snd .v2)) _ _
          ρ₃ st Q (mkC (st.mir.epoch Q + 1) (some T))
          hBound.trans_le hBound.honest_le rfl rfl hmk]
        simp only [StateT.run_bind, fwd_run_eq, hHonEq, hMirEq, bind_assoc, pure_bind, map_bind]
        refine bind_congr fun res => ?_
        let ρ₄ := Env.cons (t := .opt (fig8RrTy PQ PQC Pt ℓ)) (res.map SM.smRrEnc) ρ₃
        have hsAmb4 :
            (sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
              (.fst .v3) (.fst (.snd .v3))).eval ρ₄ = simStateEnc stAmb :=
          sAmbE_eval P Dh encT decT (.fst .v3) (.fst (.snd .v3)) ρ₄ st Q
            (hBound.chains_le Q) rfl rfl
        have hsStop4 :
            (ssSetStopped (sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
              (.fst .v3) (.fst (.snd .v3))) (.bool true)).eval ρ₄ =
            simStateEnc { stAmb with stopped := true } :=
          ssSetStopped_eval _ (.bool true) ρ₄ stAmb hsAmb4
        simp [comp_eval_ret, StateT.run_modify, Prod.map, Expr.eval]
        exact hsStop4
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      simp [comp_eval_ret, StateT.run_modify, Prod.map, Expr.eval]
      exact hsStop2
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [comp_eval_bind]
    have htrQ :
        (Comp.query (I := SIface) SM.SMTag.tr (.pair (.fst (.snd (Expr.v1 (O := OO))))
          (.pair (.pair (Expr.op (O := OO) SimOp.emptyLPub .unit)
            (Expr.op (O := OO) SimOp.defaultPlain .unit)) .none))).eval ρ₂ =
        SM.transmitQuery (St := Fig8St Pt) Q
          (⟨0, [], effectiveHkdfSalt32 none, none⟩, default) none := by
      rw [query_tr_eval]
      simp [ρ₂, ρ₁, partyDec_partyEnc, simOps, Expr.eval, Expr.v1]
    rw [htrQ]
    simp only [StateT.run_bind, liftQ, stateT_lift_run, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun trRes => ?_
    let ρ₃ := Env.cons (t := .opt (fig8CTy PQ PQC Pt ℓ)) trRes ρ₂
    rw [comp_eval_caseOpt]
    have hT1 : (Expr.fst (.snd (.snd (.snd (Expr.v1 (O := OO)))))).eval ρ₃ = T? := rfl
    rw [hT1]
    rcases T? with _ | T
    · have hsAmb3 :
          (sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (.fst .v2) (.fst (.snd .v2))).eval ρ₃ = simStateEnc stAmb :=
        sAmbE_eval P Dh encT decT (.fst .v2) (.fst (.snd .v2)) ρ₃ st Q
          (hBound.chains_le Q) rfl rfl
      have hsStop3 :
          (ssSetStopped (sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (.fst .v2) (.fst (.snd .v2))) (.bool true)).eval ρ₃ =
          simStateEnc { stAmb with stopped := true } :=
        ssSetStopped_eval _ (.bool true) ρ₃ stAmb hsAmb3
      simp [comp_eval_ret, StateT.run_modify, Prod.map, Expr.eval]
      exact hsStop3
    · dsimp only []
      let ρ₄ := Env.cons (t := .base SimSort.pt) T ρ₃
      have hmk :
          (mkCE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
              (.fst .v3) (.fst (.snd .v3)) (.fst (.snd (.snd .v3))))
            (.snd (.snd (.snd (.snd .v2))))
            (.add (pGet (mEpoch (ssMir (.fst .v3))) (.fst (.snd .v3))) (.nat 2))
            (.some .v0)).eval ρ₄ =
          mkC (st.mir.epoch Q + 2) (some T) := by
        have hhc :
            (honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
              (.fst .v3) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))).eval ρ₄ = honestC :=
          honestCE_eval P Dh encT decT K (.fst .v3) (.fst (.snd .v3))
            (.fst (.snd (.snd .v3))) ρ₄ st Q w₀ hBound.honest_le rfl rfl rfl
        have hep : (Expr.add (pGet (mEpoch (ssMir (.fst (Expr.v3 (O := OO)))))
            (.fst (.snd .v3))) (.nat 2)).eval ρ₄ = st.mir.epoch Q + 2 := by
          cases Q <;>
            simp [ρ₄, ρ₃, ρ₂, ρ₁, pGet_eval, mEpoch, ssMir, simStateEnc, simMirEnc, partyEnc,
              Expr.eval, Expr.v3]
        have hlct : (Expr.snd (.snd (.snd (.snd (Expr.v2 (O := OO)))))).eval ρ₄ = lct := rfl
        have hT : (Expr.some (Expr.v0 (O := OO))).eval ρ₄ = some T := rfl
        rw [mkCE_eval, hhc, hep, hlct, hT]
        dsimp only [mkC]
        generalize honestC = hc
        cases hc <;> rfl
      rw [bind_fwdC_eval P Dh encT decT K (.fst .v3) (.fst (.snd .v3)) _ _
        ρ₄ st Q (mkC (st.mir.epoch Q + 2) (some T))
        hBound.trans_le hBound.honest_le rfl rfl hmk]
      simp only [StateT.run_bind, fwd_run_eq, hHonEq, hMirEq, bind_assoc, pure_bind, map_bind]
      refine bind_congr fun res => ?_
      let ρ₅ := Env.cons (t := .opt (fig8RrTy PQ PQC Pt ℓ)) (res.map SM.smRrEnc) ρ₄
      have hsAmb5 :
          (sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (.fst .v4) (.fst (.snd .v4))).eval ρ₅ = simStateEnc stAmb :=
        sAmbE_eval P Dh encT decT (.fst .v4) (.fst (.snd .v4)) ρ₅ st Q
          (hBound.chains_le Q) rfl rfl
      have hsStop5 :
          (ssSetStopped (sAmbE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
            (.fst .v4) (.fst (.snd .v4))) (.bool true)).eval ρ₅ =
          simStateEnc { stAmb with stopped := true } :=
        ssSetStopped_eval _ (.bool true) ρ₅ stAmb hsAmb5
      simp [comp_eval_ret, StateT.run_modify, Prod.map, Expr.eval]
      exact hsStop5

theorem simRecvC_eval (K qep : ℕ) (k : Option ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (w : Expr OO Γ (.base .wire)) (isDel : Expr OO Γ .bool) (ρ : Env Γ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hBound : SimStateBounded K st)
    (hs : s.eval ρ = simStateEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (simRecvC P Dh encT decT K qep k s qParty w isDel).eval ρ =
      Prod.map (Option.map SM.smRrEnc) simStateEnc <$>
        ((simRecv P encT decT qep k Q (w.eval ρ) (isDel.eval ρ)).run st) := by
  unfold simRecvC simRecv
  rw [comp_eval_bind_ret]
  have h0 : (Expr.pair s (.pair qParty (.pair w isDel))).eval ρ =
      (simStateEnc st, partyEnc Q, w.eval ρ, isDel.eval ρ) := by
    simp [Expr.eval, hs, hq]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod simStateTy (.prod .bool (.prod (.base SimSort.wire) .bool)))
    (simStateEnc st, partyEnc Q, w.eval ρ, isDel.eval ρ) ρ
  rw [comp_eval_ite]
  have href :
      (orE (mWin (ssMir (.fst (Expr.v0 (O := OO)))))
        (orE (.and (.snd (.snd (.snd .v0)))
            (.not (isSomeE (mInTransitE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
              (ssMir (.fst .v0)) (otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))))))
          (.and (.not (.snd (.snd (.snd .v0))))
            (orE (isSomeE (mInTransitE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
                (ssMir (.fst .v0)) (otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))))
              (orE (.not (mSafeInjE (ssMir (.fst .v0))))
                (.not (Expr.op (O := OO) SimOp.injOK (.fst (.snd (.snd .v0)))))))))).eval ρ₁ =
      (st.mir.win ||
        ((isDel.eval ρ && (st.mir.inTransit Q.other (w.eval ρ)).isNone) ||
         (!isDel.eval ρ && ((st.mir.inTransit Q.other (w.eval ρ)).isSome || !(st.mir.safeInj 3) ||
            !(ratchetKeyAdmissible P.codec decT encT (w.eval ρ)))))) := by
    have hinTr := mInTransitE_eval (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
      (ssMir (.fst .v0)) (otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
      ρ₁ st.mir Q.other hBound.trans_le rfl
      (by simp [ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v0])
    have his := isSomeE_eval
      (mInTransitE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
        (ssMir (.fst .v0)) (otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))) ρ₁
    have hsi := mSafeInjE_eval (O' := OO) (ssMir (.fst .v0)) ρ₁ st.mir rfl
    rw [orE_eval, orE_eval]
    dsimp only [Expr.eval]
    rw [orE_eval, orE_eval]
    dsimp only [Expr.eval]
    rw [his, hinTr, hsi]
    simp [ρ₁, mWin, ssMir, simStateEnc, simMirEnc, simOps,
      Bool.or_assoc, Expr.eval, Expr.v0]
  rw [href]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hwin : st.mir.win = true
  · simp [ρ₁, hwin, comp_eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · simp only [hwin, Bool.false_eq_true, Bool.false_or, ↓reduceIte]
    by_cases hdelRef : (isDel.eval ρ && (st.mir.inTransit Q.other (w.eval ρ)).isNone) = true
    · simp [ρ₁, hdelRef, comp_eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp only [hdelRef, Bool.false_eq_true, Bool.false_or, ↓reduceIte]
      by_cases hinjRef : (!isDel.eval ρ && ((st.mir.inTransit Q.other (w.eval ρ)).isSome ||
          !(st.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT (w.eval ρ)))) = true
      · simp [ρ₁, hinjRef, comp_eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
      · simp only [hinjRef, Bool.false_eq_true, ↓reduceIte]
        rw [comp_eval_caseOpt]
        have hparseOp :
            (parseRecvE (P := P) (Dh := Dh) (encT := encT) (decT := decT) (2 ^ 32)
              (.pair (.fst (.snd .v0))
                (.pair (pGet (ssPq (.fst .v0)) (.fst (.snd .v0)))
                  (.fst (.snd (.snd .v0)))))).eval ρ₁ =
            simParseRecv P decT (2 ^ 32) (partyEnc Q) (st.pq Q) (w.eval ρ) := by
          refine parseRecvE_eval P Dh encT decT (2 ^ 32) _ ρ₁
            (partyEnc Q) (st.pq Q) (w.eval ρ) ?_
          cases Q <;>
            simp [ρ₁, pGet_eval, ssPq, simStateEnc, partyEnc, Expr.eval, Expr.v0]
        rw [hparseOp]
        unfold simParseRecv
        rw [partyDec_partyEnc]
        by_cases hlen : (w.eval ρ).length < 9
        · simp [ρ₁, hlen, comp_eval_ret, SM.smRrEnc, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
        · simp only [hlen, ↓reduceIte]
          rcases hwire :
              (signalWireCodec P.codec).parse ((w.eval ρ).take ((w.eval ρ).length - 8)) with
            _ | ⟨h, rest⟩
          · simp [ρ₁, comp_eval_ret, SM.smRrEnc, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
          · by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
            · simp [ρ₁, haddr, comp_eval_ret, SM.smRrEnc, StateT.run_pure, Prod.map,
                Expr.eval, Expr.v0]
            · simp only [haddr, Bool.false_eq_true, ↓reduceIte]
              rcases hspqr : P.spqr.recv (st.pq Q) h.pqRatchet with err | ⟨pq', salt⟩
              · simp [ρ₁, comp_eval_ret, SM.smRrEnc, StateT.run_pure, Prod.map,
                  Expr.eval, Expr.v0]
              · simp only [min_counter_add_one h.counter]
                set i := h.counter.toNat + 1
                set pk := h.senderRatchetKey
                set T? := decT h.senderRatchetKey
                set ser := (w.eval ρ).take ((w.eval ρ).length - 8)
                set tag := bytesToWord64LE ((w.eval ρ).drop ((w.eval ρ).length - 8))
                set lct : ℕ × LibsignalCiphertextWithSalt32 := (i, ((ser, tag), effectiveHkdfSalt32 salt))
                set ρ₂ := Env.cons
                  (t := parsedRecvTy (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
                  (pq', i, pk, T?, lct) ρ₁
                rw [comp_eval_caseOpt]
                have hfindC :
                    (findChainE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
                      (.pair (pGet (ssChains (.fst .v1)) (.fst (.snd .v1)))
                        (.fst (.snd (.snd .v0))))).eval ρ₂ =
                    match (st.chains Q).findIdx? (fun g => g.key == some pk) with
                    | some ci => some (ci, ghostChainEnc ((st.chains Q).getD ci ⟨none, 0, 0, []⟩))
                    | none => none := by
                  rw [← simFindChain_map_ghostChainEnc (st.chains Q) pk]
                  refine findChainE_eval P Dh encT decT _ ρ₂
                    ((st.chains Q).map ghostChainEnc) pk
                    (by rw [List.length_map]; exact hBound.chains_le Q) ?_
                  cases Q <;>
                    simp [ρ₂, ρ₁, pGet_eval, ssChains, simStateEnc, partyEnc,
                      Expr.eval, Expr.v0, Expr.v1]
                rw [hfindC]
                rcases hidx : (st.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci
                · simp only [hidx]
                  rw [comp_eval_ite]
                  have hev := evictedHonestE_eval P Dh encT decT (.fst .v1) (.fst (.snd .v1))
                    (honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
                      (.fst .v1) (.fst (.snd .v1)) (.fst (.snd (.snd .v1))))
                    ρ₂ st Q rfl rfl
                  have hhc2 := honestCE_eval P Dh encT decT K (.fst .v1) (.fst (.snd .v1))
                    (.fst (.snd (.snd .v1))) ρ₂ st Q (w.eval ρ) hBound.honest_le rfl rfl rfl
                  rw [hhc2] at hev
                  rw [hev]
                  set honestC := (st.honest.find? fun wc =>
                    wc.1 == w.eval ρ && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
                  by_cases hevCond :
                      ((honestC.map fun c => decide (c.1.1 ≠ st.mir.epoch Q + 1)) == some true) =
                        true
                  · simp only [hevCond, ↓reduceIte]
                    simp [ρ₂, ρ₁, comp_eval_ret, SM.smRrEnc, StateT.run_pure, Prod.map,
                      Expr.eval, Expr.v1]
                  · simp only [hevCond, Bool.false_eq_true, ↓reduceIte]
                    rw [comp_eval_ite]
                    have hzero : (Expr.op (O := OO) SimOp.isZeroPt
                        (.fst (.snd (.snd (.snd .v0))))).eval ρ₂ = (T? == some 0) := rfl
                    rw [hzero]
                    by_cases hzCond : (T? == some 0) = true
                    · simp [ρ₂, ρ₁, hzCond, comp_eval_ret, SM.smRrEnc, StateT.run_pure, Prod.map,
                        Expr.eval, Expr.v1]
                    · simp only [hzCond, Bool.false_eq_true, ↓reduceIte]
                      rw [ite_putS_bind_run]
                      rcases k with _ | k₀
                      · have hnone : ((none : Option ℕ) == some st.amb) = false := rfl
                        have hambNone :
                            ((inReceiveOnlyEpoch st.mir Q ||
                              (Q == Party.A && (st.chains Q).any (·.key.isNone))) &&
                              ((none : Option ℕ) == some st.amb)) = false := by
                          rw [hnone, Bool.and_false]
                        simp only [hambNone, Bool.false_eq_true, ↓reduceIte]
                        exact simRecvNewChainNormalC_eval P Dh encT decT K qep
                          ρ st Q (w.eval ρ) (isDel.eval ρ) pq' i pk T? lct hBound
                      · rw [comp_eval_ite]
                        have hambK :
                            (Expr.and
                              (ambCondE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
                                (.fst .v1) (.fst (.snd .v1)))
                              (.eqN (ssAmb (.fst .v1)) (.nat k₀))).eval ρ₂ =
                            ((inReceiveOnlyEpoch st.mir Q ||
                              (Q == Party.A && (st.chains Q).any (·.key.isNone))) &&
                              (some k₀ == some st.amb)) := by
                          rw [Expr.eval,
                            ambCondE_eval P Dh encT decT (.fst .v1) (.fst (.snd .v1))
                              ρ₂ st Q (hBound.chains_le Q) rfl rfl]
                          congr 1
                          change (st.amb == k₀) = (some k₀ == some st.amb)
                          by_cases hk : st.amb = k₀
                          · simp [hk]
                          · simp [hk, Ne.symm hk]
                        rw [hambK]
                        by_cases hkCond :
                            ((inReceiveOnlyEpoch st.mir Q ||
                              (Q == Party.A && (st.chains Q).any (·.key.isNone))) &&
                              (some k₀ == some st.amb)) = true
                        · simp only [hkCond, ↓reduceIte]
                          exact simRecvNewChainStopC_eval P Dh encT decT K
                            ρ st Q (w.eval ρ) (isDel.eval ρ) pq' i pk T? lct hBound
                        · simp only [hkCond, Bool.false_eq_true, ↓reduceIte]
                          exact simRecvNewChainNormalC_eval P Dh encT decT K qep
                            ρ st Q (w.eval ρ) (isDel.eval ρ) pq' i pk T? lct hBound
                · simp only [hidx]
                  set g := (st.chains Q).getD ci ⟨none, 0, 0, []⟩
                  set ρ₃ := Env.cons (t := .prod .nat (ghostChainTy PQ PQC Pt ℓ))
                    (ci, ghostChainEnc g) ρ₂
                  rw [comp_eval_ite]
                  have hrej : (Expr.op (O := OO) SimOp.chainRejects
                      (.pair (.snd (.snd (.snd .v0))) (.fst (.snd .v1)))).eval ρ₃ =
                      g.rejects i := by
                    simp [ρ₃, ρ₂, simOps, Expr.eval, Expr.v0, Expr.v1]
                  rw [hrej]
                  by_cases hrejCond : g.rejects i = true
                  · simp [ρ₃, ρ₂, ρ₁, hrejCond, comp_eval_ret, SM.smRrEnc, StateT.run_pure, Prod.map,
                      Expr.eval, Expr.v2]
                  · simp only [hrejCond, Bool.false_eq_true, ↓reduceIte]
                    set honestC := (st.honest.find? fun wc =>
                      wc.1 == w.eval ρ && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
                    set mkC : ℕ → Option Pt → Fig8C Pt := fun t T =>
                      match honestC with
                      | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
                      | none => ((t, T), lct)
                    have hmk :
                        (mkCE (P := P) (Dh := Dh) (encT := encT) (decT := decT)
                          (honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
                            (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2))))
                          (.snd (.snd (.snd (.snd .v1))))
                          (.fst (.snd (.snd .v0)))
                          (.fst (.snd (.snd (.snd .v1))))).eval ρ₃ =
                        mkC g.epoch T? := by
                      have hhc :
                          (honestCE (P := P) (Dh := Dh) (encT := encT) (decT := decT) K
                            (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))).eval ρ₃ =
                          honestC :=
                        honestCE_eval P Dh encT decT K (.fst .v2) (.fst (.snd .v2))
                          (.fst (.snd (.snd .v2))) ρ₃ st Q (w.eval ρ) hBound.honest_le rfl rfl rfl
                      have hlct : (Expr.snd (.snd (.snd (.snd (Expr.v1 (O := OO)))))).eval ρ₃ =
                          lct := rfl
                      have hepg : (Expr.fst (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₃ =
                          g.epoch := rfl
                      have hT : (Expr.fst (.snd (.snd (.snd (Expr.v1 (O := OO)))))).eval ρ₃ =
                          T? := rfl
                      rw [mkCE_eval, hhc, hlct, hepg, hT]
                      dsimp only [mkC]
                      generalize honestC = hc
                      cases hc <;> rfl
                    rw [bind_fwdC_eval P Dh encT decT K (.fst .v2) (.fst (.snd .v2)) _ _
                      ρ₃ st Q (mkC g.epoch T?)
                      hBound.trans_le hBound.honest_le rfl rfl hmk]
                    simp only [StateT.run_bind, fwd_run_eq, bind_assoc, pure_bind, map_bind]
                    refine bind_congr fun res => ?_
                    let ρ₄ := Env.cons (t := .opt (fig8RrTy PQ PQC Pt ℓ)) (res.map SM.smRrEnc) ρ₃
                    exact ret_onAnswerE_eval P Dh encT decT K qep
                      (.fst .v3) (.fst (.snd .v3))
                      (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))
                      (.some (.fst .v1)) (.fst (.snd (.snd .v2))) (.fst .v2) .v0
                      ρ₄ st Q res hBound rfl rfl rfl

theorem handlerImpl_simHandleC_tr (K qep : ℕ) (k : Option ℕ)
    (st : SimState PQ Pt ℓ) (Q : Party) (m : Plain ℓ) (r : Option PQC) :
    ((handlerImpl (C := simCodec PQ PQC Pt ℓ) (simHandleC P Dh encT decT K qep k)
      (.inr (.inl (.inl (.inl (.inl (Q, m, r))))))).run (simStateEnc st)) =
      Prod.map id simStateEnc <$>
        ((«guard» (simSend P qep Q m none r)).run st) := by
  unfold handlerImpl simHandleC simCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Env.get,
    bind_assoc, pure_bind]
  rw [guardC_eval P Dh encT decT _ _ _ st id (simSend P qep Q m none r) rfl rfl
    (simSendC_eval P Dh encT decT qep _ _ _ _ _ _ st Q rfl rfl)]
  rw [bind_map_left, map_eq_bind_pure_comp]
  rfl

theorem handlerImpl_simHandleC_ch (K qep : ℕ) (k : Option ℕ)
    (st : SimState PQ Pt ℓ) (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC) :
    ((handlerImpl (C := simCodec PQ PQC Pt ℓ) (simHandleC P Dh encT decT K qep k)
      (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))))).run (simStateEnc st)) =
      Prod.map id simStateEnc <$>
        ((«guard» (simSend P qep Q m₀ (some m₁) r)).run st) := by
  unfold handlerImpl simHandleC simCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Env.get,
    bind_assoc, pure_bind]
  rw [guardC_eval P Dh encT decT _ _ _ st id (simSend P qep Q m₀ (some m₁) r) rfl rfl
    (simSendC_eval P Dh encT decT qep _ _ _ _ _ _ st Q rfl rfl)]
  rw [bind_map_left, map_eq_bind_pure_comp]
  rfl

theorem handlerImpl_simHandleC_dl (K qep : ℕ) (k : Option ℕ)
    (st : SimState PQ Pt ℓ) (Q : Party) (w : List (BitVec 8))
    (hBound : SimStateBounded K st) :
    ((handlerImpl (C := simCodec PQ PQC Pt ℓ) (simHandleC P Dh encT decT K qep k)
      (.inr (.inl (.inl (.inr (Q, w)))))).run (simStateEnc st)) =
      Prod.map id simStateEnc <$>
        ((«guard» (simRecv P encT decT qep k Q w true)).run st) := by
  unfold handlerImpl simHandleC simCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Env.get,
    bind_assoc, pure_bind]
  rw [guardC_eval P Dh encT decT _ _ _ st (Option.map SM.smRrEnc)
    (simRecv P encT decT qep k Q w true) rfl rfl
    (simRecvC_eval P Dh encT decT K qep k _ _ _ _ _ st Q hBound rfl rfl)]
  rw [bind_map_left, map_eq_bind_pure_comp]
  refine bind_congr fun ⟨r', s'⟩ => ?_
  cases r' <;> simp [Prod.map]

theorem handlerImpl_simHandleC_ij (K qep : ℕ) (k : Option ℕ)
    (st : SimState PQ Pt ℓ) (Q : Party) (w : List (BitVec 8))
    (hBound : SimStateBounded K st) :
    ((handlerImpl (C := simCodec PQ PQC Pt ℓ) (simHandleC P Dh encT decT K qep k)
      (.inr (.inl (.inr (Q, w))))).run (simStateEnc st)) =
      Prod.map id simStateEnc <$>
        ((«guard» (simRecv P encT decT qep k Q w false)).run st) := by
  unfold handlerImpl simHandleC simCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Env.get,
    bind_assoc, pure_bind]
  rw [guardC_eval P Dh encT decT _ _ _ st (Option.map SM.smRrEnc)
    (simRecv P encT decT qep k Q w false) rfl rfl
    (simRecvC_eval P Dh encT decT K qep k _ _ _ _ _ st Q hBound rfl rfl)]
  rw [bind_map_left, map_eq_bind_pure_comp]
  refine bind_congr fun ⟨r', s'⟩ => ?_
  cases r' <;> simp [Prod.map]

def simImplDedup (qep : ℕ) (k : Option ℕ) :
    QueryImpl (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ)) :=
  let c : QueryImpl unifSpec (StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ)) := fun n =>
    liftQ (query (spec := unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (.inl n))
  let i₁ : QueryImpl ((Party × Plain ℓ × Option PQC) →ₒ Option (List (BitVec 8)))
      (StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ)) :=
    fun ⟨Q, m, r⟩ => «guard» (simSend (P := P) (qep := qep) Q m none r)
  let i₂ : QueryImpl ((Party × Plain ℓ × Plain ℓ × Option PQC) →ₒ Option (List (BitVec 8)))
      (StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ)) :=
    fun ⟨Q, m₀, m₁, r⟩ => «guard» (simSend (P := P) (qep := qep) Q m₀ (some m₁) r)
  let i₃ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ)))
      (StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ)) :=
    fun ⟨Q, w⟩ =>
      «guard» (simRecv (P := P) (encT := encT) (decT := decT) (qep := qep) (k := k) Q w true)
  let i₄ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ)))
      (StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ)) :=
    fun ⟨Q, w⟩ =>
      «guard» (simRecv (P := P) (encT := encT) (decT := decT) (qep := qep) (k := k) Q w false)
  let i₅ : QueryImpl (Party →ₒ Option (GhostState PQ))
      (StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ)) :=
    fun Q => «guard» (simCorrDedup P Dh encT Q)
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

theorem handlerImpl_simHandleC_cr (K qep : ℕ) (k : Option ℕ)
    (st : SimState PQ Pt ℓ) (Q : Party)
    (hBound : SimStateBounded K st) :
    ((handlerImpl (C := simCodec PQ PQC Pt ℓ) (simHandleC P Dh encT decT K qep k)
      (.inr (.inr Q))).run (simStateEnc st)) =
      Prod.map id simStateEnc <$>
        ((«guard» (simCorrDedup P Dh encT Q)).run st) := by
  unfold handlerImpl simHandleC simCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Env.get,
    bind_assoc, pure_bind]
  rw [guardC_eval P Dh encT decT _ _ _ st id (simCorrDedup P Dh encT Q) rfl rfl
    (simCorrC_eval P Dh encT decT K _ _ _ st Q hBound rfl rfl)]
  rw [bind_map_left, map_eq_bind_pure_comp]
  rfl

/-- Step-level evaluation agreement between `(simRunProg K qep k).impl` and `simImplDedup` under
`SimStateBounded K st`. -/
theorem simImpl_eval (K qep : ℕ) (k : Option ℕ)
    (q : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : SimState PQ Pt ℓ) (hBound : SimStateBounded K st) :
    (((simRunProg P Dh encT decT K qep k).impl q).run (simStateEnc st)) =
      Prod.map id simStateEnc <$>
        ((simImplDedup P Dh encT decT qep k q).run st) := by
  rcases q with n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · simp [CostedReduction.impl, handlerImpl, simRunProg, simImplDedup, simIface, simParamIface,
      liftQ, StateT.run_lift, Prod.map, map_eq_bind_pure_comp]
  · exact handlerImpl_simHandleC_tr P Dh encT decT K qep k st Q m r
  · exact handlerImpl_simHandleC_ch P Dh encT decT K qep k st Q m₀ m₁ r
  · exact handlerImpl_simHandleC_dl P Dh encT decT K qep k st Q w hBound
  · exact handlerImpl_simHandleC_ij P Dh encT decT K qep k st Q w hBound
  · exact handlerImpl_simHandleC_cr P Dh encT decT K qep k st Q hBound

/-- Query-budget invariant on `SimState PQ Pt ℓ` with `m` adversary game queries remaining. -/
def SimStateInv (K m : ℕ) (st : SimState PQ Pt ℓ) : Prop :=
  st.mir.trans.length + m ≤ K ∧ st.mir.chall.length + m ≤ K ∧
  st.honest.length + m ≤ K ∧
  (∃ U : List Pos, U.length + m ≤ K ∧ CountLe st.mir.comp U ∧ ∀ r ∈ st.mir.trans, r.pos ∈ U) ∧
  (st.chains .A).length ≤ 5 ∧ (st.chains .B).length ≤ 5

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem SimStateInv.mono {K m₁ m₂ : ℕ} {st : SimState PQ Pt ℓ}
    (hle : m₁ ≤ m₂) (h : SimStateInv K m₂ st) : SimStateInv K m₁ st := by
  rcases h.2.2.2.1 with ⟨U, hUlen, hCU, htrU⟩
  exact ⟨by have := h.1; omega, by have := h.2.1; omega, by have := h.2.2.1; omega,
    ⟨U, by omega, hCU, htrU⟩, h.2.2.2.2.1, h.2.2.2.2.2⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem SimStateInv.toBounded {K m : ℕ} {st : SimState PQ Pt ℓ}
    (h : SimStateInv K m st) : SimStateBounded K st := by
  rcases h.2.2.2.1 with ⟨U, hUlen, hCU, htrU⟩
  exact ⟨by have := h.1; omega, by have := h.2.1; omega,
    by have := h.2.2.1; omega, ⟨U, by omega, hCU, htrU⟩,
    h.2.2.2.2.1, h.2.2.2.2.2⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem SimStateInv.init {K q : ℕ} (hqK : q ≤ K) (pqA pqB : PQ) :
    SimStateInv K q (initSim (Pt := Pt) (ℓ := ℓ) pqA pqB) := by
  simp only [SimStateInv, initSim, List.length_nil, zero_add]
  exact ⟨hqK, hqK, hqK, ⟨[], by simp [hqK], countLe_nil [], fun _ h => nomatch h⟩,
    by decide, by decide⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp] theorem simBoundInv_simStateEnc (K m : ℕ) (st : SimState PQ Pt ℓ) :
    SimBoundInv (PQC := PQC) K m (simStateEnc st) ↔ SimStateInv K m st := by
  simp [SimBoundInv, SimStateInv]

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

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem guard_preserves_inv {K m : ℕ} {α : Type}
    (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α))
    (st : SimState PQ Pt ℓ) (hInv : SimStateInv K m st)
    (hx : ∀ r ∈ support (x.run st), SimStateInv K m r.2) :
    ∀ r ∈ support ((«guard» x).run st), SimStateInv K m r.2 := by
  intro r hr
  unfold «guard» at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  cases h : st.stopped
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hr
    exact hx r hr
  · simp only [h, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hInv

omit [DecidableEq Pt] [Zero Pt] in
theorem simSend_preserves_inv (qep K m : ℕ) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (rCoins : Option PQC) (st : SimState PQ Pt ℓ)
    (hInv : SimStateInv K (m + 1) st) :
    ∀ r ∈ support ((simSend P qep Q m₀ chal rCoins).run st), SimStateInv K m r.2 := by
  have hInv0 : SimStateInv K m st := hInv.mono (Nat.le_succ m)
  intro r hr
  unfold simSend at hr
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases h1 : (st.mir.win || !(noBobSendInEpoch0 st.mir Q)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hInv0
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hr
    rcases hep : st.mir.epMgmt 3 qep Q rCoins.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hInv0
    · simp only [hep] at hr
      by_cases h2 : (chal.isSome && !s₁.safeCh 3 Q) = true
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hInv0
      · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hr
        obtain ⟨htr, hch, hcp⟩ := epMgmt_lists st.mir s₁ 3 qep Q rCoins.isSome hep
        suffices hpost : ∀ (rq : PQC) (rc : Option (BitVec 256)),
            r ∈ support ((do
              let pn := if s₁.epoch Q ≠ st.mir.epoch Q then
                BitVec.ofNat 32 (st.mir.idx Q - 1) else st.pn Q
              match mkPub (P := P) st Q rq pn with
              | none => return none
              | some (pq', pub) =>
                let res ← match chal with
                  | none => liftQ (SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc)
                  | some m₁ => liftQ (SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc)
                match res with
                | none => return none
                | some c =>
                  let w := toWire c
                  let rec' : Record (Plain ℓ) (List (BitVec 8)) :=
                    ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
                  let mir' := s₁.record 3 Q () rec' chal.isSome
                  putS { st with
                    mir := mir', pq := Function.update st.pq Q pq',
                    pn := Function.update st.pn Q pn,
                    honest := (w, c) :: st.honest }
                  return some w).run st) →
              SimStateInv K m r.2 by
          rcases rCoins with _ | rq₀
          · simp only [coin, liftQ, stateT_lift_run, StateT.run_bind,
              bind_assoc, pure_bind, mem_support_bind_iff] at hr
            obtain ⟨rq, -, hr⟩ := hr
            exact hpost rq none hr
          · simp only [coin, liftQ, stateT_lift_run, StateT.run_bind,
              bind_map_left, bind_assoc, pure_bind, mem_support_bind_iff] at hr
            obtain ⟨c, -, hr⟩ := hr
            exact hpost rq₀ (some c) hr
        intro rq rc hr
        dsimp only [] at hr
        rcases hpub : mkPub P st Q rq
            (if s₁.epoch Q ≠ st.mir.epoch Q then BitVec.ofNat 32 (st.mir.idx Q - 1)
             else st.pn Q) with _ | ⟨pq', pub⟩
        · simp only [hpub, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hInv0
        · simp only [hpub] at hr
          generalize hbChal : chal.isSome = bChal at hr
          obtain ⟨res, hr⟩ : ∃ res : Option (Fig8C Pt),
              r ∈ support ((match res with
                | none => pure none
                | some c => do
                  putS { st with
                    mir := s₁.record 3 Q ()
                      ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, toWire c⟩ bChal,
                    pq := Function.update st.pq Q pq',
                    pn := Function.update st.pn Q
                      (if s₁.epoch Q ≠ st.mir.epoch Q then BitVec.ofNat 32 (st.mir.idx Q - 1)
                       else st.pn Q),
                    honest := (toWire c, c) :: st.honest }
                  pure (some (toWire c))).run st) := by
            rcases chal with _ | m₁ <;>
              (simp only [liftQ, stateT_lift_run, StateT.run_bind, bind_assoc,
                 pure_bind, mem_support_bind_iff] at hr;
               obtain ⟨res, -, hr⟩ := hr;
               exact ⟨res, hr⟩)
          rcases res with _ | c
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact hInv0
          · simp only [putS, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hr
            subst hr
            refine ⟨?_, ?_, ?_, ?_, hInv0.2.2.2.2.1, hInv0.2.2.2.2.2⟩
            · simp only [GameState.record, List.length_cons, htr]
              have := hInv.1; omega
            · simp only [GameState.record, hch]
              cases bChal <;>
                simp only [↓reduceIte, Bool.false_eq_true, List.length_cons] <;>
                (have := hInv.2.1; omega)
            · simp only [List.length_cons]
              have := hInv.2.2.1; omega
            · rcases hInv.2.2.2.1 with ⟨U, hUlen, hCU, htrU⟩
              refine ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩ :: U,
                by simp only [List.length_cons]; omega, ?_, ?_⟩
              · simp only [GameState.record, hcp]
                cases s₁.safeCh 3 Q
                · exact countLe_cons_cons _ hCU
                · exact countLe_cons_right _ hCU
              · intro r' hr'
                simp only [GameState.record, htr, List.mem_cons] at hr'
                rcases hr' with rfl | hr'
                · simp
                · exact List.mem_cons_of_mem _ (htrU r' hr')

private theorem pushChain_length_le (cs : List GhostChain) (c : GhostChain) :
    (pushChain cs c).length ≤ 5 := by
  dsimp only [pushChain]
  rw [List.length_drop, List.length_append, List.length_singleton]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem onAccept_preserves_inv (qep K m : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (msg : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (st : SimState PQ Pt ℓ) (hInv : SimStateInv K m st) :
    ∀ r ∈ support ((onAccept qep Q w isDel t i msg ci? T pq').run st),
      SimStateInv K m r.2 := by
  have hacc : ∀ pos : Pos,
      SimStateInv K m
        { st with
          chains := Function.update st.chains Q
            (match ci? with
             | some ci => (st.chains Q).modify ci (·.accept i)
             | none => pushChain (st.chains Q) (GhostChain.accept ⟨some T, t, 0, []⟩ i)),
          pq := Function.update st.pq Q pq',
          unackA := st.unackA && Q != Party.A,
          mir := st.mir.accept Q () pos } := by
    intro pos
    have hch_len : ∀ P₀ : Party,
        (Function.update st.chains Q
          (match ci? with
           | some ci => (st.chains Q).modify ci (·.accept i)
           | none => pushChain (st.chains Q) (GhostChain.accept ⟨some T, t, 0, []⟩ i))
          P₀).length ≤ 5 := by
      intro P₀
      by_cases hP : P₀ = Q
      · subst hP
        simp only [Function.update_self]
        cases ci? with
        | some ci =>
          rw [List.length_modify]
          cases P₀
          · exact hInv.2.2.2.2.1
          · exact hInv.2.2.2.2.2
        | none => exact pushChain_length_le _ _
      · rw [Function.update_of_ne hP]
        cases P₀
        · exact hInv.2.2.2.2.1
        · exact hInv.2.2.2.2.2
    refine ⟨?_, ?_, hInv.2.2.1, ?_, hch_len .A, hch_len .B⟩
    · simp only [GameState.accept, GameState.delete]
      have hle := List.length_filter_le
        (fun r : Record (Plain ℓ) (List (BitVec 8)) => r.pos != pos) st.mir.trans
      have := hInv.1; omega
    · simp only [GameState.accept, GameState.delete]
      have hle := List.length_filter_le (fun p : Pos => p != pos) st.mir.chall
      have := hInv.2.1; omega
    · rcases hInv.2.2.2.1 with ⟨U, hUlen, hCU, htrU⟩
      refine ⟨U, hUlen, ?_, ?_⟩
      · simp only [GameState.accept, GameState.delete]
        exact countLe_filter_left (· != pos) hCU
      · intro r' hr'
        simp only [GameState.accept, GameState.delete] at hr'
        exact htrU r' (List.mem_of_mem_filter hr')
  intro r hr
  unfold onAccept at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte] at hr
    split_ifs at hr with h1 h2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hInv
    · simp only [putS, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hacc ⟨Q.other, t, i⟩
    · simp only [putS, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hInv
  · simp only [↓reduceIte] at hr
    rcases hin : st.mir.inTransit Q.other w with _ | rec_
    · simp only [hin, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hInv
    · simp only [hin, putS, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hacc rec_.pos

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem onAnswer_preserves_inv (qep K m : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (st : SimState PQ Pt ℓ) (hInv : SimStateInv K m st) :
    ∀ r ∈ support ((onAnswer qep Q w isDel ci? T pq' res).run st),
      SimStateInv K m r.2 := by
  intro r hr
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · simp only [onAnswer, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hInv
  · simp only [onAnswer, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hInv
  · dsimp only [onAnswer] at hr
    exact onAccept_preserves_inv (PQ := PQ) (Pt := Pt) (ℓ := ℓ) qep K m Q w isDel t i
      ((pm.map Prod.snd).getD default) ci? T pq' st hInv r hr

omit [SampleableType PQC] in
theorem simRecv_preserves_inv (qep : ℕ) (k : Option ℕ) (K m : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ) (hInv : SimStateInv K m st) :
    ∀ r ∈ support ((simRecv P encT decT qep k Q w isDel).run st),
      SimStateInv K m r.2 := by
  intro r hr
  unfold simRecv at hr
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases hwin : st.mir.win = true
  · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hInv
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte] at hr
    by_cases hdelRef : (isDel && (st.mir.inTransit Q.other w).isNone) = true
    · simp only [hdelRef, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hInv
    · simp only [hdelRef, Bool.false_eq_true, ↓reduceIte] at hr
      by_cases hinjRef : (!isDel && ((st.mir.inTransit Q.other w).isSome ||
          !(st.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w))) = true
      · simp only [hinjRef, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hInv
      · simp only [hinjRef, Bool.false_eq_true, ↓reduceIte] at hr
        by_cases hlen : w.length < 9
        · simp only [hlen, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hInv
        · simp only [hlen, ↓reduceIte] at hr
          rcases hwire :
              (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, rest⟩
          · simp only [hwire, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact hInv
          · simp only [hwire] at hr
            by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
            · simp only [haddr, ↓reduceIte, StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at hr
              subst hr; exact hInv
            · simp only [haddr, Bool.false_eq_true, ↓reduceIte] at hr
              rcases hspqr : P.spqr.recv (st.pq Q) h.pqRatchet with err | ⟨pq', salt⟩
              · simp only [hspqr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr; exact hInv
              · simp only [hspqr] at hr
                rcases hidx :
                    (st.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
                    _ | ci
                · simp only [hidx] at hr
                  set honestC := (st.honest.find? fun wc =>
                    wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
                  by_cases hevCond :
                      ((honestC.map fun c => decide (c.1.1 ≠ st.mir.epoch Q + 1)) == some true) =
                        true
                  · simp only [hevCond, ↓reduceIte, StateT.run_pure, support_pure,
                      Set.mem_singleton_iff] at hr
                    subst hr; exact hInv
                  · simp only [hevCond, Bool.false_eq_true, ↓reduceIte] at hr
                    by_cases hzCond : (decT h.senderRatchetKey == some 0) = true
                    · simp only [hzCond, ↓reduceIte, StateT.run_pure, support_pure,
                        Set.mem_singleton_iff] at hr
                      subst hr; exact hInv
                    · simp only [hzCond, Bool.false_eq_true, ↓reduceIte] at hr
                      rw [ite_putS_bind_run] at hr
                      set amb := inReceiveOnlyEpoch st.mir Q ||
                        (Q == Party.A && (st.chains Q).any (·.key.isNone))
                      set stAmb := if amb then { st with amb := st.amb + 1 } else st
                      have hInvAmb : SimStateInv K m stAmb := by
                        dsimp only [stAmb]; split_ifs <;> exact hInv
                      have hInvStop : SimStateInv K m { stAmb with stopped := true } := hInvAmb
                      by_cases hkCond : (amb && k == some st.amb) = true
                      · simp only [hkCond, ↓reduceIte] at hr
                        by_cases hinw : (!(inReceiveOnlyEpoch st.mir Q)) = true
                        · simp only [hinw, ↓reduceIte] at hr
                          by_cases hlim : (!(decide (25000 < h.counter.toNat + 1 - 1) ||
                              decide (2 ^ 32 ≤ h.counter.toNat + 1))) = true
                          · simp only [hlim, ↓reduceIte] at hr
                            rcases hdec : decT h.senderRatchetKey with _ | T
                            · simp only [hdec, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                                pure_bind, support_pure, Set.mem_singleton_iff] at hr
                              subst hr; exact hInvStop
                            · simp only [hdec, StateT.run_bind, fwd_run_eq, bind_assoc, pure_bind,
                                StateT.run_modify, StateT.run_pure, mem_support_bind_iff,
                                support_pure, Set.mem_singleton_iff] at hr
                              obtain ⟨_, -, rfl⟩ := hr; exact hInvStop
                          · simp only [hlim, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                              StateT.run_pure, StateT.run_modify, pure_bind, support_pure,
                              Set.mem_singleton_iff] at hr
                            subst hr; exact hInvStop
                        · simp only [hinw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                            liftQ, stateT_lift_run, bind_assoc, pure_bind,
                            mem_support_bind_iff] at hr
                          obtain ⟨_, -, hr⟩ := hr
                          rcases hdec : decT h.senderRatchetKey with _ | T
                          · simp only [hdec, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                              pure_bind, support_pure, Set.mem_singleton_iff] at hr
                            subst hr; exact hInvStop
                          · simp only [hdec, StateT.run_bind, fwd_run_eq, bind_assoc, pure_bind,
                              StateT.run_modify, StateT.run_pure, mem_support_bind_iff,
                              support_pure, Set.mem_singleton_iff] at hr
                            obtain ⟨_, -, rfl⟩ := hr; exact hInvStop
                      · simp only [hkCond, Bool.false_eq_true, ↓reduceIte] at hr
                        by_cases hlim : (inReceiveOnlyEpoch st.mir Q ||
                            decide (25000 < h.counter.toNat + 1 - 1) ||
                            decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
                        · simp only [hlim, ↓reduceIte, StateT.run_pure, support_pure,
                            Set.mem_singleton_iff] at hr
                          subst hr; exact hInvAmb
                        · simp only [hlim, Bool.false_eq_true, ↓reduceIte] at hr
                          rcases hdec : decT h.senderRatchetKey with _ | T
                          · simp only [hdec, StateT.run_pure, support_pure,
                              Set.mem_singleton_iff] at hr
                            subst hr; exact hInvAmb
                          · simp only [hdec, StateT.run_bind, fwd_run_eq, bind_assoc, pure_bind,
                              mem_support_bind_iff] at hr
                            obtain ⟨res, -, hr⟩ := hr
                            exact onAnswer_preserves_inv qep K m Q w isDel none
                              h.senderRatchetKey pq' res stAmb hInvAmb r hr
                · simp only [hidx] at hr
                  set g := (st.chains Q).getD ci ⟨none, 0, 0, []⟩
                  by_cases hrej : g.rejects (h.counter.toNat + 1) = true
                  · simp only [hrej, ↓reduceIte, StateT.run_pure, support_pure,
                      Set.mem_singleton_iff] at hr
                    subst hr; exact hInv
                  · simp only [hrej, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                      fwd_run_eq, bind_assoc, pure_bind, mem_support_bind_iff] at hr
                    obtain ⟨res, -, hr⟩ := hr
                    exact onAnswer_preserves_inv qep K m Q w isDel (some ci)
                      h.senderRatchetKey pq' res st hInv r hr

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem simCorrDedup_preserves_inv (K m : ℕ) (Q : Party) (st : SimState PQ Pt ℓ)
    (hInv : SimStateInv K (m + 1) st) :
    ∀ r ∈ support ((simCorrDedup P Dh encT Q).run st), SimStateInv K m r.2 := by
  have hInv0 : SimStateInv K m st := hInv.mono (Nat.le_succ m)
  intro r hr
  unfold simCorrDedup at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases h1 :
      (st.mir.win || !(st.mir.corrAllowed Q) || inReceiveOnlyEpoch st.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 st.mir Q)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hInv0
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨⟨res, s_res⟩, hres, hr⟩ := hr
    have hsres : s_res = st := by
      simp [liftQ] at hres; exact hres.2.symm
    rw [hsres] at hr; clear hsres hres s_res
    rcases res with _ | fig8st
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hInv0
    · simp only [putS, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hr
      subst hr
      have hchA : ((if Q == Party.B && st.mir.epoch Party.B == 0 then
          match fig8st.γ with
          | .exp x => Function.update st.chains Party.A ((st.chains Party.A).map fun g =>
              if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => st.chains
        else st.chains) .A).length ≤ 5 := by
        split_ifs
        · rcases fig8st.γ with _ | x <;> simp [Function.update, hInv0.2.2.2.2.1]
        · exact hInv0.2.2.2.2.1
      have hchB : ((if Q == Party.B && st.mir.epoch Party.B == 0 then
          match fig8st.γ with
          | .exp x => Function.update st.chains Party.A ((st.chains Party.A).map fun g =>
              if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => st.chains
        else st.chains) .B).length ≤ 5 := by
        split_ifs
        · rcases fig8st.γ with _ | x <;> simp [Function.update, hInv0.2.2.2.2.2]
        · exact hInv0.2.2.2.2.2
      refine ⟨hInv0.1, hInv0.2.1, hInv0.2.2.1, ?_, hchA, hchB⟩
      rcases hInv0.2.2.2.1 with ⟨U, hUlen, hCU, htrU⟩
      refine ⟨U, hUlen, ?_, htrU⟩
      dsimp only [afterCorrDedup, GameState.leak]
      refine countLe_dedupPrepend hCU ?_
      intro x hx
      rcases List.mem_map.mp hx with ⟨r', hr', rfl⟩
      exact htrU r' (List.mem_of_mem_filter hr')

theorem simRunProg_step (K qep : ℕ) (k : Option ℕ) (m : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (v : (@simStateTy PQ PQC Pt ℓ).denote)
    (hInv : SimBoundInv K (m + 1) v) :
    (Prod.map id simStateDec <$>
      (((simRunProg P Dh encT decT K qep k).impl (.inr t)).run v)) =
      ((simImplDedup P Dh encT decT qep k (.inr t)).run (simStateDec v)) ∧
    ∀ r ∈ support (((simRunProg P Dh encT decT K qep k).impl (.inr t)).run v),
      SimBoundInv K m r.2 := by
  set st := simStateDec v
  have hv : v = simStateEnc st := (simStateEnc_simStateDec v).symm
  have hBound : SimStateBounded K st := hInv.toBounded
  have hInvSt : SimStateInv K (m + 1) st := hInv
  have hInv0 : SimStateInv K m st := hInvSt.mono (Nat.le_succ m)
  refine ⟨?_, ?_⟩
  · rw [hv, simImpl_eval P Dh encT decT K qep k (.inr t) st hBound, Functor.map_map]
    simp [Prod.map]
  · rintro ⟨u₀, s₀⟩ hr
    rw [hv, simImpl_eval P Dh encT decT K qep k (.inr t) st hBound, support_map,
      Set.mem_image] at hr
    obtain ⟨⟨u, s'⟩, hs', hEq⟩ := hr
    injection hEq with _ hs₀
    subst hs₀
    rw [simBoundInv_simStateEnc]
    rcases t with ((((⟨Q, msg, rCoins⟩ | ⟨Q, m₀, m₁, rCoins⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
    · exact guard_preserves_inv (simSend P qep Q msg none rCoins) st hInv0
        (simSend_preserves_inv P qep K m Q msg none rCoins st hInvSt) (u, s') hs'
    · exact guard_preserves_inv (simSend P qep Q m₀ (some m₁) rCoins) st hInv0
        (simSend_preserves_inv P qep K m Q m₀ (some m₁) rCoins st hInvSt) (u, s') hs'
    · exact guard_preserves_inv (simRecv P encT decT qep k Q w true) st hInv0
        (simRecv_preserves_inv P encT decT qep k K m Q w true st hInv0) (u, s') hs'
    · exact guard_preserves_inv (simRecv P encT decT qep k Q w false) st hInv0
        (simRecv_preserves_inv P encT decT qep k K m Q w false st hInv0) (u, s') hs'
    · exact guard_preserves_inv (simCorrDedup P Dh encT Q) st hInv0
        (simCorrDedup_preserves_inv P Dh encT K m Q st hInvSt) (u, s') hs'

omit [SampleableType PQC] in
theorem initSimE_eval {Γ} (pqA pqB : Expr OO Γ (.base .pq)) (ρ : Env Γ) :
    (initSimE (P := P) (Dh := Dh) (encT := encT) (decT := decT) pqA pqB).eval ρ =
      simStateEnc (initSim (pqA.eval ρ) (pqB.eval ρ)) := by
  simp [initSimE, initChainAE, initSimMirE, initSim, ssMk, mMk, simOps,
    simStateEnc, simMirEnc, ghostChainEnc, Expr.eval]
  rfl

theorem simInitC_eval (ρ : Env [.unit]) :
    (simInitC (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) P Dh encT decT).eval ρ =
      (do
        let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
        return ((), simStateEnc
          (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)))) := by
  unfold simInitC
  rw [comp_eval_bind, sample_bv256_eval]
  refine bind_congr fun pqrKey => ?_
  rw [comp_eval_ret]
  simp only [Expr.eval, initSimE_eval]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
def simFinish (k : Option ℕ) (b' : Bool) : Fig8Comp Pt ℓ Bool :=
  match k with
  | none => pure b'
  | some _ => (liftM ($ᵗ Bool : ProbComp Bool) : Fig8Comp Pt ℓ Bool)

theorem simFinishC_eval (k : Option ℕ)
    (s : (@simStateTy PQ PQC Pt ℓ).denote) (b' : Bool) :
    (simFinishC (PQ := PQ) (PQC := PQC) (Pt := Pt) (ℓ := ℓ) P Dh encT decT k).eval
      (Env.cons (t := simStateTy) s (Env.cons (t := .bool) b' Env.nil)) =
      simFinish k b' := by
  cases k <;> rfl

private theorem isQueryBoundP_congr {ι : Type} {G : OracleSpec ι} {α : Type}
    (oa : OracleComp G α) {P₁ P₂ : ι → Prop} [d₁ : DecidablePred P₁] [d₂ : DecidablePred P₂]
    (h : P₁ = P₂) (q : ℕ) :
    oa.IsQueryBoundP P₁ q ↔ oa.IsQueryBoundP P₂ q := by
  subst h
  rw [Subsingleton.elim d₁ d₂]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem makesAtMostQueries_iff_isGameQuery {St Msg Coins C : Type}
    (oa : SM.Adversary St Msg Coins C) (q : ℕ) :
    SM.MakesAtMostQueries oa q ↔
      oa.IsQueryBoundP
        (isGameQuery (G := SM.spec St Msg Coins C)) q :=
  isQueryBoundP_congr oa (by funext x; cases x <;> simp [isGameQuery]) q

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
def simStateCanon (s : SimState PQ Pt ℓ) : SimState PQ Pt ℓ :=
  { s with mir := canonComp s.mir }

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem simStateCanon_idem (s : SimState PQ Pt ℓ) :
    simStateCanon (simStateCanon s) = simStateCanon s := by
  simp [simStateCanon, canonComp_idem]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem guard_run_simStateCanon {α : Type}
    (x y : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α)) (s : SimState PQ Pt ℓ)
    (h : Prod.map id simStateCanon <$> x.run s =
         Prod.map id simStateCanon <$> y.run (simStateCanon s)) :
    Prod.map id simStateCanon <$> («guard» x).run s =
      Prod.map id simStateCanon <$> («guard» y).run (simStateCanon s) := by
  unfold «guard»
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hs : (simStateCanon s).stopped = s.stopped := rfl
  rw [hs]
  cases s.stopped
  · exact h
  · simp [StateT.run_pure, Prod.map, simStateCanon_idem]

omit [DecidableEq Pt] [Zero Pt] in
private theorem simSend_run_simStateCanon (qep : ℕ) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r : Option PQC) (s : SimState PQ Pt ℓ) :
    Prod.map id simStateCanon <$> (simSend P qep Q m₀ chal r).run s =
      Prod.map id simStateCanon <$> (simSend P qep Q m₀ chal r).run (simStateCanon s) := by
  unfold simSend
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have h1 : ((simStateCanon s).mir.win || !(noBobSendInEpoch0 (simStateCanon s).mir Q)) =
      (s.mir.win || !(noBobSendInEpoch0 s.mir Q)) := rfl
  rw [h1]
  by_cases hc1 : (s.mir.win || !(noBobSendInEpoch0 s.mir Q)) = true
  · simp [hc1, StateT.run_pure, Prod.map, simStateCanon_idem]
  · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
    have hep_canon : (simStateCanon s).mir.epMgmt 3 qep Q r.isSome =
        Option.map canonComp (s.mir.epMgmt 3 qep Q r.isSome) :=
      (canonComp_epMgmt s.mir 3 qep Q r.isSome).symm
    rw [hep_canon]
    rcases hep : s.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · simp [StateT.run_pure, Prod.map, simStateCanon_idem]
    · dsimp only [Option.map]
      have h2 : (chal.isSome && !(canonComp s₁).safeCh 3 Q) =
          (chal.isSome && !s₁.safeCh 3 Q) := rfl
      rw [h2]
      by_cases hc2 : (chal.isSome && !s₁.safeCh 3 Q) = true
      · simp [hc2, StateT.run_pure, Prod.map, simStateCanon_idem]
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        have hpost : ∀ (rq : PQC) (rc : Option (BitVec 256)),
            Prod.map id simStateCanon <$> ((do
              let pn := if s₁.epoch Q ≠ s.mir.epoch Q then
                BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q
              match mkPub (P := P) s Q rq pn with
              | none => return none
              | some (pq', pub) =>
                let res ← match chal with
                  | none => liftQ (SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc)
                  | some m₁ => liftQ (SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc)
                match res with
                | none => return none
                | some c =>
                  let w := toWire c
                  let rec' : Record (Plain ℓ) (List (BitVec 8)) :=
                    ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
                  let mir' := s₁.record 3 Q () rec' chal.isSome
                  putS { s with
                    mir := mir', pq := Function.update s.pq Q pq',
                    pn := Function.update s.pn Q pn,
                    honest := (w, c) :: s.honest }
                  return some w).run s) =
            Prod.map id simStateCanon <$> ((do
              let pn := if (canonComp s₁).epoch Q ≠ (simStateCanon s).mir.epoch Q then
                BitVec.ofNat 32 ((simStateCanon s).mir.idx Q - 1) else (simStateCanon s).pn Q
              match mkPub (P := P) (simStateCanon s) Q rq pn with
              | none => return none
              | some (pq', pub) =>
                let res ← match chal with
                  | none => liftQ (SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc)
                  | some m₁ => liftQ (SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc)
                match res with
                | none => return none
                | some c =>
                  let w := toWire c
                  let rec' : Record (Plain ℓ) (List (BitVec 8)) :=
                    ⟨⟨Q, (canonComp s₁).epoch Q, (canonComp s₁).idx Q + 1⟩, m₀, w⟩
                  let mir' := (canonComp s₁).record 3 Q () rec' chal.isSome
                  putS { simStateCanon s with
                    mir := mir', pq := Function.update (simStateCanon s).pq Q pq',
                    pn := Function.update (simStateCanon s).pn Q pn,
                    honest := (w, c) :: (simStateCanon s).honest }
                  return some w).run (simStateCanon s)) := by
          intro rq rc
          have hmk : ∀ Q rq pn, mkPub (P := P) (simStateCanon s) Q rq pn = mkPub (P := P) s Q rq pn :=
            fun _ _ _ => rfl
          dsimp only []
          simp only [hmk,
            show (canonComp s₁).epoch = s₁.epoch from rfl,
            show (canonComp s₁).idx = s₁.idx from rfl,
            show (simStateCanon s).mir.epoch = s.mir.epoch from rfl,
            show (simStateCanon s).mir.idx = s.mir.idx from rfl,
            show (simStateCanon s).pn = s.pn from rfl,
            show (simStateCanon s).pq = s.pq from rfl,
            show (simStateCanon s).honest = s.honest from rfl]
          rcases mkPub P s Q rq
              (if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1)
               else s.pn Q) with _ | ⟨pq', pub⟩
          · simp [StateT.run_pure, Prod.map, simStateCanon_idem]
          · rcases chal with _ | m₁ <;>
            · simp only [liftQ, stateT_lift_run, StateT.run_bind, bind_assoc, pure_bind, map_bind]
              refine bind_congr fun res => ?_
              rcases res with _ | c
              · simp [StateT.run_pure, Prod.map, simStateCanon_idem]
              · simp only [putS, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                  map_pure, Prod.map]
                congr 2
                simp only [simStateCanon]
                congr 1
                exact canonComp_record s₁ 3 Q () _ _
        rcases r with _ | rq₀
        · simp only [coin, liftQ, stateT_lift_run, StateT.run_bind,
            bind_assoc, pure_bind, map_bind]
          exact bind_congr fun rq => hpost rq none
        · simp only [coin, liftQ, stateT_lift_run, StateT.run_bind,
            bind_map_left, bind_assoc, pure_bind, map_bind]
          exact bind_congr fun c => hpost rq₀ (some c)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem onAccept_run_simStateCanon (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (msg : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    Prod.map id simStateCanon <$> (onAccept qep Q w isDel t i msg ci? T pq').run s =
      Prod.map id simStateCanon <$>
        (onAccept qep Q w isDel t i msg ci? T pq').run (simStateCanon s) := by
  unfold onAccept
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hqep : qep + 1 < t
    · simp [hqep, StateT.run_pure, Prod.map, simStateCanon_idem]
    · simp only [hqep, ↓reduceIte]
      have htriv : (simStateCanon s).mir.trivial 3 ⟨Q.other, t, i⟩ =
          s.mir.trivial 3 ⟨Q.other, t, i⟩ := canonComp_trivial s.mir 3 _
      rw [htriv]
      cases s.mir.trivial 3 ⟨Q.other, t, i⟩
      · simp [putS, StateT.run_set, Prod.map, simStateCanon, canonComp]
      · simp [putS, StateT.run_set, Prod.map, simStateCanon, ← canonComp_accept, canonComp_idem]
  · simp only [↓reduceIte]
    have hin : (simStateCanon s).mir.inTransit Q.other w = s.mir.inTransit Q.other w := rfl
    rw [hin]
    rcases s.mir.inTransit Q.other w with _ | r
    · simp [StateT.run_pure, Prod.map, simStateCanon_idem]
    · have hch : (simStateCanon s).mir.chall = s.mir.chall := rfl
      rw [hch]
      simp [putS, StateT.run_set, Prod.map, simStateCanon, ← canonComp_accept, canonComp_idem]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem onAnswer_run_simStateCanon (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (s : SimState PQ Pt ℓ) :
    Prod.map id simStateCanon <$> (onAnswer qep Q w isDel ci? T pq' res).run s =
      Prod.map id simStateCanon <$>
        (onAnswer qep Q w isDel ci? T pq' res).run (simStateCanon s) := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · simp [onAnswer, StateT.run_pure, Prod.map, simStateCanon_idem]
  · simp [onAnswer, StateT.run_pure, Prod.map, simStateCanon_idem]
  · exact onAccept_run_simStateCanon qep Q w isDel t i
      ((pm.map Prod.snd).getD default) ci? T pq' s

omit [SampleableType PQC] in
private theorem simRecv_run_simStateCanon (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (s : SimState PQ Pt ℓ) :
    Prod.map id simStateCanon <$> (simRecv P encT decT qep k Q w isDel).run s =
      Prod.map id simStateCanon <$>
        (simRecv P encT decT qep k Q w isDel).run (simStateCanon s) := by
  unfold simRecv
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hwin_eq : (simStateCanon s).mir.win = s.mir.win := rfl
  have hin_eq : (simStateCanon s).mir.inTransit Q.other w = s.mir.inTransit Q.other w := rfl
  have hsinj_eq : (simStateCanon s).mir.safeInj 3 = s.mir.safeInj 3 := rfl
  have hpq_eq : (simStateCanon s).pq = s.pq := rfl
  have hhon_eq : (simStateCanon s).honest = s.honest := rfl
  have hch_eq : (simStateCanon s).chains = s.chains := rfl
  have hep_eq : (simStateCanon s).mir.epoch = s.mir.epoch := rfl
  have hinw_eq : inReceiveOnlyEpoch (simStateCanon s).mir Q = inReceiveOnlyEpoch s.mir Q := rfl
  have hamb_eq : (simStateCanon s).amb = s.amb := rfl
  rw [hwin_eq, hin_eq, hsinj_eq, hpq_eq, hhon_eq, hch_eq, hep_eq, hinw_eq, hamb_eq]
  by_cases hwin : s.mir.win = true
  · simp [hwin, StateT.run_pure, Prod.map, simStateCanon_idem]
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
    by_cases hdelRef : (isDel && (s.mir.inTransit Q.other w).isNone) = true
    · simp [hdelRef, StateT.run_pure, Prod.map, simStateCanon_idem]
    · simp only [hdelRef, Bool.false_eq_true, ↓reduceIte]
      by_cases hinjRef : (!isDel && ((s.mir.inTransit Q.other w).isSome ||
          !(s.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w))) = true
      · simp [hinjRef, StateT.run_pure, Prod.map, simStateCanon_idem]
      · simp only [hinjRef, Bool.false_eq_true, ↓reduceIte]
        by_cases hlen : w.length < 9
        · simp [hlen, StateT.run_pure, Prod.map, simStateCanon_idem]
        · simp only [hlen, ↓reduceIte]
          rcases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, rest⟩
          · simp [StateT.run_pure, Prod.map, simStateCanon_idem]
          · dsimp only []
            by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
            · simp [haddr, StateT.run_pure, Prod.map, simStateCanon_idem]
            · simp only [haddr, Bool.false_eq_true, ↓reduceIte]
              rcases P.spqr.recv (s.pq Q) h.pqRatchet with err | ⟨pq', salt⟩
              · simp [StateT.run_pure, Prod.map, simStateCanon_idem]
              · dsimp only []
                generalize (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = ci?
                rcases ci? with _ | ci <;> dsimp only []
                · set honestC := (s.honest.find? fun wc =>
                    wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
                  by_cases hevCond :
                      ((honestC.map fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) =
                        true
                  · simp only [hevCond, ↓reduceIte]
                    simp [StateT.run_pure, Prod.map, simStateCanon_idem]
                  · simp only [hevCond, Bool.false_eq_true, ↓reduceIte]
                    by_cases hzCond : (decT h.senderRatchetKey == some 0) = true
                    · simp [hzCond, StateT.run_pure, Prod.map, simStateCanon_idem]
                    · simp only [hzCond, Bool.false_eq_true, ↓reduceIte]
                      rw [ite_putS_bind_run, ite_putS_bind_run]
                      set amb := inReceiveOnlyEpoch s.mir Q ||
                        (Q == Party.A && (s.chains Q).any (·.key.isNone))
                      set sAmb := if amb then { s with amb := s.amb + 1 } else s
                      have hsAmb_canon :
                          (if amb = true then
                            { mir := (simStateCanon s).mir, pq := s.pq, pn := (simStateCanon s).pn,
                              unackA := (simStateCanon s).unackA, honest := s.honest,
                              chains := s.chains, amb := s.amb + 1,
                              stopped := (simStateCanon s).stopped }
                           else simStateCanon s) = simStateCanon sAmb := by
                        dsimp only [sAmb]; split_ifs <;> rfl
                      have hcond_fwd : ∀ (s₀ : SimState PQ Pt ℓ) (c₀ : Fig8C Pt),
                          ((simStateCanon s₀).honest.any fun wc =>
                            decide (wc.2 = c₀) &&
                              ((simStateCanon s₀).mir.inTransit Q.other wc.1).isSome) =
                          (s₀.honest.any fun wc =>
                            decide (wc.2 = c₀) &&
                              (s₀.mir.inTransit Q.other wc.1).isSome) := fun _ _ => rfl
                      rw [hsAmb_canon]
                      by_cases hkCond : (amb && k == some s.amb) = true
                      · simp only [hkCond, ↓reduceIte]
                        by_cases hinw : (!(inReceiveOnlyEpoch s.mir Q)) = true
                        · simp only [hinw, ↓reduceIte]
                          by_cases hlim : (!(decide (25000 < h.counter.toNat + 1 - 1) ||
                              decide (2 ^ 32 ≤ h.counter.toNat + 1))) = true
                          · simp only [hlim, ↓reduceIte]
                            rcases decT h.senderRatchetKey with _ | T
                            · simp [StateT.run_modify, Prod.map, simStateCanon, canonComp_idem]
                            · simp only [StateT.run_bind, fwd_run_eq, bind_assoc, pure_bind,
                                StateT.run_modify, StateT.run_pure, map_bind]
                              rw [hcond_fwd]
                              refine bind_congr fun _ => ?_
                              simp [Prod.map, simStateCanon, canonComp_idem]
                          · simp only [hlim, Bool.false_eq_true, ↓reduceIte]
                            simp [StateT.run_modify, Prod.map, simStateCanon, canonComp_idem]
                        · simp only [hinw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                            liftQ, stateT_lift_run, bind_assoc, pure_bind, map_bind]
                          refine bind_congr fun _ => ?_
                          rcases decT h.senderRatchetKey with _ | T
                          · simp [StateT.run_modify, Prod.map, simStateCanon, canonComp_idem]
                          · simp only [StateT.run_bind, fwd_run_eq, bind_assoc, pure_bind,
                              StateT.run_modify, StateT.run_pure, map_bind]
                            rw [hcond_fwd]
                            refine bind_congr fun _ => ?_
                            simp [Prod.map, simStateCanon, canonComp_idem]
                      · simp only [hkCond, Bool.false_eq_true, ↓reduceIte]
                        by_cases hlim : (inReceiveOnlyEpoch s.mir Q ||
                            decide (25000 < h.counter.toNat + 1 - 1) ||
                            decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
                        · simp only [hlim, ↓reduceIte]
                          simp [StateT.run_pure, Prod.map, simStateCanon_idem]
                        · simp only [hlim, Bool.false_eq_true, ↓reduceIte]
                          rcases decT h.senderRatchetKey with _ | T
                          · simp [StateT.run_pure, Prod.map, simStateCanon_idem]
                          · simp only [StateT.run_bind, fwd_run_eq, bind_assoc, pure_bind,
                              map_bind]
                            rw [hcond_fwd]
                            exact bind_congr fun res =>
                              onAnswer_run_simStateCanon qep Q w isDel none
                                h.senderRatchetKey pq' res sAmb
                · set g := (s.chains Q).getD ci ⟨none, 0, 0, []⟩
                  by_cases hrej : g.rejects (h.counter.toNat + 1) = true
                  · simp [hrej, StateT.run_pure, Prod.map, simStateCanon_idem]
                  · simp only [hrej, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                      fwd_run_eq, bind_assoc, pure_bind, map_bind]
                    have hcond_fwd_s : ∀ (c₀ : Fig8C Pt),
                        ((simStateCanon s).honest.any fun wc =>
                          decide (wc.2 = c₀) &&
                            ((simStateCanon s).mir.inTransit Q.other wc.1).isSome) =
                        (s.honest.any fun wc =>
                          decide (wc.2 = c₀) &&
                            (s.mir.inTransit Q.other wc.1).isSome) := fun _ => rfl
                    rw [hcond_fwd_s]
                    exact bind_congr fun res =>
                      onAnswer_run_simStateCanon qep Q w isDel (some ci)
                        h.senderRatchetKey pq' res s

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem simCorrDedup_run_simStateCanon (Q : Party) (s : SimState PQ Pt ℓ) :
    Prod.map id simStateCanon <$> (simCorrDedup P Dh encT Q).run s =
      Prod.map id simStateCanon <$> (simCorr P Dh encT Q).run (simStateCanon s) := by
  unfold simCorrDedup simCorr
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hca : (simStateCanon s).mir.corrAllowed Q = s.mir.corrAllowed Q :=
    canonComp_corrAllowed s.mir Q
  have hcond :
      ((simStateCanon s).mir.win || !((simStateCanon s).mir.corrAllowed Q) ||
       inReceiveOnlyEpoch (simStateCanon s).mir Q ||
       !(noAliceCorrWhileAliceBelowEpoch10 (simStateCanon s).mir Q)) =
      (s.mir.win || !(s.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch s.mir Q ||
       !(noAliceCorrWhileAliceBelowEpoch10 s.mir Q)) := by
    rw [hca]; rfl
  rw [hcond]
  by_cases hc :
      (s.mir.win || !(s.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch s.mir Q ||
       !(noAliceCorrWhileAliceBelowEpoch10 s.mir Q)) = true
  · simp [hc, StateT.run_pure, Prod.map, simStateCanon_idem]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, liftQ, stateT_lift_run,
      bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    rcases res with _ | fig8st
    · simp [StateT.run_pure, Prod.map, simStateCanon_idem]
    · simp only [putS, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        map_pure, Prod.map]
      congr 1
      refine Prod.ext rfl ?_
      change simStateCanon { s with mir := afterCorrDedup s.mir Q, chains := _ } =
        simStateCanon { s with mir := (canonComp s.mir).afterCorr Q, chains := _ }
      simp only [simStateCanon]
      congr 1
      exact canonComp_afterCorrDedup s.mir Q

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem simCorr_run_simStateCanon (Q : Party) (s : SimState PQ Pt ℓ) :
    Prod.map id simStateCanon <$> (simCorr P Dh encT Q).run s =
      Prod.map id simStateCanon <$> (simCorr P Dh encT Q).run (simStateCanon s) := by
  unfold simCorr
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hca : (simStateCanon s).mir.corrAllowed Q = s.mir.corrAllowed Q :=
    canonComp_corrAllowed s.mir Q
  have hcond :
      ((simStateCanon s).mir.win || !((simStateCanon s).mir.corrAllowed Q) ||
       inReceiveOnlyEpoch (simStateCanon s).mir Q ||
       !(noAliceCorrWhileAliceBelowEpoch10 (simStateCanon s).mir Q)) =
      (s.mir.win || !(s.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch s.mir Q ||
       !(noAliceCorrWhileAliceBelowEpoch10 s.mir Q)) := by
    rw [hca]; rfl
  rw [hcond]
  by_cases hc :
      (s.mir.win || !(s.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch s.mir Q ||
       !(noAliceCorrWhileAliceBelowEpoch10 s.mir Q)) = true
  · simp [hc, StateT.run_pure, Prod.map, simStateCanon_idem]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, liftQ, stateT_lift_run,
      bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    rcases res with _ | fig8st
    · simp [StateT.run_pure, Prod.map, simStateCanon_idem]
    · simp only [putS, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        map_pure, Prod.map]
      congr 1
      refine Prod.ext rfl ?_
      change simStateCanon { s with mir := s.mir.afterCorr Q, chains := _ } =
        simStateCanon { s with mir := (canonComp s.mir).afterCorr Q, chains := _ }
      simp only [simStateCanon]
      congr 1
      exact canonComp_afterCorr s.mir Q

private theorem run'_simulateQ_simImplDedup_eq (qep : ℕ) (k : Option ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (s : SimState PQ Pt ℓ) :
    (simulateQ (simImplDedup P Dh encT decT qep k) A).run' s =
      (simulateQ (simImpl P Dh encT decT qep k) A).run' s := by
  refine run'_simulateQ_eq_of_idem_proj
    (simImplDedup P Dh encT decT qep k)
    (simImpl P Dh encT decT qep k) simStateCanon ?_ ?_ A rfl
  · rintro (n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)) st'
    · simp [simImplDedup, simImpl, liftQ, StateT.run_lift, Prod.map, simStateCanon_idem]
    · exact guard_run_simStateCanon _ _ st' (simSend_run_simStateCanon P qep Q m none r st')
    · exact guard_run_simStateCanon _ _ st' (simSend_run_simStateCanon P qep Q m₀ (some m₁) r st')
    · exact guard_run_simStateCanon _ _ st'
        (simRecv_run_simStateCanon P encT decT qep k Q w true st')
    · exact guard_run_simStateCanon _ _ st'
        (simRecv_run_simStateCanon P encT decT qep k Q w false st')
    · exact guard_run_simStateCanon _ _ st' (simCorrDedup_run_simStateCanon P Dh encT Q st')
  · rintro (n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)) st'
    · simp [simImpl, liftQ, StateT.run_lift, Prod.map, simStateCanon_idem]
    · exact guard_run_simStateCanon _ _ st' (simSend_run_simStateCanon P qep Q m none r st')
    · exact guard_run_simStateCanon _ _ st' (simSend_run_simStateCanon P qep Q m₀ (some m₁) r st')
    · exact guard_run_simStateCanon _ _ st'
        (simRecv_run_simStateCanon P encT decT qep k Q w true st')
    · exact guard_run_simStateCanon _ _ st'
        (simRecv_run_simStateCanon P encT decT qep k Q w false st')
    · exact guard_run_simStateCanon _ _ st' (simCorr_run_simStateCanon P Dh encT Q st')

/-- Full evaluation agreement between `simRunProg` and `simRun` when `A` makes at most `q ≤ K`
game queries. -/
theorem simRunProg_eval (K qep : ℕ) (k : Option ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (q : ℕ) (hq : SM.MakesAtMostQueries A q) (hqK : q ≤ K) :
    (simRunProg P Dh encT decT K qep k).eval (fun _ => A) () =
      simRun P Dh encT decT qep k A := by
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  have hinit_eval :
      Prod.map id simStateDec <$>
        (simRunProg (ℓ := ℓ) P Dh encT decT K qep k).init.eval (Env.cons () Env.nil) =
      (do
        let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
        return ((), initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) := by
    change Prod.map id simStateDec <$>
      (simInitC (ℓ := ℓ) P Dh encT decT).eval (Env.cons () Env.nil) = _
    rw [simInitC_eval]
    simp [map_eq_bind_pure_comp, bind_assoc, Prod.map]
  have hinit_inv :
      ∀ r ∈ support ((simRunProg (ℓ := ℓ) P Dh encT decT K qep k).init.eval (Env.cons () Env.nil)),
        SimBoundInv K q r.2 := by
    rintro ⟨u₀, (s₀ : (@simStateTy PQ PQC Pt ℓ).denote)⟩ hr
    dsimp only []
    change (u₀, s₀) ∈ support ((simInitC (ℓ := ℓ) P Dh encT decT).eval (Env.cons () Env.nil)) at hr
    rw [simInitC_eval, mem_support_bind_iff] at hr
    obtain ⟨pqrKey, -, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    injection hr with _ hs₀
    subst hs₀
    rw [simBoundInv_simStateEnc]
    exact SimStateInv.init hqK _ _
  have h1 := (simRunProg (ℓ := ℓ) P Dh encT decT K qep k).eval_eq_simulateQ_of_abs
    simStateDec (SimBoundInv K)
    (fun _ => do
      let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
      return ((), initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)))
    (simImplDedup P Dh encT decT qep k)
    (fun _ b' => simFinish k b')
    q ()
    hinit_eval hinit_inv
    (fun n s => rfl)
    (fun m t v hv => simRunProg_step P Dh encT decT K qep k m t v hv)
    (fun s b' _ => simFinishC_eval P Dh encT decT k s b')
    (fun _ hle hv => hv.mono hle)
    (fun _ => A) (fun _ => hq')
  rw [h1]
  unfold simRun
  simp only [simFinish, bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  have hsim := run'_simulateQ_simImplDedup_eq P Dh encT decT qep k A
    (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
  cases k
  · dsimp only []
    rw [← hsim, bind_pure, StateT.run'_eq, map_eq_bind_pure_comp]
    rfl
  · dsimp only []
    rw [← hsim, StateT.run'_eq, bind_map_left]

/-- Full evaluation agreement for `simProg` (`Refine.sim` at `k = none`) when `A` makes at most
`q ≤ K` game queries. -/
theorem simProg_eval (K qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (q : ℕ) (hq : SM.MakesAtMostQueries A q) (hqK : q ≤ K) :
    (simProg P Dh encT decT K qep).eval (fun _ => A) () =
      simRun P Dh encT decT qep none A :=
  simRunProg_eval P Dh encT decT K qep none A q hq hqK

end EvalAgreement

/-! ## Static query bounds and total cost -/

section CostAndQueries

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)

local notation "S" => simSig PQ PQC Pt ℓ
local notation "OO" => simOps (ℓ := ℓ) P Dh encT decT
local notation "SIface" => simIface PQ PQC Pt ℓ

@[simp] theorem guardC_queries {Γ t} (s : Expr OO Γ simStateTy)
    (body : Comp OO SIface Γ (.prod (.opt t) simStateTy))
    (w : SM.SMTag → ℕ) (wU : UniformSamplerTag SimBaseSamp → ℕ) :
    (guardC (P := P) (Dh := Dh) (encT := encT) (decT := decT) s body).queries w wU =
      body.queries w wU := by
  simp [guardC, Comp.queries]

@[simp] theorem simDrawSendCoinsC_queries {Γ} (r : Expr OO Γ (.opt (.base .pqc))) :
    (simDrawSendCoinsC (P := P) (Dh := Dh) (encT := encT) (decT := decT) r).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [simDrawSendCoinsC, Comp.queries]

@[simp] theorem simSendC_queries (qep : ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (m₀ : Expr OO Γ (.base .plain)) (chal : Expr OO Γ (.opt (.base .plain)))
    (r : Expr OO Γ (.opt (.base .pqc))) :
    (simSendC P Dh encT decT qep s qParty m₀ chal r).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [simSendC, simSendPostCoinsC, simSendPostQueryC, Comp.queries]

@[simp] theorem fwdC_queries (K : ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (c : Expr OO Γ (fig8CTy PQ PQC Pt ℓ)) :
    (fwdC (P := P) (Dh := Dh) (encT := encT) (decT := decT) K s qParty c).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [fwdC, Comp.queries]

@[simp] theorem simRecvNewChainNormalC_queries (K qep : ℕ) {Γ} :
    (simRecvNewChainNormalC (P := P) (Dh := Dh) (encT := encT) (decT := decT) (ℓ := ℓ)
      (Γ := Γ) K qep).queries (fun _ => 1) (fun _ => 0) = 1 := by
  simp [simRecvNewChainNormalC, Comp.queries]

@[simp] theorem simRecvNewChainStopC_queries (K : ℕ) {Γ} :
    (simRecvNewChainStopC (P := P) (Dh := Dh) (encT := encT) (decT := decT) (ℓ := ℓ)
      (Γ := Γ) K).queries (fun _ => 1) (fun _ => 0) = 2 := by
  simp [simRecvNewChainStopC, Comp.queries]

@[simp] theorem simRecvC_queries (K qep : ℕ) (k : Option ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool)
    (w : Expr OO Γ (.base .wire)) (isDel : Expr OO Γ .bool) :
    (simRecvC P Dh encT decT K qep k s qParty w isDel).queries
      (fun _ => 1) (fun _ => 0) =
      match k with | none => 1 | some _ => 2 := by
  cases k <;> simp [simRecvC, Comp.queries]

@[simp] theorem simCorrC_queries (K : ℕ) {Γ}
    (s : Expr OO Γ simStateTy) (qParty : Expr OO Γ .bool) :
    (simCorrC P Dh encT decT K s qParty).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [simCorrC, Comp.queries]

@[simp] theorem simHandleC_queries (K qep : ℕ) (k : Option ℕ) :
    (simHandleC (ℓ := ℓ) P Dh encT decT K qep k).queries (fun _ => 1) (fun _ => 0) =
      match k with | none => 1 | some _ => 2 := by
  cases k <;> simp [simHandleC, Comp.queries]

@[simp] theorem simInitC_queries :
    (simInitC (ℓ := ℓ) P Dh encT decT).queries (fun _ => 1) (fun _ => 0) = 0 := by
  simp [simInitC, Comp.queries]

@[simp] theorem simFinishC_queries (k : Option ℕ) :
    (simFinishC (ℓ := ℓ) P Dh encT decT k).queries (fun _ => 1) (fun _ => 0) = 0 := by
  cases k <;> simp [simFinishC, Comp.queries]

@[simp] theorem simProg_totalQueries (K qep q : ℕ) :
    (simProg (ℓ := ℓ) P Dh encT decT K qep).totalQueries (fun _ => 1) (fun _ => 0) q = q := by
  simp [CostedReduction.totalQueries, simProg, simRunProg]

@[simp] theorem simInitC_cost :
    (simInitC (ℓ := ℓ) P Dh encT decT).cost = 66 := by
  simp [simInitC, initSimE, initChainAE, initSimMirE, ssMk, mMk, simIface, simParamIface,
    simParamSamplers, simBaseSampCost, simOps, simOpCost,
    Comp.cost, Expr.cost, Expr.v0, bits]

@[simp] theorem simFinishC_cost (k : Option ℕ) :
    (simFinishC (ℓ := ℓ) P Dh encT decT k).cost = 2 := by
  cases k <;>
    simp [simFinishC, simIface, simParamIface, simParamSamplers,
      Comp.cost, Expr.cost, Expr.v1]

theorem simRunProg_totalCost (K qep : ℕ) (k : Option ℕ) (q : ℕ) :
    (simRunProg (ℓ := ℓ) P Dh encT decT K qep k).totalCost q =
      68 + q * ((simHandleC (ℓ := ℓ) P Dh encT decT K qep k).cost + 6) := by
  simp only [CostedReduction.totalCost, simRunProg, simInitC_cost, simFinishC_cost,
    simCodec, simIface, simParamIface]
  rw [Nat.max_eq_right (by omega)]
  omega

theorem simProg_totalCost (K qep q : ℕ) :
    (simProg (ℓ := ℓ) P Dh encT decT K qep).totalCost q =
      68 + q * ((simHandleC (ℓ := ℓ) P Dh encT decT K qep none).cost + 6) :=
  simRunProg_totalCost P Dh encT decT K qep none q

end CostAndQueries

end CryptoGames.Ratchet.LibsignalSim

