/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
public import Computational.Proofs.ReductionDsl.Ratchet.LibsignalSimDF
public import Computational.Proofs.ReductionDsl.SM.GameCosted
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort
public import Computational.Proofs.SpqrV1Sync.SendTotal
import Computational.Proofs.SpqrV1Sync.SendTotalExtras
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC
public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.SpecLemmas.Session.UniformStart
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.E2E.Dsl.ClampsLossless
import Computational.Proofs.GameHop.CompDedup
import Computational.Proofs.GameHop.StateSim
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Queries
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort.SimAndSM
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PrivRedQueries
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import VCVio.EvalDist.Monad.Basic

/-!
# Game Loop, Cost Bounds, and Clamping Equivalence for `simFig8`

Defines `atomicSig` state encodings, loop assembly (`simFig8ProgOfStep`), syntactic description-bit
and `GRedBounded` bounds, and clamping-equivalence theorems (`simFig8Clamp`, `simFig8ClampTG`) for
`SessionCostedReductions.simFig8`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost

open scoped ENNReal BigOperators
open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Samplers Iface Expr Comp GameCodec CostedReduction
  UniformSamplerTag bits bits_mono reductionSizeBudget handlerImpl isGameQuery
  atomicSig atomicSamplers atomicSessionOps fig8SmIface e2eSessionCodec
  B U32 BV256 BV512 PK IdKey PlainT PtT GhostStT smQT smRT
  partyToBool boolToParty fig8CtT fig8CtV fig8CtOfV fig8StT fig8StV fig8StOfV
  fsSendStT fsSendStV fsSendStOfV fsRecvStT fsRecvStV fsRecvStOfV ckaStOfV)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet (RootKey keyToBytesVec32 rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (dummyKey lFS lFig8 LibsignalMsgPublicPart)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C Fig8Comp GhostChain SimState initSim)
open CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState initSimC)
open CryptoGames.SM (Pos Record GameState RecvResult partyEnc partyDec posTy posEnc posDec)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState maxForwardJumps)
open CryptoVerification.LibsignalSession (ratchetCostBudget ratchetCostBudget_pos GRedBounded)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds gRedBounded_of_bounds_const)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mul_le size_le_budget_of_log_cost)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1Init spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes idsOf paramsV1 SessionCostedReductions)
open Computational.Proofs.E2E.Dsl.ClampsLossless (spqrV1Init_length_le_158)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
  (atomicSamplers_sizeHonest atomicSessionOps_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (sessPureOp sessSpqrKemOp atomicDraw256 eval_sessPureOp cost_sessPureOp
   eval_sessSpqrKemOp cost_sessSpqrKemOp atomicDraw256_eval atomicDraw256_cost
   atomicDraw256_queries_zero)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
  (bits_succ_le session_cost_le_ratchetCostBudget session_cost_cubic_le_ratchetCostBudget
   dummyBoolSessionRed dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le)

/-! ## State encodings -/

/-- `SM.Record (Plain ℓ) Bytes` encoded in `atomicSig ℓ Pt`. -/
@[reducible] def simRecT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod posTy (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (B (ℓ := ℓ) (Pt := Pt) 32))

/-- `GameState Unit (Plain ℓ) Bytes` encoded in `atomicSig ℓ Pt`. -/
@[reducible] def simMirT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .bool
    (.prod .bool
      (.prod (.prod .nat .nat)
        (.prod (.prod .nat .nat)
          (.prod (.opt .nat)
            (.prod (.list (simRecT ℓ Pt))
              (.prod (.list posTy)
                (.prod (.list posTy)
                  (.prod (.prod (.tbl .nat) (.tbl .nat))
                    (.prod (.list .nat)
                      (.list (.prod .bool .nat)))))))))))

/-- `GhostChain` encoded in `atomicSig ℓ Pt`: `(key?, (epoch, (last, skipped)))`. -/
@[reducible] def ghostChainT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.opt (PK (ℓ := ℓ) (Pt := Pt))) (.prod .nat (.prod .nat (.list .nat)))

/-- `SimState Bytes Pt ℓ` encoded in `atomicSig ℓ Pt`. -/
@[reducible] def simBaseT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simMirT ℓ Pt)
    (.prod (.prod (B (ℓ := ℓ) (Pt := Pt) 32) (B (ℓ := ℓ) (Pt := Pt) 32))
      (.prod (.prod (U32 (ℓ := ℓ) (Pt := Pt)) (U32 (ℓ := ℓ) (Pt := Pt)))
        (.prod .bool
          (.prod (.list (.prod (B (ℓ := ℓ) (Pt := Pt) 32) (fig8CtT (ℓ := ℓ) (Pt := Pt))))
            (.prod (.prod (.list (ghostChainT ℓ Pt)) (.list (ghostChainT ℓ Pt)))
              (.prod .nat .bool))))))

/-- `Kept Pt` encoded in `atomicSig ℓ Pt`: `(full?, rsTbl)`. -/
@[reducible] def keptT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.opt (fig8StT (ℓ := ℓ) (Pt := Pt))) (.tbl (.opt (fsRecvStT (ℓ := ℓ) (Pt := Pt))))

/-- Corruption snapshot `(Party × ℕ × GhostState Bytes)` encoded in `atomicSig ℓ Pt`. -/
@[reducible] def snapT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .bool (.prod .nat (GhostStT (ℓ := ℓ) (Pt := Pt)))

/-- Sent entry `(Fig8C Pt × RatchetSenderState)` encoded in `atomicSig ℓ Pt`. -/
@[reducible] def sentEntryT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fsSendStT (ℓ := ℓ) (Pt := Pt))

/-- Full `LibsignalToModularSchemeSimState Bytes Pt ℓ` encoded in `atomicSig ℓ Pt`. -/
@[reducible] def simFullT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simBaseT ℓ Pt)
    (.prod (.prod (keptT ℓ Pt) (keptT ℓ Pt))
      (.prod (.list (sentEntryT ℓ Pt)) (.list (snapT ℓ Pt))))

section StateEncodings

variable {ℓ : ℕ} {Pt : Type}

def simRecEnc (r : Record (Plain ℓ) Bytes) : (simRecT ℓ Pt).denote :=
  (posEnc r.pos, (r.msg, r.ct))

def simRecDec (v : (simRecT ℓ Pt).denote) : Record (Plain ℓ) Bytes :=
  ⟨posDec v.1, v.2.1, v.2.2⟩

@[simp] theorem simRecDec_simRecEnc (r : Record (Plain ℓ) Bytes) :
    simRecDec (Pt := Pt) (simRecEnc r) = r := by
  cases r; simp [simRecEnc, simRecDec]

@[simp] theorem simRecEnc_simRecDec (v : (simRecT ℓ Pt).denote) :
    simRecEnc (simRecDec (Pt := Pt) v) = v := by
  rcases v with ⟨p, m, c⟩; simp [simRecEnc, simRecDec]

def simMirEnc (s : GameState Unit (Plain ℓ) Bytes) : (simMirT ℓ Pt).denote :=
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

def simMirDec (v : (simMirT ℓ Pt).denote) : GameState Unit (Plain ℓ) Bytes :=
  let (b, (win, (epAB, (idxAB, (tL, (trs, (chall, (comp, (maAB, (leaks, corrs)))))))))) := v
  { st := fun _ => ()
    epoch := fun | .A => epAB.1 | .B => epAB.2
    idx := fun | .A => idxAB.1 | .B => idxAB.2
    tL := tL
    trans := trs.map (simRecDec (Pt := Pt))
    chall := chall.map posDec
    comp := comp.map posDec
    maxAcc := fun | .A => maAB.1 | .B => maAB.2
    b := b
    win := win
    leaks := leaks
    corrs := corrs.map (fun pe => (partyDec pe.1, pe.2)) }

@[simp] theorem simMirDec_simMirEnc (s : GameState Unit (Plain ℓ) Bytes) :
    simMirDec (Pt := Pt) (simMirEnc s) = s := by
  cases s
  simp only [simMirEnc, simMirDec, List.map_map]
  congr 1
  · funext p; cases p <;> rfl
  · funext p; cases p <;> rfl
  · rw [show (simRecDec (Pt := Pt) ∘ simRecEnc :
        Record (Plain ℓ) Bytes → Record (Plain ℓ) Bytes) = id by
      funext r; simp, List.map_id]
  · rw [show (posDec ∘ posEnc : Pos → Pos) = id by funext p; simp, List.map_id]
  · rw [show (posDec ∘ posEnc : Pos → Pos) = id by funext p; simp, List.map_id]
  · funext p; cases p <;> rfl
  · rw [show ((fun pe : Bool × ℕ => (partyDec pe.1, pe.2)) ∘
        (fun pe : Party × ℕ => (partyEnc pe.1, pe.2))) = id by
      funext ⟨p, e⟩; simp, List.map_id]

def ghostChainEnc (g : GhostChain) : (ghostChainT ℓ Pt).denote :=
  (g.key, (g.epoch, (g.last, g.skipped)))

def ghostChainDec (v : (ghostChainT ℓ Pt).denote) : GhostChain :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2⟩

@[simp] theorem ghostChainDec_ghostChainEnc (g : GhostChain) :
    ghostChainDec (ℓ := ℓ) (Pt := Pt) (ghostChainEnc g) = g := by
  cases g; rfl

def honestPairEnc (wc : Bytes × Fig8C Pt) : Bytes × (fig8CtT (ℓ := ℓ) (Pt := Pt)).denote :=
  (wc.1, fig8CtV wc.2)

def honestPairDec (v : Bytes × (fig8CtT (ℓ := ℓ) (Pt := Pt)).denote) : Bytes × Fig8C Pt :=
  (v.1, fig8CtOfV v.2)

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : ℕ)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : ℕ)
    (hj : j < bs.length) (h32 : j < 32) :
    (bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [bytesToKey32] using extractLsb'_zero_bytesToKey32_cons b (bytesToKey32 rest)
    | succ j =>
      have hcons : bytesToKey32 (b :: rest) =
          (bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons b (bytesToKey32 rest) j h32,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

@[simp] theorem bytesToKey32_keyToBytes32 (k : BitVec 256) :
    bytesToKey32 (keyToBytes32 k) = k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hj : i / 8 < 32 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToKey32 (keyToBytes32 k) (i / 8) (by simp [keyToBytes32, hj]) hj)
  simp only [keyToBytes32, List.getElem_ofFn, BitVec.getLsbD_extractLsb', hr, decide_true,
    Bool.true_and, Nat.div_add_mod] at hbyte
  exact hbyte

theorem keyToBytes32_bytesToKey32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    keyToBytes32 (bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [keyToBytes32, h]) fun j h1 h2 => ?_
  simp only [keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32 bs j h2 (by omega)

@[simp] theorem fig8CtOfV_fig8CtV (c : Fig8C Pt) :
    fig8CtOfV (ℓ := ℓ) (Pt := Pt) (fig8CtV c) = c := by
  rcases c with ⟨⟨t, T⟩, ⟨i, ⟨⟨ser, tag⟩, ⟨xs, hxs⟩⟩⟩⟩
  simp only [fig8CtV, fig8CtOfV, ReductionDsl.lctV, ReductionDsl.lctOfV,
    ReductionDsl.wireSaltCtV, ReductionDsl.wireSaltCtOfV, ReductionDsl.salt32V,
    ReductionDsl.salt32OfV]
  congr 3
  apply List.Vector.eq
  simp [keyToBytesVec32, keyToBytes32_bytesToKey32 xs hxs]

@[simp] theorem honestPairDec_honestPairEnc (wc : Bytes × Fig8C Pt) :
    honestPairDec (ℓ := ℓ) (Pt := Pt) (honestPairEnc wc) = wc := by
  rcases wc with ⟨w, c⟩; simp [honestPairEnc, honestPairDec]

def simBaseEnc (s : SimState Bytes Pt ℓ) : (simBaseT ℓ Pt).denote :=
  (simMirEnc s.mir,
   ((s.pq .A, s.pq .B),
    ((s.pn .A, s.pn .B),
     (s.unackA,
      (s.honest.map honestPairEnc,
       (((s.chains .A).map ghostChainEnc, (s.chains .B).map ghostChainEnc),
        (s.amb, s.stopped)))))))

def simBaseDec (v : (simBaseT ℓ Pt).denote) : SimState Bytes Pt ℓ :=
  let (mir, (pqAB, (pnAB, (unackA, (honest, (chainsAB, (amb, stopped))))))) := v
  { mir := simMirDec mir
    pq := fun | .A => pqAB.1 | .B => pqAB.2
    pn := fun | .A => pnAB.1 | .B => pnAB.2
    unackA := unackA
    honest := honest.map honestPairDec
    chains := fun
      | .A => chainsAB.1.map ghostChainDec
      | .B => chainsAB.2.map ghostChainDec
    amb := amb
    stopped := stopped }

@[simp] theorem simBaseDec_simBaseEnc (s : SimState Bytes Pt ℓ) :
    simBaseDec (simBaseEnc s) = s := by
  cases s
  simp only [simBaseEnc, simBaseDec, simMirDec_simMirEnc, List.map_map]
  congr 1
  · funext p; cases p <;> rfl
  · funext p; cases p <;> rfl
  · rw [show (honestPairDec (ℓ := ℓ) (Pt := Pt) ∘ honestPairEnc :
        Bytes × Fig8C Pt → Bytes × Fig8C Pt) = id by funext x; simp, List.map_id]
  · funext p; cases p <;>
      simp [show (ghostChainDec (ℓ := ℓ) (Pt := Pt) ∘ ghostChainEnc :
        GhostChain → GhostChain) = id by funext g; simp]

def keptEnc (k : Kept Pt) : (keptT ℓ Pt).denote :=
  (k.full.map fig8StV, fun t => (k.rs t).map fsRecvStV)

def keptDec (v : (keptT ℓ Pt).denote) : Kept Pt :=
  ⟨v.1.map fig8StOfV, fun t => (v.2 t).map fsRecvStOfV⟩

@[simp] theorem fsSendStOfV_fsSendStV (s : CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)) :
    fsSendStOfV (ℓ := ℓ) (Pt := Pt) (fsSendStV s) = s := by
  cases s; rfl

@[simp] theorem fsRecvStOfV_fsRecvStV
    (r : CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) :
    fsRecvStOfV (ℓ := ℓ) (Pt := Pt) (fsRecvStV r) = r := by
  cases r; rfl

@[simp] theorem fig8StOfV_fig8StV (st : Fig8St Pt) :
    fig8StOfV (ℓ := ℓ) (Pt := Pt) (fig8StV st) = st := by
  rcases st with ⟨idP, rk, vs?, vr, γ, cur?, tc⟩
  simp only [fig8StV, fig8StOfV]
  have hp : boolToParty (partyToBool idP) = idP := by cases idP <;> rfl
  have hvs : (vs?.map (fsSendStV (ℓ := ℓ) (Pt := Pt))).map fsSendStOfV = vs? := by
    cases vs? <;> simp
  have hvr : (fun t => ((vr t).map (fsRecvStV (ℓ := ℓ) (Pt := Pt))).map fsRecvStOfV) = vr := by
    funext t; cases vr t <;> simp
  have hγ : ckaStOfV (ℓ := ℓ) (Pt := Pt) (ReductionDsl.ckaStV γ) = γ := by
    cases γ <;> rfl
  rw [hp, hvs, hvr, hγ]

@[simp] theorem keptDec_keptEnc (k : Kept Pt) :
    keptDec (ℓ := ℓ) (Pt := Pt) (keptEnc k) = k := by
  rcases k with ⟨full, rs⟩
  simp only [keptEnc, keptDec]
  congr 1
  · cases full <;> simp
  · funext t; cases rs t <;> simp

def snapEnc (e : Party × ℕ × GhostState Bytes) : (snapT ℓ Pt).denote :=
  (partyEnc e.1, (e.2.1, e.2.2))

def snapDec (v : (snapT ℓ Pt).denote) : Party × ℕ × GhostState Bytes :=
  (partyDec v.1, (v.2.1, v.2.2))

@[simp] theorem snapDec_snapEnc (e : Party × ℕ × GhostState Bytes) :
    snapDec (ℓ := ℓ) (Pt := Pt) (snapEnc e) = e := by
  rcases e with ⟨p, ep, g⟩; simp [snapEnc, snapDec]

def sentEntryEnc (e : Fig8C Pt × CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)) :
    (sentEntryT ℓ Pt).denote :=
  (fig8CtV e.1, fsSendStV e.2)

def sentEntryDec (v : (sentEntryT ℓ Pt).denote) :
    Fig8C Pt × CryptoGames.FSAEAD.RatchetSenderState (BitVec 256) :=
  (fig8CtOfV v.1, fsSendStOfV v.2)

@[simp] theorem sentEntryDec_sentEntryEnc
    (e : Fig8C Pt × CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)) :
    sentEntryDec (ℓ := ℓ) (Pt := Pt) (sentEntryEnc e) = e := by
  rcases e with ⟨c, v⟩; simp [sentEntryEnc, sentEntryDec]

def simFullEnc (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) : (simFullT ℓ Pt).denote :=
  (simBaseEnc sC.base,
   ((keptEnc (sC.kept .A), keptEnc (sC.kept .B)),
    (sC.sent.map sentEntryEnc, sC.snaps.map snapEnc)))

def simFullDec (v : (simFullT ℓ Pt).denote) : LibsignalToModularSchemeSimState Bytes Pt ℓ :=
  let (base, (keptAB, (sent, snaps))) := v
  { base := simBaseDec base
    kept := fun | .A => keptDec keptAB.1 | .B => keptDec keptAB.2
    sent := sent.map sentEntryDec
    snaps := snaps.map snapDec }

@[simp] theorem simFullDec_simFullEnc (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) :
    simFullDec (simFullEnc sC) = sC := by
  cases sC
  simp only [simFullEnc, simFullDec, simBaseDec_simBaseEnc, List.map_map]
  congr 1
  · funext p; cases p <;> simp
  · rw [show (sentEntryDec (ℓ := ℓ) (Pt := Pt) ∘ sentEntryEnc : _ → _) = id by
      funext e; simp, List.map_id]
  · rw [show (snapDec (ℓ := ℓ) (Pt := Pt) ∘ snapEnc : _ → _) = id by
      funext e; simp, List.map_id]

end StateEncodings

/-! ## Loop assembly -/

section LoopAndCost

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local notation "ASig" => atomicSig ℓ Pt

theorem atomicSpqrV1InitOp_lossless (C : Crypto) (K : MlKem)
    (isAlice : Bool) (pqrKey : BitVec 256) :
    (spqrV1Init C.F K (if isAlice then .a2b else .b2a) pqrKey).take 512 =
      spqrV1Init C.F K (if isAlice then .a2b else .b2a) pqrKey :=
  List.take_of_length_le
    (Nat.le_trans (spqrV1Init_length_le_158 C.F K _ pqrKey) (by decide))

def initSimMirE {O' : Ops ASig} {Γ : List (Ty ASig)} : Expr O' Γ (simMirT ℓ Pt) :=
  .pair (.bool false)
    (.pair (.bool false)
      (.pair (.pair (.nat 0) (.nat 0))
        (.pair (.pair (.nat 0) (.nat 0))
          (.pair .none
            (.pair .nil
              (.pair .nil
                (.pair .nil
                  (.pair (.pair (.tconst (.nat 0)) (.tconst (.nat 0)))
                    (.pair .nil .nil)))))))))

def keptUnknownE {O' : Ops ASig} {Γ : List (Ty ASig)} : Expr O' Γ (keptT ℓ Pt) :=
  .pair .none (.tconst .none)

def initSimCE {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty ASig)}
    (pqA pqB : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (B 32)) :
    Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simFullT ℓ Pt) :=
  let zero32 := sessPureOp (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (.u32Lit 0) .unit
  let initChainA : Expr _ Γ (ghostChainT ℓ Pt) :=
    .pair .none (.pair (.nat 0) (.pair (.nat 0) .nil))
  let baseE : Expr _ Γ (simBaseT ℓ Pt) :=
    .pair initSimMirE
      (.pair (.pair pqA pqB)
        (.pair (.pair zero32 zero32)
          (.pair (.bool true)
            (.pair .nil
              (.pair (.pair (.cons initChainA .nil) .nil)
                (.pair (.nat 0) (.bool false)))))))
  .pair baseE (.pair (.pair keptUnknownE keptUnknownE) (.pair .nil .nil))

omit [SampleableType Pt] in
@[simp] theorem eval_initSimCE {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty ASig)}
    (pqA pqB : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (B 32)) (ρ : Env Γ) :
    (initSimCE pqA pqB).eval ρ = simFullEnc (initSimC (pqA.eval ρ) (pqB.eval ρ)) := by
  simp only [initSimCE, initSimMirE, keptUnknownE, Expr.eval, simFullEnc, initSimC, simBaseEnc,
    initSim, simMirEnc, keptEnc, Kept.unknown, List.map_nil]
  rfl

omit [SampleableType Pt] in
theorem cost_initSimCE {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty ASig)}
    (pqA pqB : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (B 32)) :
    (initSimCE pqA pqB).cost ≤ pqA.cost + pqB.cost + 80 := by
  have hb0 : bits 0 = 1 := rfl
  have hd :
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).cost
        (Sum.inl (Sum.inl (Sum.inl (Sum.inl (ReductionDsl.AtomicPureOp.u32Lit 0))))) = 1 := rfl
  simp only [initSimCE, initSimMirE, keptUnknownE, Expr.cost, hb0, hd]
  omega

/-- Concrete `init` computation for `simFig8` over `atomicSessionOps` and `fig8SmIface`. -/
def simFig8InitC (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [.unit] (.prod .unit (simFullT ℓ Pt)) :=
  .bind (atomicDraw256 (I := fig8SmIface ℓ Pt) rfl)
    (.ret (.pair .unit
      (initSimCE
        (sessSpqrKemOp .spqrV1InitOp (.pair (.bool true) (.var .zero)))
        (sessSpqrKemOp .spqrV1InitOp (.pair (.bool false) (.var .zero))))))

theorem simFig8InitC_queries_zero (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (w : (fig8SmIface ℓ Pt).Tag → ℕ) :
    (simFig8InitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).queries w (fun _ => 0) = 0 := by
  simp [simFig8InitC, Comp.queries, atomicDraw256_queries_zero]

theorem simFig8InitC_cost_le (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    (simFig8InitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost ≤ 600 := by
  let pqA : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) [BV256, .unit] (B 32) :=
    sessSpqrKemOp .spqrV1InitOp (.pair (.bool true) (.var .zero))
  let pqB : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) [BV256, .unit] (B 32) :=
    sessSpqrKemOp .spqrV1InitOp (.pair (.bool false) (.var .zero))
  have hc := cost_initSimCE pqA pqB
  have hcA : pqA.cost = 213 := rfl
  have hcB : pqB.cost = 213 := rfl
  have hdraw := atomicDraw256_cost (ℓ := ℓ) (Pt := Pt)
    (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
    (I := fig8SmIface ℓ Pt) (Γ := [.unit]) rfl
  dsimp only [simFig8InitC, Comp.cost, Expr.cost]
  dsimp only [pqA, pqB] at hc hcA hcB
  rw [hdraw]
  omega

def simFig8InitImpl (C : Crypto) (K : MlKem) :
    Fig8Comp Pt ℓ (Unit × LibsignalToModularSchemeSimState Bytes Pt ℓ) := do
  let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
  return ((), initSimC (spqrV1Init C.F K .a2b pqrKey) (spqrV1Init C.F K .b2a pqrKey))

omit [SampleableType Pt] in
private theorem initSimCE_spqrV1Init_eval (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (pqrKey : BitVec 256) :
    (initSimCE (ℓ := ℓ) (Pt := Pt)
      (sessSpqrKemOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .spqrV1InitOp (.pair (.bool true) (.var .zero)))
      (sessSpqrKemOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .spqrV1InitOp (.pair (.bool false) (.var .zero)))).eval
      (.cons pqrKey (.cons () .nil) : Env [BV256, .unit]) =
    simFullEnc (ℓ := ℓ) (Pt := Pt)
      (initSimC (spqrV1Init C.F K .a2b pqrKey) (spqrV1Init C.F K .b2a pqrKey)) := by
  rw [eval_initSimCE, eval_sessSpqrKemOp, eval_sessSpqrKemOp]
  dsimp only [ReductionDsl.AtomicSpqrKemOp.eval, Expr.eval]
  rw [atomicSpqrV1InitOp_lossless, atomicSpqrV1InitOp_lossless]
  rfl

theorem simFig8InitC_eval (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    (simFig8InitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval (.cons () .nil) =
      Prod.map id simFullEnc <$> simFig8InitImpl (ℓ := ℓ) (Pt := Pt) C K := by
  unfold simFig8InitC simFig8InitImpl
  rw [SessionProgCommon.comp_eval_bind, atomicDraw256_eval]
  have hlift : (fig8SmIface ℓ Pt).liftP ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) =
      (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256)) := by
    induction ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) using OracleComp.inductionOn with
    | pure a => rfl
    | query_bind n mx ih =>
      dsimp only [Iface.liftP] at ih ⊢
      rw [simulateQ_bind, simulateQ_query]
      exact bind_congr ih
  rw [hlift]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  rw [SessionProgCommon.comp_eval_ret]
  have hpair :
      (Expr.pair .unit
        (initSimCE
          (sessSpqrKemOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) .spqrV1InitOp (.pair (.bool true) (.var .zero)))
          (sessSpqrKemOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) .spqrV1InitOp (.pair (.bool false) (.var .zero))))).eval
        (.cons pqrKey (.cons () .nil) : Env [BV256, .unit]) =
      ((), simFullEnc (initSimC (spqrV1Init C.F K .a2b pqrKey) (spqrV1Init C.F K .b2a pqrKey))) := by
    change ((), _) = _
    rw [initSimCE_spqrV1Init_eval]
  rw [hpair]
  rfl

def simFig8FinishC (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, .bool] .bool :=
  .ret (.var (.succ .zero))

theorem simFig8FinishC_queries_zero (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (w : (fig8SmIface ℓ Pt).Tag → ℕ) :
    (simFig8FinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).queries w (fun _ => 0) = 0 :=
  rfl

theorem simFig8FinishC_cost_le (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    (simFig8FinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost ≤ 4 := by
  simp [simFig8FinishC, Comp.cost, Expr.cost]

@[simp] theorem simFig8FinishC_eval (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (s : (simFullT ℓ Pt).denote) (b : Bool) :
    (simFig8FinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval
      (.cons s (.cons b .nil)) = pure b :=
  rfl

/-- Assemble `simFig8` as a `CostedReduction` from any step handler `step` on `simFullT ℓ Pt`,
with automatic fallback to `dummyBoolSessionRed` when `¬ (ℓ < 10 ^ 6)`. -/
def simFig8ProgOfStep (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt))) :
    CostedReduction
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool .bool :=
  if _hℓ : ℓ < 10 ^ 6 then
    { σ := simFullT ℓ Pt
      init := simFig8InitC C K Dh encPt encT decT lam
      handle := step
      finish := simFig8FinishC C K Dh encPt encT decT lam }
  else
    dummyBoolSessionRed (fig8SmIface ℓ Pt) .unit

theorem simFig8ProgOfStep_totalQueries_le (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1) :
    (simFig8ProgOfStep C K Dh encPt encT decT lam step).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q := by
  unfold simFig8ProgOfStep
  split_ifs with hℓ
  · simp only [CostedReduction.totalQueries, simFig8InitC_queries_zero,
      simFig8FinishC_queries_zero, zero_add, add_zero]
    exact le_trans (Nat.mul_le_mul_left q hstep_q) (by omega)
  · rw [dummyBoolSessionRed_totalQueries]
    exact Nat.zero_le q

theorem simFig8ProgOfStep_totalCost_le (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1)) :
    (simFig8ProgOfStep C K Dh encPt encT decT lam step).totalCost q ≤
      ratchetCostBudget q (qep + 1) := by
  unfold simFig8ProgOfStep
  split_ifs with hℓ
  · have hi := simFig8InitC_cost_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hf := simFig8FinishC_cost_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hs := hstep_c hℓ
    have hmax : max 1 (step.cost + 16) ≤
        199000020 + 100000000 * q + 4096 * bits (qep + 1) := by
      omega
    have htot :
        ({ σ := simFullT ℓ Pt
           init := simFig8InitC C K Dh encPt encT decT lam
           handle := step
           finish := simFig8FinishC C K Dh encPt encT decT lam } :
          CostedReduction _ _ _ (e2eSessionCodec ℓ Pt) _ _ _ _).totalCost q ≤
        600 + q * (199000020 + 100000000 * q + 4096 * bits (qep + 1)) + 4 := by
      dsimp only [CostedReduction.totalCost]
      have hmul := Nat.mul_le_mul_left q hmax
      omega
    exact htot.trans (session_cost_le_ratchetCostBudget q (qep + 1)
      600 4 199000020 100000000 4096
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact dummyBoolSessionRed_totalCost_le (fig8SmIface ℓ Pt) rfl .unit q (qep + 1)

theorem simFig8ProgOfStep_totalCost_le_linear (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1)) :
    (simFig8ProgOfStep C K Dh encPt encT decT lam step).totalCost q ≤
      ratchetCostBudget q (qep + 1) :=
  simFig8ProgOfStep_totalCost_le C K Dh encPt encT decT lam qep q step hstep_c

end LoopAndCost

/-! ## `descBits` and `ratchetDescBudget` bounds -/

section DescBits

open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSortDescBits atomicTyDescBits varIdx atomicPureOpDescBits atomicSymOpDescBits
   atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits
   defaultDescBitBudget descBitBudget ratchetDescBudget
   descBitBudget_mono ratchetDescBudget_mono descBitBudget_le_default ratchetDescBudget_le_default
   ratchetDescBudget_le_reductionSizeBudget red_size_le_of_atomicCompDescBits)

/-- Total syntactic description bit-length of a session-level `CostedReduction` over
`atomicSessionOps` and `fig8SmIface` (charging `8` bits per sampler and oracle tag). -/
def atomicFig8RedDescBits {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {κ : Type} {G : OracleSpec κ} {GC : GameCodec (atomicSig ℓ Pt) G}
    {rIn aIn aOut out : Ty (atomicSig ℓ Pt)}
    (R : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIface ℓ Pt) G GC rIn aIn aOut out) : ℕ :=
  atomicTyDescBits R.σ + atomicTyDescBits rIn + atomicTyDescBits aIn +
    atomicTyDescBits aOut + atomicTyDescBits out +
    (atomicTyDescBits GC.Q + atomicTyDescBits GC.R) +
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.init +
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.handle +
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.finish

theorem simFullT_descBits_le (ℓ : ℕ) (Pt : Type) :
    atomicTyDescBits (simFullT ℓ Pt) ≤ 2000 := by
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by decide
  dsimp only [simFullT, simBaseT, simMirT, simRecT, ghostChainT, keptT, snapT, sentEntryT,
    fig8CtT, ReductionDsl.fig8HdrT, fig8StT, fsSendStT, fsRecvStT, ReductionDsl.ckaStT,
    ReductionDsl.lctT, ReductionDsl.wireSaltCtT, ReductionDsl.B, ReductionDsl.PB,
    ReductionDsl.BV128, ReductionDsl.U64, PK, U32, BV256, PlainT, PtT, GhostStT, posTy,
    atomicTyDescBits, atomicSortDescBits]
  rw [hb32]
  omega

theorem simFig8InitC_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (simFig8InitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam) ≤ 2000 := by
  have hb0 : bits 0 = 1 := by decide
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by decide
  dsimp only [simFig8InitC, atomicDraw256, initSimCE, initSimMirE, keptUnknownE,
    sessPureOp, sessSpqrKemOp, simRecT, ghostChainT, posTy, PlainT, PK,
    ReductionDsl.B, ReductionDsl.PB, fig8CtT, ReductionDsl.fig8HdrT, fsRecvStT,
    ReductionDsl.lctT, ReductionDsl.wireSaltCtT, ReductionDsl.BV128, ReductionDsl.U64,
    BV256, PtT, varIdx, atomicCompDescBits, atomicExprDescBits, atomicSessionOpDescBits,
    atomicPureOpDescBits, atomicTyDescBits, atomicSortDescBits]
  rw [hb0, hb32]
  omega

theorem simFig8FinishC_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (simFig8FinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam) ≤ 50 := by
  have hb1 : bits 1 = 1 := by decide
  dsimp only [simFig8FinishC, varIdx, atomicCompDescBits, atomicExprDescBits]
  rw [hb1]
  omega

theorem dummyBoolSessionRed_fig8_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {rIn : Ty (atomicSig ℓ Pt)} (hrIn : atomicTyDescBits rIn ≤ 64) (q qep : ℕ) :
    atomicFig8RedDescBits
      (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (fig8SmIface ℓ Pt) rIn) ≤
      ratchetDescBudget q qep := by
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by decide
  have hcodecQ : atomicTyDescBits (e2eSessionCodec ℓ Pt).Q ≤ 200 := by
    dsimp only [e2eSessionCodec, ReductionDsl.smQT, ReductionDsl.B, atomicTyDescBits,
      atomicSortDescBits]
    rw [hb32]
    omega
  have hcodecR : atomicTyDescBits (e2eSessionCodec ℓ Pt).R ≤ 200 := by
    dsimp only [e2eSessionCodec, ReductionDsl.smRT, atomicTyDescBits, atomicSortDescBits]
    omega
  have hhandle :
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (fig8SmIface ℓ Pt) rIn).handle ≤ 300 := by
    dsimp only [dummyBoolSessionRed, e2eSessionCodec, ReductionDsl.smRT,
      atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits]
    omega
  have hfin :
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (fig8SmIface ℓ Pt) rIn).finish ≤ 50 := by
    dsimp only [dummyBoolSessionRed, atomicCompDescBits, atomicExprDescBits]
    omega
  have hinit :
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (fig8SmIface ℓ Pt) rIn).init ≤ 50 := by
    dsimp only [dummyBoolSessionRed, atomicCompDescBits, atomicExprDescBits]
    omega
  have hbase : 2 ^ 23 ≤ ratchetDescBudget q qep := by
    unfold ratchetDescBudget descBitBudget
    omega
  unfold atomicFig8RedDescBits
  have hsig : atomicTyDescBits
      (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (fig8SmIface ℓ Pt) rIn).σ = 4 := rfl
  have hu : atomicTyDescBits (.unit : Ty (atomicSig ℓ Pt)) = 4 := rfl
  have hb : atomicTyDescBits (.bool : Ty (atomicSig ℓ Pt)) = 4 := rfl
  omega

theorem simFig8Red_descBits_le_of_parts {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (R : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool .bool)
    (q qep : ℕ)
    (hparts :
      atomicTyDescBits R.σ +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.init +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.handle +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.finish ≤
      2 ^ 22 + 2 ^ 13 * bits (ratchetCostBudget q qep + qep)) :
    atomicFig8RedDescBits R ≤ ratchetDescBudget q qep := by
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by decide
  have hcodecQ : atomicTyDescBits (e2eSessionCodec ℓ Pt).Q ≤ 200 := by
    dsimp only [e2eSessionCodec, ReductionDsl.smQT, ReductionDsl.B, atomicTyDescBits,
      atomicSortDescBits]
    rw [hb32]
    omega
  have hcodecR : atomicTyDescBits (e2eSessionCodec ℓ Pt).R ≤ 200 := by
    dsimp only [e2eSessionCodec, ReductionDsl.smRT, atomicTyDescBits, atomicSortDescBits]
    omega
  have hu : atomicTyDescBits (.unit : Ty (atomicSig ℓ Pt)) = 4 := rfl
  have hb : atomicTyDescBits (.bool : Ty (atomicSig ℓ Pt)) = 4 := rfl
  unfold atomicFig8RedDescBits ratchetDescBudget descBitBudget
  omega

theorem simFig8ProgOfStep_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))) :
    atomicFig8RedDescBits (simFig8ProgOfStep C K Dh encPt encT decT lam step) ≤
      ratchetDescBudget q (qep + 1) := by
  unfold simFig8ProgOfStep
  split_ifs with hℓ
  · apply simFig8Red_descBits_le_of_parts
    change atomicTyDescBits (simFullT ℓ Pt) +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (simFig8InitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam) +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (simFig8FinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam) ≤ _
    have hσ := simFullT_descBits_le ℓ Pt
    have hi := simFig8InitC_descBits_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hf := simFig8FinishC_descBits_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hs := hstep_d hℓ
    omega
  · exact dummyBoolSessionRed_fig8_descBits_le (by change 4 ≤ 64; omega) q (qep + 1)

private theorem two_mul_atomicSessionOps_opSize_le_local {ℓ : ℕ} {Pt : Type} [DecidableEq Pt]
    [Zero Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (o : (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).Op) :
    2 * (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).opSize o ≤
      KemFailRedLoopAndCost.atomicSessionOpDescBits o := by
  rcases o with (((o | (_ | _)) | _) | (_ | _)) | _
  · cases o <;>
      dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
        _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.atomicPureOps,
        Ops.sum, Sum.elim, _root_.ReductionDsl.AtomicPureOp.opSize,
        KemFailRedLoopAndCost.atomicSessionOpDescBits,
        KemFailRedLoopAndCost.atomicPureOpDescBits] <;> omega
  · change 2 * 0 ≤ 8 + 5; omega
  · change 2 * 0 ≤ KemFailRedLoopAndCost.atomicSymOpDescBits _ + 5; omega
  · change 2 * 0 ≤ 8 + 3; omega
  · change 2 * 0 ≤ 8 + 3; omega
  · change 2 * 0 ≤ 8 + 3; omega
  · change 2 * 0 ≤ 8 + 1; omega

theorem two_mul_expr_size_le_atomicExprDescBits {ℓ : ℕ} {Pt : Type}
    {O : Ops (atomicSig ℓ Pt)} (opBits : O.Op → ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (e : Expr O Γ t)
    (hop : ∀ o, 2 * O.opSize o ≤ opBits o :=
      by intro o; exact two_mul_atomicSessionOps_opSize_le_local o) :
    2 * e.size ≤ KemFailRedLoopAndCost.atomicExprDescBits opBits e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil =>
    simp only [Expr.size, KemFailRedLoopAndCost.atomicExprDescBits]; omega
  | add _ _ ha hb | sub _ _ ha hb | lt _ _ ha hb | eqN _ _ ha hb | and _ _ ha hb
  | pair _ _ ha hb | cons _ _ ha hb | take _ _ ha hb | tget _ _ ha hb
  | appendL _ _ _ ha hb | findB _ _ _ ha hb | anyB _ _ _ ha hb | mapB _ _ _ ha hb
  | letE _ _ ha hb =>
    simp only [Expr.size, KemFailRedLoopAndCost.atomicExprDescBits]; omega
  | mulK _ _ ha | divK _ _ ha | modK _ _ ha | not _ ha | fst _ ha | snd _ ha
  | inl _ ha | inr _ ha | some _ ha | len _ ha | tconst _ ha =>
    simp only [Expr.size, KemFailRedLoopAndCost.atomicExprDescBits]; omega
  | ite _ _ _ hc ha hb | tset _ _ _ hc ha hb | caseOpt _ _ _ hc ha hb
  | caseSum _ _ _ hc ha hb | foldrB _ _ _ _ hc ha hb =>
    simp only [Expr.size, KemFailRedLoopAndCost.atomicExprDescBits]; omega
  | op o _ ha =>
    have ho := hop o
    simp only [Expr.size, KemFailRedLoopAndCost.atomicExprDescBits]; omega

theorem two_mul_comp_size_le_atomicCompDescBits {ℓ : ℕ} {Pt : Type}
    {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T}
    (opBits : O.Op → ℕ) (sBits : I.smp.Samp → ℕ) (qBits : I.Tag → ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (c : Comp O I Γ t)
    (hop : ∀ o, 2 * O.opSize o ≤ opBits o :=
      by intro o; exact two_mul_atomicSessionOps_opSize_le_local o) :
    2 * c.size ≤ KemFailRedLoopAndCost.atomicCompDescBits opBits sBits qBits c := by
  induction c with
  | ret e =>
    have he := two_mul_expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, KemFailRedLoopAndCost.atomicCompDescBits]; omega
  | bind c k ihc ihk =>
    simp only [Comp.size, KemFailRedLoopAndCost.atomicCompDescBits]; omega
  | ite b c d ihc ihd =>
    have hb := two_mul_expr_size_le_atomicExprDescBits opBits b hop
    simp only [Comp.size, KemFailRedLoopAndCost.atomicCompDescBits]; omega
  | caseOpt e n s ihn ihs =>
    have he := two_mul_expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, KemFailRedLoopAndCost.atomicCompDescBits]; omega
  | caseSum e l r ihl ihr =>
    have he := two_mul_expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, KemFailRedLoopAndCost.atomicCompDescBits]; omega
  | sample s e =>
    have he := two_mul_expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, KemFailRedLoopAndCost.atomicCompDescBits]; omega
  | query g e =>
    have he := two_mul_expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, KemFailRedLoopAndCost.atomicCompDescBits]; omega
  | iter n e body ih =>
    have he := two_mul_expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, KemFailRedLoopAndCost.atomicCompDescBits]; omega
  | findM k l p ih | anyM k l p ih | mapM k l p ih =>
    have hl := two_mul_expr_size_le_atomicExprDescBits opBits l hop
    simp only [Comp.size, KemFailRedLoopAndCost.atomicCompDescBits]; omega
  | consumeFirstM k l p mk ih =>
    have hl := two_mul_expr_size_le_atomicExprDescBits opBits l hop
    have hmk := two_mul_expr_size_le_atomicExprDescBits opBits mk hop
    simp only [Comp.size, KemFailRedLoopAndCost.atomicCompDescBits]; omega
  | foldM k l z f ih =>
    have hl := two_mul_expr_size_le_atomicExprDescBits opBits l hop
    have hz := two_mul_expr_size_le_atomicExprDescBits opBits z hop
    simp only [Comp.size, KemFailRedLoopAndCost.atomicCompDescBits]; omega

theorem two_mul_red_size_le_atomicFig8RedDescBits {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {κ : Type} {G : OracleSpec κ} {GC : GameCodec (atomicSig ℓ Pt) G}
    {rIn aIn aOut out : Ty (atomicSig ℓ Pt)}
    (R : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIface ℓ Pt) G GC rIn aIn aOut out) :
    2 * R.size ≤ atomicFig8RedDescBits R := by
  have hi : 2 * R.init.size ≤
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.init :=
    two_mul_comp_size_le_atomicCompDescBits
      KemFailRedLoopAndCost.atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.init
  have hh : 2 * R.handle.size ≤
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.handle :=
    two_mul_comp_size_le_atomicCompDescBits
      KemFailRedLoopAndCost.atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.handle
  have hf : 2 * R.finish.size ≤
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.finish :=
    two_mul_comp_size_le_atomicCompDescBits
      KemFailRedLoopAndCost.atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.finish
  have hsum : 2 * R.size ≤
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.init +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.handle +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.finish := by
    have hmul : 2 * R.size = 2 * R.init.size + 2 * R.handle.size + 2 * R.finish.size := by
      dsimp only [CostedReduction.size]
      omega
    rw [hmul]
    exact Nat.add_le_add (Nat.add_le_add hi hh) hf
  unfold atomicFig8RedDescBits
  let T := atomicTyDescBits R.σ + atomicTyDescBits rIn + atomicTyDescBits aIn +
    atomicTyDescBits aOut + atomicTyDescBits out +
    (atomicTyDescBits GC.Q + atomicTyDescBits GC.R)
  refine hsum.trans ?_
  change _ ≤ T + _ + _ + _
  rw [Nat.add_assoc T, Nat.add_assoc T]
  exact Nat.le_add_left _ T

theorem red_size_le_atomicFig8RedDescBits {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {κ : Type} {G : OracleSpec κ} {GC : GameCodec (atomicSig ℓ Pt) G}
    {rIn aIn aOut out : Ty (atomicSig ℓ Pt)}
    (R : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIface ℓ Pt) G GC rIn aIn aOut out) :
    R.size ≤ atomicFig8RedDescBits R := by
  have h := two_mul_red_size_le_atomicFig8RedDescBits R
  omega

theorem simFig8ProgOfStep_size_le_ratchetDescBudget {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_d : ℓ < 10 ^ 6 →
      KemFailRedLoopAndCost.atomicCompDescBits KemFailRedLoopAndCost.atomicSessionOpDescBits
        (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))) :
    (simFig8ProgOfStep C K Dh encPt encT decT lam step).size ≤
      KemFailRedLoopAndCost.ratchetDescBudget q (qep + 1) :=
  (red_size_le_atomicFig8RedDescBits _).trans
    (simFig8ProgOfStep_descBits_le C K Dh encPt encT decT lam qep q step hstep_d)

theorem simFig8ProgOfStep_size_le_of_budget {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_d : ℓ < 10 ^ 6 →
      KemFailRedLoopAndCost.atomicCompDescBits KemFailRedLoopAndCost.atomicSessionOpDescBits
        (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hB : ratchetCostBudget q (qep + 1) + (qep + 1) < 2 ^ 126) :
    (simFig8ProgOfStep C K Dh encPt encT decT lam step).size ≤ reductionSizeBudget :=
  (simFig8ProgOfStep_size_le_ratchetDescBudget C K Dh encPt encT decT lam qep q step hstep_d).trans
    (KemFailRedLoopAndCost.ratchetDescBudget_le_reductionSizeBudget hB)

theorem simFig8ProgOfStep_gRedBounded_of_budget {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      KemFailRedLoopAndCost.atomicCompDescBits KemFailRedLoopAndCost.atomicSessionOpDescBits
        (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hB : ratchetCostBudget q (qep + 1) + (qep + 1) < 2 ^ 126) :
    GRedBounded (simFig8ProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  gRedBounded_of_bounds_const _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1))
    (simFig8ProgOfStep_totalCost_le C K Dh encPt encT decT lam qep q step hstep_c)
    (simFig8ProgOfStep_size_le_of_budget C K Dh encPt encT decT lam qep q step hstep_d hB)
    (simFig8ProgOfStep_totalQueries_le C K Dh encPt encT decT lam q step hstep_q)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

private theorem ratchetCostBudget_mono_qep_fig8 {q qep₁ qep₂ : ℕ} (h : qep₁ ≤ qep₂) :
    ratchetCostBudget q qep₁ ≤ ratchetCostBudget q qep₂ := by
  unfold ratchetCostBudget
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (bits_mono h) _)

theorem simFig8ProgOfStep_size_le_of_clamp {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep₀ qep q : ℕ)
    (hqep₀ : qep₀ ≤ qep)
    (hClamp : qep₀ ≤ ratchetCostBudget q (qep + 1))
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_d : ℓ < 10 ^ 6 →
      KemFailRedLoopAndCost.atomicCompDescBits KemFailRedLoopAndCost.atomicSessionOpDescBits
        (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep₀ + 1) + (qep₀ + 1))) :
    (simFig8ProgOfStep C K Dh encPt encT decT lam step).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q (qep + 1)) := by
  have h2 := (two_mul_red_size_le_atomicFig8RedDescBits _).trans
    (simFig8ProgOfStep_descBits_le C K Dh encPt encT decT lam qep₀ q step hstep_d)
  dsimp only [KemFailRedLoopAndCost.ratchetDescBudget, KemFailRedLoopAndCost.descBitBudget] at h2
  set B := ratchetCostBudget q (qep + 1)
  have hBpos : 16777216 * (q + 1) ≤ B := ratchetCostBudget_pos q (qep + 1)
  have hBmono : ratchetCostBudget q (qep₀ + 1) ≤ B :=
    ratchetCostBudget_mono_qep_fig8 (Nat.add_le_add_right hqep₀ 1)
  have hsum : ratchetCostBudget q (qep₀ + 1) + (qep₀ + 1) ≤ 4 * B := by omega
  have hbits : bits (ratchetCostBudget q (qep₀ + 1) + (qep₀ + 1)) ≤ 3 + bits B := by
    have hm1 := bits_mono hsum
    have hm2 := bits_mul_le 4 B
    have hb4 : bits 4 = 3 := by decide
    omega
  have hred : 2 ^ 22 + 3 * 2 ^ 12 ≤ reductionSizeBudget := by decide
  omega

theorem simFig8ProgOfStep_gRedBounded_of_clamp {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep₀ qep q : ℕ)
    (hqep₀ : qep₀ ≤ qep)
    (hClamp : qep₀ ≤ ratchetCostBudget q (qep + 1))
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep₀ + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      KemFailRedLoopAndCost.atomicCompDescBits KemFailRedLoopAndCost.atomicSessionOpDescBits
        (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep₀ + 1) + (qep₀ + 1))) :
    GRedBounded (simFig8ProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1))
    ((simFig8ProgOfStep_totalCost_le C K Dh encPt encT decT lam qep₀ q step hstep_c).trans
      (ratchetCostBudget_mono_qep_fig8 (Nat.add_le_add_right hqep₀ 1)))
    (simFig8ProgOfStep_size_le_of_clamp C K Dh encPt encT decT lam qep₀ qep q
      hqep₀ hClamp step hstep_d)
    (simFig8ProgOfStep_totalQueries_le C K Dh encPt encT decT lam q step hstep_q)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem simFig8ProgOfStep_size_le_of_qep_le {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (hqep : qep ≤ q + 10)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_d : ℓ < 10 ^ 6 →
      KemFailRedLoopAndCost.atomicCompDescBits KemFailRedLoopAndCost.atomicSessionOpDescBits
        (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))) :
    (simFig8ProgOfStep C K Dh encPt encT decT lam step).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q (qep + 1)) := by
  have hBpos := ratchetCostBudget_pos q (qep + 1)
  exact simFig8ProgOfStep_size_le_of_clamp C K Dh encPt encT decT lam qep qep q
    (Nat.le_refl qep) (by omega) step hstep_d

theorem simFig8ProgOfStep_gRedBounded_of_qep_le {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (hqep : qep ≤ q + 10)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      KemFailRedLoopAndCost.atomicCompDescBits KemFailRedLoopAndCost.atomicSessionOpDescBits
        (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))) :
    GRedBounded (simFig8ProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) := by
  have hBpos := ratchetCostBudget_pos q (qep + 1)
  exact simFig8ProgOfStep_gRedBounded_of_clamp C K Dh encPt encT decT lam qep qep q
    (Nat.le_refl qep) (by omega) step hstep_q hstep_c hstep_d

theorem simFig8ProgOfStep_gRedBounded_of_size {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_size : ℓ < 10 ^ 6 →
      step.size ≤ 2 ^ 21 + 2 ^ 11 * bits (ratchetCostBudget q (qep + 1))) :
    GRedBounded (simFig8ProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) := by
  refine gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1))
    (simFig8ProgOfStep_totalCost_le C K Dh encPt encT decT lam qep q step hstep_c) ?_
    (simFig8ProgOfStep_totalQueries_le C K Dh encPt encT decT lam q step hstep_q)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  apply size_le_budget_of_log_cost (C₀ := 2 ^ 22) (C₁ := 2 ^ 11) (by decide) (by decide)
  unfold simFig8ProgOfStep
  split_ifs with hℓ
  · have hi : (simFig8InitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size ≤ 100000 := by
      have h1 := two_mul_comp_size_le_atomicCompDescBits
        KemFailRedLoopAndCost.atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (simFig8InitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam)
      have h2 := simFig8InitC_descBits_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
      omega
    have hf : (simFig8FinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size ≤ 1000 := by
      have h1 := two_mul_comp_size_le_atomicCompDescBits
        KemFailRedLoopAndCost.atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (simFig8FinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam)
      have h2 := simFig8FinishC_descBits_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
      omega
    have hs := hstep_size hℓ
    dsimp only [CostedReduction.size]
    omega
  · rw [SessionProgCommon.dummyBoolSessionRed_size]
    omega

theorem simFig8ProgOfStep_gRedBounded {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      KemFailRedLoopAndCost.atomicCompDescBits KemFailRedLoopAndCost.atomicSessionOpDescBits
        (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hqep : qep ≤ q + 10) :
    GRedBounded (simFig8ProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  simFig8ProgOfStep_gRedBounded_of_qep_le C K Dh encPt encT decT lam qep q hqep
    step hstep_q hstep_c hstep_d

theorem simFig8ProgOfStep_gRedBounded_of_budget_linear {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      KemFailRedLoopAndCost.atomicCompDescBits KemFailRedLoopAndCost.atomicSessionOpDescBits
        (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hB : ratchetCostBudget q (qep + 1) + (qep + 1) < 2 ^ 126) :
    GRedBounded (simFig8ProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  gRedBounded_of_bounds_const _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1))
    (simFig8ProgOfStep_totalCost_le_linear C K Dh encPt encT decT lam qep q step hstep_c)
    (simFig8ProgOfStep_size_le_of_budget C K Dh encPt encT decT lam qep q step hstep_d hB)
    (simFig8ProgOfStep_totalQueries_le C K Dh encPt encT decT lam q step hstep_q)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem simFig8ProgOfStep_gRedBounded_of_clamp_linear {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep₀ qep q : ℕ)
    (hqep₀ : qep₀ ≤ qep)
    (hClamp : qep₀ ≤ ratchetCostBudget q (qep + 1))
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep₀ + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      KemFailRedLoopAndCost.atomicCompDescBits KemFailRedLoopAndCost.atomicSessionOpDescBits
        (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep₀ + 1) + (qep₀ + 1))) :
    GRedBounded (simFig8ProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1))
    ((simFig8ProgOfStep_totalCost_le_linear C K Dh encPt encT decT lam qep₀ q step hstep_c).trans
      (ratchetCostBudget_mono_qep_fig8 (Nat.add_le_add_right hqep₀ 1)))
    (simFig8ProgOfStep_size_le_of_clamp C K Dh encPt encT decT lam qep₀ qep q
      hqep₀ hClamp step hstep_d)
    (simFig8ProgOfStep_totalQueries_le C K Dh encPt encT decT lam q step hstep_q)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem simFig8ProgOfStep_gRedBounded_of_qep_le_linear {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (hqep : qep ≤ q + 10)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      KemFailRedLoopAndCost.atomicCompDescBits KemFailRedLoopAndCost.atomicSessionOpDescBits
        (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))) :
    GRedBounded (simFig8ProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) := by
  have hBpos := ratchetCostBudget_pos q (qep + 1)
  exact simFig8ProgOfStep_gRedBounded_of_clamp_linear C K Dh encPt encT decT lam qep qep q
    (Nat.le_refl qep) (by omega) step hstep_q hstep_c hstep_d

theorem simFig8ProgOfStep_gRedBounded_linear {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      KemFailRedLoopAndCost.atomicCompDescBits KemFailRedLoopAndCost.atomicSessionOpDescBits
        (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hqep : qep ≤ q + 10) :
    GRedBounded (simFig8ProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  simFig8ProgOfStep_gRedBounded_of_qep_le_linear C K Dh encPt encT decT lam qep q hqep
    step hstep_q hstep_c hstep_d

end DescBits

/-! ## `simFig8Clamp`, loop `.eval`, and query invariants -/

section SimFig8ClampAndEval

open CryptoGames.SM (noBobSendInEpoch0 noAliceCorrWhileAliceBelowEpoch10)
open CryptoGames.LibsignalSession (Params LengthsOk)
open CryptoGames.Ratchet.LibsignalSim
  (inReceiveOnlyEpoch SemHook SimStateInv SimCStateInv SimCStateBounded
   semSendHook semFwdAnswerHook semResyncHook semFwdEvictHook semFwdHook semRecvHook
   semCorrHook semCorrHookDedup semHandleHook semHandleHookDedup
   onAcceptPure onAnswerPure scPostSendPure evalCKClamp
   simStateCanon simStateCanon_idem simStateCCanon simStateCCanon_idem
   makesAtMostQueries_iff_isGameQuery semHandleHookDedup_preserves_sC_inv)
open Computational.Proofs.GameHop.CompDedup
  (afterCorrDedup canonComp canonComp_trivial canonComp_accept canonComp_record canonComp_epMgmt
   canonComp_corrAllowed canonComp_afterCorr canonComp_afterCorrDedup countLe_nil
   run'_simulateQ_eq_of_idem_proj)

/-- Truncate each receiver chain's `skippedKeys` list in `Fig8St Pt` to at most `B_skip` entries. -/
def fig8StTruncSk {Pt : Type} (B_skip : ℕ) (st : Fig8St Pt) : Fig8St Pt :=
  { st with
    vR := fun t => (st.vR t).map fun v => { v with skippedKeys := v.skippedKeys.take B_skip } }

def fig8StTruncSkOpt {Pt : Type} (B_skip? : Option ℕ) (st : Fig8St Pt) : Fig8St Pt :=
  match B_skip? with
  | none => st
  | some B_skip => fig8StTruncSk B_skip st

@[simp] theorem fig8StTruncSkOpt_none {Pt : Type} (st : Fig8St Pt) :
    fig8StTruncSkOpt none st = st := rfl

/-- Identity `SemHook` forwarding `SM.spec` queries to the underlying `Fig8Spec Pt ℓ` game
(with optional `B_skip?` truncation on `corrQuery` outputs). -/
def fig8IdSemHook {PQC Pt : Type} [SampleableType PQC] {ℓ : ℕ}
    (B_skip? : Option ℕ := none) :
    SemHook PQC Pt ℓ
      (unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (Fig8C Pt))
      Unit where
  sampleBv256 := liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
  samplePqc := liftM ($ᵗ PQC : ProbComp PQC)
  onSendCoins _ _ _ := pure ((), ())
  onTr Q m rc _ := do
    let res ← CryptoGames.SM.transmitQuery
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
      (C := Fig8C Pt) Q m rc
    return (res, ())
  onCh Q m₀ m₁ rc _ := do
    let res ← CryptoGames.SM.challQuery
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
      (C := Fig8C Pt) Q m₀ m₁ rc
    return (res, ())
  onDl Q c _ := do
    let res ← CryptoGames.SM.deliverQuery
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
      (C := Fig8C Pt) Q c
    return (res, ())
  onIj Q c _ := do
    let res ← CryptoGames.SM.injectQuery
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
      (C := Fig8C Pt) Q c
    return (res, ())
  onCr Q _ := do
    let res ← CryptoGames.SM.corrQuery
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
      (C := Fig8C Pt) Q
    return (res.map (fig8StTruncSkOpt B_skip?), ())
  onProbe _ _ _ := pure ()
  onDeliverPost _ _ _ _ := pure ()

/-- Semantic query implementation for `simFig8` (`afterCorr`, no `comp` dedup) at clamp `B`. -/
def simFig8Oracle {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ))
  | .inl n => StateT.lift
    (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n))
  | .inr t => StateT.mk fun sC =>
    Prod.map id Prod.fst <$>
      semHandleHook P Dh encPt encT decT lam (fig8IdSemHook (PQC := PQC) B_skip?) qep B t sC ()

/-- Deduplicated semantic query implementation for `simFig8` (`afterCorrDedup`) matching the
DSL bounded-list loop state. -/
def simFig8OracleDedup {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ))
  | .inl n => StateT.lift
    (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n))
  | .inr t => StateT.mk fun sC =>
    Prod.map id Prod.fst <$>
      semHandleHookDedup P Dh encPt encT decT lam (fig8IdSemHook (PQC := PQC) B_skip?) qep B t sC ()

/-- `B`-clamped semantic counterpart of `Refine.libsignalToModularSchemeSim` (with optional
`B_skip?` receiver `skippedKeys` cap on corruptions). -/
def simFig8Clamp {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    CryptoGames.SM.Adversary (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt) :=
  show Fig8Comp Pt ℓ Bool from do
    let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
    let sC₀ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    (simulateQ (simFig8Oracle P Dh encPt encT decT lam qep B B_skip?) A).run' sC₀

section CanonComm

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)

omit [DecidableEq Pt] [Zero Pt] in
private theorem onAcceptPure_simStateCanon' (qep : ℕ) (Q : Party) (w : Bytes)
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

omit [DecidableEq Pt] [Zero Pt] in
private theorem onAnswerPure_simStateCanon' (qep : ℕ) (Q : Party) (w : Bytes)
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (s : SimState PQ Pt ℓ) :
    Prod.map id simStateCanon (onAnswerPure qep Q w isDel ci? T pq' res s) =
      Prod.map id simStateCanon (onAnswerPure qep Q w isDel ci? T pq' res (simStateCanon s)) := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · simp [onAnswerPure, Prod.map, simStateCanon_idem]
  · simp [onAnswerPure, Prod.map, simStateCanon_idem]
  · exact onAcceptPure_simStateCanon' qep Q w isDel t i
      ((pm.map (·.2)).getD default) ci? T pq' s

omit [DecidableEq Pt] in
private theorem scPostSendPure_simStateCCanon'
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s₁ : GameState Unit (Plain ℓ) Bytes)
    (Q : Party) (m₀ : Plain ℓ) (isChall : Bool) (pq' : PQ)
    (pn : BitVec 32) (c : Fig8C Pt) :
    simStateCCanon (scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ isChall pq' pn c) =
      simStateCCanon (scPostSendPure P Dh encPt encT lam
        (simStateCCanon sC) (canonComp s₁) Q m₀ isChall pq' pn c) := by
  simp only [simStateCCanon, simStateCanon, scPostSendPure]
  congr 2
  exact canonComp_record s₁ 3 Q () _ isChall

omit [DecidableEq Pt] in
private theorem semSendHook_simStateCCanon' {ι : Type} {T : OracleSpec ι} {Ex : Type}
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
            CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) (simStateCCanon sC).base Q rq pn =
              CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn := fun _ _ _ => rfl
        dsimp only []
        simp only [hmk,
          show (canonComp s₁).epoch = s₁.epoch from rfl,
          show (simStateCCanon sC).base.mir.epoch = sC.base.mir.epoch from rfl,
          show (simStateCCanon sC).base.mir.idx = sC.base.mir.idx from rfl,
          show (simStateCCanon sC).base.pn = sC.base.pn from rfl]
        rcases CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq
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
            exact scPostSendPure_simStateCCanon' P Dh encPt encT lam sC s₁ Q m₀ chal.isSome pq' _ c

private theorem semFwdAnswerHook_simStateCCanon' {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
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
  have hon := onAnswerPure_simStateCanon' qep Q w isDel ci? Tpk pq' res sC.base
  have hrr := congrArg Prod.fst hon
  have hst := congrArg Prod.snd hon
  dsimp only [Prod.map, id_eq] at hrr hst
  simp only [map_pure, Prod.map, id_eq, simStateCCanon]
  rw [← hrr, ← hst]
  rcases res with _ | (_ | ⟨t, i, pm⟩) <;> rfl

omit [DecidableEq Pt] in
private theorem semResyncHook_simStateCCanon' {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : Bytes) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : Fig8C Pt)
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
    · have hon := onAcceptPure_simStateCanon' qep Q w true t i m' ci? Tpk pq' sC.base
      have hrr := congrArg Prod.fst hon
      have hst := congrArg Prod.snd hon
      dsimp only [Prod.map, id_eq] at hrr hst
      simp only [map_pure, Prod.map, id_eq, simStateCCanon]
      rw [← hrr, ← hst]

private theorem semFwdEvictHook_simStateCCanon' {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semFwdEvictHook P Dh encPt encT lam sh qep sC ex Q w isDel Tpk pq' c' =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semFwdEvictHook P Dh encPt encT lam sh qep (simStateCCanon sC) ex Q w isDel Tpk pq' c' := by
  unfold semFwdEvictHook
  have hsi : (simStateCCanon sC).base.mir.safeInj 3 = sC.base.mir.safeInj 3 := rfl
  rw [hsi]
  split_ifs
  · simp [Prod.map, simStateCCanon_idem]
  · exact semFwdAnswerHook_simStateCCanon' P Dh encPt encT lam sh qep sC ex Q w isDel none Tpk pq' c'

private theorem semFwdHook_simStateCCanon' {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ)
    (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semFwdHook P Dh encPt encT lam sh qep B sC ex Q w isDel ci? Tpk pq' honestC c' =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semFwdHook P Dh encPt encT lam sh qep B (simStateCCanon sC) ex Q w isDel ci? Tpk pq' honestC c' := by
  unfold semFwdHook
  rcases honestC with _ | c
  · exact semFwdAnswerHook_simStateCCanon' P Dh encPt encT lam sh qep sC ex Q w isDel ci? Tpk pq' c'
  · have hsi : (simStateCCanon sC).base.mir.safeInj 3 = sC.base.mir.safeInj 3 := rfl
    have hev : evalCKClamp P Dh encPt encT lam B (simStateCCanon sC) Q w c c' =
        evalCKClamp P Dh encPt encT lam B sC Q w c c' := rfl
    dsimp only []
    rw [hsi, hev]
    split_ifs
    · rcases evalCKClamp P Dh encPt encT lam B sC Q w c c' with _ | r
      · simp [Prod.map, simStateCCanon_idem]
      · exact semResyncHook_simStateCCanon' P Dh encPt encT lam sh qep sC ex Q w ci? Tpk pq' c r
    · exact semFwdAnswerHook_simStateCCanon' P Dh encPt encT lam sh qep sC ex Q w isDel ci? Tpk pq' c'

private theorem semRecvHook_simStateCCanon' {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : Bytes) (isDel : Bool) :
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
          !(CryptoGames.Ratchet.LibsignalInst.ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp [hr, Prod.map, simStateCCanon_idem]
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]
    rcases CryptoGames.Ratchet.LibsignalSim.simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with
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
                  exact semFwdEvictHook_simStateCCanon' P Dh encPt encT lam sh qep sCAmb ex Q w isDel pk pq' _
                · simp only [h4, Bool.false_eq_true, ↓reduceIte]
                  exact semFwdHook_simStateCCanon' P Dh encPt encT lam sh qep B sCAmb ex Q w isDel none pk pq' _ _
      · rw [hci]; dsimp only []
        by_cases hrej : (((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i) = true
        · simp only [hrej, ↓reduceIte]
          simp [Prod.map, simStateCCanon_idem]
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte]
          exact semFwdHook_simStateCCanon' P Dh encPt encT lam sh qep B sC ex Q w isDel (some ci) pk pq' _ _

omit [DecidableEq Pt] [Zero Pt] in
private theorem semCorrHookDedup_simStateCCanon' {ι : Type} {T : OracleSpec ι} {Ex : Type}
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
      have htg : ∀ cs, CryptoGames.Ratchet.LibsignalSim.toGhost (P := P)
          { (simStateCCanon sC).base with chains := cs } Q fig8st =
          CryptoGames.Ratchet.LibsignalSim.toGhost (P := P)
            { sC.base with chains := cs } Q fig8st := fun _ => rfl
      simp only [htg]
      congr 1
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      simp only [simStateCCanon, simStateCanon]
      congr 2
      exact canonComp_afterCorrDedup sC.base.mir Q

omit [DecidableEq Pt] [Zero Pt] in
private theorem semCorrHook_simStateCCanon' {ι : Type} {T : OracleSpec ι} {Ex : Type}
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
      have htg : ∀ cs, CryptoGames.Ratchet.LibsignalSim.toGhost (P := P)
          { (simStateCCanon sC).base with chains := cs } Q fig8st =
          CryptoGames.Ratchet.LibsignalSim.toGhost (P := P)
            { sC.base with chains := cs } Q fig8st := fun _ => rfl
      simp only [htg]
      congr 1
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      simp only [simStateCCanon, simStateCanon]
      congr 2
      exact canonComp_afterCorr sC.base.mir Q

theorem semHandleHookDedup_simStateCCanon' {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep B : ℕ)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semHandleHookDedup P Dh encPt encT decT lam sh qep B t sC ex =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semHandleHook P Dh encPt encT decT lam sh qep B t (simStateCCanon sC) ex := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_simStateCCanon' P Dh encPt encT lam sh qep sC ex Q m₀ none r
  · exact semSendHook_simStateCCanon' P Dh encPt encT lam sh qep sC ex Q m₀ (some m₁) r
  · unfold semHandleHookDedup semHandleHook
    have hhon : (simStateCCanon sC).base.honest = sC.base.honest := rfl
    dsimp only []
    rw [hhon]
    have hrec := semRecvHook_simStateCCanon' P Dh encPt encT decT lam sh qep B sC ex Q w true
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
  · exact semRecvHook_simStateCCanon' P Dh encPt encT decT lam sh qep B sC ex Q w false
  · exact semCorrHookDedup_simStateCCanon' P Dh encT sh sC ex Q

theorem semHandleHook_simStateCCanon' {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T Ex) (qep B : ℕ)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semHandleHook P Dh encPt encT decT lam sh qep B t sC ex =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semHandleHook P Dh encPt encT decT lam sh qep B t (simStateCCanon sC) ex := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_simStateCCanon' P Dh encPt encT lam sh qep sC ex Q m₀ none r
  · exact semSendHook_simStateCCanon' P Dh encPt encT lam sh qep sC ex Q m₀ (some m₁) r
  · unfold semHandleHook
    have hhon : (simStateCCanon sC).base.honest = sC.base.honest := rfl
    dsimp only []
    rw [hhon]
    have hrec := semRecvHook_simStateCCanon' P Dh encPt encT decT lam sh qep B sC ex Q w true
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
  · exact semRecvHook_simStateCCanon' P Dh encPt encT decT lam sh qep B sC ex Q w false
  · exact semCorrHook_simStateCCanon' P Dh encT sh sC ex Q

end CanonComm

theorem run'_simulateQ_simFig8OracleDedup_eq {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (simulateQ (simFig8OracleDedup P Dh encPt encT decT lam qep B B_skip?) A).run' sC =
      (simulateQ (simFig8Oracle P Dh encPt encT decT lam qep B B_skip?) A).run' sC := by
  refine run'_simulateQ_eq_of_idem_proj
    (simFig8OracleDedup P Dh encPt encT decT lam qep B B_skip?)
    (simFig8Oracle P Dh encPt encT decT lam qep B B_skip?)
    simStateCCanon ?_ ?_ A rfl
  · rintro (n | t) sC₀
    · simp [simFig8OracleDedup, simFig8Oracle, StateT.run_lift, Prod.map, simStateCCanon_idem]
    · dsimp only [simFig8OracleDedup, simFig8Oracle, StateT.run, StateT.mk]
      have hcomm : ∀ oa : OracleComp
          (unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
            (BitVec 256) (Fig8C Pt))
          ((CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Range t ×
            (LibsignalToModularSchemeSimState PQ Pt ℓ × Unit)),
          Prod.map id simStateCCanon <$> (Prod.map id Prod.fst <$> oa) =
            Prod.map id Prod.fst <$> (Prod.map id (Prod.map simStateCCanon id) <$> oa) := by
        intro oa; simp [Functor.map_map, Prod.map]
      exact (hcomm _).trans ((congrArg (Functor.map (Prod.map id Prod.fst))
        (semHandleHookDedup_simStateCCanon' P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := PQC) B_skip?) qep B t sC₀ ())).trans (hcomm _).symm)
  · rintro (n | t) sC₀
    · simp [simFig8Oracle, StateT.run_lift, Prod.map, simStateCCanon_idem]
    · dsimp only [simFig8Oracle, StateT.run, StateT.mk]
      have hcomm : ∀ oa : OracleComp
          (unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
            (BitVec 256) (Fig8C Pt))
          ((CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Range t ×
            (LibsignalToModularSchemeSimState PQ Pt ℓ × Unit)),
          Prod.map id simStateCCanon <$> (Prod.map id Prod.fst <$> oa) =
            Prod.map id Prod.fst <$> (Prod.map id (Prod.map simStateCCanon id) <$> oa) := by
        intro oa; simp [Functor.map_map, Prod.map]
      exact (hcomm _).trans ((congrArg (Functor.map (Prod.map id Prod.fst))
        (semHandleHook_simStateCCanon' P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := PQC) B_skip?) qep B t sC₀ ())).trans (hcomm _).symm)

theorem simCStateInv_initSimC {PQ Pt : Type} {ℓ L q : ℕ} (hqL : q ≤ L) (pqA pqB : PQ) :
    SimCStateInv L q (initSimC (Pt := Pt) (ℓ := ℓ) pqA pqB) := by
  refine ⟨?_, by simp [initSimC, hqL], by simp [initSimC, hqL]⟩
  simp only [SimStateInv, initSimC, initSim, List.length_nil, zero_add]
  exact ⟨hqL, hqL, hqL, ⟨[], by simp [hqL], countLe_nil [], fun _ h => nomatch h⟩,
    by decide, by decide⟩

/-- Game-loop `.eval` theorem for `simFig8ProgOfStep` against `simFig8Clamp`. -/
theorem simFig8ProgOfStep_eval {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (L qep B : ℕ) (B_skip? : Option ℕ := none) (hℓ : ℓ < 10 ^ 6)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep : ∀ t (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded L (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simFig8OracleDedup (paramsV1 C K idA idB) Dh encPt encT decT lam qep B B_skip?
        (.inr t)).run (simFullDec s_raw)))
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q) (hqL : q ≤ L) :
    (simFig8ProgOfStep C K Dh encPt encT decT lam step).eval (fun _ => A) () =
      simFig8Clamp (paramsV1 C K idA idB) ℓ Dh encPt encT decT lam qep B B_skip? A := by
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  let P := paramsV1 C K idA idB
  unfold simFig8ProgOfStep
  simp only [hℓ, ↓reduceDIte]
  set prog : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool .bool :=
    { σ := simFullT ℓ Pt
      init := simFig8InitC C K Dh encPt encT decT lam
      handle := step
      finish := simFig8FinishC C K Dh encPt encT decT lam }
  have hinit_eval :
      (Prod.map id (simFullDec (ℓ := ℓ) (Pt := Pt)) <$> prog.init.eval (.cons () .nil)) =
      (do
        let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
        return ((), initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) := by
    dsimp only [prog]
    rw [simFig8InitC_eval, Functor.map_map]
    unfold simFig8InitImpl
    rw [map_bind]
    refine bind_congr fun pqrKey => ?_
    rw [map_pure]
    simp only [Prod.map, id_eq, simFullDec_simFullEnc]
    rfl
  have hinit_inv :
      ∀ r ∈ support (prog.init.eval (.cons () .nil)),
        SimCStateInv L q (simFullDec (ℓ := ℓ) (Pt := Pt) r.2) := by
    rintro ⟨u₀, s_raw⟩ hr
    dsimp only [prog] at hr
    rw [simFig8InitC_eval, support_map, Set.mem_image] at hr
    obtain ⟨⟨_, sC₀⟩, hs, hEq₀⟩ := hr
    dsimp only [Prod.map, id_eq] at hEq₀
    injection hEq₀ with _ hs_raw
    rw [← hs_raw, simFullDec_simFullEnc]
    unfold simFig8InitImpl at hs
    rw [mem_support_bind_iff] at hs
    obtain ⟨pqrKey, -, hs⟩ := hs
    rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hs
    rcases hs with ⟨_, rfl⟩
    exact simCStateInv_initSimC hqL _ _
  have hU : ∀ n (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ),
      ((simFig8OracleDedup P Dh encPt encT decT lam qep B B_skip? (.inl n)).run sC) =
      (StateT.lift ((fig8SmIface ℓ Pt).fwdU n)).run sC := by
    intro n sC
    dsimp only [simFig8OracleDedup, fig8SmIface]
  have habs := prog.eval_eq_simulateQ_of_abs
    (simFullDec (ℓ := ℓ) (Pt := Pt))
    (fun m s_raw => SimCStateInv L m (simFullDec (ℓ := ℓ) (Pt := Pt) s_raw))
    (fun _ => do
      let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
      return ((), initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)))
    (simFig8OracleDedup P Dh encPt encT decT lam qep B B_skip?)
    (fun _ b => pure b)
    q ()
    hinit_eval
    hinit_inv
    hU
    (fun m t s_raw hInv => by
      have hBound : SimCStateBounded L (simFullDec s_raw) := hInv.toBounded
      have heq : (Prod.map id simFullDec <$> ((prog.impl (.inr t)).run s_raw)) =
          ((simFig8OracleDedup P Dh encPt encT decT lam qep B B_skip? (.inr t)).run
            (simFullDec s_raw)) :=
        hstep t s_raw hBound
      refine ⟨heq, ?_⟩
      rintro ⟨rr, s_raw'⟩ hmem
      have hmem' : (rr, simFullDec s_raw') ∈
          support ((simFig8OracleDedup P Dh encPt encT decT lam qep B B_skip? (.inr t)).run
            (simFullDec s_raw)) := by
        rw [← heq, support_map, Set.mem_image]
        exact ⟨(rr, s_raw'), hmem, rfl⟩
      dsimp only [simFig8OracleDedup, StateT.run, StateT.mk] at hmem'
      rw [support_map, Set.mem_image] at hmem'
      obtain ⟨⟨rr₀, sC', u'⟩, hsem, hEq⟩ := hmem'
      dsimp only [Prod.map, id_eq] at hEq
      injection hEq with _ hsC'
      rw [← hsC']
      exact semHandleHookDedup_preserves_sC_inv P Dh encPt encT decT lam
        (fig8IdSemHook (PQC := BitVec 512) B_skip?) L m qep B t (simFullDec s_raw) () hInv
        (rr₀, sC', u') hsem)
    (fun s_raw b _ => rfl)
    (fun s_raw hle hInv => hInv.mono hle)
    (fun _ => A)
    (fun _ => hq')
  rw [habs]
  dsimp only [simFig8Clamp, P]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  rw [← run'_simulateQ_simFig8OracleDedup_eq (paramsV1 C K idA idB) Dh encPt encT decT lam
    qep B B_skip? A, StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def]

theorem lengthsOk_paramsIdsWithSpqr_v1 (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) {ℓ : ℕ} (hℓ : ℓ < 2 ^ 31) :
    CryptoGames.LibsignalSession.LengthsOk (paramsV1 C K idA idB) ℓ := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro st rq st' salt msg h
    exact Nat.lt_of_le_of_lt
      (CryptoVerification.SpqrV1Sync.SendTotal.spqrV1Send_msg_len_le C.F K st rq st' salt msg h)
      (by decide)
  · intro a h
    exact Nat.lt_of_le_of_lt
      (Computational.Proofs.E2E.Dsl.SmReachInvParty.serializedPartyAddresses_length_le_128
        _ .A .B a h) (by decide)
  · intro a h
    exact Nat.lt_of_le_of_lt
      (Computational.Proofs.E2E.Dsl.SmReachInvParty.serializedPartyAddresses_length_le_128
        _ .B .A a h) (by decide)

section QueryInvariants

open CryptoGames.LibsignalSM.Proofs.QueryBounds
  (FSpec QInr QEq hQu_QInr hQu_QEq isQueryBoundP_congr isQueryBoundP_simulateQ_run_zero)
open CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM
  (QShort hQu_QShort SendMsgsOk badSendMsg shortB_mkPub)

private theorem liftProb_isQueryBoundP_zero {Pt α : Type} {ℓ : ℕ}
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p]
    (hQu : ∀ n, ¬ p (.inl n)) (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : Fig8Comp Pt ℓ α) p 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact isQueryBoundP_pure p x 0
  | query_bind t mx ih =>
    change IsQueryBoundP (query (spec := FSpec Pt ℓ) (.inl t) >>= fun u => liftM (mx u)) p 0
    rw [← Nat.add_zero 0]
    exact isQueryBoundP_bind (p := p)
      ((isQueryBoundP_query_iff p (.inl t) 0).2 fun h => absurd h (hQu t))
      fun u _ => ih u

private theorem simDrawSendCoins_isQueryBoundP {PQC Pt : Type} [SampleableType PQC] {ℓ : ℕ}
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p]
    (hQu : ∀ n, ¬ p (.inl n)) (B_skip? : Option ℕ) (r : Option PQC) :
    IsQueryBoundP (CryptoGames.Ratchet.LibsignalSim.semDrawSendCoins
      (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) B_skip?) r) p 0 := by
  cases r with
  | none =>
    dsimp only [CryptoGames.Ratchet.LibsignalSim.semDrawSendCoins, fig8IdSemHook]
    rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind (p := p) (liftProb_isQueryBoundP_zero hQu ($ᵗ PQC))
      fun rq _ => isQueryBoundP_pure p (rq, none) 0
  | some rq =>
    dsimp only [CryptoGames.Ratchet.LibsignalSim.semDrawSendCoins, fig8IdSemHook]
    rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind (p := p) (liftProb_isQueryBoundP_zero hQu ($ᵗ (BitVec 256)))
      fun rc _ => isQueryBoundP_pure p (rq, some rc) 0

private theorem semSendHook_fig8_isQueryBoundP {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (B_skip? : Option ℕ) (qep d : ℕ)
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p]
    (hQu : ∀ n, ¬ p (.inl n))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (hSendQ : ∀ pub rc,
      (∃ rq pn pq', CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn = some (pq', pub)) →
      (match chal with
       | none => p (.inr (.inl (.inl (.inl (.inl (Q, (pub, m₀), rc))))))
       | some m₁ => p (.inr (.inl (.inl (.inl (.inr (Q, (pub, m₀), (pub, m₁), rc))))))) → 0 < d) :
    IsQueryBoundP
      (semSendHook P Dh encPt encT lam
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) B_skip?) qep sC () Q m₀ chal r) p d := by
  unfold semSendHook
  by_cases hc1 : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) = true
  · simp only [hc1, ↓reduceIte]; exact isQueryBoundP_pure p _ d
  · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
    rcases sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · exact isQueryBoundP_pure p _ d
    · dsimp only []
      by_cases hc2 : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hc2, ↓reduceIte]; exact isQueryBoundP_pure p _ d
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        rw [← Nat.zero_add d]
        refine isQueryBoundP_bind (p := p) (simDrawSendCoins_isQueryBoundP hQu B_skip? r)
          fun ⟨rq, rc⟩ _ => ?_
        dsimp only [fig8IdSemHook]
        rw [pure_bind]
        set pn : BitVec 32 := if s₁.epoch Q ≠ sC.base.mir.epoch Q
          then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
        rcases hmk : CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn with
          _ | ⟨pq', pub⟩
        · exact isQueryBoundP_pure p _ d
        · dsimp only []
          rw [← Nat.add_zero d]
          cases chal with
          | none =>
            refine isQueryBoundP_bind (p := p) ?_ fun x _ => ?_
            · dsimp only [CryptoGames.SM.transmitQuery]
              rw [← Nat.add_zero d]
              exact isQueryBoundP_bind (p := p)
                ((isQueryBoundP_query_iff p _ d).2 (hSendQ pub rc ⟨rq, pn, pq', hmk⟩))
                fun r₀ _ => isQueryBoundP_pure p (r₀, ()) 0
            · rcases x with ⟨_ | c, _⟩ <;> exact isQueryBoundP_pure p _ 0
          | some m₁ =>
            refine isQueryBoundP_bind (p := p) ?_ fun x _ => ?_
            · dsimp only [CryptoGames.SM.challQuery]
              rw [← Nat.add_zero d]
              exact isQueryBoundP_bind (p := p)
                ((isQueryBoundP_query_iff p _ d).2 (hSendQ pub rc ⟨rq, pn, pq', hmk⟩))
                fun r₀ _ => isQueryBoundP_pure p (r₀, ()) 0
            · rcases x with ⟨_ | c, _⟩ <;> exact isQueryBoundP_pure p _ 0

private theorem semRecvHook_fig8_isQueryBoundP {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (B_skip? : Option ℕ) (qep B d : ℕ)
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p]
    (hDl : ∀ Q c, p (.inr (.inl (.inl (.inr (Q, c))))) → 0 < d)
    (hIj : ∀ Q c, p (.inr (.inl (.inr (Q, c)))) → 0 < d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool) :
    IsQueryBoundP
      (semRecvHook P Dh encPt encT decT lam
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) B_skip?) qep B sC () Q w isDel) p d := by
  have hDlQ : ∀ c, IsQueryBoundP
      ((fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) B_skip?).onDl Q c ()) p d := fun c => by
    dsimp only [fig8IdSemHook, CryptoGames.SM.deliverQuery]
    rw [← Nat.add_zero d]
    exact isQueryBoundP_bind (p := p) ((isQueryBoundP_query_iff p _ d).2 (hDl Q c)) fun res _ =>
      isQueryBoundP_pure p (res, ()) 0
  have hIjQ : ∀ c, IsQueryBoundP
      ((fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) B_skip?).onIj Q c ()) p d := fun c => by
    dsimp only [fig8IdSemHook, CryptoGames.SM.injectQuery]
    rw [← Nat.add_zero d]
    exact isQueryBoundP_bind (p := p) ((isQueryBoundP_query_iff p _ d).2 (hIj Q c)) fun res _ =>
      isQueryBoundP_pure p (res, ()) 0
  have hAns : ∀ sC' ci? Tpk pq' c', IsQueryBoundP
      (semFwdAnswerHook P Dh encPt encT lam
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) B_skip?) qep sC' () Q w isDel ci? Tpk pq' c')
      p d := fun sC' ci? Tpk pq' c' => by
    unfold semFwdAnswerHook
    dsimp only []
    rw [← Nat.add_zero d]
    refine isQueryBoundP_bind (p := p) ?_ fun ⟨res, _⟩ _ => isQueryBoundP_pure p _ 0
    split_ifs
    · exact hDlQ c'
    · exact hIjQ c'
  have hResync : ∀ sC' ci? Tpk pq' c r, IsQueryBoundP
      (semResyncHook P Dh encPt encT lam
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) B_skip?) qep sC' () Q w ci? Tpk pq' c r)
      p d := fun sC' ci? Tpk pq' c r => by
    unfold semResyncHook
    rcases r with _ | ⟨t, i, ⟨pub, m'⟩⟩
    · exact isQueryBoundP_pure p _ d
    · rw [← Nat.add_zero d]
      refine isQueryBoundP_bind (p := p) (hDlQ c) fun ⟨res, _⟩ _ => ?_
      rcases res with _ | (_ | _) <;> exact isQueryBoundP_pure p _ 0
  have hEvict : ∀ sC' Tpk pq' c', IsQueryBoundP
      (semFwdEvictHook P Dh encPt encT lam
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) B_skip?) qep sC' () Q w isDel Tpk pq' c')
      p d := fun sC' Tpk pq' c' => by
    unfold semFwdEvictHook
    split_ifs
    · dsimp only [fig8IdSemHook]; rw [pure_bind]; exact isQueryBoundP_pure p _ d
    · exact hAns sC' none Tpk pq' c'
  have hFwd : ∀ sC' ci? Tpk pq' hc c', IsQueryBoundP
      (semFwdHook P Dh encPt encT lam
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) B_skip?) qep B sC' () Q w isDel ci? Tpk pq' hc c')
      p d := fun sC' ci? Tpk pq' hc c' => by
    unfold semFwdHook
    rcases hc with _ | c
    · exact hAns sC' ci? Tpk pq' c'
    · dsimp only []
      split_ifs
      · rcases evalCKClamp P Dh encPt encT lam B sC' Q w c c' with _ | r
        · dsimp only [fig8IdSemHook]; rw [pure_bind]; exact isQueryBoundP_pure p _ d
        · exact hResync sC' ci? Tpk pq' c r
      · exact hAns sC' ci? Tpk pq' c'
  unfold semRecvHook
  dsimp only []
  cases href :
    (sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(CryptoGames.Ratchet.LibsignalInst.ratchetKeyAdmissible P.codec decT encT w))))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases CryptoGames.Ratchet.LibsignalSim.simParseRecvC P decT (2 ^ 32) (partyEnc Q)
        (sC.base.pq Q) w with _ | ⟨pq', i, pk, T?, lct⟩
    · exact isQueryBoundP_pure p _ d
    · rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · cases h1 :
          (((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) ==
            some true &&
          ((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.2.2.2 = lct.2.2)) ==
            some true)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases h2 : (T? == some 0)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases h3 : (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) ||
                decide (2 ^ 32 ≤ i))
            · simp only [Bool.false_eq_true, ↓reduceIte]
              rcases T? with _ | T
              · exact isQueryBoundP_pure p _ d
              · cases h4 :
                  (((Option.map (fun x => x.2)
                      (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                        sC.base.honest)).map fun c =>
                    decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact hFwd _ none pk pq' _ _
                · simp only [↓reduceIte]
                  exact hEvict _ pk pq' _
            · exact isQueryBoundP_pure p _ d
          · exact isQueryBoundP_pure p _ d
        · exact isQueryBoundP_pure p _ d
      · cases h5 :
          ((sC.base.chains Q).getD ci { key := none, epoch := 0, last := 0, skipped := [] }).rejects i
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact hFwd sC (some ci) pk pq' _ _
        · exact isQueryBoundP_pure p _ d
  · simp only [↓reduceIte]; exact isQueryBoundP_pure p _ d

private theorem semCorrHook_fig8_isQueryBoundP {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (B_skip? : Option ℕ) (d : ℕ)
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p]
    (hCr : ∀ Q, p (.inr (.inr Q)) → 0 < d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) :
    IsQueryBoundP
      (semCorrHook P Dh encT
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) B_skip?) sC () Q) p d := by
  unfold semCorrHook
  by_cases hc :
      (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
  · simp only [hc, ↓reduceIte]; exact isQueryBoundP_pure p _ d
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [← Nat.add_zero d]
    refine isQueryBoundP_bind (p := p) ?_ fun x _ => ?_
    · dsimp only [fig8IdSemHook, CryptoGames.SM.corrQuery]
      rw [← Nat.add_zero d]
      exact isQueryBoundP_bind (p := p) ((isQueryBoundP_query_iff p _ d).2 (hCr Q)) fun st? _ =>
        isQueryBoundP_pure p _ 0
    · rcases x with ⟨_ | _, _⟩ <;> exact isQueryBoundP_pure p _ 0

theorem simFig8Clamp_queries {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
    {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none) {q : ℕ}
    {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.MakesAtMostQueries
      (simFig8Clamp P ℓ Dh encPt encT decT lam qep B B_skip? A) q := by
  unfold CryptoGames.SM.MakesAtMostQueries simFig8Clamp
  refine isQueryBoundP_congr (p := QInr Pt ℓ) (by rintro (_ | _) <;> rfl) ?_
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind (p := QInr Pt ℓ)
    (liftProb_isQueryBoundP_zero hQu_QInr ($ᵗ BitVec 256)) fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simFig8Oracle P Dh encPt encT decT lam qep B B_skip?) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QInr Pt ℓ) q := by
    refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ _
    · rintro (n | o) hp sC
      · cases hp
      · dsimp only [simFig8Oracle, StateT.run]
        refine (isQueryBoundP_map_iff _ _ _).mpr ?_
        rcases o with ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
        · exact semSendHook_fig8_isQueryBoundP P Dh encPt encT lam B_skip? qep 1 hQu_QInr
            sC Q m none r (fun _ _ _ _ => Nat.zero_lt_one)
        · exact semSendHook_fig8_isQueryBoundP P Dh encPt encT lam B_skip? qep 1 hQu_QInr
            sC Q m₀ (some m₁) r (fun _ _ _ _ => Nat.zero_lt_one)
        · unfold semHandleHook
          dsimp only [fig8IdSemHook]
          rw [← Nat.add_zero 1]
          exact isQueryBoundP_bind (p := QInr Pt ℓ)
            (semRecvHook_fig8_isQueryBoundP P Dh encPt encT decT lam B_skip? qep B 1
              (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one) sC Q w true)
            fun ⟨rr, sC₁, _⟩ _ => by rw [pure_bind]; exact isQueryBoundP_pure (QInr Pt ℓ) _ 0
        · exact semRecvHook_fig8_isQueryBoundP P Dh encPt encT decT lam B_skip? qep B 1
            (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one) sC Q w false
        · exact semCorrHook_fig8_isQueryBoundP P Dh encT B_skip? 1 (fun _ _ => Nat.zero_lt_one) sC Q
    · rintro (n | o) hnp sC
      · dsimp only [simFig8Oracle, StateT.lift, StateT.run, StateT.mk]
        rw [← Nat.add_zero 0]
        exact isQueryBoundP_bind (p := QInr Pt ℓ)
          ((isQueryBoundP_query_iff (QInr Pt ℓ) (.inl n) 0).2 fun h => absurd h (hQu_QInr n))
          fun u _ => isQueryBoundP_pure (QInr Pt ℓ) (u, sC) 0
      · exact absurd rfl hnp
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

theorem simFig8Clamp_equalPub {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
    {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)
      (simFig8Clamp P ℓ Dh encPt encT decT lam qep B B_skip? A) := by
  unfold CryptoGames.SM.EqualPubChalls simFig8Clamp
  change IsQueryBoundP _ (QEq Pt ℓ) 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (p := QEq Pt ℓ)
    (liftProb_isQueryBoundP_zero hQu_QEq ($ᵗ BitVec 256)) fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simFig8Oracle P Dh encPt encT decT lam qep B B_skip?) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QEq Pt ℓ) 0 := by
    refine isQueryBoundP_simulateQ_run_zero A (fun t sC => ?_) _
    rcases t with (n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q))
    · dsimp only [simFig8Oracle, StateT.lift, StateT.run, StateT.mk]
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind (p := QEq Pt ℓ)
        ((isQueryBoundP_query_iff (QEq Pt ℓ) (.inl n) 0).2 fun h => absurd h (hQu_QEq n))
        fun u _ => isQueryBoundP_pure (QEq Pt ℓ) (u, sC) 0
    · dsimp only [simFig8Oracle, StateT.run]
      exact (isQueryBoundP_map_iff _ _ _).mpr
        (semSendHook_fig8_isQueryBoundP P Dh encPt encT lam B_skip? qep 0 hQu_QEq
          sC Q m none r (fun _ _ _ h => nomatch h))
    · dsimp only [simFig8Oracle, StateT.run]
      refine (isQueryBoundP_map_iff _ _ _).mpr
        (semSendHook_fig8_isQueryBoundP P Dh encPt encT lam B_skip? qep 0 hQu_QEq
          sC Q m₀ (some m₁) r (fun pub rc _ h => ?_))
      simp [QEq, CryptoGames.SM.unequalPubChall] at h
    · dsimp only [simFig8Oracle, StateT.run, semHandleHook, fig8IdSemHook]
      refine (isQueryBoundP_map_iff _ _ _).mpr ?_
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind (p := QEq Pt ℓ)
        (semRecvHook_fig8_isQueryBoundP P Dh encPt encT decT lam B_skip? qep B 0
          (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) sC Q w true)
        fun ⟨rr, sC₁, _⟩ _ => by rw [pure_bind]; exact isQueryBoundP_pure (QEq Pt ℓ) _ 0
    · dsimp only [simFig8Oracle, StateT.run]
      exact (isQueryBoundP_map_iff _ _ _).mpr
        (semRecvHook_fig8_isQueryBoundP P Dh encPt encT decT lam B_skip? qep B 0
          (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) sC Q w false)
    · dsimp only [simFig8Oracle, StateT.run]
      exact (isQueryBoundP_map_iff _ _ _).mpr
        (semCorrHook_fig8_isQueryBoundP P Dh encT B_skip? 0 (fun _ h => nomatch h) sC Q)
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

theorem simFig8Clamp_sendShort {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
      (simFig8Clamp P ℓ Dh encPt encT decT lam qep B B_skip? A) := by
  unfold SendMsgsOk simFig8Clamp
  change IsQueryBoundP _ (QShort Pt ℓ) 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (p := QShort Pt ℓ)
    (liftProb_isQueryBoundP_zero hQu_QShort ($ᵗ BitVec 256)) fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simFig8Oracle P Dh encPt encT decT lam qep B B_skip?) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QShort Pt ℓ) 0 := by
    refine isQueryBoundP_simulateQ_run_zero A (fun t sC => ?_) _
    rcases t with (n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q))
    · dsimp only [simFig8Oracle, StateT.lift, StateT.run, StateT.mk]
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind (p := QShort Pt ℓ)
        ((isQueryBoundP_query_iff (QShort Pt ℓ) (.inl n) 0).2 fun h => absurd h (hQu_QShort n))
        fun u _ => isQueryBoundP_pure (QShort Pt ℓ) (u, sC) 0
    · dsimp only [simFig8Oracle, StateT.run]
      refine (isQueryBoundP_map_iff _ _ _).mpr
        (semSendHook_fig8_isQueryBoundP P Dh encPt encT lam B_skip? qep 0 hQu_QShort
          sC Q m none r (fun pub rc ⟨rq, pn, pq', hmk⟩ h => ?_))
      have hpub := shortB_mkPub hL sC.base Q rq pn hmk
      simp [QShort, badSendMsg, hpub] at h
    · dsimp only [simFig8Oracle, StateT.run]
      refine (isQueryBoundP_map_iff _ _ _).mpr
        (semSendHook_fig8_isQueryBoundP P Dh encPt encT lam B_skip? qep 0 hQu_QShort
          sC Q m₀ (some m₁) r (fun pub rc ⟨rq, pn, pq', hmk⟩ h => ?_))
      have hpub := shortB_mkPub hL sC.base Q rq pn hmk
      simp [QShort, badSendMsg, hpub] at h
    · dsimp only [simFig8Oracle, StateT.run, semHandleHook, fig8IdSemHook]
      refine (isQueryBoundP_map_iff _ _ _).mpr ?_
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind (p := QShort Pt ℓ)
        (semRecvHook_fig8_isQueryBoundP P Dh encPt encT decT lam B_skip? qep B 0
          (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) sC Q w true)
        fun ⟨rr, sC₁, _⟩ _ => by rw [pure_bind]; exact isQueryBoundP_pure (QShort Pt ℓ) _ 0
    · dsimp only [simFig8Oracle, StateT.run]
      exact (isQueryBoundP_map_iff _ _ _).mpr
        (semRecvHook_fig8_isQueryBoundP P Dh encPt encT decT lam B_skip? qep B 0
          (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) sC Q w false)
    · dsimp only [simFig8Oracle, StateT.run]
      exact (isQueryBoundP_map_iff _ _ _).mpr
        (semCorrHook_fig8_isQueryBoundP P Dh encT B_skip? 0 (fun _ h => nomatch h) sC Q)
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

end QueryInvariants

/-! ## `toGhost` truncation variant -/

section ClampingAndHeadline

open CryptoGames.Ratchet.LibsignalSim (SimState evalCKClamp_eq_evalCK SimBaseClampInv)
open CryptoGames.LibsignalSM.Proofs.QueryBounds
  (FSpec QInr QEq hQu_QInr hQu_QEq isQueryBoundP_congr isQueryBoundP_simulateQ_run_zero)
open CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM
  (QShort hQu_QShort SendMsgsOk badSendMsg shortB_mkPub)

theorem fig8StTruncSk_eq_self {Pt : Type} (B_skip : ℕ) (st : Fig8St Pt)
    (h : ∀ t v, st.vR t = some v → v.skippedKeys.length ≤ B_skip) :
    fig8StTruncSk B_skip st = st := by
  cases st with
  | mk id₀ root vS vR γ curCkaMsg tcur =>
    simp only [fig8StTruncSk, CryptoGames.SM.Construction.PartyState.mk.injEq, true_and, and_true]
    funext t
    rcases hv : vR t with _ | v
    · rfl
    · simp only [Option.map, Option.some.injEq]
      cases v with
      | mk ck li sk =>
        simp only [CryptoGames.FSAEAD.RatchetReceiverState.mk.injEq, true_and]
        exact List.take_of_length_le (h t ⟨ck, li, sk⟩ hv)

theorem fig8StTruncSkOpt_eq_self {Pt : Type} (B_skip? : Option ℕ) (st : Fig8St Pt)
    (h : ∀ B_skip, B_skip? = some B_skip →
      ∀ t v, st.vR t = some v → v.skippedKeys.length ≤ B_skip) :
    fig8StTruncSkOpt B_skip? st = st := by
  cases B_skip? with
  | none => rfl
  | some B_skip => exact fig8StTruncSk_eq_self B_skip st (h B_skip rfl)

/-- Semantic corruption hook matching `SimFig8State.toGhostE` + `keptUpdateCorrE` directly:
`toGhost` receives `fig8StTruncSkOpt B_skip? fig8st` while `Kept.ofSt` keeps `fig8st` untruncated. -/
def semCorrHookTG {PQ PQC Pt : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (B_skip? : Option ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) :
    Fig8Comp Pt ℓ (Option (GhostState PQ) × LibsignalToModularSchemeSimState PQ Pt ℓ) := do
  if sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
     inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) then
    return (none, sC)
  else
    let res ← CryptoGames.SM.corrQuery
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
      (C := Fig8C Pt) Q
    match res with
    | none => return (none, sC)
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
      let ghostOut := CryptoGames.Ratchet.LibsignalSim.toGhost P
        { sC.base with chains := chains' } Q (fig8StTruncSkOpt B_skip? fig8st)
      let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        { base := base'
          kept := Function.update sC.kept Q (Kept.ofSt fig8st)
          sent := sC.sent
          snaps := (Q, sC.base.mir.epoch Q, ghostOut) :: sC.snaps }
      return (some ghostOut, sC')

def semCorrHookTGDedup {PQ PQC Pt : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (B_skip? : Option ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) :
    Fig8Comp Pt ℓ (Option (GhostState PQ) × LibsignalToModularSchemeSimState PQ Pt ℓ) := do
  if sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
     inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) then
    return (none, sC)
  else
    let res ← CryptoGames.SM.corrQuery
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
      (C := Fig8C Pt) Q
    match res with
    | none => return (none, sC)
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
      let ghostOut := CryptoGames.Ratchet.LibsignalSim.toGhost P
        { sC.base with chains := chains' } Q (fig8StTruncSkOpt B_skip? fig8st)
      let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        { base := base'
          kept := Function.update sC.kept Q (Kept.ofSt fig8st)
          sent := sC.sent
          snaps := (Q, sC.base.mir.epoch Q, ghostOut) :: sC.snaps }
      return (some ghostOut, sC')

def simFig8OracleTG {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ))
  | .inl n => StateT.lift
    (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n))
  | .inr (.inr Q) => StateT.mk fun sC => semCorrHookTG P Dh encT B_skip? sC Q
  | .inr t => StateT.mk fun sC =>
    Prod.map id Prod.fst <$>
      semHandleHook P Dh encPt encT decT lam (fig8IdSemHook (PQC := PQC) none) qep B t sC ()

def simFig8OracleTGDedup {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ))
  | .inl n => StateT.lift
    (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n))
  | .inr (.inr Q) => StateT.mk fun sC => semCorrHookTGDedup P Dh encT B_skip? sC Q
  | .inr t => StateT.mk fun sC =>
    Prod.map id Prod.fst <$>
      semHandleHookDedup P Dh encPt encT decT lam (fig8IdSemHook (PQC := PQC) none) qep B t sC ()

/-- `B`-clamped semantic counterpart of `Refine.libsignalToModularSchemeSim` using `simFig8OracleTG`. -/
def simFig8ClampTG {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    CryptoGames.SM.Adversary (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt) :=
  show Fig8Comp Pt ℓ Bool from do
    let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
    let sC₀ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    (simulateQ (simFig8OracleTG P Dh encPt encT decT lam qep B B_skip?) A).run' sC₀

private theorem semCorrHookTGDedup_simStateCCanon {PQ PQC Pt : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (B_skip? : Option ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) :
    Prod.map id simStateCCanon <$> semCorrHookTGDedup P Dh encT B_skip? sC Q =
      Prod.map id simStateCCanon <$> semCorrHookTG P Dh encT B_skip? (simStateCCanon sC) Q := by
  unfold semCorrHookTGDedup semCorrHookTG
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
    refine bind_congr fun res => ?_
    rcases res with _ | fig8st
    · simp [Prod.map, simStateCCanon_idem]
    · simp only [map_pure, Prod.map, id_eq,
        show (simStateCCanon sC).base.mir.epoch = sC.base.mir.epoch from rfl,
        show (simStateCCanon sC).base.chains = sC.base.chains from rfl,
        show (simStateCCanon sC).kept = sC.kept from rfl,
        show (simStateCCanon sC).sent = sC.sent from rfl,
        show (simStateCCanon sC).snaps = sC.snaps from rfl]
      have htg : ∀ cs st₀, CryptoGames.Ratchet.LibsignalSim.toGhost (P := P)
          { (simStateCCanon sC).base with chains := cs } Q st₀ =
          CryptoGames.Ratchet.LibsignalSim.toGhost (P := P)
            { sC.base with chains := cs } Q st₀ := fun _ _ => rfl
      simp only [htg]
      congr 1
      refine Prod.ext rfl ?_
      simp only [simStateCCanon, simStateCanon]
      congr 2
      exact canonComp_afterCorrDedup sC.base.mir Q

private theorem semCorrHookTG_simStateCCanon {PQ PQC Pt : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (B_skip? : Option ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) :
    Prod.map id simStateCCanon <$> semCorrHookTG P Dh encT B_skip? sC Q =
      Prod.map id simStateCCanon <$> semCorrHookTG P Dh encT B_skip? (simStateCCanon sC) Q := by
  unfold semCorrHookTG
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
    refine bind_congr fun res => ?_
    rcases res with _ | fig8st
    · simp [Prod.map, simStateCCanon_idem]
    · simp only [map_pure, Prod.map, id_eq,
        show (simStateCCanon sC).base.mir.epoch = sC.base.mir.epoch from rfl,
        show (simStateCCanon sC).base.chains = sC.base.chains from rfl,
        show (simStateCCanon sC).kept = sC.kept from rfl,
        show (simStateCCanon sC).sent = sC.sent from rfl,
        show (simStateCCanon sC).snaps = sC.snaps from rfl]
      have htg : ∀ cs st₀, CryptoGames.Ratchet.LibsignalSim.toGhost (P := P)
          { (simStateCCanon sC).base with chains := cs } Q st₀ =
          CryptoGames.Ratchet.LibsignalSim.toGhost (P := P)
            { sC.base with chains := cs } Q st₀ := fun _ _ => rfl
      simp only [htg]
      congr 1
      refine Prod.ext rfl ?_
      simp only [simStateCCanon, simStateCanon]
      congr 2
      exact canonComp_afterCorr sC.base.mir Q

theorem run'_simulateQ_simFig8OracleTGDedup_eq {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (simulateQ (simFig8OracleTGDedup P Dh encPt encT decT lam qep B B_skip?) A).run' sC =
      (simulateQ (simFig8OracleTG P Dh encPt encT decT lam qep B B_skip?) A).run' sC := by
  have hcomm : ∀ {t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain}
      (oa : OracleComp
        (unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) (Fig8C Pt))
        ((CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Range t ×
          (LibsignalToModularSchemeSimState PQ Pt ℓ × Unit))),
      Prod.map id simStateCCanon <$> (Prod.map id Prod.fst <$> oa) =
        Prod.map id Prod.fst <$> (Prod.map id (Prod.map simStateCCanon id) <$> oa) := by
    intro _ oa; simp [Functor.map_map, Prod.map]
  refine run'_simulateQ_eq_of_idem_proj
    (simFig8OracleTGDedup P Dh encPt encT decT lam qep B B_skip?)
    (simFig8OracleTG P Dh encPt encT decT lam qep B B_skip?)
    simStateCCanon ?_ ?_ A rfl
  · rintro (n | (t₀ | Q)) sC₀
    · simp [simFig8OracleTGDedup, simFig8OracleTG, StateT.run_lift, Prod.map, simStateCCanon_idem]
    · dsimp only [simFig8OracleTGDedup, simFig8OracleTG, StateT.run, StateT.mk]
      exact (hcomm _).trans ((congrArg (Functor.map (Prod.map id Prod.fst))
        (semHandleHookDedup_simStateCCanon' P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := PQC) none) qep B (.inl t₀) sC₀ ())).trans (hcomm _).symm)
    · exact semCorrHookTGDedup_simStateCCanon P Dh encT B_skip? sC₀ Q
  · rintro (n | (t₀ | Q)) sC₀
    · simp [simFig8OracleTG, StateT.run_lift, Prod.map, simStateCCanon_idem]
    · dsimp only [simFig8OracleTG, StateT.run, StateT.mk]
      exact (hcomm _).trans ((congrArg (Functor.map (Prod.map id Prod.fst))
        (semHandleHook_simStateCCanon' P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := PQC) none) qep B (.inl t₀) sC₀ ())).trans (hcomm _).symm)
    · exact semCorrHookTG_simStateCCanon P Dh encT B_skip? sC₀ Q

private theorem semCorrHookTGDedup_preserves_sC_inv {PQ PQC Pt : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (B_skip? : Option ℕ) (L m : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party)
    (hInv : SimCStateInv L (m + 1) sC₀) :
    ∀ x ∈ support (semCorrHookTGDedup P Dh encT B_skip? sC₀ Q),
      SimCStateInv L m x.2 := by
  have hInv0 : SimCStateInv L m sC₀ := hInv.mono (Nat.le_succ m)
  rintro ⟨_, sC₁⟩ hx
  unfold semCorrHookTGDedup at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win || !(sC₀.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC₀.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
    obtain ⟨res, hcr, hx⟩ := hx
    rcases res with _ | fig8st <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl⟩; exact hInv0
    · rcases hx with ⟨_, rfl⟩
      let ch1 : Party → List GhostChain :=
        if Q == Party.B && sC₀.base.mir.epoch Party.B == 0 then
          match fig8st.γ with
          | .exp x => Function.update sC₀.base.chains Party.A
              ((sC₀.base.chains Party.A).map fun g =>
                if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => sC₀.base.chains
        else sC₀.base.chains
      let gs0 := CryptoGames.Ratchet.LibsignalSim.toGhost P { sC₀.base with chains := ch1 } Q fig8st
      have hmem0 :
          (some gs0,
            ({ base := { sC₀.base with mir := afterCorrDedup sC₀.base.mir Q, chains := ch1 }
               kept := Function.update sC₀.kept Q (Kept.ofSt fig8st)
               sent := sC₀.sent
               snaps := (Q, sC₀.base.mir.epoch Q, gs0) :: sC₀.snaps }, ())) ∈
          support (semCorrHookDedup P Dh encT (fig8IdSemHook (PQC := PQC) none) sC₀ () Q) := by
        unfold semCorrHookDedup
        simp only [href, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff]
        refine ⟨(some fig8st, ()), ?_, by rw [support_pure, Set.mem_singleton_iff]; rfl⟩
        dsimp only [fig8IdSemHook]
        rw [mem_support_bind_iff]
        exact ⟨some fig8st, hcr, by simp⟩
      have h0 := CryptoGames.Ratchet.LibsignalSim.semCorrHookDedup_preserves_sC_inv P Dh encT
        (fig8IdSemHook (PQC := PQC) none) L m sC₀ () Q hInv _ hmem0
      exact ⟨h0.1, h0.2.1, by simp only [List.length_cons]; have := hInv.2.2; omega⟩

/-- Game-loop `.eval` theorem for `simFig8ProgOfStep` against `simFig8ClampTG`. -/
theorem simFig8ProgOfStep_eval_tg {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (L qep B : ℕ) (B_skip? : Option ℕ := none) (hℓ : ℓ < 10 ^ 6)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep : ∀ t (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded L (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simFig8OracleTGDedup (paramsV1 C K idA idB) Dh encPt encT decT lam qep B B_skip?
        (.inr t)).run (simFullDec s_raw)))
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q) (hqL : q ≤ L) :
    (simFig8ProgOfStep C K Dh encPt encT decT lam step).eval (fun _ => A) () =
      simFig8ClampTG (paramsV1 C K idA idB) ℓ Dh encPt encT decT lam qep B B_skip? A := by
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  let P := paramsV1 C K idA idB
  unfold simFig8ProgOfStep
  simp only [hℓ, ↓reduceDIte]
  set prog : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool .bool :=
    { σ := simFullT ℓ Pt
      init := simFig8InitC C K Dh encPt encT decT lam
      handle := step
      finish := simFig8FinishC C K Dh encPt encT decT lam }
  have hinit_eval :
      (Prod.map id (simFullDec (ℓ := ℓ) (Pt := Pt)) <$> prog.init.eval (.cons () .nil)) =
      (do
        let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
        return ((), initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) := by
    dsimp only [prog]
    rw [simFig8InitC_eval, Functor.map_map]
    unfold simFig8InitImpl
    rw [map_bind]
    refine bind_congr fun pqrKey => ?_
    rw [map_pure]
    simp only [Prod.map, id_eq, simFullDec_simFullEnc]
    rfl
  have hinit_inv :
      ∀ r ∈ support (prog.init.eval (.cons () .nil)),
        SimCStateInv L q (simFullDec (ℓ := ℓ) (Pt := Pt) r.2) := by
    rintro ⟨u₀, s_raw⟩ hr
    dsimp only [prog] at hr
    rw [simFig8InitC_eval, support_map, Set.mem_image] at hr
    obtain ⟨⟨_, sC₀⟩, hs, hEq₀⟩ := hr
    dsimp only [Prod.map, id_eq] at hEq₀
    injection hEq₀ with _ hs_raw
    rw [← hs_raw, simFullDec_simFullEnc]
    unfold simFig8InitImpl at hs
    rw [mem_support_bind_iff] at hs
    obtain ⟨pqrKey, -, hs⟩ := hs
    rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hs
    rcases hs with ⟨_, rfl⟩
    exact simCStateInv_initSimC hqL _ _
  have habs := prog.eval_eq_simulateQ_of_abs
    (simFullDec (ℓ := ℓ) (Pt := Pt))
    (fun m s_raw => SimCStateInv L m (simFullDec (ℓ := ℓ) (Pt := Pt) s_raw))
    (fun _ => do
      let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
      return ((), initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)))
    (simFig8OracleTGDedup P Dh encPt encT decT lam qep B B_skip?)
    (fun _ b => pure b)
    q ()
    hinit_eval
    hinit_inv
    (fun _ _ => rfl)
    (fun m t s_raw hInv => by
      have heq := hstep t s_raw hInv.toBounded
      refine ⟨heq, ?_⟩
      rintro ⟨rr, s_raw'⟩ hmem
      have hmem' : (rr, simFullDec s_raw') ∈
          support ((simFig8OracleTGDedup P Dh encPt encT decT lam qep B B_skip? (.inr t)).run
            (simFullDec s_raw)) := by
        rw [← heq, support_map, Set.mem_image]
        exact ⟨(rr, s_raw'), hmem, rfl⟩
      rcases t with t₀ | Q
      · dsimp only [simFig8OracleTGDedup, StateT.run, StateT.mk] at hmem'
        rw [support_map, Set.mem_image] at hmem'
        obtain ⟨⟨rr₀, sC', u'⟩, hsem, hEq⟩ := hmem'
        dsimp only [Prod.map, id_eq] at hEq
        injection hEq with _ hsC'
        rw [← hsC']
        exact semHandleHookDedup_preserves_sC_inv P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := BitVec 512) none) L m qep B (.inl t₀) (simFullDec s_raw) () hInv
          (rr₀, sC', u') hsem
      · exact semCorrHookTGDedup_preserves_sC_inv (PQC := BitVec 512) P Dh encT B_skip? L m
          (simFullDec s_raw) Q hInv (rr, simFullDec s_raw') hmem')
    (fun _ _ _ => rfl)
    (fun _ hle hInv => hInv.mono hle)
    (fun _ => A)
    (fun _ => hq')
  rw [habs]
  dsimp only [simFig8ClampTG, P]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  rw [← run'_simulateQ_simFig8OracleTGDedup_eq (paramsV1 C K idA idB) Dh encPt encT decT lam
    qep B B_skip? A, StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def]

private theorem semCorrHookTG_isQueryBoundP {PQ PQC Pt : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (B_skip? : Option ℕ) (d : ℕ)
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p]
    (hCr : ∀ Q, p (.inr (.inr Q)) → 0 < d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) :
    IsQueryBoundP (semCorrHookTG P Dh encT B_skip? sC Q) p d := by
  unfold semCorrHookTG
  by_cases hc :
      (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
  · simp only [hc, ↓reduceIte]; exact isQueryBoundP_pure p _ d
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [← Nat.add_zero d]
    refine isQueryBoundP_bind (p := p)
      ((isQueryBoundP_query_iff p (.inr (.inr Q)) d).2 (hCr Q)) fun res _ => ?_
    rcases res with _ | _ <;> exact isQueryBoundP_pure p _ 0

theorem simFig8ClampTG_queries {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
    {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none) {q : ℕ}
    {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.MakesAtMostQueries
      (simFig8ClampTG P ℓ Dh encPt encT decT lam qep B B_skip? A) q := by
  unfold CryptoGames.SM.MakesAtMostQueries simFig8ClampTG
  refine isQueryBoundP_congr (p := QInr Pt ℓ) (by rintro (_ | _) <;> rfl) ?_
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind (p := QInr Pt ℓ)
    (liftProb_isQueryBoundP_zero hQu_QInr ($ᵗ BitVec 256)) fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simFig8OracleTG P Dh encPt encT decT lam qep B B_skip?) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QInr Pt ℓ) q := by
    refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ _
    · rintro (n | o) hp sC
      · cases hp
      · rcases o with ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
        · dsimp only [simFig8OracleTG, StateT.run]
          exact (isQueryBoundP_map_iff _ _ _).mpr
            (semSendHook_fig8_isQueryBoundP P Dh encPt encT lam none qep 1 hQu_QInr
              sC Q m none r (fun _ _ _ _ => Nat.zero_lt_one))
        · dsimp only [simFig8OracleTG, StateT.run]
          exact (isQueryBoundP_map_iff _ _ _).mpr
            (semSendHook_fig8_isQueryBoundP P Dh encPt encT lam none qep 1 hQu_QInr
              sC Q m₀ (some m₁) r (fun _ _ _ _ => Nat.zero_lt_one))
        · dsimp only [simFig8OracleTG, StateT.run, semHandleHook, fig8IdSemHook]
          refine (isQueryBoundP_map_iff _ _ _).mpr ?_
          rw [← Nat.add_zero 1]
          exact isQueryBoundP_bind (p := QInr Pt ℓ)
            (semRecvHook_fig8_isQueryBoundP P Dh encPt encT decT lam none qep B 1
              (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one) sC Q w true)
            fun ⟨rr, sC₁, _⟩ _ => by rw [pure_bind]; exact isQueryBoundP_pure (QInr Pt ℓ) _ 0
        · dsimp only [simFig8OracleTG, StateT.run]
          exact (isQueryBoundP_map_iff _ _ _).mpr
            (semRecvHook_fig8_isQueryBoundP P Dh encPt encT decT lam none qep B 1
              (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one) sC Q w false)
        · exact semCorrHookTG_isQueryBoundP P Dh encT B_skip? 1 (fun _ _ => Nat.zero_lt_one) sC Q
    · rintro (n | o) hnp sC
      · dsimp only [simFig8OracleTG, StateT.lift, StateT.run, StateT.mk]
        rw [← Nat.add_zero 0]
        exact isQueryBoundP_bind (p := QInr Pt ℓ)
          ((isQueryBoundP_query_iff (QInr Pt ℓ) (.inl n) 0).2 fun h => absurd h (hQu_QInr n))
          fun u _ => isQueryBoundP_pure (QInr Pt ℓ) (u, sC) 0
      · exact absurd rfl hnp
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

theorem simFig8ClampTG_equalPub {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
    {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)
      (simFig8ClampTG P ℓ Dh encPt encT decT lam qep B B_skip? A) := by
  unfold CryptoGames.SM.EqualPubChalls simFig8ClampTG
  change IsQueryBoundP _ (QEq Pt ℓ) 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (p := QEq Pt ℓ)
    (liftProb_isQueryBoundP_zero hQu_QEq ($ᵗ BitVec 256)) fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simFig8OracleTG P Dh encPt encT decT lam qep B B_skip?) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QEq Pt ℓ) 0 := by
    refine isQueryBoundP_simulateQ_run_zero A (fun t sC => ?_) _
    rcases t with (n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q))
    · dsimp only [simFig8OracleTG, StateT.lift, StateT.run, StateT.mk]
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind (p := QEq Pt ℓ)
        ((isQueryBoundP_query_iff (QEq Pt ℓ) (.inl n) 0).2 fun h => absurd h (hQu_QEq n))
        fun u _ => isQueryBoundP_pure (QEq Pt ℓ) (u, sC) 0
    · dsimp only [simFig8OracleTG, StateT.run]
      exact (isQueryBoundP_map_iff _ _ _).mpr
        (semSendHook_fig8_isQueryBoundP P Dh encPt encT lam none qep 0 hQu_QEq
          sC Q m none r (fun _ _ _ h => nomatch h))
    · dsimp only [simFig8OracleTG, StateT.run]
      refine (isQueryBoundP_map_iff _ _ _).mpr
        (semSendHook_fig8_isQueryBoundP P Dh encPt encT lam none qep 0 hQu_QEq
          sC Q m₀ (some m₁) r (fun pub rc _ h => ?_))
      simp [QEq, CryptoGames.SM.unequalPubChall] at h
    · dsimp only [simFig8OracleTG, StateT.run, semHandleHook, fig8IdSemHook]
      refine (isQueryBoundP_map_iff _ _ _).mpr ?_
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind (p := QEq Pt ℓ)
        (semRecvHook_fig8_isQueryBoundP P Dh encPt encT decT lam none qep B 0
          (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) sC Q w true)
        fun ⟨rr, sC₁, _⟩ _ => by rw [pure_bind]; exact isQueryBoundP_pure (QEq Pt ℓ) _ 0
    · dsimp only [simFig8OracleTG, StateT.run]
      exact (isQueryBoundP_map_iff _ _ _).mpr
        (semRecvHook_fig8_isQueryBoundP P Dh encPt encT decT lam none qep B 0
          (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) sC Q w false)
    · exact semCorrHookTG_isQueryBoundP P Dh encT B_skip? 0 (fun _ h => nomatch h) sC Q
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

theorem simFig8ClampTG_sendShort {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
      (simFig8ClampTG P ℓ Dh encPt encT decT lam qep B B_skip? A) := by
  unfold SendMsgsOk simFig8ClampTG
  change IsQueryBoundP _ (QShort Pt ℓ) 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (p := QShort Pt ℓ)
    (liftProb_isQueryBoundP_zero hQu_QShort ($ᵗ BitVec 256)) fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simFig8OracleTG P Dh encPt encT decT lam qep B B_skip?) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QShort Pt ℓ) 0 := by
    refine isQueryBoundP_simulateQ_run_zero A (fun t sC => ?_) _
    rcases t with (n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q))
    · dsimp only [simFig8OracleTG, StateT.lift, StateT.run, StateT.mk]
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind (p := QShort Pt ℓ)
        ((isQueryBoundP_query_iff (QShort Pt ℓ) (.inl n) 0).2 fun h => absurd h (hQu_QShort n))
        fun u _ => isQueryBoundP_pure (QShort Pt ℓ) (u, sC) 0
    · dsimp only [simFig8OracleTG, StateT.run]
      refine (isQueryBoundP_map_iff _ _ _).mpr
        (semSendHook_fig8_isQueryBoundP P Dh encPt encT lam none qep 0 hQu_QShort
          sC Q m none r (fun pub rc ⟨rq, pn, pq', hmk⟩ h => ?_))
      have hpub := shortB_mkPub hL sC.base Q rq pn hmk
      simp [QShort, badSendMsg, hpub] at h
    · dsimp only [simFig8OracleTG, StateT.run]
      refine (isQueryBoundP_map_iff _ _ _).mpr
        (semSendHook_fig8_isQueryBoundP P Dh encPt encT lam none qep 0 hQu_QShort
          sC Q m₀ (some m₁) r (fun pub rc ⟨rq, pn, pq', hmk⟩ h => ?_))
      have hpub := shortB_mkPub hL sC.base Q rq pn hmk
      simp [QShort, badSendMsg, hpub] at h
    · dsimp only [simFig8OracleTG, StateT.run, semHandleHook, fig8IdSemHook]
      refine (isQueryBoundP_map_iff _ _ _).mpr ?_
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind (p := QShort Pt ℓ)
        (semRecvHook_fig8_isQueryBoundP P Dh encPt encT decT lam none qep B 0
          (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) sC Q w true)
        fun ⟨rr, sC₁, _⟩ _ => by rw [pure_bind]; exact isQueryBoundP_pure (QShort Pt ℓ) _ 0
    · dsimp only [simFig8OracleTG, StateT.run]
      exact (isQueryBoundP_map_iff _ _ _).mpr
        (semRecvHook_fig8_isQueryBoundP P Dh encPt encT decT lam none qep B 0
          (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) sC Q w false)
    · exact semCorrHookTG_isQueryBoundP P Dh encT B_skip? 0 (fun _ h => nomatch h) sC Q
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

/-! ## Clamping equivalence -/

section IdHookAndGameEquiv

open CryptoGames (AEADScheme SMScheme)
open CryptoGames.SM (partyDec_partyEnc)
open CryptoGames.LibsignalSession (SignalMessageProtoCodec SignalMessage signalWireCodec)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim
  (simSend semDrawSendCoins liftQ putS mkPub fwd onAnswer onAccept
   fwd_run_eq onAnswer_run_eq_pure onAccept_run_eq_pure
   simParseRecvC simParseRecvC_bounds pushChain fig8Clamp fsClampSim simKDecryptFig8)
open CryptoGames.Ratchet.LibsignalSimC
  (idHook runOnBaseState liftC simSendC fwdAnswerC resyncC fwdC fwdEvictC simRecvC simCorrC
   guardC simImplC simRunCWith runLibsignalToModularSchemeSim predictReceiveWithSnapshots
   predictReceive sentEval decryptWithKnownSeed)

@[simp] private theorem monadLift_prob_run {σ : Type} {M : Type → Type} [Monad M] {α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

private def runIdM {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    Fig8Comp Pt ℓ (α × (LibsignalToModularSchemeSimState PQ Pt ℓ × Unit)) := do
  let (a, sC') ← x.run sC
  return (a, (sC', ()))

@[simp] private theorem runIdM_pure {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    (a : α) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    runIdM (pure a) sC = pure (a, (sC, ())) := rfl

private theorem runIdM_guardC_neg {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (h : ¬ sC.base.stopped = true) :
    runIdM (guardC x) sC = runIdM x sC := by
  unfold runIdM guardC; simp [h]

private theorem runIdM_get_bind {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ →
      StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    runIdM (get >>= f) sC = runIdM (f sC) sC := rfl

private theorem runIdM_ite_modify {PQ Pt : Type} {ℓ : ℕ} {α : Type} (c : Bool)
    (k : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    runIdM (if c then
        (modify (fun sC : LibsignalToModularSchemeSimState PQ Pt ℓ =>
          { sC with base := { sC.base with amb := sC.base.amb + 1 } }) >>= fun _ => k)
      else k) sC =
      runIdM k { sC with base := if c then { sC.base with amb := sC.base.amb + 1 } else sC.base } := by
  cases c <;> rfl

@[simp] private theorem stateT_lift_run_id {σ : Type} {M : Type → Type} [Monad M] {α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp] private theorem runOnBaseState_idHook_run {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (runOnBaseState (H := idHook) x).run sC =
      (x.run sC.base >>= fun (a, s') => pure (a, { sC with base := s' })) := rfl

@[simp] private theorem liftC_idHook_run {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    (x : Fig8Comp Pt ℓ α) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (liftC (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (H := idHook) x).run sC =
      (x >>= fun a => pure (a, sC)) := rfl

private theorem semSendHook_idHook_eq {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    semSendHook P Dh encPt encT lam (fig8IdSemHook (PQC := PQC) none) qep sC () Q m₀ chal r =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      runIdM (guardC (simSendC (P := P) (qep := qep) (fig := fig) (H := idHook) Q m₀ chal r)) sC := by
  dsimp only []
  by_cases hstop : sC.base.stopped = true
  · unfold semSendHook runIdM guardC; simp [hstop]
  · rw [runIdM_guardC_neg _ sC hstop]
    unfold semSendHook runIdM simSendC simSend semDrawSendCoins
      CryptoGames.Ratchet.LibsignalSim.coin liftQ scPostSendPure putS
    simp only [hstop, Bool.false_or, StateT.run_bind, StateT.run_get,
      runOnBaseState_idHook_run, pure_bind, bind_assoc]
    by_cases href : (sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) = true
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte]
      rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
      · simp
      · dsimp only []
        by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
        · simp [hch]
        · simp only [hch, Bool.false_eq_true, ↓reduceIte]
          have hsc : (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none).onSendCoins =
              fun _ _ _ => pure ((), ()) := rfl
          have hbv : (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none).sampleBv256 =
              liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) := rfl
          have hpqc : (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none).samplePqc =
              liftM ($ᵗ PQC : ProbComp PQC) := rfl
          rw [hsc, hbv, hpqc]
          rcases r with _ | rq
          · simp only [StateT.run_bind, stateT_lift_run_id, pure_bind, bind_assoc]
            refine bind_congr fun x => ?_
            rcases hpub : mkPub (P := P) sC.base Q x
              (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
               else sC.base.pn Q) with _ | ⟨pq', pub⟩
            · simp
            · dsimp only []
              cases chal <;> simp only [StateT.run_bind, stateT_lift_run_id, fig8IdSemHook,
                pure_bind, bind_assoc]
              all_goals
                refine bind_congr fun res => ?_
                rcases res with _ | c
                · simp
                · rcases hkept : (sC.kept Q).full with _ | st
                  · simp [hkept]
                  · simp [hkept]; rfl
          · simp only [bind_map_left, StateT.run_bind, stateT_lift_run_id, pure_bind, bind_assoc]
            refine bind_congr fun x => ?_
            rcases hpub : mkPub (P := P) sC.base Q rq
              (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
               else sC.base.pn Q) with _ | ⟨pq', pub⟩
            · simp
            · dsimp only []
              cases chal <;> simp only [StateT.run_bind, stateT_lift_run_id, fig8IdSemHook,
                pure_bind, bind_assoc]
              all_goals
                refine bind_congr fun res => ?_
                rcases res with _ | c
                · simp
                · rcases hkept : (sC.kept Q).full with _ | st
                  · simp [hkept]
                  · simp [hkept]; rfl

private theorem semCorrHook_idHook_eq {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) :
    semCorrHook P Dh encT (fig8IdSemHook (PQC := PQC) none) sC () Q =
      runIdM (guardC (simCorrC (P := P) (encT := encT) (H := idHook) Dh Q)) sC := by
  by_cases hstop : sC.base.stopped = true
  · unfold semCorrHook runIdM guardC; simp [hstop]
  · rw [runIdM_guardC_neg _ sC hstop]
    unfold semCorrHook simCorrC
    rw [runIdM_get_bind]
    have hcond : (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
        inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) =
      (sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
        inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) := by
      simp [hstop]
    rw [hcond]
    by_cases href : (sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
        inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
    · simp [href, runIdM_pure]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, runIdM, fig8IdSemHook,
        StateT.run_bind, liftC_idHook_run, pure_bind, bind_assoc]
      refine bind_congr fun res => ?_
      rcases res with _ | fig8st
      · simp
      · dsimp only [Option.map, fig8StTruncSkOpt]
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        cases fig8st.γ <;> rfl

private theorem semFwdAnswerHook_idHook_eq {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    semFwdAnswerHook P Dh encPt encT lam (fig8IdSemHook (PQC := PQC) none) qep sC () Q w isDel ci? Tpk pq' c' =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runIdM (fwdAnswerC (qep := qep) (fig := fig) (fs := fs) (H := idHook) Q w isDel ci? Tpk pq' c') sC := by
  unfold semFwdAnswerHook runIdM fwdAnswerC
  simp only [StateT.run_bind, runOnBaseState_idHook_run, fwd_run_eq, bind_assoc]
  split_ifs <;>
    simp only [fig8IdSemHook, pure_bind, bind_assoc] <;>
    (refine bind_congr fun res => ?_;
     rcases res with _ | (_ | ⟨t, i, pm⟩) <;> simp [onAnswer_run_eq_pure])

private theorem semResyncHook_idHook_eq {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : Bytes) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : Fig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    semResyncHook P Dh encPt encT lam (fig8IdSemHook (PQC := PQC) none) qep sC () Q w ci? Tpk pq' c r =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runIdM (resyncC (qep := qep) (fig := fig) (fs := fs) (H := idHook) Q w ci? Tpk pq' c r) sC := by
  unfold semResyncHook runIdM resyncC
  rcases r with _ | ⟨t, i, ⟨pub, m'⟩⟩
  · simp
  · simp only [fig8IdSemHook, StateT.run_bind, liftC_idHook_run, pure_bind, bind_assoc]
    refine bind_congr fun res => ?_
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp [runOnBaseState_idHook_run, onAccept_run_eq_pure]

private theorem semFwdEvictHook_idHook_eq {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    semFwdEvictHook P Dh encPt encT lam (fig8IdSemHook (PQC := PQC) none) qep sC () Q w isDel Tpk pq' c' =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runIdM (fwdEvictC (qep := qep) (fig := fig) (fs := fs) (H := idHook) Q w isDel Tpk pq' c') sC := by
  unfold semFwdEvictHook fwdEvictC
  by_cases h : (isDel && !(sC.base.mir.safeInj 3)) = true
  · dsimp only [idHook, fig8IdSemHook]
    simp only [runIdM, StateT.run_bind, StateT.run_get, pure_bind, h, ↓reduceIte,
      stateT_lift_run_id, StateT.run_pure]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rw [semFwdAnswerHook_idHook_eq]
    simp only [runIdM, StateT.run_bind, StateT.run_get, pure_bind, h, Bool.false_eq_true, ↓reduceIte]

private theorem semFwdHook_idHook_eq {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (hc' : ∀ c, honestC = some c → c ≠ c' → c'.1.1 ≤ B ∧ c'.2.1 ≤ B) :
    semFwdHook P Dh encPt encT lam (fig8IdSemHook (PQC := PQC) none) qep B sC () Q w isDel ci? Tpk pq'
      honestC c' =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runIdM (fwdC (P := P) (qep := qep) (fig := fig) (fs := fs) (H := idHook)
        Q w isDel ci? Tpk pq' honestC c') sC := by
  unfold semFwdHook fwdC
  rcases honestC with _ | c
  · dsimp only []
    rw [semFwdAnswerHook_idHook_eq]
    simp [runIdM]
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
      · dsimp only [idHook, fig8IdSemHook]
        simp only [runIdM, StateT.run_bind, StateT.run_get, pure_bind, h, ↓reduceIte, heval,
          stateT_lift_run_id, StateT.run_pure]
      · dsimp only []
        rw [semResyncHook_idHook_eq]
        simp only [runIdM, StateT.run_bind, StateT.run_get, pure_bind, h, ↓reduceIte, heval]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [semFwdAnswerHook_idHook_eq]
      simp only [runIdM, StateT.run_bind, StateT.run_get, pure_bind, h, Bool.false_eq_true, ↓reduceIte]

private theorem getD_chains_epoch_le' (cs : List GhostChain) (ci B : ℕ)
    (hch : ∀ g ∈ cs, g.epoch ≤ B) :
    (cs.getD ci ⟨none, 0, 0, []⟩).epoch ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : cs[ci]? with _ | g
  · exact Nat.zero_le B
  · exact hch g (List.mem_of_getElem? h)

private theorem semRecvHook_idHook_eq {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (h232 : 2 ^ 32 ≤ B)
    (hep : sC.base.mir.epoch Q + 1 ≤ B)
    (hch : ∀ g ∈ sC.base.chains Q, g.epoch ≤ B) :
    semRecvHook P Dh encPt encT decT lam (fig8IdSemHook (PQC := PQC) none) qep B sC () Q w isDel =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runIdM (guardC (simRecvC (P := P) (encT := encT) (decT := decT)
        (qep := qep) (fig := fig) (fs := fs) (H := idHook) Q w isDel)) sC := by
  dsimp only []
  by_cases hstop : sC.base.stopped = true
  · unfold semRecvHook runIdM guardC; simp [hstop]
  · rw [runIdM_guardC_neg _ sC hstop]
    unfold semRecvHook simRecvC
    have hcond : (sC.base.stopped || sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
          !(sC.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) =
      (sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
          !(sC.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) := by
      simp [hstop]
    rw [hcond, runIdM_get_bind]
    by_cases hwin : sC.base.mir.win = true
    · simp [hwin, runIdM_pure]
    · simp only [hwin, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      by_cases hdel : (isDel && (sC.base.mir.inTransit Q.other w).isNone) = true
      · simp [hdel, runIdM_pure]
      · simp only [hdel, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        by_cases hinj : (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
            !(sC.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w))) = true
        · simp [hinj, runIdM_pure]
        · simp only [hinj, Bool.false_eq_true, ↓reduceIte]
          unfold simParseRecvC
          rw [partyDec_partyEnc]
          by_cases hlen : w.length < 9
          · simp [hlen, runIdM_pure]
          · simp only [hlen, ↓reduceIte]
            rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
              _ | ⟨h, rest⟩
            · simp [runIdM_pure]
            · cases haddr : CryptoGames.LibsignalAead.addressCheckPasses h.addresses (P.expectedAddrs Q)
              · simp [haddr, runIdM_pure]
              · cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet
                · dsimp only []
                  simp only [haddr, hpan, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
                  rcases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with _ | ⟨pq', salt⟩
                  · simp [runIdM_pure]
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
                            (fun c => decide (c.2.2.2 = CryptoGames.effectiveHkdfSalt32 salt)) == some true) = true
                      · simp only [hev, ↓reduceIte, runIdM_pure]
                      · simp only [hev, Bool.false_eq_true, ↓reduceIte]
                        by_cases hT0 : (decT h.senderRatchetKey == some 0) = true
                        · simp [hT0, runIdM_pure]
                        · simp only [hT0, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel,
                            runIdM_ite_modify]
                          by_cases hexit : (inReceiveOnlyEpoch sC.base.mir Q ||
                              decide (25000 < h.counter.toNat) ||
                              decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
                          · simp only [hexit, ↓reduceIte, runIdM_pure]
                          · simp only [hexit, Bool.false_eq_true, ↓reduceIte]
                            rcases hT : decT h.senderRatchetKey with _ | T
                            · simp only [runIdM_pure]
                            · dsimp only []
                              by_cases hev1 : (((sC.base.honest.find? fun wc =>
                                  wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                                    (fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) ==
                                      some true) = true
                              · simp only [hev1, ↓reduceIte]
                                rw [semFwdEvictHook_idHook_eq]
                              · simp only [hev1, Bool.false_eq_true, ↓reduceIte]
                                rw [semFwdHook_idHook_eq P Dh encPt encT lam qep B]
                                · rfl
                                · intro c hc hne; rw [hc] at hne ⊢
                                  by_cases hs : c.2.2.2 = CryptoGames.effectiveHkdfSalt32 salt
                                  · simp [hs] at hne
                                  · simp only [hs, ↓reduceIte]; exact ⟨hep, by omega⟩
                    · by_cases hrej :
                          ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects
                            (h.counter.toNat + 1) = true
                      · simp only [hrej, ↓reduceIte, runIdM_pure]
                      · simp only [hrej, Bool.false_eq_true, ↓reduceIte]
                        have hgep : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch ≤ B :=
                          getD_chains_epoch_le' (sC.base.chains Q) ci B hch
                        rw [semFwdHook_idHook_eq P Dh encPt encT lam qep B]
                        · rfl
                        · intro c hc hne
                          rw [hc] at hne ⊢
                          by_cases hs : c.2.2.2 = CryptoGames.effectiveHkdfSalt32 salt
                          · simp [hs] at hne
                          · simp only [hs, ↓reduceIte]; exact ⟨hgep, by omega⟩
                · simp [haddr, hpan, runIdM_pure]

private theorem simFig8Oracle_none_eq_simImplC {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (qep B : ℕ)
    (q : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (h232 : 2 ^ 32 ≤ B)
    (hep : ∀ Q : Party, sC.base.mir.epoch Q + 1 ≤ B)
    (hch : ∀ Q : Party, ∀ g ∈ sC.base.chains Q, g.epoch ≤ B) :
    (simFig8Oracle P Dh encPt encT decT lam qep B none q).run sC =
      (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
        (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (fs := lFS P.C P.codec ℓ encT idOf 25000)
        (H := idHook) Dh q).run sC := by
  have hid' : (fun R : Party => if R == Party.A then P.idA else P.idB) = idOf := funext hid
  subst hid'
  rcases q with n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rfl
  · dsimp only [simFig8Oracle, simImplC, Sum.elim_inl, Sum.elim_inr]
    change Prod.map id Prod.fst <$> semSendHook P Dh encPt encT lam (fig8IdSemHook none) qep sC () Q m none r = _
    rw [semSendHook_idHook_eq]; simp [runIdM, map_eq_bind_pure_comp]
  · dsimp only [simFig8Oracle, simImplC, Sum.elim_inl, Sum.elim_inr]
    change Prod.map id Prod.fst <$> semSendHook P Dh encPt encT lam (fig8IdSemHook none) qep sC () Q m₀ (some m₁) r = _
    rw [semSendHook_idHook_eq]; simp [runIdM, map_eq_bind_pure_comp]
  · dsimp only [simFig8Oracle, simImplC, Sum.elim_inl, Sum.elim_inr]
    change Prod.map id Prod.fst <$> semHandleHook P Dh encPt encT decT lam (fig8IdSemHook none) qep B (.inl (.inl (.inr (Q, w)))) sC () = _
    have hstep : semHandleHook P Dh encPt encT decT lam (fig8IdSemHook (PQC := PQC) none) qep B
        (.inl (.inl (.inr (Q, w)))) sC () =
        semRecvHook P Dh encPt encT decT lam (fig8IdSemHook (PQC := PQC) none) qep B
          sC () Q w true := by
      unfold semHandleHook
      dsimp only [fig8IdSemHook]
      simp only [pure_bind]
      exact bind_pure _
    rw [hstep, semRecvHook_idHook_eq P Dh encPt encT decT lam qep B sC Q w true h232 (hep Q) (hch Q)]
    simp [runIdM, map_eq_bind_pure_comp]
  · dsimp only [simFig8Oracle, simImplC, Sum.elim_inl, Sum.elim_inr]
    change Prod.map id Prod.fst <$> semRecvHook P Dh encPt encT decT lam (fig8IdSemHook none) qep B sC () Q w false = _
    rw [semRecvHook_idHook_eq P Dh encPt encT decT lam qep B sC Q w false h232 (hep Q) (hch Q)]
    simp [runIdM, map_eq_bind_pure_comp]
  · dsimp only [simFig8Oracle, simImplC, Sum.elim_inl, Sum.elim_inr]
    change Prod.map id Prod.fst <$> semCorrHook P Dh encT (fig8IdSemHook none) sC () Q = _
    rw [semCorrHook_idHook_eq]; simp [runIdM, map_eq_bind_pure_comp]

private structure SimEpochClampInv {PQ Pt : Type} {ℓ : ℕ} (B m : ℕ) (s : SimState PQ Pt ℓ) : Prop where
  hep : ∀ Q : Party, s.mir.epoch Q + m + 1 ≤ B
  htrans : ∀ r ∈ s.mir.trans, r.pos.epoch + m + 1 ≤ B
  hch : ∀ Q : Party, ∀ g ∈ s.chains Q, g.epoch + m + 1 ≤ B

private theorem SimEpochClampInv.mono {PQ Pt : Type} {ℓ : ℕ} {B m₁ m₂ : ℕ} {s : SimState PQ Pt ℓ}
    (hle : m₁ ≤ m₂) (h : SimEpochClampInv B m₂ s) : SimEpochClampInv B m₁ s where
  hep Q := by have := h.hep Q; omega
  htrans r hr := by have := h.htrans r hr; omega
  hch Q g hg := by have := h.hch Q g hg; omega

private theorem SimEpochClampInv.withAmb {PQ Pt : Type} {ℓ : ℕ} {B m : ℕ} {s : SimState PQ Pt ℓ}
    (h : SimEpochClampInv B m s) (a : ℕ) : SimEpochClampInv B m { s with amb := a } :=
  ⟨h.hep, h.htrans, h.hch⟩

private theorem simEpochClampInv_init {PQ Pt : Type} {ℓ : ℕ} (B q : ℕ) (pqA pqB : PQ)
    (hqB : q + 2 ≤ B) :
    SimEpochClampInv B q (initSim (Pt := Pt) (ℓ := ℓ) pqA pqB) where
  hep Q := by dsimp [initSim]; omega
  htrans _ hr := by simp [initSim] at hr
  hch Q g hg := by
    cases Q <;> simp [initSim] at hg
    subst hg; dsimp; omega

private theorem epMgmt_epoch_trans {St Msg C : Type}
    (s s₁ : GameState St Msg C) (Δ qep : ℕ) (Q : Party) (bad : Bool)
    (h : s.epMgmt Δ qep Q bad = some s₁) :
    (∀ R : Party, s₁.epoch R ≤ s.epoch R + 1) ∧ s₁.trans = s.trans ∧ s₁.st = s.st := by
  unfold GameState.epMgmt at h
  split_ifs at h with h1 h2 h3 h4 <;> injection h with h <;> subst h
  · refine ⟨fun R => ?_, rfl, rfl⟩
    by_cases hR : R = Q <;> simp [hR, GameState.leak]
  · refine ⟨fun R => ?_, rfl, rfl⟩
    by_cases hR : R = Q <;> simp [hR]
  · exact ⟨fun _ => Nat.le_add_right _ 1, rfl, rfl⟩

private theorem ghostChain_accept_epoch' (g : GhostChain) (i : ℕ) :
    (g.accept i).epoch = g.epoch := by
  unfold GhostChain.accept; split_ifs <;> rfl

private theorem mem_modify_accept_epoch' (cs : List GhostChain) (ci i : ℕ)
    {g' : GhostChain} (hg' : g' ∈ cs.modify ci (·.accept i)) :
    ∃ g ∈ cs, g'.epoch = g.epoch := by
  induction cs generalizing ci with
  | nil => simp at hg'
  | cons g gs ih =>
    cases ci with
    | zero =>
      change g' ∈ g.accept i :: gs at hg'
      rcases List.mem_cons.mp hg' with rfl | hg'
      · exact ⟨g, List.mem_cons_self, ghostChain_accept_epoch' g i⟩
      · exact ⟨g', List.mem_cons_of_mem g hg', rfl⟩
    | succ ci =>
      change g' ∈ g :: gs.modify ci (·.accept i) at hg'
      rcases List.mem_cons.mp hg' with rfl | hg'
      · exact ⟨g', List.mem_cons_self, rfl⟩
      · obtain ⟨g₀, hg₀, heq⟩ := ih ci hg'
        exact ⟨g₀, List.mem_cons_of_mem g hg₀, heq⟩

private theorem mem_pushChain' (cs : List GhostChain) (g₀ : GhostChain)
    {g' : GhostChain} (hg' : g' ∈ pushChain cs g₀) :
    g' = g₀ ∨ g' ∈ cs := by
  unfold pushChain at hg'
  have h1 := List.mem_of_mem_drop hg'
  rw [List.mem_append, List.mem_singleton] at h1
  exact h1.symm

private theorem onAcceptPure_epochClampInv {PQ Pt : Type} {ℓ : ℕ}
    (qep B m : ℕ) (Q : Party) (w : Bytes) (isDel : Bool) (t i : ℕ) (msg : Plain ℓ)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (st : SimState PQ Pt ℓ) (hInv : SimEpochClampInv B m st) (ht : t + m + 1 ≤ B) :
    SimEpochClampInv B m (onAcceptPure qep Q w isDel t i msg ci? T pq' st).2 := by
  have hacc : ∀ (pos : CryptoGames.SM.Pos), pos.epoch + m + 1 ≤ B →
      SimEpochClampInv B m
        { st with
          chains := Function.update st.chains Q
            (match ci? with
             | some ci => (st.chains Q).modify ci (·.accept i)
             | none => pushChain (st.chains Q) (GhostChain.accept ⟨some T, t, 0, []⟩ i)),
          pq := Function.update st.pq Q pq',
          unackA := st.unackA && Q != Party.A,
          mir := st.mir.accept Q () pos } := by
    intro pos hpos
    refine {
      hep := fun R => by
        dsimp only [GameState.accept, GameState.delete]
        by_cases hR : R = Q
        · subst hR; simp only [Function.update_self]; have := hInv.hep R; omega
        · simp only [Function.update_of_ne hR]; exact hInv.hep R
      htrans := fun r hr => by
        dsimp only [GameState.accept, GameState.delete] at hr
        exact hInv.htrans r (List.mem_of_mem_filter hr)
      hch := fun R g' hg' => by
        dsimp only [] at hg'
        by_cases hR : R = Q
        · subst hR; simp only [Function.update_self] at hg'
          rcases ci? with _ | ci
          · rcases mem_pushChain' (st.chains R) (GhostChain.accept ⟨some T, t, 0, []⟩ i) hg' with
              rfl | hg'
            · rw [ghostChain_accept_epoch']; exact ht
            · exact hInv.hch R g' hg'
          · obtain ⟨g, hg, heq⟩ := mem_modify_accept_epoch' (st.chains R) ci i hg'
            rw [heq]; exact hInv.hch R g hg
        · simp only [Function.update_of_ne hR] at hg'
          exact hInv.hch R g' hg' }
  unfold onAcceptPure
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with h1 h2
    · exact hInv
    · exact hacc ⟨Q.other, t, i⟩ ht
    · exact ⟨hInv.hep, hInv.htrans, hInv.hch⟩
  · simp only [↓reduceIte]
    rcases hin : st.mir.inTransit Q.other w with _ | r
    · exact hInv
    · exact hacc r.pos (hInv.htrans r (List.mem_of_find?_eq_some hin))

private theorem onAnswerPure_epochClampInv {PQ Pt : Type} {ℓ : ℕ}
    (qep B m : ℕ) (Q : Party) (w : Bytes) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (st : SimState PQ Pt ℓ) (hInv : SimEpochClampInv B m st)
    (hres : ∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B) :
    SimEpochClampInv B m (onAnswerPure qep Q w isDel ci? T pq' res st).2 := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hInv
  · exact hInv
  · exact onAcceptPure_epochClampInv qep B m Q w isDel t i ((pm.map (·.2)).getD default)
      ci? T pq' st hInv (hres t i pm rfl)

private theorem scPostSendPure_epochClampInv {PQ PQC Pt : Type} [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) {B m : ℕ}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {s₁ : GameState Unit (Plain ℓ) Bytes}
    {Q : Party} {qep : ℕ} {hasCoins : Bool}
    (hep : sC.base.mir.epMgmt 3 qep Q hasCoins = some s₁)
    (m₀ : Plain ℓ) (isChall : Bool) (pq' : PQ) (pn : BitVec 32) (c : Fig8C Pt)
    (hInv : SimEpochClampInv B (m + 1) sC.base) :
    SimEpochClampInv B m (scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ isChall pq' pn c).base := by
  have hInv0 := hInv.mono (Nat.le_succ m)
  obtain ⟨hep_le, htr_eq, _⟩ := epMgmt_epoch_trans sC.base.mir s₁ 3 qep Q hasCoins hep
  refine {
    hep := fun R => by
      dsimp only [scPostSendPure, GameState.record]
      have := hep_le R; have := hInv.hep R; omega
    htrans := fun r hr => by
      dsimp only [scPostSendPure, GameState.record] at hr
      rcases List.mem_cons.mp hr with rfl | hr
      · dsimp only []; have := hep_le Q; have := hInv.hep Q; omega
      · rw [htr_eq] at hr; exact hInv0.htrans r hr
    hch := hInv0.hch }

private theorem skipKeys_length {ChainKey MessageKey : Type}
    (G : ℕ → PRGScheme ChainKey (ChainKey × MessageKey))
    (n : ℕ) (w : ChainKey) (p : ℕ) (acc : List (ℕ × MessageKey)) :
    (CryptoGames.FSAEAD.skipKeys G n w p acc).2.length = acc.length + n := by
  induction n generalizing w p acc with
  | zero => rfl
  | succ n ih =>
    dsimp only [CryptoGames.FSAEAD.skipKeys]
    rw [ih, List.length_cons]
    omega

private theorem fromAEADPRG_receive_skipped_le
    {ChainKey MessageKey AssocData Message Ciphertext : Type}
    (ae : AEADScheme MessageKey (ℕ × AssocData) Message Ciphertext)
    (G : ℕ → PRGScheme ChainKey (ChainKey × MessageKey)) (maxSkip : ℕ)
    (v v' : CryptoGames.FSAEAD.RatchetReceiverState ChainKey MessageKey)
    (a : AssocData) (c : ℕ × Ciphertext) (i : ℕ) (m : Message)
    (h : (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).receive v a c = some (v', i, m)) :
    i = c.1 ∧ v'.skippedKeys.length ≤ v.skippedKeys.length + maxSkip := by
  dsimp only [CryptoGames.FSAEAD.fromAEADPRG] at h
  rcases hl : v.skippedKeys.lookup c.1 with _ | key <;> simp only [hl] at h
  · split_ifs at h with hbad
    rw [Option.map_eq_some_iff] at h
    rcases h with ⟨m', _, hm⟩
    injection hm with hv' him
    injection him with hi _
    subst hv' hi
    refine ⟨rfl, ?_⟩
    dsimp only []
    rw [skipKeys_length]
    omega
  · rw [Option.map_eq_some_iff] at h
    rcases h with ⟨m', _, hm⟩
    injection hm with hv' him
    injection him with hi _
    subst hv' hi
    exact ⟨rfl, (List.length_filter_le _ _).trans (Nat.le_add_right _ _)⟩

private theorem lFig8_receive_bounds_skip {Pt : Type} [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (st st' : Fig8St Pt) (c : Fig8C Pt) (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive st c = some (st', t, i, pm)) :
    t = c.1.1 ∧ i = c.2.1 ∧ t ≤ st.tcur + 1 ∧ st'.tcur ≤ st.tcur + 1 ∧
      ∀ t₀ v', st'.vR t₀ = some v' →
        v'.skippedKeys.length ≤ 25000 ∨
          ∃ v, st.vR t₀ = some v ∧ v'.skippedKeys.length ≤ v.skippedKeys.length + 25000 := by
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.receive] at h
  split at h
  · cases h
  · rename_i h1
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at h1
    split at h
    · cases h
    · rename_i s₁ hs₁
      have hs₁_b : s₁.tcur ≤ st.tcur + 1 ∧
          ∀ t₀ v, s₁.vR t₀ = some v → v.skippedKeys = [] ∨ st.vR t₀ = some v := by
        split_ifs at hs₁ with heq
        · rcases hc12 : c.1.2 with _ | Tn <;> rw [hc12] at hs₁
          · cases hs₁
          · injection hs₁ with hs₁; subst hs₁
            refine ⟨h1.2, fun t₀ v hv => ?_⟩
            dsimp only [] at hv
            by_cases ht : t₀ = c.1.1
            · subst ht; simp only [Function.update_self, Option.some.injEq] at hv
              subst hv; exact Or.inl rfl
            · simp only [Function.update_of_ne ht] at hv; exact Or.inr hv
        · injection hs₁ with hs₁; subst hs₁
          exact ⟨Nat.le_add_right _ 1, fun _ _ hv => Or.inr hv⟩
      split at h
      · cases h
      · rename_i v hv_s1
        rcases hfs : (lFS C codec ℓ encT idOf 25000).receive v c.1 c.2 with _ | ⟨v₁, i₁, pm₁⟩
        · rw [hfs] at h; cases h
        · rw [hfs] at h
          injection h with h
          injection h with hst' ht'
          injection ht' with ht' hi'
          injection hi' with hi' _
          subst hst' ht'
          obtain ⟨hi_eq, hv₁_le⟩ := fromAEADPRG_receive_skipped_le _ _ 25000 v v₁ c.1 c.2 i₁ pm₁ hfs
          refine ⟨rfl, hi'.symm.trans hi_eq, h1.2, hs₁_b.1, fun t₀ v' hv' => ?_⟩
          dsimp only [] at hv'
          by_cases ht₀ : t₀ = c.1.1
          · subst ht₀; simp only [Function.update_self, Option.some.injEq] at hv'
            subst hv'
            rcases hs₁_b.2 c.1.1 v hv_s1 with hnil | hstv
            · rw [hnil] at hv₁_le; exact Or.inl (by simpa using hv₁_le)
            · exact Or.inr ⟨v, hstv, hv₁_le⟩
          · simp only [Function.update_of_ne ht₀] at hv'
            rcases hs₁_b.2 t₀ v' hv' with hnil | hstv
            · rw [hnil]; exact Or.inl (Nat.zero_le _)
            · exact Or.inr ⟨v', hstv, Nat.le_add_right _ _⟩

private theorem lFig8_send_bounds_skip {Pt : Type} [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (st : Fig8St Pt) (m : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256) :
    let out := (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).send st m coins
    out.1.tcur ≤ st.tcur + 1 ∧ out.1.vR = st.vR := by
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.send]
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · simp [hs, lFS, CryptoGames.FSAEAD.fromAEADPRG]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    cases st.vS <;> simp

private theorem evalCKClamp_epoch_le' {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : Bytes)
    (c c' : Fig8C Pt) (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
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
  · rw [hk] at h; dsimp only [] at h
    rcases hs : sentEval
        (fs := fsClampSim B (lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000))
        sC.sent c c' with _ | r'
    · rw [hs] at h; dsimp only [] at h
      rcases hks : CryptoGames.Ratchet.LibsignalSimC.snapshotMessageKeySeed P sC.snaps Q c.1.1 w with _ | seed
      · rw [hks] at h; cases h
      · rw [hks] at h; injection h with h
        dsimp only [simKDecryptFig8] at h
        split at h
        · injection h with h; injection h with ht _; omega
        · cases h
    · rw [hs] at h; dsimp only [] at h
      have h1 := hs.trans h
      unfold sentEval at h1
      rcases hfind : sC.sent.find? (fun e => decide (e.1 = c)) with _ | e <;>
        simp only [hfind, Option.map] at h1
      · cases h1
      · rcases hfs : (fsClampSim B (lFS P.C P.codec ℓ encT
            (fun R => if R == Party.A then P.idA else P.idB) 25000)).receive
            ⟨e.2.chainKey, e.2.lastIndex, []⟩ c'.1 c'.2 with _ | ⟨v', i', pm'⟩ <;>
          simp only [hfs] at h1
        · cases h1
        · injection h1 with h1; injection h1 with h1; injection h1 with ht _; omega
  · rw [hk] at h; dsimp only [] at h
    have h1 := hk.trans h
    unfold Kept.eval at h1
    rcases hfull : (sC.kept Q).full with _ | st <;> simp only [hfull, Option.map] at h1
    · rcases hrs : (sC.kept Q).rs c'.1.1 with _ | v <;> simp only [hrs] at h1
      · cases h1
      · rcases hfs : (fsClampSim B (lFS P.C P.codec ℓ encT
            (fun R => if R == Party.A then P.idA else P.idB) 25000)).receive v c'.1 c'.2 with
          _ | ⟨v', i', pm'⟩ <;> simp only [hfs] at h1
        · cases h1
        · injection h1 with h1; injection h1 with h1; injection h1 with ht _; omega
    · dsimp only [fig8Clamp] at h1
      rcases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam).receive st c' with
        _ | ⟨st', t_out, i_out, pm'⟩ <;> simp only [hfig, Option.map] at h1
      · cases h1
      · obtain ⟨rfl, _⟩ := lFig8_receive_bounds_skip P.C P.codec Dh encPt encT _ lam
          st st' c' t_out i_out pm' hfig
        injection h1 with h1; injection h1 with h1; injection h1 with ht _; omega

private abbrev Fig8G (Pt : Type) (ℓ : ℕ) :=
  GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)

private structure Fig8RunClampInv {Pt : Type} {ℓ : ℕ} (B : ℕ) (B_skip? : Option ℕ) (m : ℕ)
    (gs : Fig8G Pt ℓ) : Prop where
  htcur : ∀ Q : Party, (gs.st Q).tcur + m + 1 ≤ B
  hskip : ∀ B_skip, B_skip? = some B_skip →
    m * 25000 ≤ B_skip ∧
    ∀ Q : Party, ∀ t v, (gs.st Q).vR t = some v → v.skippedKeys.length + m * 25000 ≤ B_skip

private theorem Fig8RunClampInv.mono {Pt : Type} {ℓ : ℕ} {B : ℕ} {B_skip? : Option ℕ}
    {m₁ m₂ : ℕ} {gs : Fig8G Pt ℓ} (hle : m₁ ≤ m₂) (h : Fig8RunClampInv B B_skip? m₂ gs) :
    Fig8RunClampInv B B_skip? m₁ gs where
  htcur Q := by have := h.htcur Q; omega
  hskip B_skip hBs := by
    obtain ⟨hm, hvR⟩ := h.hskip B_skip hBs
    have hmul : m₁ * 25000 ≤ m₂ * 25000 := Nat.mul_le_mul_right 25000 hle
    exact ⟨hmul.trans hm, fun Q t v hv => (Nat.add_le_add_left hmul _).trans (hvR Q t v hv)⟩

private theorem Fig8RunClampInv.withWin {Pt : Type} {ℓ : ℕ} {B : ℕ} {B_skip? : Option ℕ} {m : ℕ}
    {gs : Fig8G Pt ℓ} (h : Fig8RunClampInv B B_skip? m gs) (w : Bool) :
    Fig8RunClampInv B B_skip? m { gs with win := w } :=
  ⟨h.htcur, h.hskip⟩

private theorem fig8RunClampInv_init {Pt : Type} [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (q : ℕ) (k : RootKey × BitVec 256) (b : Bool)
    (hqB : q + 1 ≤ B) (hBs : ∀ B_skip, B_skip? = some B_skip → q * 25000 ≤ B_skip) :
    Fig8RunClampInv B B_skip? q
      (CryptoGames.SM.initState (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) k b) where
  htcur Q := by
    dsimp only [CryptoGames.SM.initState, lFig8, CryptoGames.SM.Construction.scheme,
      CryptoGames.SM.Construction.initParty]
    cases Q <;> dsimp only [] <;> omega
  hskip B_skip hEq := by
    refine ⟨hBs B_skip hEq, fun Q t v hv => ?_⟩
    dsimp only [CryptoGames.SM.initState, lFig8, CryptoGames.SM.Construction.scheme,
      CryptoGames.SM.Construction.initParty, lFS, CryptoGames.FSAEAD.fromAEADPRG] at hv
    cases Q
    · dsimp only [] at hv
      split_ifs at hv
      injection hv with hv; subst hv
      simpa using hBs B_skip hEq
    · cases hv

private def fig8GameImpl {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) :
    QueryImpl (FSpec Pt ℓ) (StateT (Fig8G Pt ℓ) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Fig8G Pt ℓ) ProbComp) +
    CryptoGames.SM.oracleImpl fig 3 (qep + 1) cfg

private theorem simulateQ_fig8GameImpl_liftProb {Pt α : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (p : ProbComp α) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg) (liftM p : Fig8Comp Pt ℓ α)).run gs =
      (p >>= fun a => pure (a, gs)) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t mx ih =>
    change (simulateQ (fig8GameImpl fig qep cfg)
      (query (spec := FSpec Pt ℓ) (.inl t) >>= fun u => liftM (mx u))).run gs =
      ((query t >>= mx) >>= fun a => pure (a, gs))
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    have hinl : (simulateQ (fig8GameImpl fig qep cfg)
        (query (spec := FSpec Pt ℓ) (.inl t))).run gs =
        (query t >>= fun u => pure (u, gs)) := by
      simp only [query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      rfl
    rw [hinl]
    simp only [bind_assoc, pure_bind]
    exact bind_congr fun u => ih u

private theorem simulateQ_fig8GameImpl_transmitQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256)) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg) (CryptoGames.SM.transmitQuery Q m rc)).run gs =
      (CryptoGames.SM.transmitImpl fig 3 (qep + 1) (Q, m, rc)).run gs := by
  simp only [CryptoGames.SM.transmitQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]; rfl

private theorem simulateQ_fig8GameImpl_challQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256)) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg) (CryptoGames.SM.challQuery Q m₀ m₁ rc)).run gs =
      (CryptoGames.SM.challImpl fig 3 (qep + 1) cfg (Q, m₀, m₁, rc)).run gs := by
  simp only [CryptoGames.SM.challQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]; rfl

private theorem simulateQ_fig8GameImpl_deliverQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (c : Fig8C Pt) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg) (CryptoGames.SM.deliverQuery Q c)).run gs =
      (CryptoGames.SM.deliverImpl fig cfg (Q, c)).run gs := by
  simp only [CryptoGames.SM.deliverQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]; rfl

private theorem simulateQ_fig8GameImpl_injectQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (c : Fig8C Pt) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg) (CryptoGames.SM.injectQuery Q c)).run gs =
      (CryptoGames.SM.injectImpl fig 3 (qep + 1) cfg (Q, c)).run gs := by
  simp only [CryptoGames.SM.injectQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]; rfl

private theorem simulateQ_fig8GameImpl_corrQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg) (CryptoGames.SM.corrQuery Q)).run gs =
      (CryptoGames.SM.corrImpl Q).run gs := by
  simp only [CryptoGames.SM.corrQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]; rfl

private theorem fig8RunClampInv_record {Pt : Type} [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m qep : ℕ) (gs s₁ : Fig8G Pt ℓ)
    (Q : Party) (bad isChall : Bool) (msg : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256)
    (hfg : Fig8RunClampInv B B_skip? (m + 1) gs)
    (hep : gs.epMgmt 3 (qep + 1) Q bad = some s₁) :
    let fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam
    let out := fig.send (s₁.st Q) msg coins
    Fig8RunClampInv B B_skip? m
      (s₁.record 3 Q out.1 ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, msg, out.2⟩ isChall) := by
  obtain ⟨_, _, hst⟩ := epMgmt_epoch_trans gs s₁ 3 (qep + 1) Q bad hep
  obtain ⟨htcur', hvR'⟩ := lFig8_send_bounds_skip C codec Dh encPt encT idOf lam (s₁.st Q) msg coins
  have hfg0 := hfg.mono (Nat.le_succ m)
  refine {
    htcur := fun R => by
      dsimp only [GameState.record]
      by_cases hR : R = Q
      · subst hR
        simp only [Function.update_self]
        rw [hst] at htcur' ⊢
        have := hfg.htcur R
        omega
      · simp only [Function.update_of_ne hR, hst]; exact hfg0.htcur R
    hskip := fun B_skip hEq => by
      obtain ⟨hm0, hvR0⟩ := hfg0.hskip B_skip hEq
      refine ⟨hm0, fun R t v hv => ?_⟩
      dsimp only [GameState.record] at hv
      by_cases hR : R = Q
      · subst hR
        simp only [Function.update_self] at hv
        rw [hvR', hst] at hv
        exact hvR0 R t v hv
      · simp only [Function.update_of_ne hR, hst] at hv; exact hvR0 R t v hv }

private theorem fig8RunClampInv_accept {Pt : Type} [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m : ℕ) (gs : Fig8G Pt ℓ)
    (Q : Party) (c : Fig8C Pt) (st' : Fig8St Pt) (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (pos : CryptoGames.SM.Pos)
    (hfg : Fig8RunClampInv B B_skip? (m + 1) gs)
    (hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c =
      some (st', t, i, pm)) :
    Fig8RunClampInv B B_skip? m (gs.accept Q st' pos) ∧ t + m + 1 ≤ B := by
  obtain ⟨_, _, ht_le, hst'_tcur, hst'_vR⟩ :=
    lFig8_receive_bounds_skip C codec Dh encPt encT idOf lam (gs.st Q) st' c t i pm hrcv
  have hfg0 := hfg.mono (Nat.le_succ m)
  have htQ := hfg.htcur Q
  refine ⟨{
    htcur := fun R => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hR : R = Q
      · subst hR; simp only [Function.update_self]; omega
      · simp only [Function.update_of_ne hR]; exact hfg0.htcur R
    hskip := fun B_skip hEq => by
      obtain ⟨hm1, hvR1⟩ := hfg.hskip B_skip hEq
      have hm1' : m * 25000 + 25000 ≤ B_skip := by rw [← Nat.succ_mul]; exact hm1
      refine ⟨(Nat.le_add_right _ 25000).trans hm1', fun R t₀ v' hv' => ?_⟩
      dsimp only [GameState.accept, GameState.delete] at hv'
      by_cases hR : R = Q
      · subst hR; simp only [Function.update_self] at hv'
        rcases hst'_vR t₀ v' hv' with hle25 | ⟨v, hv, hle⟩
        · exact (Nat.add_le_add_right hle25 _).trans ((Nat.add_comm _ _).trans_le hm1')
        · have hvB := hvR1 R t₀ v hv
          rw [Nat.succ_mul, ← Nat.add_assoc, Nat.add_right_comm] at hvB
          exact (Nat.add_le_add_right hle _).trans hvB
      · simp only [Function.update_of_ne hR] at hv'
        exact (hfg0.hskip B_skip hEq).2 R t₀ v' hv' }, by omega⟩

private theorem fig8RunClampInv_transmitImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m qep : ℕ) (gs gs' : Fig8G Pt ℓ)
    (Q : Party) (msg : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (res : Option (Fig8C Pt))
    (hfg : Fig8RunClampInv B B_skip? (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.transmitImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) 3 (qep + 1) (Q, msg, rc)).run gs)) :
    Fig8RunClampInv B B_skip? m gs' := by
  unfold CryptoGames.SM.transmitImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hfg.mono (Nat.le_succ m)
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      monadLift_prob_run, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
    rcases hep : gs.epMgmt 3 (qep + 1) Q bad with _ | s₁ <;>
      simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    · rcases hmem with ⟨_, rfl⟩; exact hfg.mono (Nat.le_succ m)
    · rcases hmem with ⟨_, rfl⟩
      exact fig8RunClampInv_record C codec Dh encPt encT idOf lam B B_skip? m qep gs s₁ Q bad false msg coins hfg hep

private theorem fig8RunClampInv_challImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs gs' : Fig8G Pt ℓ)
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (res : Option (Fig8C Pt))
    (hfg : Fig8RunClampInv B B_skip? (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.challImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) 3 (qep + 1) cfg (Q, m₀, m₁, rc)).run gs)) :
    Fig8RunClampInv B B_skip? m gs' := by
  unfold CryptoGames.SM.challImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hfg.mono (Nat.le_succ m)
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      monadLift_prob_run, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
    rcases hep : gs.epMgmt 3 (qep + 1) Q bad with _ | s₁ <;> simp only [hep] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hfg.mono (Nat.le_succ m)
    · by_cases hch : (!(s₁.safeCh 3 Q) || !(cfg.challAllowedIn (s₁.epoch Q))) = true
      · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hfg.mono (Nat.le_succ m)
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact fig8RunClampInv_record C codec Dh encPt encT idOf lam B B_skip? m qep gs s₁ Q bad true
          ((cfg.challMsg (s₁.epoch Q)).getD (if gs.b then m₁ else m₀)) coins hfg hep

private theorem fig8RunClampInv_deliverImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs gs' : Fig8G Pt ℓ) (Q : Party) (c : Fig8C Pt)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hfg : Fig8RunClampInv B B_skip? (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.deliverImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) cfg (Q, c)).run gs)) :
    Fig8RunClampInv B B_skip? m gs' ∧ ∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B := by
  unfold CryptoGames.SM.deliverImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hfg.mono (Nat.le_succ m), fun _ _ _ hc => by cases hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases htr : gs.inTransit Q.other c with _ | r <;> simp only [htr] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hfg.mono (Nat.le_succ m), fun _ _ _ hc => by cases hc⟩
    · rcases hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c with
        _ | ⟨st', t', i', m'⟩ <;> simp only [hrcv] at hmem
      · split_ifs at hmem <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
          (rcases hmem with ⟨rfl, rfl⟩;
           exact ⟨⟨(hfg.mono (Nat.le_succ m)).htcur, (hfg.mono (Nat.le_succ m)).hskip⟩,
             fun _ _ _ hc => by cases hc⟩)
      · obtain ⟨hfg', ht'⟩ :=
          fig8RunClampInv_accept C codec Dh encPt encT idOf lam B B_skip? m gs Q c st' t' i' m' r.pos hfg hrcv
        split_ifs at hmem <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
          (rcases hmem with ⟨rfl, rfl⟩;
           refine ⟨⟨hfg'.htcur, hfg'.hskip⟩, fun t i pm hc => ?_⟩;
           injection hc with hc; injection hc with ht _ _; subst ht; exact ht')

private theorem fig8RunClampInv_injectImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs gs' : Fig8G Pt ℓ) (Q : Party) (c : Fig8C Pt)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hfg : Fig8RunClampInv B B_skip? (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.injectImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) 3 (qep + 1) cfg (Q, c)).run gs)) :
    Fig8RunClampInv B B_skip? m gs' ∧ ∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B := by
  unfold CryptoGames.SM.injectImpl at hmem
  by_cases hw : (gs.win || (gs.inTransit Q.other c).isSome || !(gs.safeInj 3)) = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hfg.mono (Nat.le_succ m), fun _ _ _ hc => by cases hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c with
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
          fig8RunClampInv_accept C codec Dh encPt encT idOf lam B B_skip? m gs Q c st' t' i' m'
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
             exact ⟨⟨(hfg.mono (Nat.le_succ m)).htcur, (hfg.mono (Nat.le_succ m)).hskip⟩,
               fun _ _ _ hc => by cases hc⟩)

private theorem fig8RunClampInv_corrImpl {Pt : Type} {ℓ : ℕ}
    (B : ℕ) (B_skip? : Option ℕ) (m : ℕ) (gs gs' : Fig8G Pt ℓ) (Q : Party)
    (res : Option (Fig8St Pt)) (hfg : Fig8RunClampInv B B_skip? (m + 1) gs)
    (hmem : (res, gs') ∈ support
      ((CryptoGames.SM.corrImpl (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (C := Fig8C Pt) Q).run gs)) :
    Fig8RunClampInv B B_skip? m gs' := by
  unfold CryptoGames.SM.corrImpl at hmem
  by_cases hw : (gs.win || !(gs.corrAllowed Q)) = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hfg.mono (Nat.le_succ m)
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩
    have hfg0 := hfg.mono (Nat.le_succ m)
    exact ⟨hfg0.htcur, hfg0.hskip⟩

private theorem semSendHook_fig8Game_inv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs₀ : Fig8G Pt ℓ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (hEp : SimEpochClampInv B (m + 1) sC₀.base)
    (hFg : Fig8RunClampInv B B_skip? (m + 1) gs₀) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semSendHook P Dh encPt encT lam (fig8IdSemHook (PQC := PQC) none) qep sC₀ () Q m₀ chal r)).run gs₀),
      SimEpochClampInv B m x.1.2.1.base ∧ Fig8RunClampInv B B_skip? m x.2 := by
  intro fig
  have hEp0 := hEp.mono (Nat.le_succ m)
  have hFg0 := hFg.mono (Nat.le_succ m)
  rintro ⟨⟨_, sC₁, _⟩, gs₁⟩ hx
  unfold semSendHook at hx
  by_cases href : (sC₀.base.stopped || sC₀.base.mir.win || !(noBobSendInEpoch0 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp0, hFg0⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC₀.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;> simp only [hep] at hx
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp0, hFg0⟩
    · by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hch, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp0, hFg0⟩
      · have hsc : (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none).onSendCoins =
            fun _ _ _ => pure ((), ()) := rfl
        simp only [hch, Bool.false_eq_true, ↓reduceIte, hsc, pure_bind,
          simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx
        obtain ⟨⟨⟨rq, rc⟩, gs_c⟩, hcoins, hx⟩ := hx
        have hgs_c : gs_c = gs₀ := by
          rcases r with _ | rq₀ <;>
            dsimp only [semDrawSendCoins, fig8IdSemHook] at hcoins <;>
            simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
              simulateQ_fig8GameImpl_liftProb, pure_bind, bind_assoc,
              mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcoins <;>
            (obtain ⟨_, -, _, rfl⟩ := hcoins; rfl)
        rw [hgs_c] at hx
        rcases hpub : mkPub P sC₀.base Q rq
          (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
            BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) with _ | ⟨pq', pub⟩ <;>
          simp only [hpub] at hx
        · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp0, hFg0⟩
        · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx
          obtain ⟨⟨⟨res, _⟩, gs₂⟩, hq, hx⟩ := hx
          have hFg2 : Fig8RunClampInv B B_skip? m gs₂ := by
            rcases chal with _ | m₁
            · dsimp only [fig8IdSemHook] at hq
              simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
                simulateQ_fig8GameImpl_transmitQuery, mem_support_bind_iff, support_pure,
                Set.mem_singleton_iff, Prod.mk.injEq] at hq
              obtain ⟨⟨res', gs'⟩, htr, ⟨rfl, _⟩, rfl⟩ := hq
              exact fig8RunClampInv_transmitImpl P.C P.codec Dh encPt encT idOf lam B B_skip? m qep
                gs₀ gs₂ Q (pub, m₀) rc res hFg htr
            · dsimp only [fig8IdSemHook] at hq
              simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
                simulateQ_fig8GameImpl_challQuery, mem_support_bind_iff, support_pure,
                Set.mem_singleton_iff, Prod.mk.injEq] at hq
              obtain ⟨⟨res', gs'⟩, htr, ⟨rfl, _⟩, rfl⟩ := hq
              exact fig8RunClampInv_challImpl P.C P.codec Dh encPt encT idOf lam B B_skip? m qep cfg
                gs₀ gs₂ Q (pub, m₀) (pub, m₁) rc res hFg htr
          rcases res with _ | c <;>
            simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hx
          · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp0, hFg2⟩
          · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
            exact ⟨scPostSendPure_epochClampInv P Dh encPt encT lam hep m₀ chal.isSome pq' _ c hEp,
              hFg2⟩

private theorem semFwdAnswerHook_fig8Game_inv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs₀ : Fig8G Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (hEp : SimEpochClampInv B m sC₀.base)
    (hFg : Fig8RunClampInv B B_skip? (m + 1) gs₀) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semFwdAnswerHook P Dh encPt encT lam (fig8IdSemHook (PQC := PQC) none) qep sC₀ ()
          Q w isDel ci? Tpk pq' c')).run gs₀),
      SimEpochClampInv B m x.1.2.1.base ∧ Fig8RunClampInv B B_skip? m x.2 := by
  intro fig
  rintro ⟨⟨_, sC₁, _⟩, gs₁⟩ hx
  unfold semFwdAnswerHook at hx
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
  obtain ⟨⟨⟨res, _⟩, gs₂⟩, hq, ⟨⟨_, rfl, _⟩, rfl⟩⟩ := hx
  have hq' : Fig8RunClampInv B B_skip? m gs₁ ∧
      ∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B := by
    split_ifs at hq
    · dsimp only [fig8IdSemHook] at hq
      simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        simulateQ_fig8GameImpl_deliverQuery, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hq
      obtain ⟨⟨res', gs'⟩, hdl, ⟨rfl, _⟩, rfl⟩ := hq
      exact fig8RunClampInv_deliverImpl P.C P.codec Dh encPt encT idOf lam B B_skip? m cfg
        gs₀ gs₁ Q c' res hFg hdl
    · dsimp only [fig8IdSemHook] at hq
      simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        simulateQ_fig8GameImpl_injectQuery, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hq
      obtain ⟨⟨res', gs'⟩, hij, ⟨rfl, _⟩, rfl⟩ := hq
      exact fig8RunClampInv_injectImpl P.C P.codec Dh encPt encT idOf lam B B_skip? m qep cfg
        gs₀ gs₁ Q c' res hFg hij
  exact ⟨onAnswerPure_epochClampInv qep B m Q w isDel ci? Tpk pq' res sC₀.base hEp hq'.2, hq'.1⟩

private theorem semResyncHook_fig8Game_inv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs₀ : Fig8G Pt ℓ)
    (Q : Party) (w : Bytes) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hr : ∀ t i pm, r = some (t, i, pm) → t + m + 1 ≤ B)
    (hEp : SimEpochClampInv B m sC₀.base)
    (hFg : Fig8RunClampInv B B_skip? (m + 1) gs₀) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semResyncHook P Dh encPt encT lam (fig8IdSemHook (PQC := PQC) none) qep sC₀ ()
          Q w ci? Tpk pq' c r)).run gs₀),
      SimEpochClampInv B m x.1.2.1.base ∧ Fig8RunClampInv B B_skip? m x.2 := by
  intro fig
  rintro ⟨⟨_, sC₁, _⟩, gs₁⟩ hx
  unfold semResyncHook at hx
  rcases r with _ | ⟨t, i, pub, m'⟩
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
    exact ⟨hEp, hFg.mono (Nat.le_succ m)⟩
  · dsimp only [fig8IdSemHook] at hx
    simp only [simulateQ_bind, StateT.run_bind,
      simulateQ_fig8GameImpl_deliverQuery, pure_bind, bind_assoc, mem_support_bind_iff] at hx
    obtain ⟨⟨res, gs₂⟩, hdl, hx⟩ := hx
    have hFg' := (fig8RunClampInv_deliverImpl P.C P.codec Dh encPt encT idOf lam B B_skip? m cfg
      gs₀ gs₂ Q c res hFg hdl).1
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp, hFg'⟩
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp, hFg'⟩
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
      exact ⟨onAcceptPure_epochClampInv qep B m Q w true t i m' ci? Tpk pq' sC₀.base hEp
        (hr t i (pub, m') rfl), hFg'⟩

private theorem semFwdHook_fig8Game_inv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs₀ : Fig8G Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (hc' : ∀ c, honestC = some c → c ≠ c' → c'.1.1 + m + 1 ≤ B)
    (hEp : SimEpochClampInv B m sC₀.base)
    (hFg : Fig8RunClampInv B B_skip? (m + 1) gs₀) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semFwdHook P Dh encPt encT lam (fig8IdSemHook (PQC := PQC) none) qep B sC₀ ()
          Q w isDel ci? Tpk pq' honestC c')).run gs₀),
      SimEpochClampInv B m x.1.2.1.base ∧ Fig8RunClampInv B B_skip? m x.2 := by
  intro fig
  rintro ⟨⟨_, sC₁, _⟩, gs₁⟩ hx
  unfold semFwdHook at hx
  rcases hhc : honestC with _ | c <;> simp only [hhc] at hx
  · exact semFwdAnswerHook_fig8Game_inv P Dh encPt encT idOf lam B B_skip? m qep cfg
      sC₀ gs₀ Q w isDel ci? Tpk pq' c' hEp hFg _ hx
  · by_cases hcnd : (!(decide (c = c')) && (isDel && !(sC₀.base.mir.safeInj 3))) = true
    · simp only [hcnd, ↓reduceIte] at hx
      have hne : c ≠ c' := of_decide_eq_false (by revert hcnd; cases decide (c = c') <;> simp)
      have hc'ep := hc' c hhc hne
      rcases hev : evalCKClamp P Dh encPt encT lam B sC₀ Q w c c' with _ | r <;>
        simp only [hev] at hx
      · dsimp only [fig8IdSemHook] at hx
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
        exact ⟨hEp, hFg.mono (Nat.le_succ m)⟩
      · refine semResyncHook_fig8Game_inv P Dh encPt encT idOf lam B B_skip? m qep cfg
          sC₀ gs₀ Q w ci? Tpk pq' c r (fun t i pm hr => ?_) hEp hFg _ hx
        subst hr
        have htle := evalCKClamp_epoch_le' P Dh encPt encT lam B sC₀ Q w c c' t i pm hev
        omega
    · simp only [hcnd, Bool.false_eq_true, ↓reduceIte] at hx
      exact semFwdAnswerHook_fig8Game_inv P Dh encPt encT idOf lam B B_skip? m qep cfg
        sC₀ gs₀ Q w isDel ci? Tpk pq' c' hEp hFg _ hx

private theorem semRecvHook_fig8Game_inv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs₀ : Fig8G Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (hEp : SimEpochClampInv B (m + 1) sC₀.base)
    (hFg : Fig8RunClampInv B B_skip? (m + 1) gs₀) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semRecvHook P Dh encPt encT decT lam (fig8IdSemHook (PQC := PQC) none) qep B
          sC₀ () Q w isDel)).run gs₀),
      SimEpochClampInv B m x.1.2.1.base ∧ Fig8RunClampInv B B_skip? m x.2 := by
  intro fig
  have hEp0 := hEp.mono (Nat.le_succ m)
  have hFg0 := hFg.mono (Nat.le_succ m)
  rintro ⟨⟨_, sC₁, _⟩, gs₁⟩ hx
  unfold semRecvHook at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win ||
        (isDel && (sC₀.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC₀.base.mir.inTransit Q.other w).isSome ||
          !(sC₀.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp0, hFg0⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hparse : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC₀.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;> simp only [hparse] at hx
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp0, hFg0⟩
    · have hmkC : ∀ (honestC : Option (Fig8C Pt)) (ep : ℕ) (T1 : Option Pt),
          ep + m + 1 ≤ B →
          ∀ c, honestC = some c →
            c ≠ (match honestC with
                 | some c => if c.2.2.2 = lct.2.2 then c else ((ep, T1), lct)
                 | none => ((ep, T1), lct)) →
            (match honestC with
             | some c => if c.2.2.2 = lct.2.2 then c else ((ep, T1), lct)
             | none => ((ep, T1), lct)).1.1 + m + 1 ≤ B := by
        intro honestC ep T1 hep c hhc hne
        subst hhc
        by_cases hs : c.2.2.2 = lct.2.2
        · simp [hs] at hne
        · simp [hs, hep]
      rcases hidx : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · let sCAmb : LibsignalToModularSchemeSimState PQ Pt ℓ :=
          { sC₀ with base :=
              if inReceiveOnlyEpoch sC₀.base.mir Q ||
                  (Q == Party.A && (sC₀.base.chains Q).any (·.key.isNone))
              then { sC₀.base with amb := sC₀.base.amb + 1 }
              else sC₀.base }
        have hEpAmb : SimEpochClampInv B m sCAmb.base := by
          dsimp only [sCAmb]
          split_ifs
          · exact hEp0.withAmb _
          · exact hEp0
        by_cases hc1 :
            ((((sC₀.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true &&
             (((sC₀.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [hc1, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp0, hFg0⟩
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hx
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp0, hFg0⟩
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hx
            by_cases hc2 :
                (inReceiveOnlyEpoch sC₀.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
                Set.mem_singleton_iff, Prod.mk.injEq] at hx
              rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEpAmb, hFg0⟩
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hx
              rcases hT : T? with _ | T <;> simp only [hT] at hx
              · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq] at hx
                rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEpAmb, hFg0⟩
              · have hep1 : (sC₀.base.mir.epoch Q + 1) + m + 1 ≤ B := by
                  have := hEp.hep Q; omega
                by_cases hev_b :
                    ((((sC₀.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte] at hx
                  change ((_, sC₁, _), gs₁) ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
                    (semFwdEvictHook P Dh encPt encT lam (fig8IdSemHook (PQC := PQC) none) qep
                      sCAmb () Q w isDel pk pq' ((sC₀.base.mir.epoch Q + 1, some T), lct))).run gs₀) at hx
                  unfold semFwdEvictHook at hx
                  by_cases hfe : (isDel && !(sCAmb.base.mir.safeInj 3)) = true
                  · dsimp only [fig8IdSemHook] at hx
                    simp only [hfe, ↓reduceIte, pure_bind, simulateQ_pure, StateT.run_pure,
                      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
                    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEpAmb, hFg0⟩
                  · simp only [hfe, Bool.false_eq_true, ↓reduceIte] at hx
                    exact semFwdAnswerHook_fig8Game_inv P Dh encPt encT idOf lam B B_skip? m qep cfg
                      sCAmb gs₀ Q w isDel none pk pq' _ hEpAmb hFg _ hx
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte] at hx
                  exact semFwdHook_fig8Game_inv P Dh encPt encT idOf lam B B_skip? m qep cfg
                    sCAmb gs₀ Q w isDel none pk pq' _ _
                    (hmkC _ (sC₀.base.mir.epoch Q + 1) (some T) hep1) hEpAmb hFg _ hx
      · by_cases hrej : ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp0, hFg0⟩
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hx
          have hgep : ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch + m + 1 ≤ B := by
            rw [List.getD_eq_getElem?_getD]
            rcases h : (sC₀.base.chains Q)[ci]? with _ | g
            · dsimp only [Option.getD]; have := hEp.hep Q; omega
            · dsimp only [Option.getD]; have := hEp.hch Q g (List.mem_of_getElem? h); omega
          exact semFwdHook_fig8Game_inv P Dh encPt encT idOf lam B B_skip? m qep cfg
            sC₀ gs₀ Q w isDel (some ci) pk pq' _ _
            (hmkC _ ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch T? hgep) hEp0 hFg _ hx

private theorem semCorrHook_fig8Game_inv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs₀ : Fig8G Pt ℓ) (Q : Party)
    (hEp : SimEpochClampInv B (m + 1) sC₀.base)
    (hFg : Fig8RunClampInv B B_skip? (m + 1) gs₀) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semCorrHook P Dh encT (fig8IdSemHook (PQC := PQC) none) sC₀ () Q)).run gs₀),
      SimEpochClampInv B m x.1.2.1.base ∧ Fig8RunClampInv B B_skip? m x.2 := by
  intro fig
  have hEp0 := hEp.mono (Nat.le_succ m)
  have hFg0 := hFg.mono (Nat.le_succ m)
  rintro ⟨⟨_, sC₁, _⟩, gs₁⟩ hx
  unfold semCorrHook at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win || !(sC₀.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC₀.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp0, hFg0⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte, fig8IdSemHook,
      bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_fig8GameImpl_corrQuery, mem_support_bind_iff] at hx
    obtain ⟨⟨res, gs₂⟩, hcr, hx⟩ := hx
    have hFg' := fig8RunClampInv_corrImpl B B_skip? m gs₀ gs₂ Q res hFg hcr
    rcases res with _ | fig8st
    · dsimp only [Option.map] at hx
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hEp0, hFg'⟩
    · dsimp only [Option.map, fig8StTruncSkOpt] at hx
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
      refine ⟨{
        hep := fun R => hEp0.hep R
        htrans := fun r hr => hEp0.htrans r hr
        hch := fun R g' hg' => by
          dsimp only [] at hg'
          split_ifs at hg'
          · generalize fig8st.γ = γ at hg'
            cases γ with
            | pub _ =>
              dsimp only [] at hg'
              exact hEp0.hch R g' hg'
            | exp _ =>
              dsimp only [] at hg'
              by_cases hR : R = Party.A
              · subst hR
                simp only [Function.update_self, List.mem_map] at hg'
                obtain ⟨g, hg, hge⟩ := hg'
                have hg_ep : g'.epoch = g.epoch := by split_ifs at hge <;> (subst hge; rfl)
                rw [hg_ep]; exact hEp0.hch Party.A g hg
              · simp only [Function.update_of_ne hR] at hg'
                exact hEp0.hch R g' hg'
          · exact hEp0.hch R g' hg' }, hFg'⟩

private theorem simFig8Oracle_none_step_inv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs₀ : Fig8G Pt ℓ)
    (hEp : SimEpochClampInv B (m + 1) sC₀.base)
    (hFg : Fig8RunClampInv B B_skip? (m + 1) gs₀) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        ((simFig8Oracle P Dh encPt encT decT lam qep B none (.inr t)).run sC₀)).run gs₀),
      SimEpochClampInv B m x.1.2.base ∧ Fig8RunClampInv B B_skip? m x.2 := by
  intro fig
  rintro ⟨⟨ans, sC₁⟩, gs₁⟩ hx
  change ((ans, sC₁), gs₁) ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
    (Prod.map id Prod.fst <$>
      semHandleHook P Dh encPt encT decT lam (fig8IdSemHook (PQC := PQC) none) qep B t sC₀ ())).run gs₀) at hx
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hx
  obtain ⟨⟨⟨u, sC', _⟩, gs'⟩, hmem, hEq⟩ := hx
  simp only [Prod.map, id_eq, Prod.mk.injEq] at hEq
  rcases hEq with ⟨⟨_, rfl⟩, rfl⟩
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_fig8Game_inv P Dh encPt encT idOf lam B B_skip? m qep cfg
      sC₀ gs₀ Q m₀ none r hEp hFg _ hmem
  · exact semSendHook_fig8Game_inv P Dh encPt encT idOf lam B B_skip? m qep cfg
      sC₀ gs₀ Q m₀ (some m₁) r hEp hFg _ hmem
  · have hstep : semHandleHook P Dh encPt encT decT lam (fig8IdSemHook (PQC := PQC) none) qep B
        (.inl (.inl (.inr (Q, w)))) sC₀ () =
        semRecvHook P Dh encPt encT decT lam (fig8IdSemHook (PQC := PQC) none) qep B
          sC₀ () Q w true := by
      unfold semHandleHook
      dsimp only [fig8IdSemHook]
      simp only [pure_bind]
      exact bind_pure _
    rw [hstep] at hmem
    exact semRecvHook_fig8Game_inv P Dh encPt encT decT idOf lam B B_skip? m qep cfg
      sC₀ gs₀ Q w true hEp hFg _ hmem
  · exact semRecvHook_fig8Game_inv P Dh encPt encT decT idOf lam B B_skip? m qep cfg
      sC₀ gs₀ Q w false hEp hFg _ hmem
  · exact semCorrHook_fig8Game_inv P Dh encPt encT idOf lam B B_skip? m qep cfg
      sC₀ gs₀ Q hEp hFg _ hmem

private theorem simFig8Oracle_fig8GameImpl_step_eq {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (B : ℕ) (B_skip? : Option ℕ) (m qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ)
    (hFg : Fig8RunClampInv B B_skip? (m + 1) gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    (simulateQ (fig8GameImpl fig qep cfg)
      ((simFig8Oracle P Dh encPt encT decT lam qep B B_skip? (.inr t)).run sC)).run gs =
    (simulateQ (fig8GameImpl fig qep cfg)
      ((simFig8Oracle P Dh encPt encT decT lam qep B none (.inr t)).run sC)).run gs ∧
    (simulateQ (fig8GameImpl fig qep cfg)
      ((simFig8OracleTG P Dh encPt encT decT lam qep B B_skip? (.inr t)).run sC)).run gs =
    (simulateQ (fig8GameImpl fig qep cfg)
      ((simFig8Oracle P Dh encPt encT decT lam qep B none (.inr t)).run sC)).run gs := by
  intro fig
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · have htrunc : fig8StTruncSkOpt B_skip? (gs.st Q) = gs.st Q :=
      fig8StTruncSkOpt_eq_self B_skip? (gs.st Q) fun B_skip hBs t₀ v hv => by
        have := (hFg.hskip B_skip hBs).2 Q t₀ v hv; omega
    change
      (simulateQ (fig8GameImpl fig qep cfg)
        (Prod.map id Prod.fst <$>
          semCorrHook P Dh encT (fig8IdSemHook (PQC := PQC) B_skip?) sC () Q)).run gs =
      (simulateQ (fig8GameImpl fig qep cfg)
        (Prod.map id Prod.fst <$>
          semCorrHook P Dh encT (fig8IdSemHook (PQC := PQC) none) sC () Q)).run gs ∧
      (simulateQ (fig8GameImpl fig qep cfg)
        (semCorrHookTG P Dh encT B_skip? sC Q)).run gs =
      (simulateQ (fig8GameImpl fig qep cfg)
        (Prod.map id Prod.fst <$>
          semCorrHook P Dh encT (fig8IdSemHook (PQC := PQC) none) sC () Q)).run gs
    unfold semCorrHook semCorrHookTG
    by_cases href :
        (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
         inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
    · simp only [href, ↓reduceIte, map_pure, Prod.map, id_eq, and_self]
    · refine ⟨?_, ?_⟩
      · dsimp only [fig8IdSemHook]
        simp only [href, Bool.false_eq_true, ↓reduceIte, map_bind, bind_assoc, pure_bind,
          simulateQ_bind, StateT.run_bind, simulateQ_fig8GameImpl_corrQuery]
        unfold CryptoGames.SM.corrImpl
        by_cases hw : (gs.win || !(gs.corrAllowed Q)) = true
        · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
            pure_bind, Option.map_none]
        · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
            StateT.run_set, StateT.run_pure, pure_bind, Option.map_some, htrunc,
            fig8StTruncSkOpt_none]
      · dsimp only [fig8IdSemHook]
        simp only [href, Bool.false_eq_true, ↓reduceIte, map_bind, bind_assoc, pure_bind,
          simulateQ_bind, StateT.run_bind, simulateQ_fig8GameImpl_corrQuery]
        unfold CryptoGames.SM.corrImpl
        by_cases hw : (gs.win || !(gs.corrAllowed Q)) = true
        · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
            pure_bind, Option.map_none, map_pure, Prod.map, id_eq]
        · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
            StateT.run_set, StateT.run_pure, pure_bind, Option.map_some, htrunc,
            fig8StTruncSkOpt_none, map_pure, Prod.map, id_eq]
          cases (gs.st Q).γ <;> rfl

private theorem simulateQ_fig8GameImpl_inl {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (n : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg)
      ((StateT.lift (query (spec := FSpec Pt ℓ) (.inl n)) :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) _).run sC)).run gs =
      (query (spec := unifSpec) n >>= fun u => pure ((u, sC), gs)) := by
  have h : (StateT.lift (query (spec := FSpec Pt ℓ) (.inl n)) :
      StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) _).run sC =
      (liftM ((query (spec := unifSpec) n : ProbComp _) >>= fun u => pure (u, sC)) : Fig8Comp Pt ℓ _) := by
    change (query (spec := FSpec Pt ℓ) (.inl n) >>= fun u => pure (u, sC)) = _
    rw [liftM_bind]
    exact bind_congr fun _ => rfl
  rw [h, simulateQ_fig8GameImpl_liftProb, bind_assoc]
  exact bind_congr fun _ => by simp

private theorem simulateQ_fig8GameImpl_simFig8Oracle_eq {PQ PQC Pt : Type} [Inhabited PQ]
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (B : ℕ) (B_skip? : Option ℕ) (m qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (h232 : 2 ^ 32 ≤ B) {α : Type}
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes) α)
    (hq : oa.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)) m)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ)
    (hEp : SimEpochClampInv B m sC.base)
    (hFg : Fig8RunClampInv B B_skip? m gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    (simulateQ (fig8GameImpl fig qep cfg)
      ((simulateQ (simFig8Oracle P Dh encPt encT decT lam qep B B_skip?) oa).run sC)).run gs =
    (simulateQ (fig8GameImpl fig qep cfg)
      ((simulateQ (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
        (fig := fig) (fs := fs) (H := idHook) Dh) oa).run sC)).run gs ∧
    (simulateQ (fig8GameImpl fig qep cfg)
      ((simulateQ (simFig8OracleTG P Dh encPt encT decT lam qep B B_skip?) oa).run sC)).run gs =
    (simulateQ (fig8GameImpl fig qep cfg)
      ((simulateQ (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
        (fig := fig) (fs := fs) (H := idHook) Dh) oa).run sC)).run gs := by
  intro fig fs
  induction oa using OracleComp.inductionOn generalizing m sC gs with
  | pure a => exact ⟨rfl, rfl⟩
  | query_bind q mx ih =>
    have hq' := (isQueryBoundP_query_bind_iff _ q mx m).mp hq
    rw [simulateQ_query_bind, simulateQ_query_bind, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
      StateT.run_bind, simulateQ_bind]
    dsimp only [liftM, monadLift, MonadLiftT.monadLift]
    rcases q with n | t
    · have hqu : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)) m :=
        fun u => by simpa [isGameQuery] using hq'.2 u
      have hinl1 :
          (simFig8Oracle P Dh encPt encT decT lam qep B B_skip? (.inl n)).run sC =
          (StateT.lift (query (spec := FSpec Pt ℓ) (.inl n)) :
            StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) _).run sC := rfl
      have hinl2 :
          (simFig8OracleTG P Dh encPt encT decT lam qep B B_skip? (.inl n)).run sC =
          (StateT.lift (query (spec := FSpec Pt ℓ) (.inl n)) :
            StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) _).run sC := rfl
      have hinl3 :
          (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
            (fig := fig) (fs := fs) (H := idHook) Dh (.inl n)).run sC =
          (StateT.lift (query (spec := FSpec Pt ℓ) (.inl n)) :
            StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) _).run sC := rfl
      rw [hinl1, hinl2, hinl3, simulateQ_fig8GameImpl_inl]
      simp only [bind_assoc, pure_bind]
      exact ⟨bind_congr fun u => (ih u m (hqu u) sC gs hEp hFg).1,
             bind_congr fun u => (ih u m (hqu u) sC gs hEp hFg).2⟩
    · have hm_pos : 0 < m := by simpa [isGameQuery] using hq'.1
      rcases m with _ | m'
      · omega
      have hqu : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)) m' :=
        fun u => by simpa [isGameQuery] using hq'.2 u
      obtain ⟨hStep1, hStep2⟩ := simFig8Oracle_fig8GameImpl_step_eq P Dh encPt encT decT idOf lam
        B B_skip? m' qep cfg t sC gs hFg
      have hImplEq :
          (simFig8Oracle P Dh encPt encT decT lam qep B none (.inr t)).run sC =
          (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
            (fig := fig) (fs := fs) (H := idHook) Dh (.inr t)).run sC :=
        simFig8Oracle_none_eq_simImplC P Dh encPt encT decT idOf hid lam qep B (.inr t) sC h232
          (fun Q => by have := hEp.hep Q; omega)
          (fun Q g hg => by have := hEp.hch Q g hg; omega)
      have hInv := simFig8Oracle_none_step_inv P Dh encPt encT decT idOf lam
        B B_skip? m' qep cfg t sC gs hEp hFg
      dsimp only [fig, fs] at hStep1 hStep2 hImplEq hInv ⊢
      rw [hStep1, hStep2, ← hImplEq]
      exact ⟨bind_congr_of_forall_mem_support _ fun x hx =>
               (ih x.1.1 m' (hqu x.1.1) x.1.2 x.2 (hInv x hx).1 (hInv x hx).2).1,
             bind_congr_of_forall_mem_support _ fun x hx =>
               (ih x.1.1 m' (hqu x.1.1) x.1.2 x.2 (hInv x hx).1 (hInv x hx).2).2⟩

/-- Running `simFig8Clamp` in the real Fig. 8 `SM.run` game is syntactically identical to running
`Refine.libsignalToModularSchemeSim` whenever `2 ^ 32 ≤ B`, `q + 2 ≤ B`, and `q * 25000 ≤ B_skip`
(if `B_skip? = some B_skip`). -/
theorem sm_run_simFig8Clamp_eq {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hBs : ∀ B_skip, B_skip? = some B_skip → q * 25000 ≤ B_skip) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8Clamp P ℓ Dh encPt encT decT lam qep B B_skip? A) =
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (CryptoGames.LibsignalSM.Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf
        lam qep A) := by
  intro fig
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  unfold CryptoGames.SM.run simFig8Clamp CryptoGames.LibsignalSM.Refine.libsignalToModularSchemeSim
    runLibsignalToModularSchemeSim simRunCWith
  dsimp only [idHook]
  refine bind_congr fun k => ?_
  change (simulateQ (fig8GameImpl fig qep cfg) _).run (CryptoGames.SM.initState fig k b) =
    (simulateQ (fig8GameImpl fig qep cfg) _).run (CryptoGames.SM.initState fig k b)
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_fig8GameImpl_liftProb, bind_assoc,
    pure_bind, StateT.run'_eq, simulateQ_map, StateT.run_map]
  refine bind_congr fun pqrKey => congrArg (Functor.map (Prod.map Prod.fst id)) ?_
  exact (simulateQ_fig8GameImpl_simFig8Oracle_eq P Dh encPt encT decT idOf hid lam B B_skip? q qep
    cfg h232 A hq' (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
    (CryptoGames.SM.initState fig k b)
    (simEpochClampInv_init B q _ _ hqB)
    (fig8RunClampInv_init P.C P.codec Dh encPt encT idOf lam B B_skip? q k b (by omega) hBs)).1

/-- Running `simFig8ClampTG` in the real Fig. 8 `SM.run` game is syntactically identical to running
`Refine.libsignalToModularSchemeSim` whenever `2 ^ 32 ≤ B`, `q + 2 ≤ B`, and `q * 25000 ≤ B_skip`. -/
theorem sm_run_simFig8ClampTG_eq {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hBs : ∀ B_skip, B_skip? = some B_skip → q * 25000 ≤ B_skip) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampTG P ℓ Dh encPt encT decT lam qep B B_skip? A) =
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (CryptoGames.LibsignalSM.Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf
        lam qep A) := by
  intro fig
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  unfold CryptoGames.SM.run simFig8ClampTG CryptoGames.LibsignalSM.Refine.libsignalToModularSchemeSim
    runLibsignalToModularSchemeSim simRunCWith
  dsimp only [idHook]
  refine bind_congr fun k => ?_
  change (simulateQ (fig8GameImpl fig qep cfg) _).run (CryptoGames.SM.initState fig k b) =
    (simulateQ (fig8GameImpl fig qep cfg) _).run (CryptoGames.SM.initState fig k b)
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_fig8GameImpl_liftProb, bind_assoc,
    pure_bind, StateT.run'_eq, simulateQ_map, StateT.run_map]
  refine bind_congr fun pqrKey => congrArg (Functor.map (Prod.map Prod.fst id)) ?_
  exact (simulateQ_fig8GameImpl_simFig8Oracle_eq P Dh encPt encT decT idOf hid lam B B_skip? q qep
    cfg h232 A hq' (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
    (CryptoGames.SM.initState fig k b)
    (simEpochClampInv_init B q _ _ hqB)
    (fig8RunClampInv_init P.C P.codec Dh encPt encT idOf lam B B_skip? q k b (by omega) hBs)).2

theorem sm_game_simFig8Clamp_eq {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hBs : ∀ B_skip, B_skip? = some B_skip → q * 25000 ≤ B_skip) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CryptoGames.SM.game fig 3 (qep + 1) cfg
      (simFig8Clamp P ℓ Dh encPt encT decT lam qep B B_skip? A) =
    CryptoGames.SM.game fig 3 (qep + 1) cfg
      (CryptoGames.LibsignalSM.Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf
        lam qep A) := by
  unfold CryptoGames.SM.game
  refine bind_congr fun b => ?_
  rw [sm_run_simFig8Clamp_eq P Dh encPt encT decT idOf hid lam qep B B_skip? cfg b hq h232 hqB hBs]

theorem sm_game_simFig8ClampTG_eq {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hBs : ∀ B_skip, B_skip? = some B_skip → q * 25000 ≤ B_skip) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CryptoGames.SM.game fig 3 (qep + 1) cfg
      (simFig8ClampTG P ℓ Dh encPt encT decT lam qep B B_skip? A) =
    CryptoGames.SM.game fig 3 (qep + 1) cfg
      (CryptoGames.LibsignalSM.Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf
        lam qep A) := by
  unfold CryptoGames.SM.game
  refine bind_congr fun b => ?_
  rw [sm_run_simFig8ClampTG_eq P Dh encPt encT decT idOf hid lam qep B B_skip? cfg b hq h232 hqB hBs]

theorem simCNoneWinEvent_eq_sm_run_simFig8Clamp {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hBs : ∀ B_skip, B_skip? = some B_skip → q * 25000 ≤ B_skip) :
    CryptoGames.LibsignalSM.Proofs.Refinement.simCNoneWinEvent P ℓ Dh encPt encT decT idOf lam
      qep A =
    (do
      let b ← $ᵗ Bool
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let (_, s) ← CryptoGames.SM.run fig 3 (qep + 1) CryptoGames.SM.Config.h1 b
        (simFig8Clamp P ℓ Dh encPt encT decT lam qep B B_skip? A)
      return s.win) := by
  unfold CryptoGames.LibsignalSM.Proofs.Refinement.simCNoneWinEvent
  refine bind_congr fun b => ?_
  dsimp only []
  rw [← sm_run_simFig8Clamp_eq P Dh encPt encT decT idOf hid lam qep B B_skip?
    CryptoGames.SM.Config.h1 b hq h232 hqB hBs]

theorem simCNoneWinEvent_eq_sm_run_simFig8ClampTG {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hBs : ∀ B_skip, B_skip? = some B_skip → q * 25000 ≤ B_skip) :
    CryptoGames.LibsignalSM.Proofs.Refinement.simCNoneWinEvent P ℓ Dh encPt encT decT idOf lam
      qep A =
    (do
      let b ← $ᵗ Bool
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let (_, s) ← CryptoGames.SM.run fig 3 (qep + 1) CryptoGames.SM.Config.h1 b
        (simFig8ClampTG P ℓ Dh encPt encT decT lam qep B B_skip? A)
      return s.win) := by
  unfold CryptoGames.LibsignalSM.Proofs.Refinement.simCNoneWinEvent
  refine bind_congr fun b => ?_
  dsimp only []
  rw [← sm_run_simFig8ClampTG_eq P Dh encPt encT decT idOf hid lam qep B B_skip?
    CryptoGames.SM.Config.h1 b hq h232 hqB hBs]

end IdHookAndGameEquiv

/-! ## `SimFig8EvalOk` and `SimFig8AtomicStepBundle` -/

section AtomicStepBundle

open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSessionOpDescBits atomicCompDescBits ratchetDescBudget)

/-- Type of the `simFig8` costed reduction program in `SessionCostedReductions`. -/
abbrev SimFig8RedProg (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt] (ℓ : ℕ)
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) : Type :=
  CostedReduction
    (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
    (fig8SmIface ℓ Pt)
    (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (e2eSessionCodec ℓ Pt)
    .unit .unit .bool .bool

/-- Semantic evaluation contract for a `SimFig8RedProg` against `Refine.libsignalToModularSchemeSim`
at `(idA, idB, qep, q)` when `ℓ < 10 ^ 6`. -/
structure SimFig8EvalOk (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt] (ℓ : ℕ)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (prog : SimFig8RedProg Pt ℓ C K Dh encPt encT decT lam) : Prop where
  queries : ℓ < 10 ^ 6 →
    ∀ (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes),
      CryptoGames.SM.MakesAtMostQueries A q →
      CryptoGames.SM.MakesAtMostQueries (prog.eval (fun _ => A) ()) q
  equalPub : ℓ < 10 ^ 6 →
    ∀ (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes),
      CryptoGames.SM.MakesAtMostQueries A q →
      CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)
        (prog.eval (fun _ => A) ())
  sendShort : ℓ < 10 ^ 6 →
    ∀ (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes),
      CryptoGames.SM.MakesAtMostQueries A q →
      CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk
        (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
        (prog.eval (fun _ => A) ())
  sm_game_eq : ℓ < 10 ^ 6 →
    ∀ cfg (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes),
      CryptoGames.SM.MakesAtMostQueries A q →
      CryptoGames.SM.game (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
          3 (qep + 1) cfg (prog.eval (fun _ => A) ()) =
        CryptoGames.SM.game (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
          3 (qep + 1) cfg
          (CryptoGames.LibsignalSM.Refine.libsignalToModularSchemeSim (paramsV1 C K idA idB) ℓ
            Dh encPt encT decT (idsOf idA idB) lam qep A)
  simCNoneWinEvent_eq : ℓ < 10 ^ 6 →
    ∀ (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes),
      CryptoGames.SM.MakesAtMostQueries A q →
      CryptoGames.LibsignalSM.Proofs.Refinement.simCNoneWinEvent (paramsV1 C K idA idB) ℓ
          Dh encPt encT decT (idsOf idA idB) lam qep A =
        (do
          let b ← $ᵗ Bool
          let (_, s) ← CryptoGames.SM.run
            (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
            3 (qep + 1) CryptoGames.SM.Config.h1 b (prog.eval (fun _ => A) ())
          return s.win)

private theorem paramsV1_idsOf_eq (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (R : Party) :
    (if R == Party.A then (paramsV1 C K idA idB).idA else (paramsV1 C K idA idB).idB) =
      idsOf idA idB R := by
  cases R <;> rfl

theorem simFig8ProgOfStep_evalOk {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (L qep q B : ℕ) (B_skip? : Option ℕ := none)
    (hqL : q ≤ L) (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hBs : ∀ B_skip, B_skip? = some B_skip → q * 25000 ≤ B_skip)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep : ∀ t (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded L (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simFig8OracleDedup (paramsV1 C K idA idB) Dh encPt encT decT lam qep B B_skip?
        (.inr t)).run (simFullDec s_raw))) :
    SimFig8EvalOk Pt ℓ C K idA idB Dh encPt encT decT lam qep q
      (simFig8ProgOfStep C K Dh encPt encT decT lam step) where
  queries hℓ A hq := by
    rw [simFig8ProgOfStep_eval C K idA idB Dh encPt encT decT lam L qep B B_skip? hℓ step hstep A q hq hqL]
    exact simFig8Clamp_queries (paramsV1 C K idA idB) Dh encPt encT decT lam qep B B_skip? hq
  equalPub hℓ A hq := by
    rw [simFig8ProgOfStep_eval C K idA idB Dh encPt encT decT lam L qep B B_skip? hℓ step hstep A q hq hqL]
    exact simFig8Clamp_equalPub (paramsV1 C K idA idB) Dh encPt encT decT lam qep B B_skip? A
  sendShort hℓ A hq := by
    rw [simFig8ProgOfStep_eval C K idA idB Dh encPt encT decT lam L qep B B_skip? hℓ step hstep A q hq hqL]
    exact simFig8Clamp_sendShort (paramsV1 C K idA idB)
      (lengthsOk_paramsIdsWithSpqr_v1 C K idA idB (by omega))
      Dh encPt encT decT lam qep B B_skip? A
  sm_game_eq hℓ cfg A hq := by
    rw [simFig8ProgOfStep_eval C K idA idB Dh encPt encT decT lam L qep B B_skip? hℓ step hstep A q hq hqL]
    exact sm_game_simFig8Clamp_eq (paramsV1 C K idA idB) Dh encPt encT decT (idsOf idA idB)
      (paramsV1_idsOf_eq C K idA idB) lam qep B B_skip? cfg hq h232 hqB hBs
  simCNoneWinEvent_eq hℓ A hq := by
    rw [simFig8ProgOfStep_eval C K idA idB Dh encPt encT decT lam L qep B B_skip? hℓ step hstep A q hq hqL]
    exact simCNoneWinEvent_eq_sm_run_simFig8Clamp (paramsV1 C K idA idB) Dh encPt encT decT
      (idsOf idA idB) (paramsV1_idsOf_eq C K idA idB) lam qep B B_skip? hq h232 hqB hBs

theorem simFig8ProgOfStep_evalOk_tg {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (L qep q B : ℕ) (B_skip? : Option ℕ := none)
    (hqL : q ≤ L) (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hBs : ∀ B_skip, B_skip? = some B_skip → q * 25000 ≤ B_skip)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep : ∀ t (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded L (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simFig8OracleTGDedup (paramsV1 C K idA idB) Dh encPt encT decT lam qep B B_skip?
        (.inr t)).run (simFullDec s_raw))) :
    SimFig8EvalOk Pt ℓ C K idA idB Dh encPt encT decT lam qep q
      (simFig8ProgOfStep C K Dh encPt encT decT lam step) where
  queries hℓ A hq := by
    rw [simFig8ProgOfStep_eval_tg C K idA idB Dh encPt encT decT lam L qep B B_skip? hℓ step hstep A q hq hqL]
    exact simFig8ClampTG_queries (paramsV1 C K idA idB) Dh encPt encT decT lam qep B B_skip? hq
  equalPub hℓ A hq := by
    rw [simFig8ProgOfStep_eval_tg C K idA idB Dh encPt encT decT lam L qep B B_skip? hℓ step hstep A q hq hqL]
    exact simFig8ClampTG_equalPub (paramsV1 C K idA idB) Dh encPt encT decT lam qep B B_skip? A
  sendShort hℓ A hq := by
    rw [simFig8ProgOfStep_eval_tg C K idA idB Dh encPt encT decT lam L qep B B_skip? hℓ step hstep A q hq hqL]
    exact simFig8ClampTG_sendShort (paramsV1 C K idA idB)
      (lengthsOk_paramsIdsWithSpqr_v1 C K idA idB (by omega))
      Dh encPt encT decT lam qep B B_skip? A
  sm_game_eq hℓ cfg A hq := by
    rw [simFig8ProgOfStep_eval_tg C K idA idB Dh encPt encT decT lam L qep B B_skip? hℓ step hstep A q hq hqL]
    exact sm_game_simFig8ClampTG_eq (paramsV1 C K idA idB) Dh encPt encT decT (idsOf idA idB)
      (paramsV1_idsOf_eq C K idA idB) lam qep B B_skip? cfg hq h232 hqB hBs
  simCNoneWinEvent_eq hℓ A hq := by
    rw [simFig8ProgOfStep_eval_tg C K idA idB Dh encPt encT decT lam L qep B B_skip? hℓ step hstep A q hq hqL]
    exact simCNoneWinEvent_eq_sm_run_simFig8ClampTG (paramsV1 C K idA idB) Dh encPt encT decT
      (idsOf idA idB) (paramsV1_idsOf_eq C K idA idB) lam qep B B_skip? hq h232 hqB hBs

/-- Complete bundle packaging a `simFig8` costed reduction program together with its `GRedBounded`
proof (`ratchetCostBudget q (qep + 1)`), its syntactic `descBits` bound
(`ratchetDescBudget q (qep + 1)`), and its `SimFig8EvalOk` game/refinement contract for all
`(idA, idB)`. -/
structure SimFig8AtomicStepBundle (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) where
  prog : SimFig8RedProg Pt ℓ C K Dh encPt encT decT lam
  gRedBounded : GRedBounded prog (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1))
  descBits_le : atomicFig8RedDescBits prog ≤ ratchetDescBudget q (qep + 1)
  evalOk : ∀ idA idB, SimFig8EvalOk Pt ℓ C K idA idB Dh encPt encT decT lam qep q prog

def SimFig8AtomicStepBundle.ofDedup {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (L qep q B : ℕ) (B_skip? : Option ℕ := none)
    (hqL : q ≤ L) (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B) (hqep : qep ≤ q + 10)
    (hBs : ∀ B_skip, B_skip? = some B_skip → q * 25000 ≤ B_skip)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hstep : ∀ idA idB t (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded L (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simFig8OracleDedup (paramsV1 C K idA idB) Dh encPt encT decT lam qep B B_skip?
        (.inr t)).run (simFullDec s_raw))) :
    SimFig8AtomicStepBundle Pt ℓ C K Dh encPt encT decT lam qep q where
  prog := simFig8ProgOfStep C K Dh encPt encT decT lam step
  gRedBounded := simFig8ProgOfStep_gRedBounded C K Dh encPt encT decT lam qep q step hstep_q hstep_c hstep_d hqep
  descBits_le := simFig8ProgOfStep_descBits_le C K Dh encPt encT decT lam qep q step hstep_d
  evalOk idA idB := simFig8ProgOfStep_evalOk C K idA idB Dh encPt encT decT lam L qep q B B_skip?
    hqL h232 hqB hBs step (hstep idA idB)

def SimFig8AtomicStepBundle.ofTGDedup {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (L qep q B : ℕ) (B_skip? : Option ℕ := none)
    (hqL : q ≤ L) (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B) (hqep : qep ≤ q + 10)
    (hBs : ∀ B_skip, B_skip? = some B_skip → q * 25000 ≤ B_skip)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hstep : ∀ idA idB t (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded L (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simFig8OracleTGDedup (paramsV1 C K idA idB) Dh encPt encT decT lam qep B B_skip?
        (.inr t)).run (simFullDec s_raw))) :
    SimFig8AtomicStepBundle Pt ℓ C K Dh encPt encT decT lam qep q where
  prog := simFig8ProgOfStep C K Dh encPt encT decT lam step
  gRedBounded := simFig8ProgOfStep_gRedBounded C K Dh encPt encT decT lam qep q step hstep_q hstep_c hstep_d hqep
  descBits_le := simFig8ProgOfStep_descBits_le C K Dh encPt encT decT lam qep q step hstep_d
  evalOk idA idB := simFig8ProgOfStep_evalOk_tg C K idA idB Dh encPt encT decT lam L qep q B B_skip?
    hqL h232 hqB hBs step (hstep idA idB)

def SimFig8AtomicStepBundle.ofDedupLinear {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (L qep q B : ℕ) (B_skip? : Option ℕ := none)
    (hqL : q ≤ L) (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B) (hqep : qep ≤ q + 10)
    (hBs : ∀ B_skip, B_skip? = some B_skip → q * 25000 ≤ B_skip)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hstep : ∀ idA idB t (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded L (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simFig8OracleDedup (paramsV1 C K idA idB) Dh encPt encT decT lam qep B B_skip?
        (.inr t)).run (simFullDec s_raw))) :
    SimFig8AtomicStepBundle Pt ℓ C K Dh encPt encT decT lam qep q where
  prog := simFig8ProgOfStep C K Dh encPt encT decT lam step
  gRedBounded := simFig8ProgOfStep_gRedBounded_linear C K Dh encPt encT decT lam qep q step hstep_q hstep_c hstep_d hqep
  descBits_le := simFig8ProgOfStep_descBits_le C K Dh encPt encT decT lam qep q step hstep_d
  evalOk idA idB := simFig8ProgOfStep_evalOk C K idA idB Dh encPt encT decT lam L qep q B B_skip?
    hqL h232 hqB hBs step (hstep idA idB)

def SimFig8AtomicStepBundle.ofTGDedupLinear {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (L qep q B : ℕ) (B_skip? : Option ℕ := none)
    (hqL : q ≤ L) (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B) (hqep : qep ≤ q + 10)
    (hBs : ∀ B_skip, B_skip? = some B_skip → q * 25000 ≤ B_skip)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hstep : ∀ idA idB t (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded L (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simFig8OracleTGDedup (paramsV1 C K idA idB) Dh encPt encT decT lam qep B B_skip?
        (.inr t)).run (simFullDec s_raw))) :
    SimFig8AtomicStepBundle Pt ℓ C K Dh encPt encT decT lam qep q where
  prog := simFig8ProgOfStep C K Dh encPt encT decT lam step
  gRedBounded := simFig8ProgOfStep_gRedBounded_linear C K Dh encPt encT decT lam qep q step hstep_q hstep_c hstep_d hqep
  descBits_le := simFig8ProgOfStep_descBits_le C K Dh encPt encT decT lam qep q step hstep_d
  evalOk idA idB := simFig8ProgOfStep_evalOk_tg C K idA idB Dh encPt encT decT lam L qep q B B_skip?
    hqL h232 hqB hBs step (hstep idA idB)

end AtomicStepBundle


end ClampingAndHeadline

end SimFig8ClampAndEval

end Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
