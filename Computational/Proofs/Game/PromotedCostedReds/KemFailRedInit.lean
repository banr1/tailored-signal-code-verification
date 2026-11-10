/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
import Computational.Proofs.E2E.Dsl.ClampsLossless
import Computational.Proofs.ReductionDsl.FsAtomicMacros
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync

/-!
# Atomic Initializer and State Encodings for `KemFailRed`

Defines the `atomicSessionOps` state encodings (`kemFailStateT`), initializer `kemFailInitC`, and
candidate extractor `kemFailFinishOptE` for `KemFailRed`, and proves state-encoding roundtrips and
exact `.eval` relations.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp bytesToWordLE bits
  atomicSig atomicSessionOps coinOnlyIface
  B U8 U32 U64 BV256 BV512 PlainT
  lpubT lpubV lpubOfV fig8CtT fig8CtV fig8CtOfV fig8StT fig8StV fig8StOfV)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoGames.Ratchet.LibsignalInst (lFig8 LibsignalMsgPublicPart)
open CryptoGames.Ratchet.LibsignalSim (SimKemSeed SimKemEncRand SimKemCoins SimKemFailTrack
  simInitKemFailTrack simDefaultKemCand KemExtraRaw fig8GsTy Fig8St Fig8C
  SimOp simOpsUnitCost kemTrackEnc)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC)
open CryptoGames.LibsignalSM.Proofs.Refinement (KemFailTrackState initKemFailTrack)
open CryptoGames.SM (Pos Record GameState initState posTy posEnc posDec posDec_posEnc)
open CryptoGames.LibsignalSession (Crypto ShaCompress IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State spqrV1Init coinBytes coinBytes_length)
open CryptoVerification.E2E (Bytes idsOf paramsV1)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (sessPureOp sessSpqrKemOp
  eval_sessPureOp cost_sessPureOp eval_sessSpqrKemOp cost_sessSpqrKemOp)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State (eLet eval_eLet cost_eLet
  descBits_eLet atomicTyDescBits_posTy atomicTyDescBits_fig8CtT atomicTyDescBits_fig8StT
  atomicTyDescBits_simFullT bits_eq_of_bounds)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost (simFullT simFullEnc
  simFullDec initSimCE eval_initSimCE cost_initSimCE atomicSpqrV1InitOp_lossless
  fig8CtOfV_fig8CtV fig8StOfV_fig8StV)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept (fig8InitAtomicE
  fig8InitAtomicE_eval fig8InitAtomicE_cost fig8InitAtomicE_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost (kemCandBvToVec
  kemCandVecToBv kemCandBvToVec_kemCandVecToBv kemCandVecToBv_kemCandBvToVec
  coinBytes_bytesToWordLE512 keyToBytes32_bytesToWordLE256
  bytesToWordLE512_coinBytes bytesToWordLE256_keyToBytes32
  kemFailInitCoinsC kemFailInitCoinsC_queries_zero kemFailInitCoinsC_cost
  kemFailInitCoinsC_eval kemFailInitCoinsC_descBits_le
  kemFailClampInitState kemFailSimInitState
  atomicSortDescBits atomicTyDescBits varIdx atomicPureOpDescBits
  atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)

/-! ## State types and encodings -/

@[reducible] def fig8RecT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod posTy
    (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt)))
      (fig8CtT (ℓ := ℓ) (Pt := Pt)))

@[reducible] def fig8MirT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .bool
    (.prod .bool
      (.prod (.prod .nat .nat)
        (.prod (.prod .nat .nat)
          (.prod (.opt .nat)
            (.prod (.list (fig8RecT ℓ Pt))
              (.prod (.list posTy)
                (.prod (.list posTy)
                  (.prod (.prod (.tbl .nat) (.tbl .nat))
                    (.prod (.list .nat)
                      (.list (.prod .bool .nat)))))))))))

/-- Full `Fig8` mirror `GameState` encoded in `atomicSig ℓ Pt`. -/
@[reducible] def fig8GsT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8StT (ℓ := ℓ) (Pt := Pt))) (fig8MirT ℓ Pt)

@[reducible] def kemCoinsT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .sum .unit (.sum (BV512 (ℓ := ℓ) (Pt := Pt)) (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) (BV256 (ℓ := ℓ) (Pt := Pt))))

@[reducible] def kemSentEntryT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.prod (U64 (ℓ := ℓ) (Pt := Pt)) (B (ℓ := ℓ) (Pt := Pt) 64)) (U32 (ℓ := ℓ) (Pt := Pt))

/-- `SimKemFailTrack` state encoded in `atomicSig ℓ Pt`. -/
@[reducible] def kemTrackT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (U64 (ℓ := ℓ) (Pt := Pt))
    (.prod (kemCoinsT ℓ Pt)
      (.prod (.prod (B (ℓ := ℓ) (Pt := Pt) 32) (B (ℓ := ℓ) (Pt := Pt) 32))
        (.prod (.list (kemSentEntryT ℓ Pt))
          (.prod (.prod (.tbl .nat) (.tbl .nat))
            (.opt (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) (BV256 (ℓ := ℓ) (Pt := Pt))))))))

/-- Combined `KemFailRed` state `(sC, (gFig, tr))` encoded in `atomicSig ℓ Pt`. -/
@[reducible] def kemFailStateT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt) (.prod (fig8GsT ℓ Pt) (kemTrackT ℓ Pt))

section StateEncodings

variable {ℓ : ℕ} {Pt : Type}

def fig8RecEnc (r : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (fig8RecT ℓ Pt).denote :=
  (posEnc r.pos, ((lpubV r.msg.1, r.msg.2), fig8CtV r.ct))

def fig8RecDec (v : (fig8RecT ℓ Pt).denote) :
    Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
  ⟨posDec v.1, (lpubOfV v.2.1.1, v.2.1.2), fig8CtOfV v.2.2⟩

def fig8GsEnc (g : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (fig8GsT ℓ Pt).denote :=
  ((fig8StV (g.st .A), fig8StV (g.st .B)),
   (g.b,
    (g.win,
     ((g.epoch .A, g.epoch .B),
      ((g.idx .A, g.idx .B),
       (g.tL,
        (g.trans.map fig8RecEnc,
         (g.chall.map posEnc,
          (g.comp.map posEnc,
           ((g.maxAcc .A, g.maxAcc .B),
            (g.leaks,
             g.corrs.map fun (p, e) => (CryptoGames.SM.partyEnc p, e))))))))))))

def fig8GsDec (v : (fig8GsT ℓ Pt).denote) :
    GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
  let ((stA, stB), (b, (win, ((epA, epB), ((iA, iB), (tL, (trs, (chall, (comp,
    ((mA, mB), (leaks, corrs))))))))))) := v
  { st := fun | .A => fig8StOfV stA | .B => fig8StOfV stB
    b := b
    win := win
    epoch := fun | .A => epA | .B => epB
    idx := fun | .A => iA | .B => iB
    tL := tL
    trans := trs.map fig8RecDec
    chall := chall.map posDec
    comp := comp.map posDec
    maxAcc := fun | .A => mA | .B => mB
    leaks := leaks
    corrs := corrs.map fun (p, e) => (CryptoGames.SM.partyDec p, e) }

def fig8ClampGsEnc (g : (@fig8GsTy Bytes (BitVec 512) Pt ℓ).denote) : (fig8GsT ℓ Pt).denote :=
  let ((stA, stB), (b, (win, ((epA, epB), ((iA, iB), (tL, (trs, (chall, (comp,
    ((mA, mB), (leaks, corrs))))))))))) := g
  ((fig8StV stA, fig8StV stB),
   (b, (win, ((epA, epB), ((iA, iB), (tL,
    (trs.map (fun (p, ((lp, m), ct)) => (p, ((lpubV lp, m), fig8CtV ct))),
     (chall, (comp, ((mA, mB), (leaks, corrs)))))))))))

def kemCoinsAtomicEnc : SimKemCoins → (kemCoinsT ℓ Pt).denote
  | .init => .inl ()
  | .seed s => .inr (.inl (bytesToWordLE 512 s.toList))
  | .both s r => .inr (.inr (bytesToWordLE 512 s.toList, bytesToWordLE 256 r.toList))

def kemCoinsAtomicDec : (kemCoinsT ℓ Pt).denote → SimKemCoins
  | .inl () => .init
  | .inr (.inl s) => .seed ⟨coinBytes s, coinBytes_length s⟩
  | .inr (.inr (s, r)) => .both ⟨coinBytes s, coinBytes_length s⟩ (keyToBytesVec32 r)

def kemTrackAtomicEnc {F : ShaCompress} (tr : SimKemFailTrack F) : (kemTrackT ℓ Pt).denote :=
  (tr.e,
   (kemCoinsAtomicEnc tr.c,
    ((V1State.encodeRaw (tr.st .A).into_pb, V1State.encodeRaw (tr.st .B).into_pb),
     (tr.sentB.map (fun (m, ctr) => ((m.epoch, _root_.ReductionDsl.spqrMsgPayloadSuffix m), ctr)),
      ((tr.sendCtr .A, tr.sendCtr .B),
       tr.cand.map kemCandVecToBv)))))

def kemFailClampStateEnc [Zero Pt]
    (s : LibsignalToModularSchemeSimState Bytes Pt ℓ × KemExtraRaw Bytes (BitVec 512) Pt ℓ) :
    (kemFailStateT ℓ Pt).denote :=
  (simFullEnc s.1, (fig8ClampGsEnc s.2.1, kemTrackAtomicEnc s.2.2.1.2))

def kemFailSimStateEnc {F : ShaCompress}
    (s : LibsignalToModularSchemeSimState Bytes Pt ℓ ×
      (GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
      KemFailTrackState F) :
    (kemFailStateT ℓ Pt).denote :=
  (simFullEnc s.1, (fig8GsEnc s.2.1.1, kemTrackAtomicEnc (kemTrackEnc s.2.2)))

end StateEncodings

/-! ## Atomic initializer and finish expressions -/

section AtomicInit

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

def initSimCAtomicE {Γ : List (Ty ASig)} (pqrKeyE : Expr AOps Γ BV256) :
    Expr AOps Γ (simFullT ℓ Pt) :=
  eLet pqrKeyE
    (initSimCE
      (sessSpqrKemOp .spqrV1InitOp (.pair (.bool true) (.var .zero)))
      (sessSpqrKemOp .spqrV1InitOp (.pair (.bool false) (.var .zero))))

def initFig8MirAtomicE {O' : Ops ASig} {Γ : List (Ty ASig)} (bE : Expr O' Γ .bool) :
    Expr O' Γ (fig8MirT ℓ Pt) :=
  .pair bE
    (.pair (.bool false)
      (.pair (.pair (.nat 0) (.nat 0))
        (.pair (.pair (.nat 0) (.nat 0))
          (.pair .none
            (.pair .nil
              (.pair .nil
                (.pair .nil
                  (.pair (.pair (.tconst (.nat 0)) (.tconst (.nat 0)))
                    (.pair .nil .nil)))))))))

def initFig8GsAtomicE (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (bE : Expr AOps Γ .bool) (k1E k2E : Expr AOps Γ BV256) :
    Expr AOps Γ (fig8GsT ℓ Pt) :=
  .pair (fig8InitAtomicE idA idB (.pair k1E k2E)) (initFig8MirAtomicE bE)

def initV1BraidStAtomicE (isAlice : Bool) {Γ : List (Ty ASig)}
    (pqrKeyE : Expr AOps Γ BV256) : Expr AOps Γ (B 32) :=
  let ver1 := sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (.u8Lit 1#8) .unit
  let dirE := sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (.u32Lit (if isAlice then 0#32 else 1#32)) .unit
  let authKeyE := sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) .bv256ToBytes32 pqrKeyE
  .caseOpt (.snd (sessSpqrKemOp .spqrNegotiateInit (.pair ver1 (.pair dirE authKeyE))))
    (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.bytesLit 32 []) .unit)
    (.caseOpt (.var .zero)
      (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (.bytesLit 32 []) .unit)
      (.var .zero))

def initKemTrackAtomicE {Γ : List (Ty ASig)} (pqrKeyE : Expr AOps Γ BV256) :
    Expr AOps Γ (kemTrackT ℓ Pt) :=
  eLet pqrKeyE
    (let e1 := sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
       (decT := decT) (lam := lam) (.u64Lit 1#64) .unit
     let c0 : Expr AOps (BV256 :: Γ) (kemCoinsT ℓ Pt) := .inl .unit
     let v1A := initV1BraidStAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
       (encT := encT) (decT := decT) (lam := lam) true (.var .zero)
     let v1B := initV1BraidStAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
       (encT := encT) (decT := decT) (lam := lam) false (.var .zero)
     .pair e1
       (.pair c0
         (.pair (.pair v1A v1B)
           (.pair .nil
             (.pair (.pair (.tconst (.nat 0)) (.tconst (.nat 0)))
               .none)))))

def kemFailMkInitE (idA idB : IdentityKey) :
    Expr AOps [BV256, BV256, BV256, .bool, .unit] (kemFailStateT ℓ Pt) :=
  let pqrKeyE : Expr AOps [BV256, BV256, BV256, .bool, .unit] BV256 := .var .zero
  let k2E : Expr AOps [BV256, BV256, BV256, .bool, .unit] BV256 := .var (.succ .zero)
  let k1E : Expr AOps [BV256, BV256, BV256, .bool, .unit] BV256 := .var (.succ (.succ .zero))
  let bE : Expr AOps [BV256, BV256, BV256, .bool, .unit] .bool :=
    .var (.succ (.succ (.succ .zero)))
  .pair (initSimCAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) pqrKeyE)
    (.pair (initFig8GsAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB bE k1E k2E)
      (initKemTrackAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) pqrKeyE))

/-- Atomic `init` computation for `KemFailRed` over `coinOnlyIface ℓ Pt`. -/
def kemFailInitC (idA idB : IdentityKey) :
    Comp AOps (coinOnlyIface ℓ Pt) [.unit] (.prod .unit (kemFailStateT ℓ Pt)) :=
  kemFailInitCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (kemFailMkInitE idA idB)

/-- Candidate extractor projecting `tr.cand` from `kemFailStateT ℓ Pt`. -/
def kemFailFinishOptE : Expr AOps [kemFailStateT ℓ Pt, .bool] (.opt (.prod BV512 BV256)) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.var .zero)))))))

end AtomicInit

/-! ## Encoding roundtrips and evaluation relations -/

section EvalAndEncodings

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem fig8RecDec_fig8RecEnc
    (r : Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    fig8RecDec (fig8RecEnc r) = r := by
  rcases r with ⟨pos, ⟨lp, m⟩, ct⟩
  simp [fig8RecEnc, fig8RecDec, posDec_posEnc, fig8CtOfV_fig8CtV]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem fig8GsDec_fig8GsEnc
    (g : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    fig8GsDec (fig8GsEnc g) = g := by
  rcases g with ⟨st, ep, idx, tL, trs, chall, comp, mAcc, b, win, leaks, corrs⟩
  simp only [fig8GsEnc, fig8GsDec, List.map_map]
  have hst : (fun x => match x with
      | .A => fig8StOfV (ℓ := ℓ) (fig8StV (st .A))
      | .B => fig8StOfV (ℓ := ℓ) (fig8StV (st .B))) = st := by
    funext p; cases p <;> simp [fig8StOfV_fig8StV]
  have hep : (fun x => match x with | .A => ep .A | .B => ep .B) = ep := by
    funext p; cases p <;> rfl
  have hidx : (fun x => match x with | .A => idx .A | .B => idx .B) = idx := by
    funext p; cases p <;> rfl
  have hmAcc : (fun x => match (motive := Party → ℕ → ℕ) x with | .A => mAcc .A | .B => mAcc .B) = mAcc := by
    funext p; cases p <;> rfl
  have htrs : (fig8RecDec (ℓ := ℓ) (Pt := Pt) ∘ fig8RecEnc) = id := by
    funext r; exact fig8RecDec_fig8RecEnc r
  have hpos : (posDec ∘ posEnc) = id := by
    funext p; exact posDec_posEnc p
  have hcorrs : ((fun (x : Bool × ℕ) => (CryptoGames.SM.partyDec x.1, x.2)) ∘
      (fun (x : Party × ℕ) => (CryptoGames.SM.partyEnc x.1, x.2))) = id := by
    funext ⟨p, e⟩; simp [CryptoGames.SM.partyDec_partyEnc]
  rw [hst, hep, hidx, hmAcc, htrs, hpos, hcorrs, List.map_id, List.map_id, List.map_id, List.map_id]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem kemCoinsAtomicDec_kemCoinsAtomicEnc (c : SimKemCoins) :
    kemCoinsAtomicDec (ℓ := ℓ) (Pt := Pt) (kemCoinsAtomicEnc c) = c := by
  cases c with
  | init => rfl
  | seed s =>
    have h := kemCandBvToVec_kemCandVecToBv (s, ⟨List.replicate 32 0, by simp⟩)
    injection h with h1 _
    dsimp only [kemCoinsAtomicEnc, kemCoinsAtomicDec]
    dsimp only [kemCandVecToBv, kemCandBvToVec] at h1
    exact congrArg SimKemCoins.seed h1
  | both s r =>
    have h := kemCandBvToVec_kemCandVecToBv (s, r)
    injection h with h1 h2
    dsimp only [kemCoinsAtomicEnc, kemCoinsAtomicDec]
    dsimp only [kemCandVecToBv, kemCandBvToVec] at h1 h2
    rw [h1, h2]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem kemCoinsAtomicEnc_kemCoinsAtomicDec (v : (kemCoinsT ℓ Pt).denote) :
    kemCoinsAtomicEnc (kemCoinsAtomicDec (ℓ := ℓ) (Pt := Pt) v) = v := by
  rcases v with ⟨⟩ | s | ⟨s, r⟩
  · rfl
  · have h := kemCandVecToBv_kemCandBvToVec (s, (0 : BitVec 256))
    injection h with h1 _
    simpa [kemCoinsAtomicEnc, kemCoinsAtomicDec, kemCandVecToBv, kemCandBvToVec] using h1
  · simpa [kemCoinsAtomicEnc, kemCoinsAtomicDec, kemCandVecToBv, kemCandBvToVec] using
      kemCandVecToBv_kemCandBvToVec (s, r)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem kemTrackEnc_initKemFailTrack (F : ShaCompress) (pqrKey : BitVec 256) :
    kemTrackEnc (initKemFailTrack F pqrKey) = simInitKemFailTrack F pqrKey :=
  rfl

omit [SampleableType Pt] in
theorem initSimCAtomicE_eval {Γ : List (Ty ASig)} (pqrKeyE : Expr AOps Γ BV256) (ρ : Env Γ) :
    (initSimCAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) pqrKeyE).eval ρ =
    simFullEnc (ℓ := ℓ) (Pt := Pt)
      (initSimC (spqrV1Init C.F K .a2b (pqrKeyE.eval ρ))
                (spqrV1Init C.F K .b2a (pqrKeyE.eval ρ))) := by
  rw [initSimCAtomicE, eval_eLet, eval_initSimCE, eval_sessSpqrKemOp, eval_sessSpqrKemOp]
  dsimp only [Expr.eval, Env.get, _root_.ReductionDsl.AtomicSpqrKemOp.eval]
  rw [atomicSpqrV1InitOp_lossless C K true, atomicSpqrV1InitOp_lossless C K false]
  rfl

omit [SampleableType Pt] in
theorem initFig8GsAtomicE_eval_clamp (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (bE : Expr AOps Γ .bool) (k1E k2E : Expr AOps Γ BV256) (ρ : Env Γ) :
    (initFig8GsAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB bE k1E k2E).eval ρ =
    fig8ClampGsEnc (ℓ := ℓ) (Pt := Pt)
      (((simOpsUnitCost (ℓ := ℓ) (paramsV1 C K idA idB) Dh encPt encT decT lam K id).eval
          SimOp.fig8Init (k1E.eval ρ, k2E.eval ρ)),
       (bE.eval ρ, false, (0, 0), (0, 0), none, [], [], [], (fun _ => 0, fun _ => 0), [], [])) := by
  have hfig := fig8InitAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (.pair k1E k2E) ρ
  have hpC : (paramsV1 C K idA idB).C = C := rfl
  have hpCodec : (paramsV1 C K idA idB).codec = CryptoVerification.LibsignalProtoCodec.protoSignalCodec := rfl
  have hpA : (paramsV1 C K idA idB).idA = idA := rfl
  have hpB : (paramsV1 C K idA idB).idB = idB := rfl
  dsimp only [initFig8GsAtomicE, initFig8MirAtomicE, Expr.eval]
  rw [hfig]
  dsimp only [Expr.eval, fig8ClampGsEnc, List.map, simOpsUnitCost,
    CryptoGames.Ratchet.LibsignalSim.simParamOps]
  rw [hpC, hpCodec, hpA, hpB]

omit [SampleableType Pt] in
theorem initFig8GsAtomicE_eval_sim (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (bE : Expr AOps Γ .bool) (k1E k2E : Expr AOps Γ BV256) (ρ : Env Γ) :
    (initFig8GsAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB bE k1E k2E).eval ρ =
    fig8GsEnc (ℓ := ℓ) (Pt := Pt)
      (initState (lFig8 Dh encPt (paramsV1 C K idA idB).C (paramsV1 C K idA idB).codec ℓ
        encT (idsOf idA idB) 25000 lam) (k1E.eval ρ, k2E.eval ρ) (bE.eval ρ)) := by
  have hfig := fig8InitAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (.pair k1E k2E) ρ
  have hpC : (paramsV1 C K idA idB).C = C := rfl
  have hpCodec : (paramsV1 C K idA idB).codec = CryptoVerification.LibsignalProtoCodec.protoSignalCodec := rfl
  have hid : (fun R => if R == Party.A then idA else idB) = idsOf idA idB := by
    funext R; cases R <;> rfl
  dsimp only [initFig8GsAtomicE, initFig8MirAtomicE, Expr.eval]
  rw [hfig, hpC, hpCodec, hid]
  dsimp only [Expr.eval, fig8GsEnc, initState, List.map]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem eval_caseOpt_snd_some_some {O' : Ops ASig} {Γ : List (Ty ASig)} {τ : Ty ASig}
    (e : Expr O' Γ (.prod .bool (.opt (.opt τ))))
    (d1 : Expr O' Γ τ) (d2 : Expr O' (.opt τ :: Γ) τ)
    (ρ : Env Γ) (b : Bool) (v : τ.denote) (he : e.eval ρ = (b, some (some v))) :
    (Expr.caseOpt (.snd e) d1 (.caseOpt (.var .zero) d2 (.var .zero))).eval ρ = v := by
  dsimp only [Expr.eval]
  rw [he]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem eval_pair_eq {O' : Ops ASig} {Γ : List (Ty ASig)} {α β : Ty ASig}
    (a : Expr O' Γ α) (b : Expr O' Γ β) (ρ : Env Γ) :
    (Expr.pair a b).eval ρ = (a.eval ρ, b.eval ρ) := rfl

omit [SampleableType Pt] in
theorem initV1BraidStAtomicE_eval (isAlice : Bool) {Γ : List (Ty ASig)}
    (pqrKeyE : Expr AOps Γ BV256) (ρ : Env Γ) :
    (initV1BraidStAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) isAlice pqrKeyE).eval ρ =
    V1State.encodeRaw
      (((simInitKemFailTrack C.F (pqrKeyE.eval ρ)).st (if isAlice then .A else .B)).into_pb) := by
  have hv1 : (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.u8Lit 1#8) .unit).eval ρ = 1#8 := by
    rw [eval_sessPureOp]; rfl
  have hdir : (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.u32Lit (if isAlice then 0#32 else 1#32)) .unit).eval ρ =
      (if isAlice then 0#32 else 1#32) := by
    rw [eval_sessPureOp]; rfl
  have hkey : (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .bv256ToBytes32 pqrKeyE).eval ρ =
      keyToBytes32 (pqrKeyE.eval ρ) := by
    rw [eval_sessPureOp]; rfl
  have hop : (sessSpqrKemOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .spqrNegotiateInit
      (.pair (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) (.u8Lit 1#8) .unit)
        (.pair (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) (.u32Lit (if isAlice then 0#32 else 1#32)) .unit)
          (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) .bv256ToBytes32 pqrKeyE)))).eval ρ =
    (false, some (some (V1State.encodeRaw
      (((simInitKemFailTrack C.F (pqrKeyE.eval ρ)).st (if isAlice then .A else .B)).into_pb)))) := by
    rw [eval_sessSpqrKemOp, eval_pair_eq, eval_pair_eq, hv1, hdir, hkey]
    dsimp only [_root_.ReductionDsl.AtomicSpqrKemOp.eval]
    have hEq : _root_.ReductionDsl.spqrNegotiateInitEval (ℓ := ℓ) (Pt := Pt) C.F K 1#8
        (if isAlice then 0#32 else 1#32) (keyToBytes32 (pqrKeyE.eval ρ)) =
      CryptoVerification.E2E.Costed.spqrNegotiateInitEval (ℓ := ℓ) C.F K 1#8
        (if isAlice then 0#32 else 1#32) (keyToBytes32 (pqrKeyE.eval ρ)) := rfl
    rw [hEq, Computational.Proofs.E2E.Dsl.ClampsLossless.spqrNegotiateInitEval_clamp_lossless]
    have hv : CryptoVerification.LibsignalSpqrV1.Version.fromU8? 1#8 = some .v1 := rfl
    cases isAlice
    · have hd : CryptoVerification.LibsignalSpqrV1.Direction.fromI32?
          (if false = true then 0#32 else 1#32) = some .b2a := rfl
      have hdec : CryptoVerification.LibsignalSpqrV1.spqrPolyApi.decoder_new 96 =
          .ok (.ok (CryptoVerification.SpqrV1Sync.InSync.freshDec 96)) := by
        simp only [CryptoVerification.LibsignalSpqrV1.spqrPolyApi,
          CryptoVerification.SpqrV1Sync.InSync.decoderNew_eq 96 (by decide), Except.mapError]
      have hinit : CryptoVerification.LibsignalSpqrV1.initInner
          (CryptoVerification.LibsignalSpqrV1.spqrDeps C.F K) .v1 .b2a
          (keyToBytes32 (pqrKeyE.eval ρ)) =
          .ok (some (((simInitKemFailTrack C.F (pqrKeyE.eval ρ)).st .B).into_pb)) := by
        unfold CryptoVerification.LibsignalSpqrV1.initInner
        dsimp only [CryptoVerification.LibsignalSpqrV1.spqrDeps,
          CryptoVerification.LibsignalSpqrV1.spqrAuthApi,
          CryptoVerification.LibsignalSpqrV1.States.init_b,
          CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.new,
          CryptoVerification.LibsignalSpqrV1.HEADER_SIZE,
          CryptoVerification.LibsignalSpqrV1.AUTHENTICATOR_MACSIZE]
        rw [hdec]
        rfl
      unfold Computational.Proofs.E2E.Dsl.ClampsLossless.spqrNegotiateInitRaw
      rw [hv, hd]
      dsimp only
      rw [hinit]
      rfl
    · have hd : CryptoVerification.LibsignalSpqrV1.Direction.fromI32?
          (if true = true then 0#32 else 1#32) = some .a2b := rfl
      have hinit : CryptoVerification.LibsignalSpqrV1.initInner
          (CryptoVerification.LibsignalSpqrV1.spqrDeps C.F K) .v1 .a2b
          (keyToBytes32 (pqrKeyE.eval ρ)) =
          .ok (some (((simInitKemFailTrack C.F (pqrKeyE.eval ρ)).st .A).into_pb)) := rfl
      unfold Computational.Proofs.E2E.Dsl.ClampsLossless.spqrNegotiateInitRaw
      rw [hv, hd]
      dsimp only
      rw [hinit]
      rfl
  exact eval_caseOpt_snd_some_some _ _ _ ρ false _ hop

omit [SampleableType Pt] in
theorem initKemTrackAtomicE_eval {Γ : List (Ty ASig)}
    (pqrKeyE : Expr AOps Γ BV256) (ρ : Env Γ) :
    (initKemTrackAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) pqrKeyE).eval ρ =
    kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (simInitKemFailTrack C.F (pqrKeyE.eval ρ)) := by
  rw [initKemTrackAtomicE, eval_eLet, eval_pair_eq, eval_pair_eq, eval_pair_eq,
    eval_pair_eq, eval_pair_eq, eval_pair_eq, eval_pair_eq,
    eval_sessPureOp, initV1BraidStAtomicE_eval, initV1BraidStAtomicE_eval]
  have hv0 : (Expr.var (O := AOps) .zero).eval (Env.cons (pqrKeyE.eval ρ) ρ) = pqrKeyE.eval ρ := rfl
  rw [hv0]
  dsimp only [Expr.eval, _root_.ReductionDsl.AtomicPureOp.eval, kemTrackAtomicEnc, kemCoinsAtomicEnc]
  simp only [ite_true, Bool.false_eq_true, ite_false, simInitKemFailTrack, List.map_nil, Option.map_none]

omit [SampleableType Pt] in
theorem kemFailMkInitE_eval_clamp (idA idB : IdentityKey) (b : Bool) (k1 k2 pqrKey : BitVec 256) :
    (kemFailMkInitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB).eval
      (.cons pqrKey (.cons k2 (.cons k1 (.cons b (.cons () .nil))))) =
    kemFailClampStateEnc
      (kemFailClampInitState (paramsV1 C K idA idB) Dh encPt encT decT lam K b k1 k2 pqrKey) := by
  let ρ0 : Env ([BV256, BV256, BV256, .bool, .unit] : List (Ty ASig)) :=
    .cons pqrKey (.cons k2 (.cons k1 (.cons b (.cons () .nil))))
  have hg0 : ρ0.get .zero = pqrKey := rfl
  have hg1 : ρ0.get (.succ .zero) = k2 := rfl
  have hg2 : ρ0.get (.succ (.succ .zero)) = k1 := rfl
  have hg3 : ρ0.get (.succ (.succ (.succ .zero))) = b := rfl
  rw [kemFailMkInitE, eval_pair_eq, eval_pair_eq,
    initSimCAtomicE_eval, initFig8GsAtomicE_eval_clamp, initKemTrackAtomicE_eval]
  dsimp only [Expr.eval]
  rw [hg0, hg1, hg2, hg3]
  have hpSpqr : (paramsV1 C K idA idB).spqr.init = spqrV1Init C.F K := rfl
  have hpCF : (paramsV1 C K idA idB).C.F = C.F := rfl
  dsimp only [kemFailClampStateEnc, kemFailClampInitState,
    simOpsUnitCost, CryptoGames.Ratchet.LibsignalSim.simParamOps]
  rw [hpSpqr, hpCF]

omit [SampleableType Pt] in
theorem kemFailMkInitE_eval_sim (idA idB : IdentityKey) (b : Bool) (k1 k2 pqrKey : BitVec 256) :
    (kemFailMkInitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB).eval
      (.cons pqrKey (.cons k2 (.cons k1 (.cons b (.cons () .nil))))) =
    kemFailSimStateEnc
      (kemFailSimInitState (paramsV1 C K idA idB) Dh encPt encT (idsOf idA idB) lam b k1 k2 pqrKey) := by
  let ρ0 : Env ([BV256, BV256, BV256, .bool, .unit] : List (Ty ASig)) :=
    .cons pqrKey (.cons k2 (.cons k1 (.cons b (.cons () .nil))))
  have hg0 : ρ0.get .zero = pqrKey := rfl
  have hg1 : ρ0.get (.succ .zero) = k2 := rfl
  have hg2 : ρ0.get (.succ (.succ .zero)) = k1 := rfl
  have hg3 : ρ0.get (.succ (.succ (.succ .zero))) = b := rfl
  rw [kemFailMkInitE, eval_pair_eq, eval_pair_eq,
    initSimCAtomicE_eval, initFig8GsAtomicE_eval_sim, initKemTrackAtomicE_eval]
  dsimp only [Expr.eval]
  rw [hg0, hg1, hg2, hg3]
  have hpSpqr : (paramsV1 C K idA idB).spqr.init = spqrV1Init C.F K := rfl
  have hpCF : (paramsV1 C K idA idB).C.F = C.F := rfl
  dsimp only [kemFailSimStateEnc, kemFailSimInitState]
  rw [kemTrackEnc_initKemFailTrack, hpSpqr, hpCF]

theorem kemFailInitC_eval_clamp (idA idB : IdentityKey) :
    (kemFailInitC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB).eval (.cons () .nil) =
    (do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      let pqrKey ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      return ((), kemFailClampStateEnc
        (kemFailClampInitState (paramsV1 C K idA idB) Dh encPt encT decT lam K b k1 k2 pqrKey))) := by
  rw [kemFailInitC, kemFailInitCoinsC_eval]
  simp only [kemFailMkInitE_eval_clamp]

theorem kemFailInitC_eval_sim (idA idB : IdentityKey) :
    (kemFailInitC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB).eval (.cons () .nil) =
    (do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      let pqrKey ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      return ((), kemFailSimStateEnc
        (kemFailSimInitState (paramsV1 C K idA idB) Dh encPt encT (idsOf idA idB) lam b k1 k2 pqrKey))) := by
  rw [kemFailInitC, kemFailInitCoinsC_eval]
  simp only [kemFailMkInitE_eval_sim]

omit [SampleableType Pt] in
@[simp] theorem kemFailFinishOptE_eval (s : (kemFailStateT ℓ Pt).denote) (b : Bool) :
    (kemFailFinishOptE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)).eval (.cons s (.cons b .nil)) =
    s.2.2.2.2.2.2.2 := rfl

end EvalAndEncodings

end Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit
