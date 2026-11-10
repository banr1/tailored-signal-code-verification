/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize

/-!
# Tracker-Halted `spkLeakRed` Combinators and Cost/Size Bounds

Defines the `ReductionDsl` state encodings, initializer `spkInitHaltedC`, unified send/challenge
handler `spkSendOrChallHaltedC`, and deliver handler `spkDlArmHaltedC` over `atomicSessionOps`,
together with query, cost, and size bounds.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProgSub

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Samplers Iface Expr Comp
  UniformSamplerTag bits atomicSig atomicSessionOps atomicSamplers atomicPrfIface
  extractPtPrfIface BV256 BV512 U32 U64 PtT PK GhostStT PlainT B smQT smRT recvResultT)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (Pos Record RecvResult GameState partyEnc posTy posEnc orE boolEq otherE pGet pSet)
open CryptoGames.LibsignalSession (Crypto ShaCompress IdentityKey PublicKey GhostState)
open CryptoGames.Ratchet.LibsignalSim (SimKemFailTrack)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes configRefuseEarlyBobCorr)
open CryptoVerification.E2E.Costed (e2eSig e2eOps)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendC drSendC_queries drSendC_cost)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (e2eGsTy e2eGsEnc e2eGsSt e2eGsB
  e2eGsWin e2eGsEpoch e2eGsIdx smRWireE eval_smRWireE cost_smRWireE
  e2eSendOKE eval_e2eSendOKE cost_e2eSendOKE_le
  e2eEpMgmtE eval_e2eEpMgmtE cost_e2eEpMgmtE_le
  e2eSafeChE eval_e2eSafeChE cost_e2eSafeChE_le
  e2eRecordE eval_e2eRecordE cost_e2eRecordE_le)
open Computational.Proofs.E2E.Dsl.DrSessionSim (mkE2ECoinSamplers
  e2eSamIfNec512C e2eSamIfNec512C_queries_zero
  e2eSamIfNec512C_cost drCrArmC drCrArmC_queries drCrArmC_cost)
open Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
  (drSendC_spqr_size_le drCrArmC_size_le size_smRWireE_le
   size_e2eSendOKE_le size_e2eEpMgmtE_le size_e2eSafeChE_le size_e2eRecordE_le)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (zeroPqxdhPrims sessPureOp sessSpqrKemOp cost_sessPureOp
   atomicDraw256 atomicDraw256_cost
   liftTy liftVal liftExpr liftExpr_cost
   wk1Expr wk1Expr_cost wk1Comp wk1Comp_queries wk1Comp_cost
   coinE2EIface coinE2ESamplers liftCompCoins liftCompCoins_queries_zero liftCompCoins_cost)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
  (letE_eval liftExpr_size_le liftCompCoins_size_le wk1Expr_size wk1Comp_size)
open Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg
  (spkInitGsE2EE cost_spkInitGsE2EE size_spkInitGsE2EE
   sPureOp cost_sPureOp sGroupOp cost_sGroupOp size_sGroupOp
   cost_senderKeyPtAtomicE cost_prepRecvB0StateAtomicE receiveSpkAtomicC
   dlPreE2EE cost_dlPreE2EE dlPostE2EE cost_dlPostE2EE
   ijPreE2EE cost_ijPreE2EE ijPostE2EE cost_ijPostE2EE
   spkDlArmC spkDlArmC_queries spkDlArmC_cost spkDlArmC_size_le
   spkIjArmC spkIjArmC_queries spkIjArmC_cost spkIjArmC_size_le)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (sessionEmbed kemCoinsT kemSentEntryT kemTrackT kemTrackAtomicEnc
   initKemFailTrackE initKemFailTrackE_cost_le initKemFailTrackE_size_le
   stepKemFailSendC stepKemFailSendC_queries_zero stepKemFailSendC_cost_le stepKemFailSendC_size_le
   kemOnDeliverPostE kemOnDeliverPostE_cost_le kemOnDeliverPostE_size_le)
open Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg
  (liftExpr_cost_exact liftCompCoins_cost_exact drReceiveAtomicC_cost_exact)

/-! ## State encodings and wire lookup -/

section StateProjections

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt := 0)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[expose, reducible] def kemSessTrackT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (kemTrackT ℓ Pt) (.list (.prod (B (ℓ := ℓ) (Pt := Pt) 32) .bool))

@[expose, reducible] def spkBaseStTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ))

/-- Combined `spkLeakRedRInProgHalted` state type pairing `(s, gs)` with `(tr, honestWires)`. -/
@[expose, reducible] def spkHaltedStTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (spkBaseStTy ℓ Pt) (kemSessTrackT ℓ Pt)

@[expose] def kemSessTrackAtomicEnc {F : ShaCompress}
    (st : SimKemFailTrack F × List (Bytes × Party)) :
    (kemSessTrackT ℓ Pt).denote :=
  (kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) st.1,
   st.2.map fun wp => (wp.1, partyEnc wp.2))

@[expose] def spkHaltedSimEnc (s : BitVec 256)
    (gst : GameState (GhostState Bytes) (Plain ℓ) Bytes ×
      (SimKemFailTrack C.F × List (Bytes × Party))) :
    (spkHaltedStTy ℓ Pt).denote :=
  ((s, liftVal (Pt := Pt) (e2eGsEnc gst.1)),
   kemSessTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) gst.2)

/-- Reverse index search in `honestWires` matching `honestWires.reverse.findIdx?` when
`honestWires.length ≤ q`. -/
@[expose] def findRevHonestWiresIdxE (q : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) : Expr AOps Γ (.opt .nat) :=
  .letE (.pair wiresE (.pair qBE wE))
    (.fst (.foldrB q (.fst .v0) (.pair .none (.nat 0))
      (let qOther := otherE (.fst (.snd .v2))
       let w := Expr.snd (.snd .v2)
       let wEntry := Expr.fst .v0
       let pEntry := Expr.snd .v0
       let eqW := sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
         (decT := decT) (lam := lam) (.bytesEq 32 32) (.pair wEntry w)
       let eqSender := boolEq pEntry qOther
       let matched := Expr.and eqW eqSender
       let prevOpt := Expr.fst .v1
       let cnt := Expr.snd .v1
       let nextOpt := Expr.caseOpt prevOpt (.ite matched (.some cnt) .none) (.some .v0)
       .pair nextOpt (.add cnt (.nat 1)))))

private def stepRevIdx {α : Type} (p : α → Bool) (x : α) (acc : Option ℕ × ℕ) : Option ℕ × ℕ :=
  (match acc.1 with
   | none => if p x then some acc.2 else none
   | some k => some k,
   acc.2 + 1)

private theorem foldl_stepRevIdx_some {α : Type} (p : α → Bool) :
    ∀ (ys : List α) (i k : ℕ),
      (ys.foldl (fun acc x => stepRevIdx p x acc) (some i, k)).1 = some i
  | [], _, _ => rfl
  | _ :: rest, i, k => foldl_stepRevIdx_some p rest i (k + 1)

private theorem foldl_stepRevIdx_none {α : Type} (p : α → Bool) :
    ∀ (ys : List α) (k : ℕ),
      (ys.foldl (fun acc x => stepRevIdx p x acc) (none, k)).1 = (ys.findIdx? p).map (· + k)
  | [], _ => rfl
  | y :: rest, k => by
    rw [List.findIdx?_cons, List.foldl_cons]
    cases hp : p y
    · have h0 : stepRevIdx p y (none, k) = (none, k + 1) := by simp [stepRevIdx, hp]
      rw [h0, foldl_stepRevIdx_none p rest (k + 1)]
      rcases rest.findIdx? p with _ | m
      · simp
      · simp; omega
    · have h0 : stepRevIdx p y (none, k) = (some k, k + 1) := by simp [stepRevIdx, hp]
      rw [h0, foldl_stepRevIdx_some p rest k (k + 1)]
      simp

private theorem foldr_eq_foldl_rev {α β : Type} (f : α → β → β) :
    ∀ (xs : List α) (z : β), xs.foldr f z = xs.reverse.foldl (fun acc x => f x acc) z
  | [], _ => rfl
  | x :: rest, z => by
    rw [List.foldr_cons, foldr_eq_foldl_rev f rest z,
      List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem foldr_stepRevIdx_eq_findIdx {α : Type} (p : α → Bool) (xs : List α) :
    (xs.foldr (stepRevIdx p) (none, 0)).1 = xs.reverse.findIdx? p := by
  rw [foldr_eq_foldl_rev, foldl_stepRevIdx_none]
  rcases xs.reverse.findIdx? p with _ | m <;> simp

theorem findRevHonestWiresIdxE_eval (q : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32))
    (ρ : Env Γ)
    (honestWires : List (Bytes × Party)) (Q : Party) (w : Bytes)
    (hLen : honestWires.length ≤ q)
    (hwires : wiresE.eval ρ = honestWires.map fun wp => (wp.1, partyEnc wp.2))
    (hq : qBE.eval ρ = partyEnc Q)
    (hw : wE.eval ρ = w) :
    (findRevHonestWiresIdxE C K Dh encPt encT decT lam q wiresE qBE wE).eval ρ =
      honestWires.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) := by
  unfold findRevHonestWiresIdxE
  rw [letE_eval]
  have hp0 : (Expr.pair wiresE (.pair qBE wE)).eval ρ =
      (honestWires.map (fun wp => (wp.1, partyEnc wp.2)), (partyEnc Q, w)) := by
    simp only [Expr.eval, hwires, hq, hw]
  rw [hp0]
  have htake : (honestWires.map fun wp => (wp.1, partyEnc wp.2)).take q =
      honestWires.map fun wp => (wp.1, partyEnc wp.2) := by
    apply List.take_of_length_le
    simpa using hLen
  simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, htake, List.foldr_map]
  rw [← foldr_stepRevIdx_eq_findIdx (fun wp : Bytes × Party => wp.1 == w && wp.2 == Q.other)
    honestWires]
  congr 1
  congr 1
  funext wp acc
  have heqW :
      (AOps).eval (.inl (.inl (.inl (.inl (.bytesEq 32 32))))) (wp.1, w) = (wp.1 == w) := rfl
  rw [heqW, CryptoGames.SM.boolEq_eval]
  rcases wp with ⟨wEntry, _ | _⟩ <;> cases Q <;> rcases acc with ⟨_ | k, cnt⟩ <;>
    simp [stepRevIdx, otherE, partyEnc, Party.other, Expr.eval]

theorem findRevHonestWiresIdxE_cost (q : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) :
    (findRevHonestWiresIdxE C K Dh encPt encT decT lam q wiresE qBE wE).cost ≤
      wiresE.cost + qBE.cost + wE.cost + 125 * q + 20 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hop : (AOps).cost (.inl (.inl (.inl (.inl (.bytesEq 32 32))))) = 64 := rfl
  let ΓI : List (Ty ASig) :=
    .prod (B 32) .bool :: .prod (.opt .nat) .nat ::
      .prod (.list (.prod (B 32) .bool)) (.prod .bool (B 32)) :: Γ
  let bodyE : Expr AOps ΓI (.prod (.opt .nat) .nat) :=
    .pair
      (.caseOpt (.fst .v1)
        (.ite
          (.and
            (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) (.bytesEq 32 32) (.pair (.fst .v0) (.snd (.snd .v2))))
            (boolEq (.snd .v0) (otherE (.fst (.snd .v2)))))
          (.some (.snd .v1)) .none)
        (.some .v0))
      (.add (.snd .v1) (.nat 1))
  have hbody : bodyE.cost ≤ 120 := by
    dsimp only [bodyE]
    simp only [boolEq, otherE, Expr.cost, hop, Expr.v0, Expr.v1, Expr.v2, hb1]
    omega
  have hqmul : q * (bodyE.cost + 1) ≤ 125 * q := by
    have h := Nat.mul_le_mul_left q (show bodyE.cost + 1 ≤ 125 by omega)
    omega
  change (Expr.letE (.pair wiresE (.pair qBE wE))
    (.fst (.foldrB q (.fst .v0) (.pair .none (.nat 0)) bodyE))).cost ≤ _
  simp only [Expr.cost, Expr.v0, hb0]
  generalize bodyE.cost = cb at hbody hqmul ⊢
  omega

theorem findRevHonestWiresIdxE_size (q : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) :
    (findRevHonestWiresIdxE C K Dh encPt encT decT lam q wiresE qBE wE).size ≤
      wiresE.size + qBE.size + wE.size + bits q + 60 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hop : ∀ (o : _root_.ReductionDsl.AtomicPureOp),
      (AOps).opSize (.inl (.inl (.inl (.inl o)))) = o.opSize := fun _ => rfl
  simp only [findRevHonestWiresIdxE, boolEq, otherE, sessPureOp, Expr.size, hop,
    _root_.ReductionDsl.AtomicPureOp.opSize, Expr.v0, Expr.v1, Expr.v2, hb0, hb1]
  omega

end StateProjections

/-! ## Initializer and pure send helpers -/

section InitAndSendHelpers

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt := 0)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT
local notation "PrfI" => extractPtPrfIface ℓ Pt

private theorem atomicDraw256_size {O0 : Ops (atomicSig ℓ Pt)} {ι : Type}
    {T : OracleSpec ι} {I0 : Iface (atomicSig ℓ Pt) T} (h : I0.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    (atomicDraw256 (O := O0) (I := I0) h (Γ := Γ)).size = 2 := by
  rcases I0 with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  rfl

/-- Tracker-halted `spkLeakRed` initializer over `atomicSessionOps`. -/
@[expose] def spkInitHaltedC :
    Comp AOps PrfI [BV256] (.prod .unit (spkHaltedStTy ℓ Pt)) :=
  .bind (Comp.sample (I := PrfI) UniformSamplerTag.bool .unit)
    (.bind (atomicDraw256 (I := PrfI) rfl)
      (.bind (atomicDraw256 (I := PrfI) rfl)
        (.bind (atomicDraw256 (I := PrfI) rfl)
          (.bind
            (Comp.query (I := PrfI) ()
              (sGroupOp .ptDh
                (.pair .v4
                  (sGroupOp .ptDh (.pair .v1 (sGroupOp .ptBase .unit))))))
            (let sE : Expr AOps _ BV256 := .var (.succ (.succ (.succ (.succ (.succ .zero)))))
             let gsE : Expr AOps _ (liftTy (Pt := Pt) (e2eGsTy ℓ)) :=
               .letE
                 (.pair .v4
                   (.pair sE
                     (.pair (sGroupOp .rootExpandPrg .v0)
                       (.pair .v3 (.pair .v2 .v1)))))
                 (wk1Expr
                   (liftExpr
                     (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K)
                       (decT := decT) (encT := encT) idA idB)))
             let tr0E : Expr AOps _ (kemTrackT ℓ Pt) :=
               initKemFailTrackE (sessionEmbed ℓ Pt C K Dh encPt encT decT lam) .v1
             .ret (.pair .unit (.pair (.pair sE gsE) (.pair tr0E .nil))))))))

theorem spkInitHaltedC_queries :
    (spkInitHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [spkInitHaltedC, atomicDraw256, Comp.queries]

theorem spkInitHaltedC_cost_tier1 :
    (spkInitHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).cost ≤ 70000 := by
  let ΓI : List (Ty ASig) := [BV256, BV256, BV256, BV256, .bool, BV256]
  let emb := sessionEmbed ℓ Pt C K Dh encPt encT decT lam
  have hl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB) rfl
  have hgs := cost_spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  have htr := initKemFailTrackE_cost_le emb (.v1 : Expr AOps ΓI BV256)
  dsimp only [spkInitHaltedC, emb] at htr ⊢
  generalize initKemFailTrackE (sessionEmbed ℓ Pt C K Dh encPt encT decT lam)
    (.v1 : Expr AOps ΓI BV256) = tr0 at htr ⊢
  simp only [cost_sGroupOp, extractPtPrfIface, atomicPrfIface, atomicSamplers,
    _root_.ReductionDsl.unifSamplers, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    _root_.ReductionDsl.AtomicGroupOp.cost, atomicDraw256_cost, wk1Expr_cost] at hl htr ⊢
  omega

theorem spkInitHaltedC_cost :
    (spkInitHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).cost ≤ 2100000 :=
  (spkInitHaltedC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).trans
    (by omega)

theorem spkInitHaltedC_size_le :
    (spkInitHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).size ≤ 6000 := by
  let ΓI : List (Ty ASig) := [BV256, BV256, BV256, BV256, .bool, BV256]
  let emb := sessionEmbed ℓ Pt C K Dh encPt encT decT lam
  have hl := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs := size_spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  have htr := initKemFailTrackE_size_le emb (.v1 : Expr AOps ΓI BV256)
  dsimp only [spkInitHaltedC, emb] at htr ⊢
  generalize initKemFailTrackE (sessionEmbed ℓ Pt C K Dh encPt encT decT lam)
    (.v1 : Expr AOps ΓI BV256) = tr0 at htr ⊢
  simp only [size_sGroupOp, atomicDraw256_size, wk1Expr_size,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hl htr ⊢
  omega

@[expose] def sendGate1E2EE : Expr EOps [.prod (e2eGsTy ℓ) .bool] .bool :=
  orE (.not (e2eSendOKE (.fst .v0) (.snd .v0))) (e2eGsWin (.fst .v0))

theorem cost_sendGate1E2EE :
    (sendGate1E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).cost ≤ 250 := by
  have hok := cost_e2eSendOKE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) .bool] (e2eGsTy ℓ)) (.snd .v0)
  dsimp only [sendGate1E2EE]
  generalize e2eSendOKE (O' := EOps)
    (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) .bool] (e2eGsTy ℓ)) (.snd .v0) = okE at hok ⊢
  simp only [orE, e2eGsWin, Expr.cost, Expr.v0] at hok ⊢
  omega

theorem size_sendGate1E2EE :
    (sendGate1E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).size ≤ 50 := by
  have hok := size_e2eSendOKE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) .bool] (e2eGsTy ℓ)) (.snd .v0)
  dsimp only [sendGate1E2EE]
  generalize e2eSendOKE (O' := EOps)
    (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) .bool] (e2eGsTy ℓ)) (.snd .v0) = okE at hok ⊢
  simp only [orE, e2eGsWin, Expr.size, Expr.v0] at hok ⊢
  omega

theorem eval_sendGate1E2EE (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) :
    (sendGate1E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).eval
      (.cons (e2eGsEnc st, partyEnc party) .nil) =
    (!(configRefuseEarlyBobCorr decT encT).sendOK st party || st.win) := by
  let ρ0 : Env [.prod (e2eGsTy ℓ) .bool] := .cons (e2eGsEnc st, partyEnc party) .nil
  dsimp only [sendGate1E2EE]
  have hok := eval_e2eSendOKE (ℓ := ℓ) (Pt := Pt) (O' := EOps) decT encT
    (.fst .v0) (.snd .v0) ρ0 st party rfl rfl
  have hwin : (e2eGsWin (.fst (Expr.v0 (O := EOps)))).eval ρ0 = st.win := rfl
  rw [CryptoGames.SM.orE_eval]
  change (!(e2eSendOKE (.fst .v0) (.snd .v0)).eval ρ0 ||
    (e2eGsWin (.fst .v0)).eval ρ0) = _
  rw [hok, hwin]

@[expose] def sendGate2E2EE (qep : ℕ) :
    Expr EOps [.prod (e2eGsTy ℓ) (.prod .bool (.prod .bool .bool))] (.opt (e2eGsTy ℓ)) :=
  .caseOpt (e2eEpMgmtE 3 qep (.fst .v0) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))))
    .none
    (.ite (.and (.fst (.snd .v1)) (.not (e2eSafeChE 3 .v0 (.fst (.snd (.snd .v1))))))
      .none
      (.some .v0))

theorem cost_sendGate2E2EE (qep : ℕ) :
    (sendGate2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) qep).cost ≤
      600 + bits qep + bits (qep + 1) := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (.prod .bool .bool))
  have hep := cost_e2eEpMgmtE_le (ℓ := ℓ) (O' := EOps) 3 qep
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
  have hsc := cost_e2eSafeChE_le (ℓ := ℓ) (O' := EOps) 3
    (.v0 : Expr EOps [e2eGsTy ℓ, t0] (e2eGsTy ℓ)) (.fst (.snd (.snd .v1)))
  have hb3 : bits 3 = 2 := rfl
  dsimp only [sendGate2E2EE]
  generalize e2eEpMgmtE (O' := EOps) 3 qep
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) _ _ = epE at hep ⊢
  generalize e2eSafeChE (O' := EOps) 3
    (.v0 : Expr EOps [e2eGsTy ℓ, t0] (e2eGsTy ℓ)) _ = scE at hsc ⊢
  simp only [Expr.cost, Expr.v0, Expr.v1, hb3] at hep hsc ⊢
  omega

theorem size_sendGate2E2EE (qep : ℕ) :
    (sendGate2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) qep).size ≤
      700 + 2 * bits qep := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (.prod .bool .bool))
  have hep := size_e2eEpMgmtE_le (ℓ := ℓ) (O' := EOps) 3 qep
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
  have hsc := size_e2eSafeChE_le (ℓ := ℓ) (O' := EOps) 3
    (.v0 : Expr EOps [e2eGsTy ℓ, t0] (e2eGsTy ℓ)) (.fst (.snd (.snd .v1)))
  have hb3 : bits 3 = 2 := rfl
  dsimp only [sendGate2E2EE]
  generalize e2eEpMgmtE (O' := EOps) 3 qep
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) _ _ = epE at hep ⊢
  generalize e2eSafeChE (O' := EOps) 3
    (.v0 : Expr EOps [e2eGsTy ℓ, t0] (e2eGsTy ℓ)) _ = scE at hsc ⊢
  simp only [Expr.size, Expr.v0, Expr.v1, hb3] at hep hsc ⊢
  omega

theorem eval_sendGate2E2EE (qep : ℕ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (isChall : Bool) (party : Party) (bad : Bool) :
    (sendGate2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) qep).eval
      (.cons (e2eGsEnc st, (isChall, (partyEnc party, bad))) .nil) =
    match st.epMgmt 3 qep party bad with
    | none => none
    | some s₁ =>
      if isChall && !(s₁.safeCh 3 party) then none else some (e2eGsEnc s₁) := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (.prod .bool .bool))
  let ρ0 : Env [t0] := .cons (e2eGsEnc st, (isChall, (partyEnc party, bad))) .nil
  dsimp only [sendGate2E2EE]
  have hep :
      (e2eEpMgmtE (O' := EOps) 3 qep (.fst .v0) (.fst (.snd (.snd .v0)))
        (.snd (.snd (.snd .v0)))).eval ρ0 =
      (st.epMgmt 3 qep party bad).map e2eGsEnc :=
    eval_e2eEpMgmtE (ℓ := ℓ) (O' := EOps) 3 qep
      (.fst .v0) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))) ρ0 st party rfl rfl
  change (Expr.caseOpt (e2eEpMgmtE 3 qep (.fst .v0) (.fst (.snd (.snd .v0)))
      (.snd (.snd (.snd .v0)))) .none _).eval ρ0 = _
  simp only [Expr.eval]
  rw [hep]
  cases hmgmt : st.epMgmt 3 qep party bad with
  | none => rfl
  | some s₁ =>
    dsimp only [Option.map]
    let ρ1 : Env [e2eGsTy ℓ, t0] := .cons (e2eGsEnc s₁) ρ0
    have hsc := eval_e2eSafeChE (ℓ := ℓ) (O' := EOps) 3 .v0 (.fst (.snd (.snd .v1)))
      ρ1 s₁ party rfl rfl
    have hisc : (Expr.fst (.snd (Expr.v1 (O := EOps)))).eval ρ1 = isChall := rfl
    have hv0 : (Expr.v0 (O := EOps)).eval ρ1 = e2eGsEnc s₁ := rfl
    change (if ((Expr.fst (.snd (Expr.v1 (O := EOps)))).eval ρ1 &&
        !(e2eSafeChE 3 .v0 (.fst (.snd (.snd .v1)))).eval ρ1) = true
      then none else some ((Expr.v0 (O := EOps)).eval ρ1)) = _
    rw [hisc, hsc, hv0]

@[expose] def sendPrepInE2EE :
    Expr EOps
      [.prod (e2eGsTy ℓ)
        (.prod (e2eGsTy ℓ)
          (.prod .bool
            (.prod .bool
              (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.PlainT))))]
      (.prod CryptoVerification.E2E.Costed.GhostStT CryptoVerification.E2E.Costed.PlainT) :=
  let gs := Expr.fst .v0
  let s1 := Expr.fst (.snd .v0)
  let isChall := Expr.fst (.snd (.snd .v0))
  let p := Expr.fst (.snd (.snd (.snd .v0)))
  let m0 := Expr.fst (.snd (.snd (.snd (.snd .v0))))
  let m1 := Expr.snd (.snd (.snd (.snd (.snd .v0))))
  .pair (pGet (e2eGsSt s1) p) (.ite (.and isChall (e2eGsB gs)) m1 m0)

theorem cost_sendPrepInE2EE :
    (sendPrepInE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).cost ≤ 80 := by
  simp only [sendPrepInE2EE, pGet, e2eGsSt, e2eGsB, Expr.cost, Expr.v0]
  omega

theorem size_sendPrepInE2EE :
    (sendPrepInE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).size ≤ 80 := by
  simp only [sendPrepInE2EE, pGet, e2eGsSt, e2eGsB, Expr.size, Expr.v0]
  omega

theorem eval_sendPrepInE2EE
    (st s₁ : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (isChall : Bool) (party : Party) (m0 m1 : Plain ℓ) :
    (sendPrepInE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).eval
      (.cons (e2eGsEnc st, (e2eGsEnc s₁, (isChall, (partyEnc party, (m0, m1))))) .nil) =
    (s₁.st party, if isChall && st.b then m1 else m0) := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod (e2eGsTy ℓ)
    (.prod .bool (.prod .bool
      (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.PlainT))))
  let ρ0 : Env [t0] :=
    .cons (e2eGsEnc st, (e2eGsEnc s₁, (isChall, (partyEnc party, (m0, m1))))) .nil
  have hpget := CryptoGames.SM.pGet_eval (O' := EOps)
    (e2eGsSt (.fst (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))) ρ0 s₁.st party rfl rfl
  have hm :
      (Expr.ite (.and (.fst (.snd (.snd (Expr.v0 (O := EOps))))) (e2eGsB (.fst .v0)))
        (.snd (.snd (.snd (.snd (.snd .v0)))))
        (.fst (.snd (.snd (.snd (.snd .v0)))))).eval ρ0 =
      (if isChall && st.b then m1 else m0) := by
    simp only [ρ0, e2eGsB, Expr.eval, Expr.v0, Env.get, e2eGsEnc]
  change ((pGet (e2eGsSt (.fst (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))).eval ρ0,
    (Expr.ite (.and (.fst (.snd (.snd (Expr.v0 (O := EOps))))) (e2eGsB (.fst .v0)))
      (.snd (.snd (.snd (.snd (.snd .v0)))))
      (.fst (.snd (.snd (.snd (.snd .v0)))))).eval ρ0) = _
  rw [hpget, hm]

@[expose] def sendPostE2EE (q : ℕ) :
    Expr EOps
      [.prod (e2eGsTy ℓ)
        (.prod (e2eGsTy ℓ)
          (.prod .bool
            (.prod .bool
              (.prod CryptoVerification.E2E.Costed.PlainT
                (.prod CryptoVerification.E2E.Costed.PlainT
                  (.prod CryptoVerification.E2E.Costed.GhostStT
                    (CryptoVerification.E2E.Costed.B 32)))))))]
      (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
        (e2eGsTy ℓ)) :=
  let gs := Expr.fst .v0
  let s1 := Expr.fst (.snd .v0)
  let isChall := Expr.fst (.snd (.snd .v0))
  let p := Expr.fst (.snd (.snd (.snd .v0)))
  let m0 := Expr.fst (.snd (.snd (.snd (.snd .v0))))
  let m1 := Expr.fst (.snd (.snd (.snd (.snd (.snd .v0)))))
  let st' := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  let ct' := Expr.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  let mSend := Expr.ite (.and isChall (e2eGsB gs)) m1 m0
  let posE : Expr EOps _ posTy :=
    .pair p (.pair (pGet (e2eGsEpoch s1) p) (.add (pGet (e2eGsIdx s1) p) (.nat 1)))
  .pair (smRWireE (.some ct')) (e2eRecordE q 3 s1 p st' posE mSend ct' isChall)

theorem cost_sendPostE2EE (q : ℕ) :
    (sendPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).cost ≤
      500 + 250 * q := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod (e2eGsTy ℓ) (.prod .bool (.prod .bool
    (.prod CryptoVerification.E2E.Costed.PlainT (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32)))))))
  let gs : Expr EOps [t0] (e2eGsTy ℓ) := .fst .v0
  let s1 : Expr EOps [t0] (e2eGsTy ℓ) := .fst (.snd .v0)
  let isChall : Expr EOps [t0] .bool := .fst (.snd (.snd .v0))
  let p : Expr EOps [t0] .bool := .fst (.snd (.snd (.snd .v0)))
  let m0 : Expr EOps [t0] CryptoVerification.E2E.Costed.PlainT :=
    .fst (.snd (.snd (.snd (.snd .v0))))
  let m1 : Expr EOps [t0] CryptoVerification.E2E.Costed.PlainT :=
    .fst (.snd (.snd (.snd (.snd (.snd .v0)))))
  let st' : Expr EOps [t0] CryptoVerification.E2E.Costed.GhostStT :=
    .fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  let ct' : Expr EOps [t0] (CryptoVerification.E2E.Costed.B 32) :=
    .snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  let mSend : Expr EOps [t0] CryptoVerification.E2E.Costed.PlainT :=
    .ite (.and isChall (e2eGsB gs)) m1 m0
  let posE : Expr EOps [t0] posTy :=
    .pair p (.pair (pGet (e2eGsEpoch s1) p) (.add (pGet (e2eGsIdx s1) p) (.nat 1)))
  have hrec := cost_e2eRecordE_le (ℓ := ℓ) (O' := EOps) q 3 s1 p st' posE mSend ct' isChall
  have hw := cost_smRWireE (ℓ := ℓ) (O' := EOps) (stT := CryptoVerification.E2E.Costed.GhostStT)
    (.some ct')
  have hb1 : bits 1 = 1 := rfl
  have hb3 : bits 3 = 2 := rfl
  dsimp only [sendPostE2EE]
  generalize e2eRecordE (O' := EOps) q 3 s1 p st' posE mSend ct' isChall = recE at hrec ⊢
  generalize smRWireE (O' := EOps) (stT := CryptoVerification.E2E.Costed.GhostStT)
    (.some ct') = wireE at hw ⊢
  simp only [gs, s1, isChall, p, m0, m1, st', ct', mSend, posE,
    pGet, e2eGsB, e2eGsEpoch, e2eGsIdx, Expr.cost, Expr.v0, hb1, hb3] at hrec hw ⊢
  omega

theorem size_sendPostE2EE (q : ℕ) :
    (sendPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).size ≤
      760 + 2 * bits q := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod (e2eGsTy ℓ) (.prod .bool (.prod .bool
    (.prod CryptoVerification.E2E.Costed.PlainT (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32)))))))
  let gs : Expr EOps [t0] (e2eGsTy ℓ) := .fst .v0
  let s1 : Expr EOps [t0] (e2eGsTy ℓ) := .fst (.snd .v0)
  let isChall : Expr EOps [t0] .bool := .fst (.snd (.snd .v0))
  let p : Expr EOps [t0] .bool := .fst (.snd (.snd (.snd .v0)))
  let m0 : Expr EOps [t0] CryptoVerification.E2E.Costed.PlainT :=
    .fst (.snd (.snd (.snd (.snd .v0))))
  let m1 : Expr EOps [t0] CryptoVerification.E2E.Costed.PlainT :=
    .fst (.snd (.snd (.snd (.snd (.snd .v0)))))
  let st' : Expr EOps [t0] CryptoVerification.E2E.Costed.GhostStT :=
    .fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  let ct' : Expr EOps [t0] (CryptoVerification.E2E.Costed.B 32) :=
    .snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  let mSend : Expr EOps [t0] CryptoVerification.E2E.Costed.PlainT :=
    .ite (.and isChall (e2eGsB gs)) m1 m0
  let posE : Expr EOps [t0] posTy :=
    .pair p (.pair (pGet (e2eGsEpoch s1) p) (.add (pGet (e2eGsIdx s1) p) (.nat 1)))
  have hrec := size_e2eRecordE_le (ℓ := ℓ) (O' := EOps) q 3 s1 p st' posE mSend ct' isChall
  have hw := size_smRWireE_le (ℓ := ℓ) (O' := EOps) (stT := CryptoVerification.E2E.Costed.GhostStT)
    (.some ct')
  have hb1 : bits 1 = 1 := rfl
  have hb3 : bits 3 = 2 := rfl
  dsimp only [sendPostE2EE]
  generalize e2eRecordE (O' := EOps) q 3 s1 p st' posE mSend ct' isChall = recE at hrec ⊢
  generalize smRWireE (O' := EOps) (stT := CryptoVerification.E2E.Costed.GhostStT)
    (.some ct') = wireE at hw ⊢
  simp only [gs, s1, isChall, p, m0, m1, st', ct', mSend, posE,
    pGet, e2eGsB, e2eGsEpoch, e2eGsIdx, Expr.size, Expr.v0, hb1, hb3] at hrec hw ⊢
  omega

theorem eval_sendPostE2EE (q : ℕ)
    (st s₁ : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (isChall : Bool) (party : Party) (m0 m1 : Plain ℓ)
    (st' : GhostState Bytes) (ct' : Bytes)
    (htr : s₁.trans.length ≤ q) (hcp : (dedupComp s₁.comp).length ≤ q) :
    (sendPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).eval
      (.cons (e2eGsEnc st, (e2eGsEnc s₁, (isChall, (partyEnc party, (m0, (m1, (st', ct'))))))) .nil) =
    let mSend := if isChall && st.b then m1 else m0
    ((some ct', (none, none)),
     e2eGsEnc (s₁.record 3 party st' ⟨⟨party, s₁.epoch party, s₁.idx party + 1⟩, mSend, ct'⟩ isChall)) := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod (e2eGsTy ℓ) (.prod .bool (.prod .bool
    (.prod CryptoVerification.E2E.Costed.PlainT (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32)))))))
  let ρ0 : Env [t0] :=
    .cons (e2eGsEnc st, (e2eGsEnc s₁, (isChall, (partyEnc party, (m0, (m1, (st', ct'))))))) .nil
  let gs : Expr EOps [t0] (e2eGsTy ℓ) := .fst .v0
  let s1 : Expr EOps [t0] (e2eGsTy ℓ) := .fst (.snd .v0)
  let isChallE : Expr EOps [t0] .bool := .fst (.snd (.snd .v0))
  let p : Expr EOps [t0] .bool := .fst (.snd (.snd (.snd .v0)))
  let m0E : Expr EOps [t0] CryptoVerification.E2E.Costed.PlainT :=
    .fst (.snd (.snd (.snd (.snd .v0))))
  let m1E : Expr EOps [t0] CryptoVerification.E2E.Costed.PlainT :=
    .fst (.snd (.snd (.snd (.snd (.snd .v0)))))
  let st'E : Expr EOps [t0] CryptoVerification.E2E.Costed.GhostStT :=
    .fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  let ct'E : Expr EOps [t0] (CryptoVerification.E2E.Costed.B 32) :=
    .snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  let mSendE : Expr EOps [t0] CryptoVerification.E2E.Costed.PlainT :=
    .ite (.and isChallE (e2eGsB gs)) m1E m0E
  let posE : Expr EOps [t0] posTy :=
    .pair p (.pair (pGet (e2eGsEpoch s1) p) (.add (pGet (e2eGsIdx s1) p) (.nat 1)))
  have hpos : posE.eval ρ0 = posEnc ⟨party, s₁.epoch party, s₁.idx party + 1⟩ := by
    have hep := CryptoGames.SM.pGet_eval (t := .nat) (O' := EOps)
      (e2eGsEpoch s1) p ρ0 s₁.epoch party rfl rfl
    have hidx := CryptoGames.SM.pGet_eval (t := .nat) (O' := EOps)
      (e2eGsIdx s1) p ρ0 s₁.idx party rfl rfl
    simp only [posE, Expr.eval, hep, hidx]
    rfl
  have hmSend : mSendE.eval ρ0 = (if isChall && st.b then m1 else m0) := by
    simp only [ρ0, mSendE, gs, isChallE, m0E, m1E, e2eGsB, Expr.eval, Expr.v0, Env.get, e2eGsEnc]
  have hrec := eval_e2eRecordE (ℓ := ℓ) (O' := EOps) q 3 s1 p st'E posE mSendE ct'E isChallE
    ρ0 s₁ party ⟨party, s₁.epoch party, s₁.idx party + 1⟩ htr hcp rfl rfl hpos
  dsimp only [sendPostE2EE]
  change (Expr.pair (smRWireE (.some ct'E))
    (e2eRecordE q 3 s1 p st'E posE mSendE ct'E isChallE)).eval ρ0 = _
  simp only [Expr.eval, eval_smRWireE, hrec, hmSend]
  rfl

/-! ## Send/challenge and deliver handlers -/

@[expose, reducible] def sendOrChallArgT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .bool
    (.prod .bool
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt))
        (.prod (PlainT (ℓ := ℓ) (Pt := Pt))
          (.opt (BV512 (ℓ := ℓ) (Pt := Pt))))))

/-- Unified tracker-halted `transmit`/`chall` handler over `atomicSessionOps` and `PrfI`. -/
@[expose] def spkSendOrChallHaltedC (q qep : ℕ) :
    Comp AOps PrfI
      [.prod (spkHaltedStTy ℓ Pt) (sendOrChallArgT ℓ Pt)]
      (.prod (smRT GhostStT) (spkHaltedStTy ℓ Pt)) :=
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI
  let emb := sessionEmbed ℓ Pt C K Dh encPt encT decT lam
  let noneAns {Γ : List (Ty ASig)} : Expr AOps Γ (smRT GhostStT) :=
    .pair .none (.pair .none .none)
  let stH0 := Expr.fst .v0
  let gs0 := Expr.snd (.fst stH0)
  let p0 := Expr.fst (.snd (.snd .v0))
  let optR0 := Expr.snd (.snd (.snd (.snd (.snd .v0))))
  let gate1A := Expr.letE (.pair gs0 p0)
    (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (sendGate1E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
  .ite gate1A
    (.ret (.pair noneAns stH0))
    (.bind (.ret optR0)
      (.bind
        (wk1Comp (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
          (e2eSamIfNec512C coins
            (.v0 : Expr EOps [.opt CryptoVerification.E2E.Costed.BV512]
              (.opt CryptoVerification.E2E.Costed.BV512)))))
        (let stH2 := Expr.fst .v2
         let gs2 := Expr.snd (.fst stH2)
         let isChall2 := Expr.fst (.snd .v2)
         let p2 := Expr.fst (.snd (.snd .v2))
         let gate2A : Expr AOps _ (.opt (liftTy (Pt := Pt) (e2eGsTy ℓ))) :=
           .letE (.pair gs2 (.pair isChall2 (.pair p2 (.snd .v0))))
             (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
               (encT := encT) (decT := decT) (lam := lam)
               (sendGate2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) qep)))
         .caseOpt gate2A
           (.ret (.pair noneAns stH2))
           (let stH3 := Expr.fst .v3
            let tr3 := Expr.fst (.snd stH3)
            let p3 := Expr.fst (.snd (.snd .v3))
            .bind
              (stepKemFailSendC emb q (I := PrfI) tr3 p3 (.fst .v1))
              (let stH4 := Expr.fst .v4
               let base4 := Expr.fst stH4
               let gs4 := Expr.snd base4
               let wires4 := Expr.snd (.snd stH4)
               let arg4 := Expr.snd .v4
               let isChall4 := Expr.fst arg4
               let p4 := Expr.fst (.snd arg4)
               let m0_4 := Expr.fst (.snd (.snd arg4))
               let m1_4 := Expr.fst (.snd (.snd (.snd arg4)))
               .ite (.fst .v0)
                 (.ret (.pair noneAns (.pair base4 (.pair (.snd .v0) wires4))))
                 (let prepInA : Expr AOps _ (.prod GhostStT PlainT) :=
                    .letE (.pair gs4 (.pair .v1 (.pair isChall4 (.pair p4 (.pair m0_4 m1_4)))))
                      (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                        (encT := encT) (decT := decT) (lam := lam)
                        (sendPrepInE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
                  .bind (.ret (.pair (.fst prepInA) (.pair (.snd prepInA) (.fst .v2))))
                    (.bind
                      (wk1Comp (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh)
                        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
                        (drSendC hooks (coinE2EIface PrfI)
                          (.v0 : Expr EOps
                            [.prod CryptoVerification.E2E.Costed.GhostStT
                              (.prod CryptoVerification.E2E.Costed.PlainT
                                CryptoVerification.E2E.Costed.BV512)] _))))
                      (let vRoot6 : Expr AOps _ (.prod (spkHaltedStTy ℓ Pt) (sendOrChallArgT ℓ Pt)) :=
                         .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
                       let stH6 := Expr.fst vRoot6
                       let gs6 := Expr.snd (.fst stH6)
                       let arg6 := Expr.snd vRoot6
                       let isChall6 := Expr.fst arg6
                       let p6 := Expr.fst (.snd arg6)
                       let m0_6 := Expr.fst (.snd (.snd arg6))
                       let m1_6 := Expr.fst (.snd (.snd (.snd arg6)))
                       let postA :=
                         Expr.letE
                           (.pair gs6 (.pair .v3 (.pair isChall6 (.pair p6
                             (.pair m0_6 (.pair m1_6 .v0))))))
                           (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh)
                             (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
                             (sendPostE2EE (ℓ := ℓ) (C := C) (K := K)
                               (decT := decT) (encT := encT) q)))
                       let vRoot7 : Expr AOps _ (.prod (spkHaltedStTy ℓ Pt) (sendOrChallArgT ℓ Pt)) :=
                         .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
                       let stH7 := Expr.fst vRoot7
                       let s7 := Expr.fst (.fst stH7)
                       let wires7 := Expr.snd (.snd stH7)
                       let p7 := Expr.fst (.snd (.snd vRoot7))
                       .ret
                         (.letE postA
                           (.pair (.fst .v0)
                             (.pair (.pair s7 (.snd .v0))
                               (.pair (.snd .v3)
                                 (.cons (.pair (.snd .v1) p7) wires7)))))))))))))

theorem spkSendOrChallHaltedC_queries_zero (q qep : ℕ) :
    (spkSendOrChallHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [spkSendOrChallHaltedC, wk1Comp_queries, liftCompCoins_queries_zero,
    stepKemFailSendC_queries_zero, Comp.queries]

private theorem noKemKeyGenComp_drSendC_v0 :
    SpkHop2RInProg.NoKemKeyGenComp
      (drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2EIface (ℓ := ℓ) PrfI)
        (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
          (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
            Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]) .v0) =
      true := by
  dsimp only [drSendC, spqrDslHooks,
    Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendPostE,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.sendAddrsE]
  cases CryptoVerification.E2E.serializedPartyAddresses
    CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .B .A <;>
  cases CryptoVerification.E2E.serializedPartyAddresses
    CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .A .B <;>
  rfl

private theorem liftCompCoins_drSendC_cost_le :
    (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
      (drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2EIface (ℓ := ℓ) PrfI)
        (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
          (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
            Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]) .v0)).cost ≤
      1 + 67810 + 10 * (ℓ / 32 + 1) := by
  have h1 := liftCompCoins_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2EIface (ℓ := ℓ) PrfI)
      (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
        (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
          Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]) .v0)
    (noKemKeyGenComp_drSendC_v0 (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (encT := encT) (decT := decT))
  have h2 := drSendC_cost (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2EIface (ℓ := ℓ) PrfI)
    (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]) .v0
  exact (h1.trans h2).trans (by simp [Expr.v0, Expr.cost])

theorem spkSendOrChallHaltedC_cost_tier1 (q qep : ℕ) :
    (spkSendOrChallHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost ≤
      1300000 + 10 * (ℓ / 32 + 1) + 310 * q + 32 * bits qep + 32 * bits (qep + 1) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI
  let emb := sessionEmbed ℓ Pt C K Dh encPt encT decT lam
  let tRoot : Ty ASig := .prod (spkHaltedStTy ℓ Pt) (sendOrChallArgT ℓ Pt)
  let Γ3 : List (Ty ASig) :=
    [liftTy (Pt := Pt) (e2eGsTy ℓ), .prod BV512 .bool, .opt BV512, tRoot]
  have hg1l := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendGate1E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hg1 := cost_sendGate1E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let cSamE := e2eSamIfNec512C coins (.v0 : Expr EOps [.opt CryptoVerification.E2E.Costed.BV512] _)
  have hsam1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl cSamE
  have hsam2 : cSamE.cost ≤ 1 + 12 := e2eSamIfNec512C_cost coins
    (.v0 : Expr EOps [.opt CryptoVerification.E2E.Costed.BV512] _)
  have hsamq : cSamE.queries (fun _ => 0) (fun _ => 1) ≤ 1 := by
    simp [cSamE, coins, e2eSamIfNec512C, coinE2ESamplers, mkE2ECoinSamplers, Comp.queries]
  have hg2l := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendGate2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) qep)
  have hg2 := cost_sendGate2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) qep
  have hkf := stepKemFailSendC_cost_le emb q (I := PrfI) (Γ := Γ3)
    (.fst (.snd (.fst .v3))) (.fst (.snd (.snd .v3))) (.fst .v1)
  have hprepl := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendPrepInE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hprep := cost_sendPrepInE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  have hdr := liftCompCoins_drSendC_cost_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
  have hpostl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q) rfl
  have hpost := cost_sendPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  dsimp only [spkSendOrChallHaltedC, cSamE, coins, hooks, emb]
    at hsam1 hsam2 hsamq hkf ⊢
  generalize liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendGate1E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)) = lg1 at hg1l ⊢
  generalize liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (e2eSamIfNec512C (coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI)
      (.v0 : Expr EOps [.opt CryptoVerification.E2E.Costed.BV512] _)) =
    lSam at hsam1 ⊢
  generalize liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendGate2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) qep) = lg2 at hg2l ⊢
  generalize stepKemFailSendC (sessionEmbed ℓ Pt C K Dh encPt encT decT lam) q (I := PrfI)
    (Γ := Γ3) (.fst (.snd (.fst .v3))) (.fst (.snd (.snd .v3))) (.fst .v1) = cKf at hkf ⊢
  generalize liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendPrepInE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)) = lprep at hprepl ⊢
  generalize liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2EIface PrfI)
      (.v0 : Expr EOps [.prod CryptoVerification.E2E.Costed.GhostStT
        (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)] _)) =
    lDr at hdr ⊢
  generalize liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q) = lpost at hpostl ⊢
  simp only [wk1Comp_cost, wk1Expr_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hkf ⊢
  omega

theorem spkSendOrChallHaltedC_cost (q qep : ℕ) :
    (spkSendOrChallHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost ≤
      96000000 + 320 * (ℓ / 32 + 1) + 10000 * q + 32 * bits qep + 32 * bits (qep + 1) := by
  have h := spkSendOrChallHaltedC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  omega

theorem spkSendOrChallHaltedC_size_le (q qep : ℕ) :
    (spkSendOrChallHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).size ≤
      200000 + 18 * bits q + 18 * bits qep + bits (q + 1) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI
  let emb := sessionEmbed ℓ Pt C K Dh encPt encT decT lam
  let tRoot : Ty ASig := .prod (spkHaltedStTy ℓ Pt) (sendOrChallArgT ℓ Pt)
  let Γ3 : List (Ty ASig) :=
    [liftTy (Pt := Pt) (e2eGsTy ℓ), .prod BV512 .bool, .opt BV512, tRoot]
  have hg1l := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendGate1E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hg1 := size_sendGate1E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let cSamE := e2eSamIfNec512C coins (.v0 : Expr EOps [.opt CryptoVerification.E2E.Costed.BV512] _)
  have hsam1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl cSamE
  have hsam2 : cSamE.size ≤ 20 := by
    simp [cSamE, coins, e2eSamIfNec512C, coinE2ESamplers, mkE2ECoinSamplers,
      Comp.size, Expr.size, Expr.v0]
  have hg2l := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendGate2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) qep)
  have hg2 := size_sendGate2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) qep
  have hkf := stepKemFailSendC_size_le emb q (I := PrfI) (Γ := Γ3)
    (.fst (.snd (.fst .v3))) (.fst (.snd (.snd .v3))) (.fst .v1)
  have hprepl := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendPrepInE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hprep := size_sendPrepInE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let cDrE := drSendC hooks (coinE2EIface PrfI)
    (.v0 : Expr EOps [.prod CryptoVerification.E2E.Costed.GhostStT
      (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)] _)
  have hdr1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl cDrE
  have hdr2 := drSendC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (coinE2EIface PrfI)
    (.v0 : Expr EOps [.prod CryptoVerification.E2E.Costed.GhostStT
      (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)] _)
  have hpostl := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpost := size_sendPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  dsimp only [spkSendOrChallHaltedC, cSamE, cDrE, coins, hooks, emb] at hsam1 hsam2 hkf hdr1 hdr2 ⊢
  generalize stepKemFailSendC (sessionEmbed ℓ Pt C K Dh encPt encT decT lam) q (I := PrfI)
    (Γ := Γ3) (.fst (.snd (.fst .v3))) (.fst (.snd (.snd .v3))) (.fst .v1) = cKf at hkf ⊢
  simp only [wk1Comp_size, wk1Expr_size, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
    at hsam1 hsam2 hkf hdr1 hdr2 ⊢
  omega

private theorem receiveSpkAtomicC_cost_tier1 {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).cost ≤
      sE.cost + gE.cost + cE.cost + rcE.cost + 5105000 + 9 * (ℓ / 32 + 1) := by
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  have hsk := cost_senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst (.snd (.snd .v0)) : Expr AOps (t0 :: Γ) (B 32))
  have hprep := cost_prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.pair (.fst (.snd .v2)) (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0)) :
      Expr AOps (BV256 :: .prod PK PtT :: t0 :: Γ) (.prod GhostStT (.prod PK (.prod BV256 BV256))))
  have hdr1 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI
    (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))) :
      Expr AOps (GhostStT :: BV256 :: .prod PK PtT :: t0 :: Γ)
        (.prod GhostStT (.prod (B 32) BV256)))
  have hdr2 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI
    (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))) :
      Expr AOps (t0 :: Γ) (.prod GhostStT (.prod (B 32) BV256)))
  have hb0 : bits 0 = 1 := by decide
  simp only [receiveSpkAtomicC, cost_sPureOp, cost_sGroupOp,
    extractPtPrfIface, atomicPrfIface, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    _root_.ReductionDsl.AtomicPureOp.cost, _root_.ReductionDsl.AtomicGroupOp.cost, hb0]
    at hsk hprep hdr1 hdr2 ⊢
  omega

theorem spkDlArmC_cost_tier1 (q : ℕ) :
    (spkDlArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).cost ≤
      5107000 + 9 * (ℓ / 32 + 1) + 500 * q := by
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  have hpre1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q) rfl
  have hpre2 := cost_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hpost1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q) rfl
  have hpost2 := cost_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hrecv := receiveSpkAtomicC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    (.fst .v2 : Expr AOps [BV256, .prod GhostStT posTy, t0] BV256)
    (.fst .v1) (.snd (.snd (.snd .v2))) .v0
  simp only [spkDlArmC, atomicDraw256_cost, wk1Expr_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5] at hpre1 hpost1 hrecv ⊢
  omega

theorem spkIjArmC_cost_tier1 (q qep : ℕ) :
    (spkIjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost ≤
      5107000 + 10 * (ℓ / 32 + 1) + 530 * q + bits (qep + 1) := by
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  have hpre1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)) rfl
  have hpre2 := cost_ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)
  have hpost1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1) qep) rfl
  have hpost2 := cost_ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    q (2 + 1) qep
  have hrecv := receiveSpkAtomicC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    (.fst .v2 : Expr AOps [BV256, GhostStT, t0] BV256)
    .v1 (.snd (.snd (.snd .v2))) .v0
  have hb3 : bits (2 + 1) = 2 := by decide
  simp only [spkIjArmC, atomicDraw256_cost, wk1Expr_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5, hb3] at hpre1 hpost1 hpost2 hrecv ⊢
  omega

/-- Tracker-updating `.dl` (`deliverSpkTrackHalted`) handler over `atomicSessionOps` and `PrfI`. -/
@[expose] def spkDlArmHaltedC (q : ℕ) :
    Comp AOps PrfI
      [.prod (spkHaltedStTy ℓ Pt) (.prod .bool (B 32))]
      (.prod (smRT GhostStT) (spkHaltedStTy ℓ Pt)) :=
  let emb := sessionEmbed ℓ Pt C K Dh encPt encT decT lam
  let stH0 := Expr.fst .v0
  let wires0 := Expr.snd (.snd stH0)
  let qB0 := Expr.fst (.snd .v0)
  let w0 := Expr.snd (.snd .v0)
  .bind (.ret (findRevHonestWiresIdxE C K Dh encPt encT decT lam q wires0 qB0 w0))
    (let stH1 := Expr.fst .v1
     let s1 := Expr.fst (.fst stH1)
     let gs1 := Expr.snd (.fst stH1)
     .bind (.ret (.pair s1 (.pair gs1 (.snd .v1))))
       (.bind (wk1Comp (spkDlArmC C K Dh encPt encT decT lam q))
         (let stH3 := Expr.fst .v3
          let tr3 := Expr.fst (.snd stH3)
          let wires3 := Expr.snd (.snd stH3)
          let qB3 := Expr.fst (.snd .v3)
          let tr' := kemOnDeliverPostE emb q qB3 .v2 (.fst (.snd (.fst .v0))) tr3
          .ret (.pair (.fst .v0) (.pair (.snd .v0) (.pair tr' wires3))))))

theorem spkDlArmHaltedC_queries (q : ℕ) :
    (spkDlArmHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [spkDlArmHaltedC, wk1Comp_queries, spkDlArmC_queries, Comp.queries]

theorem spkDlArmHaltedC_cost_tier1 (q : ℕ) :
    (spkDlArmHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).cost ≤
      5120000 + 9 * (ℓ / 32 + 1) + 670 * q := by
  let emb := sessionEmbed ℓ Pt C K Dh encPt encT decT lam
  let t0 : Ty ASig := .prod (spkHaltedStTy ℓ Pt) (.prod .bool (B 32))
  let t1 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  let t2 : Ty ASig := .prod (smRT GhostStT) (spkBaseStTy ℓ Pt)
  let Γ3 : List (Ty ASig) := [t2, t1, .opt .nat, t0]
  have hf := findRevHonestWiresIdxE_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
    (Γ := [t0]) (.snd (.snd (.fst .v0))) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hdl := spkDlArmC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
  have hpost := kemOnDeliverPostE_cost_le emb q (Γ := Γ3)
    (.fst (.snd .v3)) .v2 (.fst (.snd (.fst .v0))) (.fst (.snd (.fst .v3)))
  dsimp only [spkDlArmHaltedC, emb] at hpost ⊢
  simp only [wk1Comp_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hf hpost ⊢
  generalize (findRevHonestWiresIdxE C K Dh encPt encT decT lam q _ _ _).cost = cf at hf ⊢
  generalize (spkDlArmC C K Dh encPt encT decT lam q).cost = cdl at hdl ⊢
  generalize (kemOnDeliverPostE (sessionEmbed ℓ Pt C K Dh encPt encT decT lam)
    q _ _ _ _).cost = cp at hpost ⊢
  omega

theorem spkDlArmHaltedC_cost (q : ℕ) :
    (spkDlArmHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).cost ≤
      163500000 + 257 * (ℓ / 32 + 1) + 16500 * q := by
  have h := spkDlArmHaltedC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
  omega

theorem spkDlArmHaltedC_size_le (q : ℕ) :
    (spkDlArmHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).size ≤
      765000 + 54 * bits q := by
  let emb := sessionEmbed ℓ Pt C K Dh encPt encT decT lam
  let t0 : Ty ASig := .prod (spkHaltedStTy ℓ Pt) (.prod .bool (B 32))
  let t1 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  let t2 : Ty ASig := .prod (smRT GhostStT) (spkBaseStTy ℓ Pt)
  let Γ3 : List (Ty ASig) := [t2, t1, .opt .nat, t0]
  have hf := findRevHonestWiresIdxE_size (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
    (Γ := [t0]) (.snd (.snd (.fst .v0))) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hdl := spkDlArmC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
  have hpost := kemOnDeliverPostE_size_le emb q (Γ := Γ3)
    (.fst (.snd .v3)) .v2 (.fst (.snd (.fst .v0))) (.fst (.snd (.fst .v3)))
  dsimp only [spkDlArmHaltedC, emb] at hpost ⊢
  generalize kemOnDeliverPostE (sessionEmbed ℓ Pt C K Dh encPt encT decT lam) q
    (.fst (.snd .v3)) .v2 (.fst (.snd (.fst .v0))) (.fst (.snd (.fst .v3)) : Expr AOps Γ3 _) =
    ePost at hpost ⊢
  simp only [wk1Comp_size, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hf hpost ⊢
  omega

end InitAndSendHelpers

end Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProgSub
