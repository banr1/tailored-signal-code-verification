/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.DrSessionSim -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrCost -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
import Computational.Proofs.Game.PromotedCostedReds.SimFig8State
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness

/-!
# Tracker-Halted Step Combinators for `epoch0Distinguisher`

Defines the `ReductionDsl` state encodings, reverse honest-wire lookup `findRevHonestWiresIdxE`,
shared pre/post-send stages, and 5-oracle step handler `epoch0OracleStepTrackC` with cost, size,
and evaluation bounds.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Step

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp bits
  atomicSig atomicSessionOps coinOnlyIface
  U32 U64 BV256 BV512 B GhostStT PlainT AtomicPureOp)
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (configEpoch0Distinguisher kemTrackEnc)
open CryptoGames.SM (Pos Record RecvResult GameState ConfigR
  samIfNec deliverR injectR corrR oracleImplR spec
  partyEnc posTy posEnc orE boolEq isSomeE otherE pGet pSet
  letE_eval ite_eval pair_eval some_eval orE_eval boolEq_eval isSomeE_eval otherE_eval pGet_eval)
open CryptoGames.LibsignalSession (Crypto ShaCompress IdentityKey PublicKey GhostState)
open CryptoGames.LibsignalSM.Proofs.Refinement (KemFailTrackState stepKemFailSend stepKemFailDeliver)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes paramsIdsWithSpqr sessionSchemeFixedSpk)
open CryptoVerification.E2E.Costed (e2eSig e2eOps smQT smQenc smRT partyToBool)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp SmReachBounded)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (SpqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendC drSendC_queries drSendC_cost drSendC_eval)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (partyToBool_eq_partyEnc smRenc
  smRWireE eval_smRWireE cost_smRWireE
  e2eGsTy e2eGsEnc e2eGsSt e2eGsB e2eGsWin e2eGsEpoch e2eGsIdx
  e2eSendOKE eval_e2eSendOKE cost_e2eSendOKE_le
  e2eEpMgmtE eval_e2eEpMgmtE cost_e2eEpMgmtE_le
  e2eSafeChE eval_e2eSafeChE cost_e2eSafeChE_le
  e2eRecordE eval_e2eRecordE cost_e2eRecordE_le)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSim (E2ECoinSamplers mkE2ECoinSamplers
  e2eSamIfNec512C e2eSamIfNec512C_queries_zero e2eSamIfNec512C_cost e2eSamIfNec512C_eval
  drDlArmC drDlArmC_queries_zero drDlArmC_cost drDlArmC_eval)
open Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize (drSendC_spqr_size_le
  drDlArmC_spqr_size_le size_e2eSendOKE_le size_e2eEpMgmtE_le
  size_e2eSafeChE_le size_e2eRecordE_le)
open Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg (epoch0IjArmC
  epoch0IjArmC_queries_zero epoch0IjArmC_cost epoch0IjArmC_spqr_size_le epoch0IjArmC_eval
  epoch0CrArmC epoch0CrArmC_queries epoch0CrArmC_cost epoch0CrArmC_size_le epoch0CrArmC_eval
  epoch0FinishE eval_epoch0FinishE cost_epoch0FinishE_le size_epoch0FinishE_le)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (sessPureOp sessSpqrKemOp
  eval_sessPureOp cost_sessPureOp zeroPqxdhPrims liftTy liftVal liftExpr liftExpr_cost liftExpr_eval
  coinE2EIface coinE2ESamplers
  liftCompCoins liftCompCoins_queries_zero liftCompCoins_cost liftCompCoins_eval
  pullEnv renExpr renExpr_cost renExpr_eval renComp renComp_queries renComp_cost renComp_eval)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (comp_eval_ret comp_eval_bind
  comp_eval_bind_ret comp_eval_ite comp_eval_caseOpt comp_eval_caseSum
  liftP_unif_eq_self liftVal_smQenc liftExpr_size_le liftCompCoins_size_le
  renExpr_size renComp_size)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State (sOpPure sOpSpqr)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (varIdx atomicSessionOpDescBits atomicExprDescBits atomicSessionOps_opSize_le
    expr_size_le_atomicExprDescBits)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit (kemCoinsT kemSentEntryT
  kemTrackT kemTrackAtomicEnc)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrCost (boolOrE boolEqE
  trE_e trE_c trE_st trE_sentB trE_sendCtr trE_cand trMk
  bytes2EqLitE issue1275ScanStepE swapPairsStepE issue1275FixEsC honestExchangeFailsAtomicC
  encRandBvAtomicE isKeysUnsampledV1E isHeaderReceivedV1E ekSideIsAE nextKemCoinsAtomicE
  nextKemCandAtomicC stepPostKemSendE stepKemFailSendAtomicC
  stepKemFailSendAtomicC_queries_zero stepKemFailSendAtomicC_cost)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub (stepKemFailSendAtomicC_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness (KemTrackDeliverInv
  kemOnDeliverPostAtomicE_eval)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
  (kemOnDeliverPostAtomicE kemOnDeliverPostAtomicE_cost kemOnDeliverPostAtomicE_descBits_le)

/-! ## Combined DSL state and `findRevHonestWiresIdxE` -/

section StateAndLookup

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT
local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

abbrev kemSessionTrackT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (kemTrackT ℓ Pt) (.list (.prod (B 32) .bool))

abbrev epoch0HaltedStTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (kemSessionTrackT ℓ Pt)

@[expose] noncomputable def kemSessionTrackEnc {F : ShaCompress}
    (st : KemFailTrackState F × List (Bytes × Party)) :
    (kemSessionTrackT ℓ Pt).denote :=
  (kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (kemTrackEnc st.1),
   st.2.map fun wp => (wp.1, partyEnc wp.2))

@[expose] noncomputable def epoch0HaltedEnc {F : ShaCompress}
    (s : GameState (GhostState Bytes) (Plain ℓ) Bytes ×
      (KemFailTrackState F × List (Bytes × Party))) :
    (epoch0HaltedStTy ℓ Pt).denote :=
  (liftVal (Pt := Pt) (e2eGsEnc s.1), kemSessionTrackEnc (ℓ := ℓ) (Pt := Pt) s.2)

@[expose] def headRen {S0 : Sig} {t₀ : Ty S0} {Γ : List (Ty S0)} : ∀ {u}, Var [t₀] u → Var (t₀ :: Γ) u
  | _, .zero => .zero

@[expose] def call1C {S0 : Sig} {O0 : Ops S0} {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T}
    {t₀ outT : Ty S0} {Γ : List (Ty S0)}
    (c : Comp O0 I0 [t₀] outT) (arg : Expr O0 Γ t₀) : Comp O0 I0 Γ outT :=
  .bind (.ret arg) (renComp headRen c)

@[simp] theorem call1C_queries {S0 : Sig} {O0 : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I0 : Iface S0 T} {t₀ outT : Ty S0} {Γ : List (Ty S0)}
    (c : Comp O0 I0 [t₀] outT) (arg : Expr O0 Γ t₀)
    (w : I0.Tag → ℕ) (ws : I0.smp.Samp → ℕ) :
    (call1C c arg).queries w ws = c.queries w ws := by
  simp [call1C, Comp.queries, renComp_queries]

theorem call1C_cost {S0 : Sig} {O0 : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I0 : Iface S0 T} {t₀ outT : Ty S0} {Γ : List (Ty S0)}
    (c : Comp O0 I0 [t₀] outT) (arg : Expr O0 Γ t₀) :
    (call1C c arg).cost = arg.cost + c.cost + 2 := by
  simp [call1C, Comp.cost, renComp_cost]; omega

theorem call1C_size {S0 : Sig} {O0 : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I0 : Iface S0 T} {t₀ outT : Ty S0} {Γ : List (Ty S0)}
    (c : Comp O0 I0 [t₀] outT) (arg : Expr O0 Γ t₀) :
    (call1C c arg).size = arg.size + c.size + 2 := by
  simp [call1C, Comp.size, renComp_size]; omega

theorem call1C_eval {S0 : Sig} {O0 : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I0 : Iface S0 T} {t₀ outT : Ty S0} {Γ : List (Ty S0)}
    (c : Comp O0 I0 [t₀] outT) (arg : Expr O0 Γ t₀) (ρ : Env Γ) :
    (call1C c arg).eval ρ = c.eval (.cons (arg.eval ρ) .nil) := by
  unfold call1C
  simp only [Comp.eval, pure_bind, renComp_eval]
  rfl

/-- Compute `honestWires.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other)` in `O(q)` via
`Expr.foldrB q` over the prepend-only `honestWires` list `List (B 32 × Bool)`. -/
@[expose] def findRevHonestWiresIdxE (q : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) : Expr AOps Γ (.opt .nat) :=
  .letE (.pair qBE wE)
    (.snd
      (.foldrB q (renExpr Var.succ wiresE) (.pair (.nat 0) .none)
        (let elem := Expr.v0
         let acc := Expr.v1
         let qw := Expr.v2
         let curIdx := Expr.fst acc
         let foundOpt := Expr.snd acc
         let isMatch :=
           Expr.and
             (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
               (decT := decT) (lam := lam) (.bytesEq 32 32) (.pair (.fst elem) (.snd qw)))
             (boolEq (.snd elem) (otherE (.fst qw)))
         .pair (.add curIdx (.nat 1))
           (.caseOpt foundOpt
             (.ite isMatch (.some curIdx) .none)
             (.some .v0)))))

private def stepRevIdx {α : Type} (p : α → Bool) (acc : ℕ × Option ℕ) (x : α) : ℕ × Option ℕ :=
  (acc.1 + 1,
    match acc.2 with
    | none => if p x then some acc.1 else none
    | some j => some j)

private theorem foldl_stepRevIdx_some {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (k j : ℕ),
      (xs.foldl (stepRevIdx p) (k, some j)).2 = some j
  | [], _, _ => rfl
  | _ :: xs, k, j => foldl_stepRevIdx_some p xs (k + 1) j

private theorem foldl_stepRevIdx_none {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (k : ℕ),
      (xs.foldl (stepRevIdx p) (k, none)).2 = (xs.findIdx? p).map (· + k)
  | [], _ => rfl
  | x :: xs, k => by
    simp only [List.foldl_cons, stepRevIdx, List.findIdx?_cons]
    cases hpx : p x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [foldl_stepRevIdx_none p xs (k + 1)]
      cases xs.findIdx? p with
      | none => rfl
      | some i =>
        simp only [Option.map_some]
        exact congrArg some (by omega)
    · simp only [↓reduceIte, Nat.zero_add, Option.map_some]
      exact foldl_stepRevIdx_some p xs (k + 1) k

private theorem foldr_eq_foldl_rev {α β : Type} (f : α → β → β) :
    ∀ (xs : List α) (z : β),
      xs.foldr f z = xs.reverse.foldl (fun b a => f a b) z
  | [], _ => rfl
  | x :: xs, z => by
    rw [List.foldr_cons, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ← foldr_eq_foldl_rev f xs z]

private theorem foldr_stepRevIdx_eq_findIdx {α : Type} (p : α → Bool) (xs : List α) :
    (xs.foldr (fun x acc => stepRevIdx p acc x) (0, none)).2 = xs.reverse.findIdx? p := by
  rw [foldr_eq_foldl_rev, foldl_stepRevIdx_none]
  cases xs.reverse.findIdx? p <;> simp

private theorem partyEnc_beq_iff (p q : Party) :
    (partyEnc p == partyEnc q) = (p == q) := by
  cases p <;> cases q <;> rfl

private theorem pullEnv_shift {S0 : Sig} {Γ Δ : List (Ty S0)} {t₀ : Ty S0}
    (f : ∀ {t}, Var Γ t → Var Δ t) (x : t₀.denote) (ρ : Env Δ) :
    AtomicSessionBridge.pullEnv (S0 := S0) (fun v => (f v).succ) (.cons (t := t₀) x ρ) =
      AtomicSessionBridge.pullEnv (S0 := S0) f ρ := by
  induction Γ with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Env.cons _) (ih (fun v => f v.succ))

private theorem pullEnv_id {S0 : Sig} {Γ : List (Ty S0)} (ρ : Env Γ) :
    AtomicSessionBridge.pullEnv (S0 := S0) (fun v => v) ρ = ρ := by
  induction ρ with
  | nil => rfl
  | cons a ρ ih => exact congrArg (Env.cons a) ((pullEnv_shift (fun v => v) a ρ).trans ih)

theorem findRevHonestWiresIdxE_eval (q : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32))
    (ρ : Env Γ) (hw : List (Bytes × Party)) (Q : Party) (w : Bytes)
    (hLen : hw.length ≤ q)
    (hwires : wiresE.eval ρ = hw.map fun wp => (wp.1, partyEnc wp.2))
    (hq : qBE.eval ρ = partyEnc Q)
    (hwE : wE.eval ρ = w) :
    (findRevHonestWiresIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q wiresE qBE wE).eval ρ =
      hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) := by
  unfold findRevHonestWiresIdxE
  rw [letE_eval, pair_eval, hq, hwE]
  let tQW : Ty ASig := .prod .bool (B 32)
  let ρ₀ : Env (tQW :: Γ) := .cons (t := tQW) (partyEnc Q, w) ρ
  have hren : (AtomicSessionBridge.renExpr Var.succ wiresE).eval ρ₀ =
      hw.map (fun wp => (wp.1, partyEnc wp.2)) := by
    rw [AtomicSessionBridge.renExpr_eval]
    have hp : AtomicSessionBridge.pullEnv (S0 := ASig) Var.succ ρ₀ = ρ :=
      (pullEnv_shift (t₀ := tQW) (fun v => v) (partyEnc Q, w) ρ).trans (pullEnv_id ρ)
    rw [hp, hwires]
  change (Expr.snd (.foldrB q (AtomicSessionBridge.renExpr Var.succ wiresE) (.pair (.nat 0) .none) _)).eval ρ₀ = _
  have hlenMap : (hw.map (fun wp => (wp.1, partyEnc wp.2))).length ≤ q := by
    rw [List.length_map]; exact hLen
  simp only [Expr.eval, hren, List.take_of_length_le hlenMap]
  let pEnc : Bytes × Bool → Bool := fun x => (x.1 == w) && (x.2 == !partyEnc Q)
  have heqW : ∀ (a b : Bytes),
      (AOps).eval (.inl (.inl (.inl (.inl (.bytesEq 32 32))))) (a, b) = (a == b) :=
    fun _ _ => rfl
  rw [show (List.foldr _ (0, none) (hw.map (fun wp => (wp.1, partyEnc wp.2)))).2 =
      (List.foldr (fun x acc => stepRevIdx pEnc acc x) (0, none)
        (hw.map (fun wp => (wp.1, partyEnc wp.2)))).2 by
    congr 2; funext x ⟨cnt, o⟩
    simp only [Expr.v0, Expr.v1, Expr.v2, Expr.eval, Env.get, ρ₀, heqW]
    cases o with
    | none =>
      simp only [stepRevIdx, pEnc]
      congr 2
      rw [boolEq_eval, otherE_eval]
      rfl
    | some j => rfl]
  rw [foldr_stepRevIdx_eq_findIdx pEnc, ← List.map_reverse, List.findIdx?_map]
  congr 1
  funext ⟨w', p'⟩
  have hother : (!partyEnc Q) = partyEnc Q.other := by cases Q <;> rfl
  simp only [Function.comp_def, pEnc, hother, partyEnc_beq_iff]

theorem findRevHonestWiresIdxE_cost (q : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) :
    (findRevHonestWiresIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q wiresE qBE wE).cost ≤
      wiresE.cost + qBE.cost + wE.cost + 100 * q + 20 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hop : (AOps).cost (.inl (.inl (.inl (.inl (.bytesEq 32 32))))) = 64 := rfl
  let ΓI : List (Ty ASig) :=
    .prod (B 32) .bool :: .prod .nat (.opt .nat) :: .prod .bool (B 32) :: Γ
  let bodyE : Expr AOps ΓI (.prod .nat (.opt .nat)) :=
    .pair (.add (.fst .v1) (.nat 1))
      (.caseOpt (.snd .v1)
        (.ite
          (.and
            (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) (.bytesEq 32 32) (.pair (.fst .v0) (.snd .v2)))
            (boolEq (.snd .v0) (otherE (.fst .v2))))
          (.some (.fst .v1)) .none)
        (.some .v0))
  have hbody : bodyE.cost ≤ 95 := by
    dsimp only [bodyE, sessPureOp]
    simp only [boolEq, otherE, Expr.cost, Expr.v0, Expr.v1, Expr.v2, hb1, hop]
    omega
  have hqmul : q * (bodyE.cost + 1) ≤ 100 * q := by
    have h := Nat.mul_le_mul_left q (show bodyE.cost + 1 ≤ 100 by omega)
    omega
  change (Expr.letE (.pair qBE wE)
    (.snd (.foldrB q (renExpr Var.succ wiresE) (.pair (.nat 0) .none) bodyE))).cost ≤ _
  simp only [AtomicSessionBridge.renExpr_cost, Expr.cost, hb0]
  generalize bodyE.cost = cb at hbody hqmul ⊢
  omega

theorem findRevHonestWiresIdxE_size (q : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) :
    (findRevHonestWiresIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q wiresE qBE wE).size ≤
      wiresE.size + qBE.size + wE.size + bits q + 60 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hop : (AOps).opSize (.inl (.inl (.inl (.inl (.bytesEq 32 32))))) = 0 := rfl
  simp only [findRevHonestWiresIdxE, boolEq, otherE, SessionProgCommon.renExpr_size, sessPureOp,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, hb0, hb1, hop]
  omega

end StateAndLookup

/-! ## Pre/post-send stages and tracker-halted step handler -/

section StepHalted

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT
local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

private theorem issue1275FixEsC_size_le {Γ : List (Ty ASig)} (esE : Expr AOps Γ (B 2080)) :
    (issue1275FixEsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) esE).size ≤ esE.size + 400 := by
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hb256 : bits 256 = 9 := by decide
  have hb1024 : bits 1024 = 11 := by decide
  have hb1536 : bits 1536 = 11 := by decide
  have hb2048 : bits 2048 = 12 := by decide
  have haP : ∀ (o : _root_.ReductionDsl.AtomicPureOp),
      (AOps).opSize (.inl (.inl (.inl (.inl o)))) = o.opSize := fun _ => rfl
  have hscan : (issue1275ScanStepE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (Γ := B 2080 :: Γ)).size ≤ 135 := by
    simp only [issue1275ScanStepE, bytes2EqLitE, boolOrE, SimFig8State.eLet, sOpPure, sessPureOp,
      Expr.size, haP, _root_.ReductionDsl.AtomicPureOp.opSize, List.length_cons,
      List.length_nil, Expr.v0, Expr.v1, hb1, hb2]
    omega
  have hswap : (swapPairsStepE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ)).size ≤ 60 := by
    simp only [swapPairsStepE, sOpPure, sessPureOp, Expr.size, haP,
      _root_.ReductionDsl.AtomicPureOp.opSize, Expr.v0, hb1, hb2]
    omega
  dsimp only [issue1275FixEsC]
  generalize issue1275ScanStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := B 2080 :: Γ) = eScan at hscan ⊢
  generalize swapPairsStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ) = eSwap at hswap ⊢
  simp only [sOpPure, sessPureOp, Comp.size, Expr.size, haP,
    _root_.ReductionDsl.AtomicPureOp.opSize, List.length_nil,
    Expr.v0, Expr.v1, Expr.v2, hb256, hb1024, hb1536, hb2048]
  omega

theorem stepKemFailSendAtomicC_size_le (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q trE qBE rqE).size ≤
      trE.size + qBE.size + rqE.size + bits (q + 1) + 1200 := by
  let Γ0 := Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ
  let Γc := BV512 :: Ty.sum BV512 (.prod BV512 BV256) ::
    Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ0
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hb3 : bits 3 = 2 := rfl
  have haP : ∀ (o : _root_.ReductionDsl.AtomicPureOp),
      (AOps).opSize (.inl (.inl (.inl (.inl o)))) = o.opSize := fun _ => rfl
  have haS : ∀ (o : _root_.ReductionDsl.AtomicSpqrKemOp),
      (AOps).opSize (.inr o) = 0 := fun _ => rfl
  have hfix := issue1275FixEsC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .prod (B 960) (.prod (B 2080) BV256) ::
      .prod (_root_.ReductionDsl.AtomicSpqrKemOp.kem768FromSeed.cod ℓ Pt) BV256 :: Γc)
    (.fst (.snd .v0))
  have hcand : (nextKemCandAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ0) (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))).size ≤
      650 := by
    dsimp only [nextKemCandAtomicC, honestExchangeFailsAtomicC, encRandBvAtomicE,
      isHeaderReceivedV1E, ekSideIsAE, boolEqE, trE_cand, trE_st, trE_e, trE_c, pGet]
    simp only [sOpPure, sOpSpqr, sessPureOp, sessSpqrKemOp, Comp.size, Expr.size, haP, haS,
      _root_.ReductionDsl.AtomicPureOp.opSize, List.length_cons, List.length_nil,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb1, hb2] at hfix ⊢
    omega
  have hpost : (stepPostKemSendE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q (Γ := .opt (.prod BV512 BV256) :: Γ0)
      (.fst .v1) (.fst (.snd .v1)) (.snd (.snd .v1)) .v0).size ≤ bits (q + 1) + 450 := by
    dsimp only [stepPostKemSendE, nextKemCoinsAtomicE, isKeysUnsampledV1E, isHeaderReceivedV1E,
      encRandBvAtomicE, SimFig8State.eLet, trMk, trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr,
      trE_cand, pGet, pSet]
    dsimp only [sOpPure, sOpSpqr, sessPureOp, sessSpqrKemOp, Expr.size, Expr.v0, Expr.v1, Expr.v2]
    simp only [haP, haS, _root_.ReductionDsl.AtomicPureOp.opSize, List.length_cons, List.length_nil,
      hb1]
    omega
  dsimp only [stepKemFailSendAtomicC] at hcand hpost ⊢
  simp only [Comp.size, Expr.size, Expr.v0, Expr.v1] at hcand hpost ⊢
  omega

abbrev preSendInTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (e2eGsTy ℓ)
    (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.PlainT
        (.prod (.opt CryptoVerification.E2E.Costed.BV512) .bool))))

abbrev preSendOutTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .opt (.prod (e2eGsTy ℓ) (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512))

@[expose] def preSendE2EC {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (coins : E2ECoinSamplers ℓ zeroPqxdhPrims C K decT encT I)
    (Δ qep : ℕ) {Γ : List (Ty ESig)}
    (argE : Expr EOps Γ (preSendInTy ℓ)) :
    Comp EOps I Γ (preSendOutTy ℓ) :=
  .bind (.ret argE)
    (let gs0 : Expr EOps _ (e2eGsTy ℓ) := .fst .v0
     let p0 : Expr EOps _ .bool := .fst (.snd .v0)
     let optR0 : Expr EOps _ (.opt CryptoVerification.E2E.Costed.BV512) :=
       .fst (.snd (.snd (.snd (.snd .v0))))
     .ite (orE (.not (e2eSendOKE gs0 p0)) (e2eGsWin gs0))
       (.ret .none)
       (.bind (e2eSamIfNec512C coins optR0)
         (.caseOpt (e2eEpMgmtE Δ qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0))
           (.ret .none)
           (let s1 : Expr EOps _ (e2eGsTy ℓ) := .v0
            let rCoins : Expr EOps _ CryptoVerification.E2E.Costed.BV512 := .fst .v1
            let gs2 : Expr EOps _ (e2eGsTy ℓ) := .fst .v2
            let p2 : Expr EOps _ .bool := .fst (.snd .v2)
            let m0_2 : Expr EOps _ CryptoVerification.E2E.Costed.PlainT := .fst (.snd (.snd .v2))
            let m1_2 : Expr EOps _ CryptoVerification.E2E.Costed.PlainT := .fst (.snd (.snd (.snd .v2)))
            let isCh2 : Expr EOps _ .bool := .snd (.snd (.snd (.snd (.snd .v2))))
            let mEff : Expr EOps _ CryptoVerification.E2E.Costed.PlainT :=
              .ite isCh2 (.ite (e2eGsB gs2) m1_2 m0_2) m0_2
            .ite (.and isCh2 (.not (e2eSafeChE Δ s1 p2)))
              (.ret .none)
              (.ret (.some (.pair s1 (.pair mEff rCoins))))))))

theorem preSendE2EC_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (coins : E2ECoinSamplers ℓ zeroPqxdhPrims C K decT encT I)
    (Δ qep : ℕ) {Γ : List (Ty ESig)} (argE : Expr EOps Γ (preSendInTy ℓ)) (w : I.Tag → ℕ) :
    (preSendE2EC coins Δ qep argE).queries w (fun _ => 0) = 0 := by
  simp [preSendE2EC, Comp.queries, e2eSamIfNec512C_queries_zero]

theorem preSendE2EC_cost {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (coins : E2ECoinSamplers ℓ zeroPqxdhPrims C K decT encT I)
    (Δ qep : ℕ) {Γ : List (Ty ESig)} (argE : Expr EOps Γ (preSendInTy ℓ)) :
    (preSendE2EC coins Δ qep argE).cost ≤ argE.cost + 2000 + 2 * bits Δ + bits qep := by
  let t0 := preSendInTy ℓ
  let t1 : Ty ESig := .prod CryptoVerification.E2E.Costed.BV512 .bool
  have hsendOK := cost_e2eSendOKE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hsam := e2eSamIfNec512C_cost coins
    (.fst (.snd (.snd (.snd (.snd .v0)))) : Expr EOps (t0 :: Γ) (.opt CryptoVerification.E2E.Costed.BV512))
  have hep := cost_e2eEpMgmtE_le (ℓ := ℓ) (O' := EOps) Δ qep
    (.fst .v1 : Expr EOps (t1 :: t0 :: Γ) (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0)
  have hsafe := cost_e2eSafeChE_le (ℓ := ℓ) (O' := EOps) Δ
    (.v0 : Expr EOps (e2eGsTy ℓ :: t1 :: t0 :: Γ) (e2eGsTy ℓ)) (.fst (.snd .v2))
  simp only [preSendE2EC, orE, e2eGsWin, e2eGsB, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2] at hsendOK hsam hep hsafe ⊢
  omega

theorem preSendE2EC_size_le {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (coins : E2ECoinSamplers ℓ zeroPqxdhPrims C K decT encT I)
    (h512 : ∀ {Γ'}, (coins.draw512 (Γ := Γ')).size ≤ 4)
    (Δ qep : ℕ) {Γ : List (Ty ESig)} (argE : Expr EOps Γ (preSendInTy ℓ)) :
    (preSendE2EC coins Δ qep argE).size ≤ argE.size + 2 * bits Δ + 2 * bits qep + 800 := by
  let t0 := preSendInTy ℓ
  let t1 : Ty ESig := .prod CryptoVerification.E2E.Costed.BV512 .bool
  have hd := h512 (Γ' := t0 :: Γ)
  have hsendOK := size_e2eSendOKE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hep := size_e2eEpMgmtE_le (ℓ := ℓ) (O' := EOps) Δ qep
    (.fst .v1 : Expr EOps (t1 :: t0 :: Γ) (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0)
  have hsafe := size_e2eSafeChE_le (ℓ := ℓ) (O' := EOps) Δ
    (.v0 : Expr EOps (e2eGsTy ℓ :: t1 :: t0 :: Γ) (e2eGsTy ℓ)) (.fst (.snd .v2))
  simp only [preSendE2EC, e2eSamIfNec512C, orE, e2eGsWin, e2eGsB, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2] at hsendOK hep hsafe hd ⊢
  omega

abbrev postSendInTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (e2eGsTy ℓ)
    (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.BV512 .bool)))

@[expose] def postSendE2EC (hooks : SpqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface ESig T)
    (q Δ : ℕ) {Γ : List (Ty ESig)}
    (argE : Expr EOps Γ (postSendInTy ℓ)) :
    Comp EOps I Γ (.prod (CryptoVerification.E2E.Costed.B 32) (e2eGsTy ℓ)) :=
  .bind (.ret argE)
    (.bind (drSendC hooks I
        (.pair (pGet (e2eGsSt (.fst .v0)) (.fst (.snd .v0)))
          (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))))))
      (let st' : Expr EOps _ CryptoVerification.E2E.Costed.GhostStT := .fst .v0
       let ct' : Expr EOps _ (CryptoVerification.E2E.Costed.B 32) := .snd .v0
       let s1 : Expr EOps _ (e2eGsTy ℓ) := .fst .v1
       let p1 : Expr EOps _ .bool := .fst (.snd .v1)
       let m1 : Expr EOps _ CryptoVerification.E2E.Costed.PlainT := .fst (.snd (.snd .v1))
       let isCh1 : Expr EOps _ .bool := .snd (.snd (.snd (.snd .v1)))
       let posE : Expr EOps _ posTy :=
         .pair p1 (.pair (pGet (e2eGsEpoch s1) p1) (.add (pGet (e2eGsIdx s1) p1) (.nat 1)))
       .ret (.pair ct' (e2eRecordE q Δ s1 p1 st' posE m1 ct' isCh1))))

theorem postSendE2EC_queries_zero (hooks : SpqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface ESig T)
    (q Δ : ℕ) {Γ : List (Ty ESig)} (argE : Expr EOps Γ (postSendInTy ℓ))
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (postSendE2EC hooks I q Δ argE).queries w ws = 0 := by
  simp [postSendE2EC, Comp.queries, drSendC_queries]

theorem postSendE2EC_cost (hooks : SpqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface ESig T)
    (q Δ : ℕ) {Γ : List (Ty ESig)} (argE : Expr EOps Γ (postSendInTy ℓ)) :
    (postSendE2EC hooks I q Δ argE).cost ≤
      argE.cost + 68280 + 10 * (ℓ / 32 + 1) + 135 * q + bits Δ := by
  let t0 := postSendInTy ℓ
  let tOut : Ty ESig := .prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32)
  have hsend := drSendC_cost hooks I
    (.pair (pGet (e2eGsSt (.fst .v0)) (.fst (.snd .v0)))
      (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))) :
      Expr EOps (t0 :: Γ)
        (.prod CryptoVerification.E2E.Costed.GhostStT
          (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)))
  have hrec := cost_e2eRecordE_le (ℓ := ℓ) (O' := EOps) q Δ
    (.fst .v1 : Expr EOps (tOut :: t0 :: Γ) (e2eGsTy ℓ))
    (.fst (.snd .v1)) (.fst .v0)
    (.pair (.fst (.snd .v1))
      (.pair (pGet (e2eGsEpoch (.fst .v1)) (.fst (.snd .v1)))
        (.add (pGet (e2eGsIdx (.fst .v1)) (.fst (.snd .v1))) (.nat 1))))
    (.fst (.snd (.snd .v1))) (.snd .v0) (.snd (.snd (.snd (.snd .v1))))
  have hb1 : bits 1 = 1 := rfl
  simp only [postSendE2EC, pGet, e2eGsSt, e2eGsEpoch, e2eGsIdx, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, hb1] at hsend hrec ⊢
  omega

theorem postSendE2EC_spqr_size_le {ι : Type} {T : OracleSpec ι} (I : Iface ESig T)
    (q Δ : ℕ) {Γ : List (Ty ESig)} (argE : Expr EOps Γ (postSendInTy ℓ)) :
    (postSendE2EC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) I q Δ argE).size ≤
      argE.size + 2 * bits q + bits Δ + 20000 := by
  let t0 := postSendInTy ℓ
  let tOut : Ty ESig := .prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32)
  have hsend := drSendC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) I
    (.pair (pGet (e2eGsSt (.fst .v0)) (.fst (.snd .v0)))
      (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))) :
      Expr EOps (t0 :: Γ)
        (.prod CryptoVerification.E2E.Costed.GhostStT
          (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)))
  have hrec := size_e2eRecordE_le (ℓ := ℓ) (O' := EOps) q Δ
    (.fst .v1 : Expr EOps (tOut :: t0 :: Γ) (e2eGsTy ℓ))
    (.fst (.snd .v1)) (.fst .v0)
    (.pair (.fst (.snd .v1))
      (.pair (pGet (e2eGsEpoch (.fst .v1)) (.fst (.snd .v1)))
        (.add (pGet (e2eGsIdx (.fst .v1)) (.fst (.snd .v1))) (.nat 1))))
    (.fst (.snd (.snd .v1))) (.snd .v0) (.snd (.snd (.snd (.snd .v1))))
  have hb1 : bits 1 = 1 := rfl
  simp only [postSendE2EC, pGet, e2eGsSt, e2eGsEpoch, e2eGsIdx, Comp.size, Expr.size,
    Expr.v0, Expr.v1, hb1] at hsend hrec ⊢
  omega

private theorem liftP_pure {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S0 T) {α : Type} (a : α) : I.liftP (pure a) = pure a := by
  simp [Iface.liftP]

private theorem liftP_bind {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S0 T) {α β : Type} (oa : ProbComp α) (f : α → ProbComp β) :
    I.liftP (oa >>= f) = I.liftP oa >>= fun x => I.liftP (f x) := by
  simp [Iface.liftP]

@[expose] noncomputable def preSendModel (Δ qep : ℕ)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (party : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512)) (isChall : Bool) :
    ProbComp (Option (GameState (GhostState Bytes) (Plain ℓ) Bytes × (Plain ℓ × BitVec 512))) := do
  if !(cfg.sendOK st party) || st.win then
    return none
  else
    let (coins, bad) ← samIfNec optR
    match st.epMgmt Δ qep party bad with
    | none => return none
    | some s1 =>
      if isChall && !(s1.safeCh Δ party) then
        return none
      else
        return some (s1, (if isChall then (if st.b then m1 else m0) else m0, coins))

theorem preSendE2EC_eval {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (coins : E2ECoinSamplers ℓ zeroPqxdhPrims C K decT encT I)
    (Δ qep : ℕ) {Γ : List (Ty ESig)} (argE : Expr EOps Γ (preSendInTy ℓ)) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (party : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512)) (isChall : Bool)
    (harg : argE.eval ρ = (e2eGsEnc st, (partyEnc party, (m0, (m1, (optR, isChall)))))) :
    (preSendE2EC coins Δ qep argE).eval ρ =
      Option.map (fun x => (e2eGsEnc x.1, x.2)) <$>
        I.liftP (preSendModel Δ qep
          (configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT))
          st party m0 m1 optR isChall) := by
  set cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes :=
    configEpoch0Distinguisher (ratchetKeyAdmissible protoSignalCodec decT encT)
  unfold preSendE2EC preSendModel
  dsimp only [Comp.eval]
  rw [harg, pure_bind]
  set ρ₁ := Env.cons (t := preSendInTy ℓ)
    (e2eGsEnc st, (partyEnc party, (m0, (m1, (optR, isChall))))) ρ
  have hSendOK : (e2eSendOKE (.fst (Expr.v0 (O := EOps))) (.fst (.snd .v0))).eval ρ₁ =
      cfg.sendOK st party :=
    eval_e2eSendOKE decT encT (.fst .v0) (.fst (.snd .v0)) ρ₁ st party rfl rfl
  have hNotSendOK :
      (Expr.not (e2eSendOKE (.fst (Expr.v0 (O := EOps))) (.fst (.snd .v0)))).eval ρ₁ =
        !cfg.sendOK st party :=
    congrArg Bool.not hSendOK
  have hWin : (e2eGsWin (.fst (Expr.v0 (O := EOps)))).eval ρ₁ = st.win := rfl
  have hCond :
      (orE (.not (e2eSendOKE (.fst (Expr.v0 (O := EOps))) (.fst (.snd .v0))))
        (e2eGsWin (.fst .v0))).eval ρ₁ =
      (!cfg.sendOK st party || st.win) := by
    rw [orE_eval, hNotSendOK, hWin]
  rw [hCond]
  by_cases href : !cfg.sendOK st party || st.win
  · simp [href, Expr.eval]
  · have hOptR :
        (Expr.fst (.snd (.snd (.snd (.snd (Expr.v0 (O := EOps))))))).eval ρ₁ = optR := rfl
    simp only [href, Bool.false_eq_true, ↓reduceIte, e2eSamIfNec512C_eval coins, hOptR,
      liftP_bind, map_bind]
    refine congrArg (I.liftP (samIfNec optR) >>= ·) (funext fun ⟨rCoins, bad⟩ => ?_)
    let t1 : Ty ESig := .prod CryptoVerification.E2E.Costed.BV512 .bool
    set ρ₂ := Env.cons (t := t1) (rCoins, bad) ρ₁
    have hep : (e2eEpMgmtE Δ qep (.fst (Expr.v1 (O := EOps))) (.fst (.snd .v1)) (.snd .v0)).eval ρ₂ =
        (st.epMgmt Δ qep party bad).map e2eGsEnc :=
      eval_e2eEpMgmtE Δ qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0) ρ₂ st party rfl rfl
    rw [hep]
    cases hepEq : st.epMgmt Δ qep party bad with
    | none => simp [Expr.eval]
    | some s1 =>
      simp only [Option.map_some]
      set ρ₃ := Env.cons (t := e2eGsTy ℓ) (e2eGsEnc s1) ρ₂
      have hSafe : (e2eSafeChE Δ (Expr.v0 (O := EOps)) (.fst (.snd .v2))).eval ρ₃ =
          s1.safeCh Δ party :=
        eval_e2eSafeChE Δ .v0 (.fst (.snd .v2)) ρ₃ s1 party rfl rfl
      simp only [Expr.eval, hSafe]
      cases isChall <;> cases hsafe : s1.safeCh Δ party <;>
        simp [ρ₃, ρ₂, ρ₁, e2eGsB, e2eGsEnc, Expr.eval, Expr.v0, Expr.v1, Expr.v2]

theorem postSendE2EC_eval (hooks : SpqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface ESig T)
    (q Δ : ℕ) {Γ : List (Ty ESig)} (argE : Expr EOps Γ (postSendInTy ℓ)) (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (s1 : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (party : Party) (mEff : Plain ℓ) (rCoins : BitVec 512) (isChall : Bool)
    (hgParty : PartyReachInv C K (s1.st party))
    (htr1_le : s1.trans.length ≤ q) (hcp1_le : (dedupComp s1.comp).length ≤ q)
    (harg : argE.eval ρ = (e2eGsEnc s1, (partyEnc party, (mEff, (rCoins, isChall))))) :
    (postSendE2EC hooks I q Δ argE).eval ρ =
      let out := (sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins).send
        (s1.st party) mEff rCoins
      pure (out.2,
        e2eGsEnc (s1.record Δ party out.1 ⟨⟨party, s1.epoch party, s1.idx party + 1⟩, mEff, out.2⟩
          isChall)) := by
  unfold postSendE2EC
  simp only [Comp.eval, Expr.eval, harg, pure_bind]
  set ρ₁ := Env.cons (t := postSendInTy ℓ)
    (e2eGsEnc s1, (partyEnc party, (mEff, (rCoins, isChall)))) ρ
  have hSendIn :
      (Expr.pair (pGet (e2eGsSt (.fst (Expr.v0 (O := EOps)))) (.fst (.snd .v0)))
        (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))))).eval ρ₁ =
      (s1.st party, (mEff, rCoins)) := by
    rw [pair_eval, pGet_eval _ _ ρ₁ s1.st party rfl rfl]; rfl
  have hgParty' : PartyReachInv C K
      ((Expr.pair (pGet (e2eGsSt (.fst (Expr.v0 (O := EOps)))) (.fst (.snd .v0)))
        (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))))).eval ρ₁).1 := by
    rw [hSendIn]; exact hgParty
  rw [drSendC_eval hooks I _ ρ₁ idA idB spkCoins hgParty', hSendIn]
  simp only [pure_bind]
  set out := (sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins).send
    (s1.st party) mEff rCoins
  set ρ₂ := Env.cons
    (t := .prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32))
    out ρ₁
  have hpos2 :
      (Expr.pair (.fst (.snd (Expr.v1 (O := EOps))))
        (.pair (pGet (e2eGsEpoch (.fst .v1)) (.fst (.snd .v1)))
          (.add (pGet (e2eGsIdx (.fst .v1)) (.fst (.snd .v1))) (.nat 1)))).eval ρ₂ =
      posEnc ⟨party, s1.epoch party, s1.idx party + 1⟩ := by
    have hep2 : (pGet (e2eGsEpoch (.fst (Expr.v1 (O := EOps)))) (.fst (.snd .v1))).eval ρ₂ =
        s1.epoch party := pGet_eval (t := .nat) _ _ ρ₂ s1.epoch party rfl rfl
    have hidx2 : (pGet (e2eGsIdx (.fst (Expr.v1 (O := EOps)))) (.fst (.snd .v1))).eval ρ₂ =
        s1.idx party := pGet_eval (t := .nat) _ _ ρ₂ s1.idx party rfl rfl
    simp only [Expr.eval, hep2, hidx2]; rfl
  have hrec2 := eval_e2eRecordE q Δ (.fst .v1 : Expr EOps _ (e2eGsTy ℓ)) (.fst (.snd .v1))
    (.fst .v0)
    (.pair (.fst (.snd .v1))
      (.pair (pGet (e2eGsEpoch (.fst .v1)) (.fst (.snd .v1)))
        (.add (pGet (e2eGsIdx (.fst .v1)) (.fst (.snd .v1))) (.nat 1))))
    (.fst (.snd (.snd .v1))) (.snd .v0) (.snd (.snd (.snd (.snd .v1))))
    ρ₂ s1 party ⟨party, s1.epoch party, s1.idx party + 1⟩
    htr1_le hcp1_le rfl rfl hpos2
  simp only [Expr.eval, hrec2]; rfl

abbrev smRATy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  liftTy (Pt := Pt) (smRT CryptoVerification.E2E.Costed.GhostStT)

@[expose] def smRWireAE {Γ : List (Ty ASig)} (w? : Expr AOps Γ (.opt (B 32))) :
    Expr AOps Γ (smRATy ℓ Pt) :=
  .pair w? (.pair .none .none)

abbrev sendReqATy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .bool (.prod (PlainT (ℓ := ℓ) (Pt := Pt))
    (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (.prod (.opt BV512) .bool)))

/-- Unified `AOps` `.tr`/`.ch` handler gating `postSendE2EC` with `O(1)` `stepKemFailSendAtomicC`. -/
@[expose] def sendOrChallTrackC (q Δ qep : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt))
    (reqE : Expr AOps Γ (sendReqATy ℓ Pt)) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ (.prod (smRATy ℓ Pt) (epoch0HaltedStTy ℓ Pt)) :=
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  let cPreA := liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (preSendE2EC coins Δ qep (Γ := [preSendInTy ℓ]) .v0)
  let cPostA := liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (postSendE2EC hooks (coinE2EIface (coinOnlyIface ℓ Pt)) q Δ (Γ := [postSendInTy ℓ]) .v0)
  .bind (.ret (.pair stE reqE))
    (.bind (call1C cPreA (.pair (.fst (.fst .v0)) (.snd .v0)))
      (.caseOpt .v0
        (.ret (.pair (smRWireAE .none) (.fst .v1)))
        (.bind
          (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) q
            (.fst (.snd (.fst .v2))) (.fst (.snd .v2)) (.snd (.snd .v0)))
          (.ite (isSomeE (trE_cand (.fst .v0)))
            (.ret (.pair (smRWireAE .none)
              (.pair (.fst (.fst .v3)) (.pair (.snd .v0) (.snd (.snd (.fst .v3)))))))
            (.bind
              (call1C cPostA
                (.pair (.fst .v1)
                  (.pair (.fst (.snd .v3))
                    (.pair (.fst (.snd .v1))
                      (.pair (.snd (.snd .v1))
                        (.snd (.snd (.snd (.snd (.snd .v3))))))))))
              (.ret (.pair (smRWireAE (.some (.fst .v0)))
                (.pair (.snd .v0)
                  (.pair (.fst .v1)
                    (.cons (.pair (.fst .v0) (.fst (.snd .v4)))
                      (.snd (.snd (.fst .v4)))))))))))))

theorem sendOrChallTrackC_queries_zero (q Δ qep : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt)) (reqE : Expr AOps Γ (sendReqATy ℓ Pt))
    (w : Empty → ℕ) :
    (sendOrChallTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q Δ qep stE reqE).queries w (fun _ => 0) = 0 := by
  simp [sendOrChallTrackC, Comp.queries, call1C_queries, liftCompCoins_queries_zero,
    stepKemFailSendAtomicC_queries_zero]

theorem sendOrChallTrackC_cost (q Δ qep : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt)) (reqE : Expr AOps Γ (sendReqATy ℓ Pt)) :
    (sendOrChallTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q Δ qep stE reqE).cost ≤
      stE.cost + reqE.cost + 17350000 + 320 * (ℓ / 32 + 1) + 4330 * q +
        96 * bits Δ + 32 * bits qep := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  let cPreE := preSendE2EC coins Δ qep (Γ := [preSendInTy ℓ]) .v0
  let cPostE := postSendE2EC hooks (coinE2EIface (coinOnlyIface ℓ Pt)) q Δ (Γ := [postSendInTy ℓ]) .v0
  have hpre1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cPreE
  have hpre2 := preSendE2EC_cost coins Δ qep (Γ := [preSendInTy ℓ]) .v0
  have hpost1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cPostE
  have hpost2 := postSendE2EC_cost hooks (coinE2EIface (coinOnlyIface ℓ Pt)) q Δ
    (Γ := [postSendInTy ℓ]) .v0
  let tPair := Ty.prod (epoch0HaltedStTy ℓ Pt) (sendReqATy ℓ Pt)
  let tPre := liftTy (Pt := Pt) (preSendOutTy ℓ)
  let tSome := Ty.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) BV512)
  have htr := stepKemFailSendAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q
    (Γ := tSome :: tPre :: tPair :: Γ)
    (.fst (.snd (.fst .v2))) (.fst (.snd .v2)) (.snd (.snd .v0))
  dsimp only [sendOrChallTrackC, cPreE, cPostE, hooks, coins] at hpre1 hpre2 hpost1 hpost2 ⊢
  simp only [call1C_cost, smRWireAE, isSomeE, trE_cand, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hpre1 hpre2 hpost1 hpost2 htr ⊢
  omega

theorem sendOrChallTrackC_size_le (q Δ qep : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt)) (reqE : Expr AOps Γ (sendReqATy ℓ Pt)) :
    (sendOrChallTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q Δ qep stE reqE).size ≤
      stE.size + reqE.size + 18 * bits q + bits (q + 1) + 27 * bits Δ + 18 * bits qep +
        190000 := by
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  have h512 : ∀ {Γ'}, (coins.draw512 (Γ := Γ')).size ≤ 4 := by
    intro Γ'; simp [coins, coinE2ESamplers, mkE2ECoinSamplers, Comp.size, Expr.size]
  let cPreE := preSendE2EC coins Δ qep (Γ := [preSendInTy ℓ]) .v0
  let cPostE := postSendE2EC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    (coinE2EIface (coinOnlyIface ℓ Pt)) q Δ (Γ := [postSendInTy ℓ]) .v0
  have hpre1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cPreE
  have hpre2 := preSendE2EC_size_le coins h512 Δ qep (Γ := [preSendInTy ℓ]) .v0
  have hpost1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cPostE
  have hpost2 := postSendE2EC_spqr_size_le (C := C) (K := K) (decT := decT) (encT := encT)
    (coinE2EIface (coinOnlyIface ℓ Pt)) q Δ (Γ := [postSendInTy ℓ]) .v0
  let tPair := Ty.prod (epoch0HaltedStTy ℓ Pt) (sendReqATy ℓ Pt)
  let tPre := liftTy (Pt := Pt) (preSendOutTy ℓ)
  let tSome := Ty.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) BV512)
  have htr := stepKemFailSendAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q
    (Γ := tSome :: tPre :: tPair :: Γ)
    (.fst (.snd (.fst .v2))) (.fst (.snd .v2)) (.snd (.snd .v0))
  dsimp only [sendOrChallTrackC, cPreE, cPostE, coins] at hpre1 hpre2 hpost1 hpost2 ⊢
  simp only [call1C_size, smRWireAE, isSomeE, trE_cand, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hpre1 hpre2 hpost1 hpost2 htr ⊢
  omega

/-- `AOps` `.dl` arm handler indexing `honestWires.reverse.findIdx?` before `drDlArmC` and
updating `kemOnDeliverPostAtomicE`. -/
@[expose] def dlArmTrackC (q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt))
    (dlArg : Expr AOps Γ (.prod .bool (B 32))) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ (.prod (smRATy ℓ Pt) (epoch0HaltedStTy ℓ Pt)) :=
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  let cDlA := liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (drDlArmC hooks coins q
      (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))])
      (.fst .v0) (.snd .v0))
  .bind (.ret (.pair stE dlArg))
    (.bind
      (.ret (findRevHonestWiresIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) q
        (.snd (.snd (.fst .v0))) (.fst (.snd .v0)) (.snd (.snd .v0))))
      (.bind (call1C cDlA (.pair (.fst (.fst .v1)) (.snd .v1)))
        (.ret (.pair (.fst .v0)
          (.pair (.snd .v0)
            (.pair
              (kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam) q
                (.fst (.snd .v2)) .v1 (.fst (.snd (.fst .v0))) (.fst (.snd (.fst .v2))))
              (.snd (.snd (.fst .v2)))))))))

theorem dlArmTrackC_queries_zero (q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt)) (dlArg : Expr AOps Γ (.prod .bool (B 32)))
    (w : Empty → ℕ) :
    (dlArmTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q stE dlArg).queries w (fun _ => 0) = 0 := by
  simp [dlArmTrackC, Comp.queries, call1C_queries, liftCompCoins_queries_zero]

theorem dlArmTrackC_cost (q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt)) (dlArg : Expr AOps Γ (.prod .bool (B 32))) :
    (dlArmTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q stE dlArg).cost ≤
      stE.cost + dlArg.cost + 163370000 + 256 * (ℓ / 32 + 1) + 11820 * q := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  let cDlE := drDlArmC hooks coins q
    (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]) (.fst .v0) (.snd .v0)
  have hdl1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cDlE
  have hdl2 := drDlArmC_cost hooks coins q
    (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]) (.fst .v0) (.snd .v0)
  let tPair := Ty.prod (epoch0HaltedStTy ℓ Pt) (.prod .bool (B 32))
  let tDlOut := Ty.prod (smRATy ℓ Pt) (liftTy (Pt := Pt) (e2eGsTy ℓ))
  have hfind := findRevHonestWiresIdxE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := tPair :: Γ)
    (.snd (.snd (.fst .v0))) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hpost := kemOnDeliverPostAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := tDlOut :: .opt .nat :: tPair :: Γ)
    (.fst (.snd .v2)) .v1 (.fst (.snd (.fst .v0))) (.fst (.snd (.fst .v2)))
  dsimp only [dlArmTrackC, cDlE, hooks, coins] at hdl1 hdl2 ⊢
  simp only [call1C_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hdl1 hdl2 hfind hpost ⊢
  omega

theorem dlArmTrackC_size_le (q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt)) (dlArg : Expr AOps Γ (.prod .bool (B 32))) :
    (dlArmTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q stE dlArg).size ≤
      stE.size + dlArg.size + 54 * bits q + 720000 := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  have h256 : ∀ {Γ'}, (coins.draw256 (Γ := Γ')).size ≤ 4 := fun {_} => by
    simp [coins, coinE2ESamplers, mkE2ECoinSamplers, Comp.size, Expr.size]
  let cDlE := drDlArmC hooks coins q
    (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]) (.fst .v0) (.snd .v0)
  have hdl1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cDlE
  have hdl2 := drDlArmC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) coins h256 q
    (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]) (.fst .v0) (.snd .v0)
  let tPair := Ty.prod (epoch0HaltedStTy ℓ Pt) (.prod .bool (B 32))
  let tDlOut := Ty.prod (smRATy ℓ Pt) (liftTy (Pt := Pt) (e2eGsTy ℓ))
  have hfind := findRevHonestWiresIdxE_size (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := tPair :: Γ)
    (.snd (.snd (.fst .v0))) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hpost1 := expr_size_le_atomicExprDescBits atomicSessionOpDescBits
    (kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q (Γ := tDlOut :: .opt .nat :: tPair :: Γ)
      (.fst (.snd .v2)) .v1 (.fst (.snd (.fst .v0))) (.fst (.snd (.fst .v2))))
  have hpost2 := kemOnDeliverPostAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := tDlOut :: .opt .nat :: tPair :: Γ)
    (.fst (.snd .v2)) .v1 (.fst (.snd (.fst .v0))) (.fst (.snd (.fst .v2)))
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb2 : bits 2 = 2 := by decide
  dsimp only [dlArmTrackC, cDlE, hooks, coins] at hdl1 hdl2 ⊢
  generalize kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q
    (.fst (.snd .v2)) .v1 (.fst (.snd (.fst .v0))) (.fst (.snd (.fst .v2)) :
      Expr AOps (tDlOut :: .opt .nat :: tPair :: Γ) _) = ePost at hpost1 hpost2 ⊢
  simp only [atomicExprDescBits, varIdx, Expr.v0, Expr.v1, Expr.v2, hb0, hb1, hb2] at hpost2
  simp only [call1C_size, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2]
    at hdl1 hdl2 hfind ⊢
  omega

@[expose] def liftGsArmTrackC {argT : Ty ASig}
    (cArm : Comp AOps (coinOnlyIface ℓ Pt) [.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) argT]
      (.prod (smRATy ℓ Pt) (liftTy (Pt := Pt) (e2eGsTy ℓ))))
    {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt)) (argE : Expr AOps Γ argT) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ (.prod (smRATy ℓ Pt) (epoch0HaltedStTy ℓ Pt)) :=
  .bind (.ret (.pair stE argE))
    (.bind (call1C cArm (.pair (.fst (.fst .v0)) (.snd .v0)))
      (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd (.fst .v1))))))

theorem liftGsArmTrackC_queries {argT : Ty ASig}
    (cArm : Comp AOps (coinOnlyIface ℓ Pt) [.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) argT]
      (.prod (smRATy ℓ Pt) (liftTy (Pt := Pt) (e2eGsTy ℓ))))
    {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt)) (argE : Expr AOps Γ argT)
    (w : Empty → ℕ) :
    (liftGsArmTrackC cArm stE argE).queries w (fun _ => 0) =
      cArm.queries w (fun _ => 0) := by
  simp [liftGsArmTrackC, Comp.queries, call1C_queries]

theorem liftGsArmTrackC_cost {argT : Ty ASig}
    (cArm : Comp AOps (coinOnlyIface ℓ Pt) [.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) argT]
      (.prod (smRATy ℓ Pt) (liftTy (Pt := Pt) (e2eGsTy ℓ))))
    {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt)) (argE : Expr AOps Γ argT) :
    (liftGsArmTrackC cArm stE argE).cost ≤ stE.cost + argE.cost + cArm.cost + 30 := by
  simp only [liftGsArmTrackC, call1C_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
  omega

theorem liftGsArmTrackC_size {argT : Ty ASig}
    (cArm : Comp AOps (coinOnlyIface ℓ Pt) [.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) argT]
      (.prod (smRATy ℓ Pt) (liftTy (Pt := Pt) (e2eGsTy ℓ))))
    {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt)) (argE : Expr AOps Γ argT) :
    (liftGsArmTrackC cArm stE argE).size ≤ stE.size + argE.size + cArm.size + 30 := by
  simp only [liftGsArmTrackC, call1C_size, Comp.size, Expr.size, Expr.v0, Expr.v1]
  omega

/-- Combined 5-oracle step handler for `oracleImplRSessionTrackHalted` over `AOps`. -/
@[expose] def epoch0OracleStepTrackC (q Δ qep : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt))
    (qryE : Expr AOps Γ (liftTy (Pt := Pt) smQT)) :
    Comp AOps (coinOnlyIface ℓ Pt) Γ (.prod (smRATy ℓ Pt) (epoch0HaltedStTy ℓ Pt)) :=
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  let cIjA := liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (epoch0IjArmC hooks coins q Δ qep
      (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]) (.fst .v0) (.snd .v0))
  let cCrA := liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (epoch0CrArmC (C := C) (K := K) (decT := decT) (encT := encT)
      (I := coinE2EIface (coinOnlyIface ℓ Pt)) q
      (Γ := [.prod (e2eGsTy ℓ) .bool]) (.fst .v0) (.snd .v0))
  .bind (.ret (.pair stE qryE))
    (.caseSum (.snd .v0)
      (sendOrChallTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) q Δ qep (.fst .v1)
        (.pair (.fst .v0) (.pair (.fst (.snd .v0))
          (.pair (.fst (.snd .v0)) (.pair (.snd (.snd .v0)) (.bool false))))))
      (.caseSum .v0
        (sendOrChallTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) q Δ qep (.fst .v2)
          (.pair (.fst .v0) (.pair (.fst (.snd .v0))
            (.pair (.fst (.snd (.snd .v0))) (.pair (.snd (.snd (.snd .v0))) (.bool true))))))
        (.caseSum .v0
          (dlArmTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) q (.fst .v3) .v0)
          (.caseSum .v0
            (liftGsArmTrackC cIjA (.fst .v4) .v0)
            (liftGsArmTrackC cCrA (.fst .v4) .v0)))))

theorem epoch0OracleStepTrackC_queries_zero (q Δ qep : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt))
    (qryE : Expr AOps Γ (liftTy (Pt := Pt) smQT)) (w : Empty → ℕ) :
    (epoch0OracleStepTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q Δ qep stE qryE).queries w (fun _ => 0) = 0 := by
  simp [epoch0OracleStepTrackC, Comp.queries, sendOrChallTrackC_queries_zero,
    dlArmTrackC_queries_zero, liftGsArmTrackC_queries, liftCompCoins_queries_zero]

theorem epoch0OracleStepTrackC_cost (q Δ qep : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt))
    (qryE : Expr AOps Γ (liftTy (Pt := Pt) smQT)) :
    (epoch0OracleStepTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q Δ qep stE qryE).cost ≤
      stE.cost + qryE.cost + 163380000 + 320 * (ℓ / 32 + 1) + 13440 * q +
        96 * bits Δ + 32 * bits qep + 32 * bits (qep + 1) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  let cIjE := epoch0IjArmC hooks coins q Δ qep
    (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]) (.fst .v0) (.snd .v0)
  let cCrE := epoch0CrArmC (C := C) (K := K) (decT := decT) (encT := encT)
    (I := coinE2EIface (coinOnlyIface ℓ Pt)) q (Γ := [.prod (e2eGsTy ℓ) .bool]) (.fst .v0) (.snd .v0)
  let tTop : Ty ASig := .prod (epoch0HaltedStTy ℓ Pt) (liftTy (Pt := Pt) smQT)
  let r1T : Ty ASig :=
    .sum (.prod .bool (.prod (PlainT (ℓ := ℓ) (Pt := Pt))
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (.opt BV512))))
      (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))
  let r2T : Ty ASig := .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)
  let r3T : Ty ASig := .sum (.prod .bool (B 32)) .bool
  have htr := sendOrChallTrackC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q Δ qep
    (Γ := .prod .bool (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (.opt BV512)) :: tTop :: Γ) (.fst .v1)
    (.pair (.fst .v0) (.pair (.fst (.snd .v0))
      (.pair (.fst (.snd .v0)) (.pair (.snd (.snd .v0)) (.bool false)))))
  have hch := sendOrChallTrackC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q Δ qep
    (Γ := .prod .bool (.prod (PlainT (ℓ := ℓ) (Pt := Pt))
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (.opt BV512))) :: r1T :: tTop :: Γ) (.fst .v2)
    (.pair (.fst .v0) (.pair (.fst (.snd .v0))
      (.pair (.fst (.snd (.snd .v0))) (.pair (.snd (.snd (.snd .v0))) (.bool true)))))
  have hdl := dlArmTrackC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q
    (Γ := .prod .bool (B 32) :: r2T :: r1T :: tTop :: Γ) (.fst .v3) .v0
  have hij0 := liftGsArmTrackC_cost
    (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cIjE)
    (Γ := .prod .bool (B 32) :: r3T :: r2T :: r1T :: tTop :: Γ) (.fst .v4) .v0
  have hij1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cIjE
  have hij2 := epoch0IjArmC_cost hooks coins q Δ qep
    (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]) (.fst .v0) (.snd .v0)
  have hcr0 := liftGsArmTrackC_cost
    (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cCrE)
    (Γ := .bool :: r3T :: r2T :: r1T :: tTop :: Γ) (.fst .v4) .v0
  have hcr1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cCrE
  have hcr2 := epoch0CrArmC_cost (C := C) (K := K) (decT := decT) (encT := encT)
    (I := coinE2EIface (coinOnlyIface ℓ Pt)) q (Γ := [.prod (e2eGsTy ℓ) .bool]) (.fst .v0) (.snd .v0)
  dsimp only [epoch0OracleStepTrackC, cIjE, cCrE, hooks, coins] at hij0 hij1 hij2 hcr0 hcr1 hcr2 ⊢
  simp only [Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
    at htr hch hdl hij0 hij1 hij2 hcr0 hcr1 hcr2 ⊢
  omega

theorem epoch0OracleStepTrackC_size_le (q Δ qep : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (epoch0HaltedStTy ℓ Pt))
    (qryE : Expr AOps Γ (liftTy (Pt := Pt) smQT)) :
    (epoch0OracleStepTrackC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q Δ qep stE qryE).size ≤
      stE.size + qryE.size + 162 * bits q + 2 * bits (q + 1) + 72 * bits Δ +
        36 * bits qep + 9 * bits (qep + 1) + 1825000 := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  have h256 : ∀ {Γ'}, (coins.draw256 (Γ := Γ')).size ≤ 4 := fun {_} => by
    simp [coins, coinE2ESamplers, mkE2ECoinSamplers, Comp.size, Expr.size]
  let cIjE := epoch0IjArmC hooks coins q Δ qep
    (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]) (.fst .v0) (.snd .v0)
  let cCrE := epoch0CrArmC (C := C) (K := K) (decT := decT) (encT := encT)
    (I := coinE2EIface (coinOnlyIface ℓ Pt)) q (Γ := [.prod (e2eGsTy ℓ) .bool]) (.fst .v0) (.snd .v0)
  let tTop : Ty ASig := .prod (epoch0HaltedStTy ℓ Pt) (liftTy (Pt := Pt) smQT)
  let r1T : Ty ASig :=
    .sum (.prod .bool (.prod (PlainT (ℓ := ℓ) (Pt := Pt))
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (.opt BV512))))
      (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))
  let r2T : Ty ASig := .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)
  let r3T : Ty ASig := .sum (.prod .bool (B 32)) .bool
  have htr := sendOrChallTrackC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q Δ qep
    (Γ := .prod .bool (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (.opt BV512)) :: tTop :: Γ) (.fst .v1)
    (.pair (.fst .v0) (.pair (.fst (.snd .v0))
      (.pair (.fst (.snd .v0)) (.pair (.snd (.snd .v0)) (.bool false)))))
  have hch := sendOrChallTrackC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q Δ qep
    (Γ := .prod .bool (.prod (PlainT (ℓ := ℓ) (Pt := Pt))
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (.opt BV512))) :: r1T :: tTop :: Γ) (.fst .v2)
    (.pair (.fst .v0) (.pair (.fst (.snd .v0))
      (.pair (.fst (.snd (.snd .v0))) (.pair (.snd (.snd (.snd .v0))) (.bool true)))))
  have hdl := dlArmTrackC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q
    (Γ := .prod .bool (B 32) :: r2T :: r1T :: tTop :: Γ) (.fst .v3) .v0
  have hij0 := liftGsArmTrackC_size
    (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cIjE)
    (Γ := .prod .bool (B 32) :: r3T :: r2T :: r1T :: tTop :: Γ) (.fst .v4) .v0
  have hij1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cIjE
  have hij2 := epoch0IjArmC_spqr_size_le (C := C) (K := K) (decT := decT) (encT := encT)
    coins h256 q Δ qep
    (Γ := [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]) (.fst .v0) (.snd .v0)
  have hcr0 := liftGsArmTrackC_size
    (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cCrE)
    (Γ := .bool :: r3T :: r2T :: r1T :: tTop :: Γ) (.fst .v4) .v0
  have hcr1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl cCrE
  have hcr2 := epoch0CrArmC_size_le (C := C) (K := K) (decT := decT) (encT := encT)
    (I := coinE2EIface (coinOnlyIface ℓ Pt)) q (Γ := [.prod (e2eGsTy ℓ) .bool]) (.fst .v0) (.snd .v0)
  dsimp only [epoch0OracleStepTrackC, cIjE, cCrE, hooks, coins] at hij0 hij1 hij2 hcr0 hcr1 hcr2 ⊢
  simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
    at htr hch hdl hij0 hij1 hij2 hcr0 hcr1 hcr2 ⊢
  omega

@[expose] def finRen {S : Sig} {s t u : Ty S} : ∀ {v}, Var [s, u] v → Var [s, t, u] v
  | _, .zero => .zero
  | _, .succ .zero => .succ (.succ .zero)

@[expose] def epoch0HaltedFinishE (q : ℕ) : Expr AOps [epoch0HaltedStTy ℓ Pt, .bool] .bool :=
  .letE (.fst .v0)
    (renExpr finRen
      (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (epoch0FinishE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)))

theorem cost_epoch0HaltedFinishE_le (q : ℕ) :
    (epoch0HaltedFinishE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q).cost ≤
      384 * q + 4810 := by
  let finE2E := epoch0FinishE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have h1 := liftExpr_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) finE2E
  have h2 := cost_epoch0FinishE_le (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  dsimp only [epoch0HaltedFinishE, finE2E] at h1 ⊢
  simp only [renExpr_cost, Expr.cost, Expr.v0]
  omega

theorem size_epoch0HaltedFinishE_le (q : ℕ) :
    (epoch0HaltedFinishE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q).size ≤
      9 * bits q + 460 := by
  let finE2E := epoch0FinishE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have h1 := liftExpr_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) finE2E
  have h2 := size_epoch0FinishE_le (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  dsimp only [epoch0HaltedFinishE, finE2E] at h1 ⊢
  simp only [renExpr_size, Expr.size, Expr.v0]
  omega

theorem eval_epoch0HaltedFinishE (q : ℕ)
    (s : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (ts : KemFailTrackState C.F × List (Bytes × Party)) (b' : Bool)
    (hcorrs : s.corrs.length ≤ q) :
    (epoch0HaltedFinishE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q).eval
      (.cons (epoch0HaltedEnc (s, ts)) (.cons b' .nil)) =
      ((decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))) := by
  unfold epoch0HaltedFinishE
  rw [letE_eval, renExpr_eval]
  set ρFin : Env [epoch0HaltedStTy ℓ Pt, .bool] :=
    .cons (t := epoch0HaltedStTy ℓ Pt) (epoch0HaltedEnc (ℓ := ℓ) (Pt := Pt) (s, ts))
      (.cons (t := .bool) b' .nil)
  have hpull :
      pullEnv finRen
        (.cons (t := liftTy (Pt := Pt) (e2eGsTy ℓ))
          ((Expr.fst (Expr.v0 (O := AOps))).eval ρFin) ρFin) =
      .cons (t := liftTy (Pt := Pt) (e2eGsTy ℓ)) (liftVal (Pt := Pt) (e2eGsEnc s))
        (.cons (t := .bool) b' .nil) := rfl
  rw [hpull]
  have hev := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (epoch0FinishE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
    (.cons (e2eGsEnc s) (.cons b' .nil))
  change (liftExpr (epoch0FinishE q)).eval
      (.cons (liftVal (Pt := Pt) (e2eGsEnc s)) (.cons b' .nil)) = _ at hev
  rw [hev, eval_epoch0FinishE q s b' hcorrs]
  rfl

@[expose] def flatSt2 {S₁ S₂ : Type} {m : Type → Type} [Functor m] {α : Type}
    (c : StateT S₁ (StateT S₂ m) α) : StateT (S₁ × S₂) m α :=
  fun ⟨s₁, s₂⟩ => (fun ⟨⟨a, s₁'⟩, s₂'⟩ => (a, (s₁', s₂'))) <$> ((c.run s₁).run s₂)

theorem simulateQ_run_flatSt2 {ι : Type} {ospec : OracleSpec.{0, 0} ι} {S₁ S₂ α : Type}
    (impl : QueryImpl ospec (StateT S₁ (StateT S₂ ProbComp)))
    (oa : OracleComp ospec α) (s₁ : S₁) (s₂ : S₂) :
    ((simulateQ impl oa).run s₁).run s₂ =
      (fun ⟨a, ⟨s₁', s₂'⟩⟩ => ((a, s₁'), s₂')) <$>
        (simulateQ (fun q => flatSt2 (impl q)) oa).run (s₁, s₂) := by
  induction oa using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure a => simp
  | query_bind q k ih =>
    have hflat : (flatSt2 (impl q)).run (s₁, s₂) =
        (fun ⟨⟨a, s₁'⟩, s₂'⟩ => (a, (s₁', s₂'))) <$> (((impl q).run s₁).run s₂) := rfl
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      StateT.run_bind, hflat, map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind]
    refine congrArg (((impl q).run s₁).run s₂ >>= ·) (funext fun ⟨⟨u, s₁'⟩, s₂'⟩ => ?_)
    simpa only [map_eq_bind_pure_comp, Function.comp_def, id_eq] using ih u s₁' s₂'

end StepHalted

end Computational.Proofs.Game.PromotedCostedReds.HaltedEpoch0Step
