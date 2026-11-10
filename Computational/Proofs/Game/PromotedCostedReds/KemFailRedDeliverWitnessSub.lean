/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8State
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
public import Computational.Proofs.E2E.Dsl.SpqrSimChain
public import Computational.Proofs.E2E.Dsl.ClampsLossless

/-!
# Atomic SPQR V1 Braid-Tracker Delivery Combinators and Bounds

Defines the atomic state encodings and expressions for `simStepKemFailDeliver`
(`kemTrackDeliverAtomicE`, `kemOnDeliverPostAtomicE`) over `atomicSessionOps`, together with cost
and description-size bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub

open _root_.ReductionDsl (Ty Env Expr bits
  atomicSig atomicSessionOps AtomicPureOp AtomicSpqrKemOp B U32 U64 BV256 BV512 PlainT
  partyToBool fig8CtT fig8CtV recvResultT spqrMsgPayloadSuffix bytesToWordLE)
open CryptoGames (Party)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (sendsInE otherE)
open CryptoGames.Ratchet.LibsignalSim (SimFig8C SimKemCoins SimKemFailTrack)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State encode_varint)
open CryptoVerification.E2E (Bytes)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost (honestPairEnc)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (eLet sOpPure sOpSpqr eval_eLet cost_eLet descBits_eLet
   eval_sOpPure cost_sOpPure descBits_sOpPure
   cost_sOpSpqr descBits_sOpSpqr bits_zero bits_eq_of_bounds)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSortDescBits atomicTyDescBits atomicPureOpDescBits
   atomicSessionOpDescBits atomicExprDescBits varIdx kemCandVecToBv)

@[reducible] def kemCoinsT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .sum .unit (.sum (BV512 (ℓ := ℓ) (Pt := Pt)) (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) (BV256 (ℓ := ℓ) (Pt := Pt))))

@[reducible] def kemSentEntryT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.prod (U64 (ℓ := ℓ) (Pt := Pt)) (B (ℓ := ℓ) (Pt := Pt) 64)) (U32 (ℓ := ℓ) (Pt := Pt))

/-- `SimKemFailTrack` state type in `atomicSig ℓ Pt`. -/
@[reducible] def kemTrackT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (U64 (ℓ := ℓ) (Pt := Pt))
    (.prod (kemCoinsT ℓ Pt)
      (.prod (.prod (B (ℓ := ℓ) (Pt := Pt) 32) (B (ℓ := ℓ) (Pt := Pt) 32))
        (.prod (.list (kemSentEntryT ℓ Pt))
          (.prod (.prod (.tbl .nat) (.tbl .nat))
            (.opt (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) (BV256 (ℓ := ℓ) (Pt := Pt))))))))

@[reducible] def kemCoinsAtomicEnc {ℓ : ℕ} {Pt : Type} : SimKemCoins → (kemCoinsT ℓ Pt).denote
  | .init => .inl ()
  | .seed s => .inr (.inl (bytesToWordLE 512 s.toList))
  | .both s r => .inr (.inr (bytesToWordLE 512 s.toList, bytesToWordLE 256 r.toList))

@[reducible] def kemTrackAtomicEnc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (tr : SimKemFailTrack F) : (kemTrackT ℓ Pt).denote :=
  (tr.e,
   (kemCoinsAtomicEnc tr.c,
    ((V1State.encodeRaw (tr.st .A).into_pb, V1State.encodeRaw (tr.st .B).into_pb),
     (tr.sentB.map (fun (m, ctr) => ((m.epoch, spqrMsgPayloadSuffix m), ctr)),
      ((tr.sendCtr .A, tr.sendCtr .B),
       tr.cand.map kemCandVecToBv)))))

section Helpers

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

/-- Coerce a `B 64` SPQR payload suffix of length `≤ 48` losslessly into `B 32` via
`.spqrAssembleMsg`. -/
def b64Take48ToB32E {Γ : List (Ty ASig)} (suf : Expr AOps Γ (B 64)) : Expr AOps Γ (B 32) :=
  sOpPure (.bytesDrop 32)
    (.pair (.nat 3)
      (sOpPure .spqrAssembleMsg
        (.pair (sOpPure (.u64Lit 0#64) .unit)
          (.pair (sOpPure (.u32Lit 0#32) .unit) suf))))

def listNthOptB (L : ℕ) {t : Ty ASig} {Γ : List (Ty ASig)}
    (xsE : Expr AOps Γ (.list t)) (jE : Expr AOps Γ .nat) : Expr AOps Γ (.opt t) :=
  eLet (.pair xsE jE) (
    let xs := Expr.fst .v0
    let len := Expr.foldrB L xs (.nat 0) (.add (.nat 1) .v1)
    .snd (.foldrB L xs (.pair len .none)
      (let dec := Expr.sub (.fst .v1) (.nat 1)
       .pair dec (.ite (.eqN dec (.snd .v2)) (.some .v0) (.snd .v1)))))

/-- Reverse index search in `honest` matching `honest.reverse.findIdx?` when `honest.length ≤ L`. -/
def findRevHonestIdxE (L : ℕ) {Γ : List (Ty ASig)}
    (honestE : Expr AOps Γ (.list (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) : Expr AOps Γ (.opt .nat) :=
  eLet (.pair honestE (.pair qBE wE)) (
    .fst (.foldrB L (.fst .v0) (.pair .none (.nat 0)) (
      let qOther := otherE (.fst (.snd .v2))
      let w := Expr.snd (.snd .v2)
      let wEntry := Expr.fst .v0
      let epEntry := Expr.fst (.fst (.snd .v0))
      let eqW := sOpPure (.bytesEq 32 32) (.pair wEntry w)
      let eqSender := sendsInE qOther epEntry
      let matched := Expr.and eqW eqSender
      let prevOpt := Expr.fst .v1
      let cnt := Expr.snd .v1
      let nextOpt := Expr.caseOpt prevOpt (.ite matched (.some cnt) .none) (.some .v0)
      .pair nextOpt (.add cnt (.nat 1)))))

/-- Atomic expression implementing `simStepKemFailDeliver C.F K tr Q j` over `kemTrackT ℓ Pt`. -/
def kemTrackDeliverAtomicE (L : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt))
    (qBE : Expr AOps Γ .bool)
    (jE : Expr AOps Γ .nat) : Expr AOps Γ (kemTrackT ℓ Pt) :=
  eLet (.pair trE (.pair qBE jE)) (
    let tr0 := Expr.fst .v0
    let j0 := Expr.snd (.snd .v0)
    let sentB0 := Expr.fst (.snd (.snd (.snd tr0)))
    .caseOpt (listNthOptB L sentB0 j0) tr0 (
      let tr1 := Expr.fst .v1
      let q1 := Expr.fst (.snd .v1)
      let mEp1 := Expr.fst (.fst .v0)
      let mSuf1 := b64Take48ToB32E (.snd (.fst .v0))
      let v1Pair1 := Expr.fst (.snd (.snd tr1))
      let stQ1 := Expr.ite q1 (.snd v1Pair1) (.fst v1Pair1)
      let recvOut := sOpSpqr .spqrBraidRecv (.pair stQ1 (.pair mEp1 mSuf1))
      .caseOpt (.snd (.snd recvOut)) tr1 (
        let newV1 := Expr.snd .v0
        let mEp2 := Expr.fst (.fst .v1)
        let mSuf2 := b64Take48ToB32E (.snd (.fst .v1))
        let tr2 := Expr.fst .v2
        let q2 := Expr.fst (.snd .v2)
        let e2 := Expr.fst tr2
        let c2 := Expr.fst (.snd tr2)
        let v1Pair2 := Expr.fst (.snd (.snd tr2))
        let rest2 := Expr.snd (.snd (.snd tr2))
        let v1Pair' := Expr.pair (.ite q2 (.fst v1Pair2) newV1) (.ite q2 newV1 (.snd v1Pair2))
        let eNext := sOpPure .u64Add (.pair e2 (sOpPure (.u64Lit 1#64) .unit))
        let isNoneNext := Expr.and
          (sOpPure .u64Eq (.pair mEp2 eNext))
          (sOpPure (.bytesEq 32 32) (.pair mSuf2 (sOpPure (.bytesLit 32 [0#8]) .unit)))
        let isBoth := Expr.caseSum c2 (.bool false) (.caseSum .v0 (.bool false) (.bool true))
        let advance := Expr.and isNoneNext isBoth
        .pair (.ite advance eNext e2)
          (.pair (.ite advance (.inl .unit) c2)
            (.pair v1Pair' rest2)))))

def kemOnDeliverPostAtomicE (L : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool)
    (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) : Expr AOps Γ (kemTrackT ℓ Pt) :=
  eLet (.pair qBE (.pair jOptE (.pair rrOptE trE))) (
    let rr0 := Expr.fst (.snd (.snd .v0))
    let tr0 := Expr.snd (.snd (.snd .v0))
    .caseOpt rr0 tr0
      (.caseSum .v0
        (.snd (.snd (.snd .v2)))
        (.caseOpt (.fst (.snd .v2))
          (.snd (.snd (.snd .v2)))
          (kemTrackDeliverAtomicE L (.snd (.snd (.snd .v3))) (.fst .v3) .v0))))

end Helpers

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

private theorem foldr_len_aux {α : Type} :
    ∀ (ys : List α), ys.foldr (fun _ (acc : ℕ) => 1 + acc) 0 = ys.length
  | [] => rfl
  | _ :: rest => by
    simp only [List.foldr_cons, foldr_len_aux rest, List.length_cons]
    omega

private theorem foldr_nthOpt_aux {α : Type} (idx : ℕ) :
    ∀ (ys : List α) (off : ℕ),
      ys.foldr (fun y (p : ℕ × Option α) =>
        (p.1 - 1, if decide (p.1 - 1 = idx) = true then some y else p.2)) (off + ys.length, none) =
        (off, if off ≤ idx then ys[idx - off]? else none)
  | [], off => by simp
  | y :: rest, off => by
    have hlen : off + (y :: rest).length = (off + 1) + rest.length := by
      simp only [List.length_cons]; omega
    simp only [List.foldr_cons, hlen, foldr_nthOpt_aux idx rest (off + 1)]
    have hsub1 : (off + 1) - 1 = off := Nat.add_sub_cancel off 1
    rw [hsub1]
    by_cases heq : off = idx
    · subst heq
      simp
    · by_cases hle : off ≤ idx
      · have hle' : off + 1 ≤ idx := by omega
        have hidx : idx - off = (idx - (off + 1)) + 1 := by omega
        simp [heq, hle, hle', hidx]
      · have hle' : ¬ (off + 1 ≤ idx) := by omega
        simp [heq, hle, hle']

private theorem sendsIn_other_eq_senderOf_beq (t : ℕ) (Q : Party) :
    (if !partyToBool Q then decide (t % 2 = 0) else decide (t % 2 = 1)) =
      (Party.senderOf t == Q.other) := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;>
    cases Q <;> simp [Party.senderOf, Party.other, partyToBool, h]

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

section EvalCostDesc

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

theorem b64Take48ToB32E_eval {Γ : List (Ty ASig)} (suf : Expr AOps Γ (B 64))
    (ρ : Env Γ) (bs : Bytes) (hsuf : suf.eval ρ = bs) (hlen : bs.length ≤ 48) :
    (b64Take48ToB32E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) suf).eval ρ = bs := by
  have hpre : encode_varint ((0#32).zeroExtend 64) (encode_varint 0#64 [1#8]) = [1#8, 0#8, 0#8] :=
    rfl
  have ht64 : bs.take 64 = bs := List.take_of_length_le (by omega)
  have ht96 : ([1#8, 0#8, 0#8] ++ bs).take 96 = [1#8, 0#8, 0#8] ++ bs :=
    List.take_of_length_le (by simp; omega)
  simp only [b64Take48ToB32E, eval_sOpPure, AtomicPureOp.eval, Expr.eval, hsuf, hpre, ht64, ht96]
  rfl

theorem b64Take48ToB32E_cost {Γ : List (Ty ASig)} (suf : Expr AOps Γ (B 64)) :
    (b64Take48ToB32E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) suf).cost ≤ suf.cost + 200 := by
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  simp only [b64Take48ToB32E, cost_sOpPure, AtomicPureOp.cost, Expr.cost, hb3_bits, h32]
  omega

theorem b64Take48ToB32E_descBits_le {Γ : List (Ty ASig)} (suf : Expr AOps Γ (B 64)) :
    atomicExprDescBits atomicSessionOpDescBits
      (b64Take48ToB32E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) suf) ≤
    atomicExprDescBits atomicSessionOpDescBits suf + 2000 := by
  simp only [b64Take48ToB32E, descBits_sOpPure, atomicPureOpDescBits, atomicExprDescBits,
    hb32_pnat, hb3_bits]
  omega

theorem listNthOptB_eval (L : ℕ) {t : Ty ASig} {Γ : List (Ty ASig)}
    (xsE : Expr AOps Γ (.list t)) (jE : Expr AOps Γ .nat) (ρ : Env Γ)
    (xs : List t.denote) (j : ℕ) (hxs : xsE.eval ρ = xs) (hj : jE.eval ρ = j)
    (hlen : xs.length ≤ L) :
    (listNthOptB (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L xsE jE).eval ρ = xs[j]? := by
  have htake : xs.take L = xs := List.take_of_length_le hlen
  have haux := foldr_nthOpt_aux j xs 0
  simp only [Nat.zero_add, Nat.zero_le, ↓reduceIte, Nat.sub_zero] at haux
  simp only [listNthOptB, eval_eLet, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get,
    hxs, hj, htake, foldr_len_aux, haux]

theorem listNthOptB_cost (L : ℕ) {t : Ty ASig} {Γ : List (Ty ASig)}
    (xsE : Expr AOps Γ (.list t)) (jE : Expr AOps Γ .nat) :
    (listNthOptB (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L xsE jE).cost ≤
    xsE.cost + jE.cost + 32 * L + 64 := by
  have hm : max 2 2 = 2 := rfl
  simp only [listNthOptB, cost_eLet, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    bits_zero, hb1_bits, Nat.reduceAdd, hm]
  omega

theorem listNthOptB_descBits_le (L : ℕ) {t : Ty ASig} {Γ : List (Ty ASig)}
    (xsE : Expr AOps Γ (.list t)) (jE : Expr AOps Γ .nat) :
    atomicExprDescBits atomicSessionOpDescBits
      (listNthOptB (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) L xsE jE) ≤
    atomicExprDescBits atomicSessionOpDescBits xsE +
      atomicExprDescBits atomicSessionOpDescBits jE +
      atomicTyDescBits t + 8 * bits L + 1000 := by
  dsimp only [listNthOptB, eLet, Expr.v0, Expr.v1, Expr.v2, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, bits_zero, hb1_bits, hb2_bits]
  omega

theorem findRevHonestIdxE_eval (L : ℕ) {Γ : List (Ty ASig)}
    (honestE : Expr AOps Γ (.list (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (ρ : Env Γ) (honest : List (Bytes × SimFig8C Pt)) (Q : Party) (w : Bytes)
    (hhon : honestE.eval ρ = honest.map honestPairEnc)
    (hq : qBE.eval ρ = partyToBool Q)
    (hw : wE.eval ρ = w)
    (hlen : honest.length ≤ L) :
    (findRevHonestIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L honestE qBE wE).eval ρ =
    honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) := by
  let p : Bytes × SimFig8C Pt → Bool :=
    fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other
  have htake : (honest.map (honestPairEnc (ℓ := ℓ) (Pt := Pt))).take L =
      honest.map honestPairEnc :=
    List.take_of_length_le (by simpa using hlen)
  simp only [findRevHonestIdxE, otherE, sendsInE, eval_eLet, eval_sOpPure, AtomicPureOp.eval,
    Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, hhon, hq, hw, htake, List.foldr_map]
  rw [← foldr_stepRevIdx_eq_findIdx p honest]
  refine congrArg Prod.fst (congrFun (congrFun (congrArg List.foldr ?_) (none, 0)) honest)
  funext wc acc
  unfold honestPairEnc fig8CtV stepRevIdx
  dsimp only [p]
  rw [sendsIn_other_eq_senderOf_beq wc.2.1.1 Q]
  cases acc.1 <;> rfl

theorem findRevHonestIdxE_cost (L : ℕ) {Γ : List (Ty ASig)}
    (honestE : Expr AOps Γ (.list (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) :
    (findRevHonestIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L honestE qBE wE).cost ≤
    honestE.cost + qBE.cost + wE.cost + 120 * L + 64 := by
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hm1 : max 6 6 = 6 := rfl
  have hm2 : max 3 1 = 3 := rfl
  have hm3 : max 94 2 = 94 := rfl
  simp only [findRevHonestIdxE, otherE, sendsInE, cost_eLet, cost_sOpPure, AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, bits_zero, hb1_bits, hb2_bits, h32,
    Nat.reduceAdd, hm1, hm2, hm3]
  omega

theorem findRevHonestIdxE_descBits_le (L : ℕ) {Γ : List (Ty ASig)}
    (honestE : Expr AOps Γ (.list (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) :
    atomicExprDescBits atomicSessionOpDescBits
      (findRevHonestIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) L honestE qBE wE) ≤
    atomicExprDescBits atomicSessionOpDescBits honestE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits wE +
      8 * bits L + 2000 := by
  simp only [findRevHonestIdxE, otherE, sendsInE, descBits_eLet, descBits_sOpPure,
    Expr.v0, Expr.v1, Expr.v2, atomicPureOpDescBits, atomicExprDescBits, atomicTyDescBits,
    varIdx, Nat.reduceAdd, bits_zero, hb1_bits, hb2_bits, hb32_pnat]
  omega

private theorem atomicTyDescBits_kemSentEntryT :
    atomicTyDescBits (kemSentEntryT ℓ Pt) ≤ 50 := by
  dsimp only [kemSentEntryT, U64, B, U32, atomicTyDescBits, atomicSortDescBits]
  rw [hb64_pnat]
  omega

private theorem b64Take48ToB32E_descBits_tight {Γ : List (Ty ASig)} (suf : Expr AOps Γ (B 64)) :
    atomicExprDescBits atomicSessionOpDescBits
      (b64Take48ToB32E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) suf) ≤
    atomicExprDescBits atomicSessionOpDescBits suf + 250 := by
  simp only [b64Take48ToB32E, descBits_sOpPure, atomicPureOpDescBits, atomicExprDescBits,
    hb32_pnat, hb3_bits]
  omega

theorem kemTrackDeliverAtomicE_cost (L : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool) (jE : Expr AOps Γ .nat) :
    (kemTrackDeliverAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L trE qBE jE).cost ≤
    trE.cost + qBE.cost + jE.cost + 32 * L + 8000 := by
  let Γ0 : List (Ty ASig) := .prod (kemTrackT ℓ Pt) (.prod .bool .nat) :: Γ
  let Γ1 : List (Ty ASig) := kemSentEntryT ℓ Pt :: Γ0
  let Γ2 : List (Ty ASig) :=
    .prod (.opt (.prod (U64 (ℓ := ℓ) (Pt := Pt)) (BV256 (ℓ := ℓ) (Pt := Pt))))
      (B (ℓ := ℓ) (Pt := Pt) 32) :: Γ1
  have hnth := listNthOptB_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L (t := kemSentEntryT ℓ Pt) (Γ := Γ0)
    (.fst (.snd (.snd (.snd (.fst .v0))))) (.snd (.snd .v0))
  have hsuf1 := b64Take48ToB32E_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ1) (.snd (.fst .v0))
  have hsuf2 := b64Take48ToB32E_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) (.snd (.fst .v1))
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  dsimp only [kemTrackDeliverAtomicE, Γ0, Γ1, Γ2] at hnth hsuf1 hsuf2 ⊢
  generalize listNthOptB (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L _ _ = eNth at hnth ⊢
  generalize b64Take48ToB32E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (.snd (.fst .v0)) = eSuf1 at hsuf1 ⊢
  generalize b64Take48ToB32E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (.snd (.fst .v1)) = eSuf2 at hsuf2 ⊢
  simp only [cost_eLet, cost_sOpPure, cost_sOpSpqr, AtomicPureOp.cost, AtomicSpqrKemOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, h32, List.length_cons, List.length_nil]
    at hnth hsuf1 hsuf2 ⊢
  omega

theorem kemTrackDeliverAtomicE_descBits_le (L : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool) (jE : Expr AOps Γ .nat) :
    atomicExprDescBits atomicSessionOpDescBits
      (kemTrackDeliverAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) L trE qBE jE) ≤
    atomicExprDescBits atomicSessionOpDescBits trE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits jE +
      8 * bits L + 8000 := by
  let Γ0 : List (Ty ASig) := .prod (kemTrackT ℓ Pt) (.prod .bool .nat) :: Γ
  let Γ1 : List (Ty ASig) := kemSentEntryT ℓ Pt :: Γ0
  let Γ2 : List (Ty ASig) :=
    .prod (.opt (.prod (U64 (ℓ := ℓ) (Pt := Pt)) (BV256 (ℓ := ℓ) (Pt := Pt))))
      (B (ℓ := ℓ) (Pt := Pt) 32) :: Γ1
  have hnth := listNthOptB_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L (t := kemSentEntryT ℓ Pt) (Γ := Γ0)
    (.fst (.snd (.snd (.snd (.fst .v0))))) (.snd (.snd .v0))
  have hsent := atomicTyDescBits_kemSentEntryT (ℓ := ℓ) (Pt := Pt)
  have hsuf1 := b64Take48ToB32E_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.snd (.fst .v0))
  have hsuf2 := b64Take48ToB32E_descBits_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.snd (.fst .v1))
  dsimp only [kemTrackDeliverAtomicE, Γ0, Γ1, Γ2] at hnth hsuf1 hsuf2 ⊢
  generalize listNthOptB (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L _ _ = eNth at hnth ⊢
  generalize atomicTyDescBits (kemSentEntryT ℓ Pt) = nSent at hnth hsent ⊢
  generalize b64Take48ToB32E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (.snd (.fst .v0)) = eSuf1 at hsuf1 ⊢
  generalize b64Take48ToB32E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (.snd (.fst .v1)) = eSuf2 at hsuf2 ⊢
  simp only [descBits_eLet, descBits_sOpPure, descBits_sOpSpqr,
    Expr.v0, Expr.v1, Expr.v2, BV512, BV256,
    atomicPureOpDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    varIdx, List.length_cons, List.length_nil, Nat.reduceAdd,
    bits_zero, hb1_bits, hb2_bits, hb32_pnat] at hnth hsuf1 hsuf2 ⊢
  omega

theorem kemOnDeliverPostAtomicE_cost (L : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) :
    (kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L qBE jOptE rrOptE trE).cost ≤
    qBE.cost + jOptE.cost + rrOptE.cost + trE.cost + 32 * L + 8200 := by
  let Γ0 : List (Ty ASig) :=
    .prod .bool (.prod (.opt .nat)
      (.prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (kemTrackT ℓ Pt))) :: Γ
  let Γ3 : List (Ty ASig) :=
    .nat :: .prod .nat (.prod .nat (.opt (PlainT (ℓ := ℓ) (Pt := Pt)))) ::
      recvResultT (ℓ := ℓ) (Pt := Pt) :: Γ0
  have hdel := kemTrackDeliverAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) L (Γ := Γ3)
    (.snd (.snd (.snd .v3))) (.fst .v3) .v0
  dsimp only [kemOnDeliverPostAtomicE, Γ0, Γ3] at hdel ⊢
  generalize kemTrackDeliverAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L _ _ _ = eDel at hdel ⊢
  simp only [cost_eLet, Expr.cost, Expr.v0, Expr.v2, Expr.v3] at hdel ⊢
  omega

theorem kemOnDeliverPostAtomicE_descBits_le (L : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) :
    atomicExprDescBits atomicSessionOpDescBits
      (kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) L qBE jOptE rrOptE trE) ≤
    atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits jOptE +
      atomicExprDescBits atomicSessionOpDescBits rrOptE +
      atomicExprDescBits atomicSessionOpDescBits trE +
      8 * bits L + 10000 := by
  let Γ0 : List (Ty ASig) :=
    .prod .bool (.prod (.opt .nat)
      (.prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (kemTrackT ℓ Pt))) :: Γ
  let Γ3 : List (Ty ASig) :=
    .nat :: .prod .nat (.prod .nat (.opt (PlainT (ℓ := ℓ) (Pt := Pt)))) ::
      recvResultT (ℓ := ℓ) (Pt := Pt) :: Γ0
  have hdel := kemTrackDeliverAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) L (Γ := Γ3)
    (.snd (.snd (.snd .v3))) (.fst .v3) .v0
  dsimp only [kemOnDeliverPostAtomicE, Γ0, Γ3] at hdel ⊢
  generalize kemTrackDeliverAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L _ _ _ = eDel at hdel ⊢
  simp only [descBits_eLet, Expr.v0, Expr.v2, Expr.v3, atomicExprDescBits, varIdx,
    Nat.reduceAdd, bits_zero, hb2_bits, hb3_bits] at hdel ⊢
  omega

end EvalCostDesc

end Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
