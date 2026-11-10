/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FSAEAD.HybridCosted -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.FSAEAD.HybridInv -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Soundness -- proof-setup: allow-public-import
public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalBound
public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Notation
import Computational.Proofs.ReductionDsl.SimRel
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.ReductionDsl.Tables
import Computational.Proofs.GameHop.StateSim
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Two-stage simulation infrastructure for ACD19 Theorem 5 reductions

Query bounds, state encodings, handler evaluation lemmas, and the two-stage simulation theorem
`run1_eval2_eq_simulateQ` connecting `HybridCosted` programs to `multiImplWith`.
-/

public section

set_option autoImplicit false

namespace CryptoGames.FSAEAD.Thm5.Costed

open ReductionDsl CryptoGames.FSAEAD.Costed CryptoGames.PRG.Costed CryptoGames.OTCCA.Costed
open OracleComp OracleSpec
open scoped Computational.Proofs.ReductionDsl.Notation

local macro_rules
  | `(rdsl_pat| .transmit $p:term)        => `(rdsl_pat| .inl $p)
  | `(rdsl_pat| .challenge $p:term)       => `(rdsl_pat| .inr (.inl $p))
  | `(rdsl_pat| .corruptSender $p:term)   => `(rdsl_pat| .inr (.inr (.inl $p)))
  | `(rdsl_pat| .corruptReceiver $p:term) => `(rdsl_pat| .inr (.inr (.inr (.inl $p))))
  | `(rdsl_pat| .deliver $p:term)         => `(rdsl_pat| .inr (.inr (.inr (.inr (.inl $p)))))
  | `(rdsl_pat| .inject $p:term)          => `(rdsl_pat| .inr (.inr (.inr (.inr (.inr $p)))))
  | `(rdsl_pat| .unknown $p:term)         => `(rdsl_pat| .inl $p)
  | `(rdsl_pat| .seed $p:term)            => `(rdsl_pat| .inr (.inl $p))
  | `(rdsl_pat| .mat $p:term)             => `(rdsl_pat| .inr (.inr $p))


local notation "HSig" CK:arg MK:arg AD:arg M:arg C:arg => fsSig CK MK AD Unit M C

local notation "HSamp" CK:arg MK:arg AD:arg M:arg C:arg =>
  unifSamplers (S := fsSig CK MK AD Unit M C) fsStateSampleSort (fun _ => 1)

local notation "hybOps" CK:arg MK:arg AD:arg M:arg C:arg ae:arg G:arg kPRG:arg kAEAD:arg =>
  Ops.sum
    (prgOps (S := fsSig CK MK AD Unit M C)
      (Ty.prod Ty.nat (bt FSort.ss)) (Ty.prod (bt FSort.ss) (bt FSort.rs))
      (fun pw => PRGScheme.gen (G (Prod.fst pw)) (Prod.snd pw)) kPRG)
    (otccaOps (S := fsSig CK MK AD Unit M C)
      (bt FSort.rs) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.ad)
      (bt FSort.msg) (bt FSort.ct) ae kAEAD Ty.unit (fun _ => ()))

local notation "prgRedZeroIface" CK:arg MK:arg AD:arg M:arg C:arg ideal:arg kIdeal:arg =>
  Iface.withSamp
    (Iface.withSamp (prgIface (fsSig CK MK AD Unit M C))
      (idealSamplers (S := fsSig CK MK AD Unit M C)
        (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.ct) ideal kIdeal))
    (unifSamplers (S := fsSig CK MK AD Unit M C) fsStateSampleSort (fun _ => 1))

local notation "multiRedIface" CK:arg MK:arg AD:arg M:arg C:arg ideal:arg kIdeal:arg =>
  Iface.withSamp
    (otccaIface (S := fsSig CK MK AD Unit M C)
      (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.msg) (bt FSort.ct) ideal kIdeal)
    (unifSamplers (S := fsSig CK MK AD Unit M C) fsStateSampleSort (fun _ => 1))


section QueryHelpers
variable {CK MK AD M C : Type} [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  [SampleableType MK] [SampleableType CK]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (kPRG kAEAD : ℕ)
  (ideal : ℕ × AD → ProbComp C) (kIdeal : ℕ)

theorem prgRedZeroProg_totalQueries (q maxSkip j : ℕ) :
    (prgRedZeroProg ae G kPRG kAEAD ideal kIdeal q maxSkip j).totalQueries
      Empty.elim (fun _ => 0) q = 0 := by
  simp [TwoStageCostedReduction.totalQueries, prgRedZeroProg, hybHandlePreC, hybChDoneC,
    hybResumeC, hybHandlePostC, hybFinishC, corruptReceiverResumeBody, corruptReceiverDBody,
    transmitBody, challengeBody, corruptSenderBody, deliverBody, injectBody, receiveBody,
    genUpToC, genUpToBody, genStepKcBody, encIdxBody, decIdxBody, prependNewSkippedBody,
    senderKeyBody, revealBody, chainFromC, chainFromBody, callC, Comp.queries]

theorem multiRedProg_totalQueries (q maxSkip N : ℕ) (la : Bool) :
    (multiRedProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la).totalQueries
      (fun _ => 1) (fun _ => 0) q = q := by
  simp [TwoStageCostedReduction.totalQueries, multiRedProg, hybHandlePreC, hybChDoneC,
    hybResumeC, hybHandlePostC, hybFinishC, corruptReceiverResumeBody, corruptReceiverDBody,
    transmitBody, challengeBody, corruptSenderBody, deliverBody, injectBody, receiveBody,
    genUpToC, genUpToBody, genStepKcBody, encIdxBody, decIdxBody, prependNewSkippedBody,
    senderKeyBody, revealBody, chainFromC, chainFromBody, otSpecialEncC, otSpecialDecC,
    callC, Comp.queries]

theorem multiRedProg_eval1_queries (q maxSkip N : ℕ) (la : Bool)
    (A : RatchetAdversary CK MK AD M C) :
    ((multiRedProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la).eval1
      (fun _ => A) () q false).IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec (ℕ × AD) M C)) q := by
  have h := (multiRedProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la).eval1_queryBound
    (isGameQuery (G := AEADScheme.otccaSpec (ℕ × AD) M C))
    (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => le_rfl)
    (fun n => by simp [Iface.withSamp, otccaIface, isGameQuery])
    (fun _ => A) () q false
  refine h.mono (le_of_eq ?_)
  simp [multiRedProg, hybHandlePreC, hybChDoneC, transmitBody, challengeBody, corruptSenderBody,
    deliverBody, injectBody, receiveBody, genUpToC, genUpToBody, genStepKcBody,
    encIdxBody, decIdxBody, prependNewSkippedBody, senderKeyBody, revealBody,
    chainFromC, chainFromBody, otSpecialEncC, otSpecialDecC, callC, Comp.queries]

theorem multiRedProg_eval2_queries (q maxSkip N : ℕ) (la : Bool)
    (m : Mid (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      Bool Unit (stTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)).denote Unit) :
    ((multiRedProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la).eval2 m () q false).IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec (ℕ × AD) M C)) 0 := by
  have h := (multiRedProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la).eval2_queryBound
    (isGameQuery (G := AEADScheme.otccaSpec (ℕ × AD) M C))
    (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => le_rfl)
    (fun n => by simp [Iface.withSamp, otccaIface, isGameQuery])
    m () q false
  refine h.mono (le_of_eq ?_)
  simp [multiRedProg, hybResumeC, hybHandlePostC, hybFinishC, corruptReceiverResumeBody,
    corruptReceiverDBody, senderKeyBody, revealBody, chainFromC, chainFromBody,
    callC, Comp.queries]

end QueryHelpers

section Soundness

section Encodings

variable {CK MK AD M C : Type}

local notation "HSig'" => fsSig CK MK AD Unit M C
local notation "HT'" => Ty HSig'
local notation "recTy'" => recTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "kcTy'" => kcTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "slotTy'" => slotTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "hsTy'" => hsTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "stTy'" => stTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)

@[expose] def encRec (r : Record AD M (ℕ × C)) : ℕ × (AD × (M × (ℕ × C))) :=
  (r.idx, (r.ad, (r.msg, r.ct)))

@[expose] def encSlot : Slot CK MK → (slotTy').denote
  | .unknown => .inl ()
  | .seed w => .inr (.inl w)
  | .mat pos mt => .inr (.inr (pos, mt))

@[expose] def encKc (ks : List MK) : ℕ × (ℕ → Option MK) :=
  (ks.length, fun p => ks[p]?)

@[expose] def encSkipped (sk : List ℕ) : ℕ → Bool :=
  fun i => decide (i ∈ sk)

@[expose] def encHS (st : HState CK MK AD M C) : (hsTy').denote :=
  ((((st.b, st.lastSentIdx), (st.senderCorruptedAt, st.receiverIdx)),
    (st.ended, (st.win, st.lf))),
   ((st.inTransit.map encRec, st.challengesInTransit),
    (encKc st.keys, (st.corrKey, encSkipped st.skipped))))

@[expose] def encSt (s : HSt CK MK AD M C) : (stTy').denote :=
  (encHS s.1, encSlot s.2)

@[simp] theorem encRec_idx (r : Record AD M (ℕ × C)) : (encRec r).1 = r.idx := rfl
@[simp] theorem encRec_ad (r : Record AD M (ℕ × C)) : (encRec r).2.1 = r.ad := rfl
@[simp] theorem encRec_msg (r : Record AD M (ℕ × C)) : (encRec r).2.2.1 = r.msg := rfl
@[simp] theorem encRec_ct (r : Record AD M (ℕ × C)) : (encRec r).2.2.2 = r.ct := rfl

@[simp] theorem encKc_fst (ks : List MK) : (encKc ks).1 = ks.length := rfl
@[simp] theorem encKc_snd (ks : List MK) : (encKc ks).2 = fun p => ks[p]? := rfl

@[simp] theorem encSt_fst (s : HSt CK MK AD M C) : (encSt s).1 = encHS s.1 := rfl
@[simp] theorem encSt_snd (s : HSt CK MK AD M C) : (encSt s).2 = encSlot s.2 := rfl

@[simp] theorem encHS_b (h : HState CK MK AD M C) : (encHS h).1.1.1.1 = h.b := rfl
@[simp] theorem encHS_lastSent (h : HState CK MK AD M C) :
    (encHS h).1.1.1.2 = h.lastSentIdx := rfl
@[simp] theorem encHS_corrAt (h : HState CK MK AD M C) :
    (encHS h).1.1.2.1 = h.senderCorruptedAt := rfl
@[simp] theorem encHS_recvIdx (h : HState CK MK AD M C) :
    (encHS h).1.1.2.2 = h.receiverIdx := rfl
@[simp] theorem encHS_ended (h : HState CK MK AD M C) : (encHS h).1.2.1 = h.ended := rfl
@[simp] theorem encHS_win (h : HState CK MK AD M C) : (encHS h).1.2.2.1 = h.win := rfl
@[simp] theorem encHS_lf (h : HState CK MK AD M C) : (encHS h).1.2.2.2 = h.lf := rfl
@[simp] theorem encHS_inTransit (h : HState CK MK AD M C) :
    (encHS h).2.1.1 = h.inTransit.map encRec := rfl
@[simp] theorem encHS_challs (h : HState CK MK AD M C) :
    (encHS h).2.1.2 = h.challengesInTransit := rfl
@[simp] theorem encHS_kc (h : HState CK MK AD M C) :
    (encHS h).2.2.1 = encKc h.keys := rfl
@[simp] theorem encHS_nKeys (h : HState CK MK AD M C) :
    (encHS h).2.2.1.1 = h.keys.length := rfl
@[simp] theorem encHS_keysT (h : HState CK MK AD M C) :
    (encHS h).2.2.1.2 = fun p => h.keys[p]? := rfl
@[simp] theorem encHS_corrKey (h : HState CK MK AD M C) : (encHS h).2.2.2.1 = h.corrKey := rfl
@[simp] theorem encHS_skipped (h : HState CK MK AD M C) :
    (encHS h).2.2.2.2 = encSkipped h.skipped := rfl

@[simp] theorem callE_eval {O : Ops HSig'} {Γ : List HT'} {a b : HT'}
    (arg : Expr O Γ a) (body : Expr O (a :: Γ) b) (ρ : Env Γ) :
    (callE arg body).eval ρ = body.eval (.cons (arg.eval ρ) ρ) := rfl

@[simp] theorem callC_eval {O : Ops HSig'} {ι : Type} {T : OracleSpec ι} {I : Iface HSig' T}
    {Γ : List HT'} {a b : HT'} (arg : Expr O Γ a) (body : Comp O I (a :: Γ) b) (ρ : Env Γ) :
    (callC arg body).eval ρ = body.eval (.cons (arg.eval ρ) ρ) := by
  simp [Comp.eval]

end Encodings

section PureEval

variable {CK MK AD M C : Type}
  {O : Ops (fsSig CK MK AD Unit M C)} {Γ : List (Ty (fsSig CK MK AD Unit M C))} (ρ : Env Γ)

local notation "hsTy'" => hsTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "kcTy'" => kcTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)

@[simp] theorem initHSE_eval (b : Expr O Γ .bool) :
    (initHSE (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b).eval ρ =
      encHS ({ b := b.eval ρ } : HState CK MK AD M C) := by
  dsimp only [initHSE, mkHS, Expr.eval, encHS, encKc]
  have hsk : (fun _ : ℕ => false) = encSkipped [] := by funext x; rfl
  rw [hsk]
  rfl

@[simp] theorem cond_true_left (a b : Bool) : (if a = true then true else b) = (a || b) := by
  cases a <;> rfl

@[simp] theorem ite_le_max (a b : ℕ) :
    (if a ≤ b then b else a) = max a b := by
  by_cases h : a ≤ b
  · simp [h]
  · simp [h, Nat.max_eq_left (by omega : b ≤ a)]

@[expose] def isCompAt (corrAt : Option ℕ) (i : ℕ) : Bool :=
  match corrAt with
  | some j => decide (j < i)
  | none => false

theorem isCompromised_eq_isCompAt (h : HState CK MK AD M C) (i : ℕ) :
    h.isCompromised i = isCompAt h.senderCorruptedAt i := rfl

@[simp] theorem isCompromisedE_eval (st : Expr O Γ hsTy') (i : Expr O Γ .nat) :
    (isCompromisedE st i).eval ρ = isCompAt (st.eval ρ).1.1.2.1 (i.eval ρ) := by
  cases h : (st.eval ρ).1.1.2.1 <;>
    simp [isCompromisedE, isCompromisedBody, hsCorrAt, isCompAt, Expr.v0, Expr.v1, Expr.eval,
      Env.get, h]

theorem keys_append_getElem? (xs : List MK) (K : MK) :
    (fun p => if p = xs.length then some K else xs[p]?) = (fun p => (xs ++ [K])[p]?) := by
  funext p
  by_cases hp : p < xs.length
  · have hne : p ≠ xs.length := by omega
    simp [hp, hne, List.getElem?_append_left hp]
  · by_cases heq : p = xs.length
    · subst heq; simp
    · have h1 : xs[p]? = none := List.getElem?_eq_none (by omega)
      have h2 : (xs ++ [K])[p]? = none := List.getElem?_eq_none (by simp; omega)
      simp [heq, h1, h2]

theorem appendKcE_eval (kc : Expr O Γ kcTy') (K : Expr O Γ (bt .rs))
    (ks : List MK) (hkc : kc.eval ρ = encKc ks) :
    (appendKcE kc K).eval ρ = encKc (ks ++ [K.eval ρ]) := by
  dsimp only [appendKcE]
  simp only [Expr.eval, hkc, encKc, List.length_append, List.length_singleton,
    keys_append_getElem?]

theorem withKcE_eval (hs : Expr O Γ hsTy') (kc : Expr O Γ kcTy')
    (h : HState CK MK AD M C) (ks : List MK)
    (hhs : hs.eval ρ = encHS h) (hkc : kc.eval ρ = encKc ks) :
    (withKcE hs kc).eval ρ = encHS { h with keys := ks } := by
  dsimp only [withKcE]
  simp only [Expr.eval, hhs, hkc, encHS]

theorem withSkippedE_eval (hs : Expr O Γ hsTy') (sk : Expr O Γ (.tbl .bool))
    (h : HState CK MK AD M C) (sk' : List ℕ)
    (hhs : hs.eval ρ = encHS h) (hsk : sk.eval ρ = encSkipped sk') :
    (withSkippedE hs sk).eval ρ = encHS { h with skipped := sk' } := by
  dsimp only [withSkippedE]
  simp only [Expr.eval, hhs, hsk, encHS]

theorem encSkipped_eq_contains : ∀ (sk : List ℕ) (i : ℕ), encSkipped sk i = sk.contains i
  | [], _ => rfl
  | x :: xs, i => by
    by_cases h : i = x
    · subst h; simp [encSkipped]
    · have hne : x ≠ i := Ne.symm h
      simp [encSkipped, h]

theorem skippedContainsE_eval_eq (st : Expr O Γ hsTy') (i : Expr O Γ .nat)
    (h : HState CK MK AD M C) (hst : st.eval ρ = encHS h) :
    (skippedContainsE st i).eval ρ = h.skipped.contains (i.eval ρ) := by
  simp only [Expr.eval, hst, encHS_skipped, encSkipped_eq_contains]

theorem tset_false_encSkipped (sk : List ℕ) (i : ℕ) :
    (fun j => if j = i then false else encSkipped sk j) =
      encSkipped (sk.filter (· != i)) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [encSkipped, List.mem_filter]
  · simp [encSkipped, List.mem_filter, hj, bne_iff_ne]

@[simp] theorem skippedRemoveE_eval (st : Expr O Γ hsTy') (i : Expr O Γ .nat) :
    (skippedRemoveE st i).eval ρ =
      (skippedRemoveBody (O := O)).eval (.cons (t := .prod hsTy' .nat) (st.eval ρ, i.eval ρ) ρ) :=
  rfl

@[simp] theorem skippedRemoveBody_eval (h : HState CK MK AD M C) (i : ℕ) :
    (skippedRemoveBody (O := O)).eval (.cons (t := .prod hsTy' .nat) (encHS h, i) ρ) =
      encHS { h with skipped := h.skipped.filter (· != i) } := by
  simp only [skippedRemoveBody, withSkippedE, hsSkipped, Expr.v0, Expr.eval, Env.get,
    encHS, tset_false_encSkipped]

theorem foldr_filter_recIdx' (i : ℕ) :
    ∀ xs : List (Record AD M (ℕ × C)),
      List.foldr (fun x acc => if x.1 = i then acc else x :: acc) [] (List.map encRec xs) =
        List.map encRec (List.filter (fun x => x.idx != i) xs)
  | [] => rfl
  | r :: xs => by
    simp only [List.map_cons, List.foldr_cons, foldr_filter_recIdx' i xs, List.filter_cons,
      encRec, bne, beq_eq_decide]
    split <;> simp_all [encRec]

theorem foldr_filter_nat' (i : ℕ) :
    ∀ xs : List ℕ,
      List.foldr (fun x acc => if x = i then acc else x :: acc) [] xs =
        List.filter (fun x => x != i) xs
  | [] => rfl
  | x :: xs => by
    simp only [List.foldr_cons, foldr_filter_nat' i xs, List.filter_cons, bne, beq_eq_decide]
    split <;> simp_all

@[simp] theorem removeFromTransitE_eval (q : ℕ) (st : Expr O Γ hsTy') (i : Expr O Γ .nat) :
    (removeFromTransitE q st i).eval ρ =
      (removeFromTransitBody (O := O) q).eval
        (.cons (t := .prod hsTy' .nat) (st.eval ρ, i.eval ρ) ρ) := rfl

@[simp] theorem anyUncompInTransitE_eval (q : ℕ) (st : Expr O Γ hsTy') :
    (anyUncompInTransitE q st).eval ρ =
      (anyUncompInTransitBody (O := O) q).eval (.cons (t := hsTy') (st.eval ρ) ρ) := rfl

@[simp] theorem anyUncompInTransitBody_eval (q : ℕ) (h : HState CK MK AD M C)
    (htr : h.inTransit.length ≤ q) :
    (anyUncompInTransitBody (O := O) q).eval (.cons (t := hsTy') (encHS h) ρ) =
      h.inTransit.any (fun r => !h.isCompromised r.idx) := by
  have htr' : (h.inTransit.map encRec).take q = h.inTransit.map encRec :=
    List.take_of_length_le (by simpa using htr)
  simp only [anyUncompInTransitBody, hsInTransit, isCompromisedE_eval, recIdx, Expr.v0, Expr.v1,
    Expr.eval, Env.get, encHS_inTransit, encHS_corrAt, isCompromised_eq_isCompAt, htr',
    List.any_map]
  rfl

@[simp] theorem challsContainsE_eval (q : ℕ) (st : Expr O Γ hsTy') (i : Expr O Γ .nat) :
    (challsContainsE q st i).eval ρ =
      (challsContainsBody (O := O) q).eval
        (.cons (t := .prod hsTy' .nat) (st.eval ρ, i.eval ρ) ρ) := rfl

end PureEval

section HybOpsPureEval

variable {CK MK AD M C : Type} [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (kPRG kAEAD : ℕ)
  {Γ : List (Ty (fsSig CK MK AD Unit M C))} (ρ : Env Γ)

local notation "hsTy'" => hsTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)

@[simp] theorem findInTransitE_eval (q : ℕ)
    (st : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ hsTy')
    (qry : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.prod (bt .ad) (.prod .nat (bt .ct)))) :
    (findInTransitE ae G kPRG kAEAD q st qry).eval ρ =
      (findInTransitBody ae G kPRG kAEAD q).eval
        (.cons (t := .prod hsTy' (.prod (bt .ad) (.prod .nat (bt .ct))))
          (st.eval ρ, qry.eval ρ) ρ) := rfl

@[simp] theorem findInTransitBody_eval (q : ℕ) (h : HState CK MK AD M C)
    (qry : AD × (ℕ × C)) (htr : h.inTransit.length ≤ q) :
    (findInTransitBody ae G kPRG kAEAD q).eval
      (.cons (t := .prod hsTy' (.prod (bt .ad) (.prod .nat (bt .ct)))) (encHS h, qry) ρ) =
      (h.inTransit.find? (fun r => r.ad == qry.1 && r.ct == qry.2)).map encRec := by
  have htr' : (h.inTransit.map encRec).take q = h.inTransit.map encRec :=
    List.take_of_length_le (by simpa using htr)
  simp only [findInTransitBody, hsInTransit, Expr.v0, Expr.v1, Expr.eval, Env.get,
    encHS_inTransit, htr', List.find?_map]
  congr 1

theorem findInTransitE_eval_eq (q : ℕ)
    (st : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ hsTy')
    (qry : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.prod (bt .ad) (.prod .nat (bt .ct))))
    (h : HState CK MK AD M C) (hst : st.eval ρ = encHS h)
    (htr : h.inTransit.length ≤ q) :
    (findInTransitE ae G kPRG kAEAD q st qry).eval ρ =
      (h.inTransit.find? (fun r => r.ad == (qry.eval ρ).1 && r.ct == (qry.eval ρ).2)).map
        encRec := by
  rw [findInTransitE_eval, hst]
  exact findInTransitBody_eval ae G kPRG kAEAD ρ q h (qry.eval ρ) htr

@[simp] theorem anyInTransitE_eval (q : ℕ)
    (st : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ hsTy')
    (qry : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.prod (bt .ad) (.prod .nat (bt .ct)))) :
    (anyInTransitE ae G kPRG kAEAD q st qry).eval ρ =
      (anyInTransitBody ae G kPRG kAEAD q).eval
        (.cons (t := .prod hsTy' (.prod (bt .ad) (.prod .nat (bt .ct))))
          (st.eval ρ, qry.eval ρ) ρ) := rfl

@[simp] theorem anyInTransitBody_eval (q : ℕ) (h : HState CK MK AD M C)
    (qry : AD × (ℕ × C)) (htr : h.inTransit.length ≤ q) :
    (anyInTransitBody ae G kPRG kAEAD q).eval
      (.cons (t := .prod hsTy' (.prod (bt .ad) (.prod .nat (bt .ct)))) (encHS h, qry) ρ) =
      h.inTransit.any (fun r => r.ad == qry.1 && r.ct == qry.2) := by
  have htr' : (h.inTransit.map encRec).take q = h.inTransit.map encRec :=
    List.take_of_length_le (by simpa using htr)
  simp only [anyInTransitBody, hsInTransit, Expr.v0, Expr.v1, Expr.eval, Env.get,
    encHS_inTransit, htr', List.any_map]
  congr 1

theorem anyInTransitE_eval_eq (q : ℕ)
    (st : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ hsTy')
    (qry : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.prod (bt .ad) (.prod .nat (bt .ct))))
    (h : HState CK MK AD M C) (hst : st.eval ρ = encHS h)
    (htr : h.inTransit.length ≤ q) :
    (anyInTransitE ae G kPRG kAEAD q st qry).eval ρ =
      h.inTransit.any (fun r => r.ad == (qry.eval ρ).1 && r.ct == (qry.eval ρ).2) := by
  rw [anyInTransitE_eval, hst]
  exact anyInTransitBody_eval ae G kPRG kAEAD ρ q h (qry.eval ρ) htr

end HybOpsPureEval

/-! ## Monadic subroutine evaluation -/

section Subroutines

theorem iterM_step_eq {m : Type → Type} [Monad m] {α : Type}
    {f g : α → m α} (hfg : ∀ a, f a = g a) :
    ∀ (n : ℕ) (a : α), iterM f n a = iterM g n a
  | 0, _ => rfl
  | n + 1, a => by
    simp only [iterM, hfg a]
    congr 1; funext x
    exact iterM_step_eq hfg n x

@[simp] theorem liftP_withSamp {S : Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S T) (X : Samplers S) {α : Type} (p : ProbComp α) :
    (I.withSamp X).liftP p = I.liftP p := rfl

@[simp] theorem samp_withSamp_inr {S : Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S T) (X : Samplers S) (s : X.Samp) (x : (X.sDom s).denote) :
    (I.withSamp X).smp.samp (Sum.inr s) x = X.samp s x := rfl

@[simp] theorem samp_withSamp_inl {S : Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S T) (X : Samplers S) (s : I.smp.Samp) (x : (I.smp.sDom s).denote) :
    (I.withSamp X).smp.samp (Sum.inl s) x = I.smp.samp s x := rfl

@[simp] theorem liftP_mk {S : Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S T) (X : Samplers S) {α : Type} (p : ProbComp α) :
    ({ I with smp := X } : Iface S T).liftP p = I.liftP p := rfl

variable {CK MK AD M C : Type} [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  [SampleableType MK] [SampleableType CK]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (kPRG kAEAD : ℕ)
  {ι : Type} {T : OracleSpec.{0, 0} ι} [MonadLiftT ProbComp (OracleComp T)]
  {I₀ : Iface (fsSig CK MK AD Unit M C) T}
  (hliftP : ∀ {α : Type} (p : ProbComp α), I₀.liftP p = (liftM p : OracleComp T α))
  {Γ : List (Ty (fsSig CK MK AD Unit M C))} (ρ : Env Γ)

local notation "HT'" => Ty (fsSig CK MK AD Unit M C)
local notation "recTy'" => recTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "kcTy'" => kcTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "slotTy'" => slotTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "hsTy'" => hsTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "stTy'" => stTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] [SampleableType MK] [SampleableType CK] in
include hliftP in
theorem liftP_map_eq {α β : Type} (f : α → β) (p : ProbComp α) :
    (liftM (f <$> p) : OracleComp T β) = f <$> (liftM p : OracleComp T α) := by
  rw [← hliftP, ← hliftP]
  simp [Iface.liftP]

include hliftP in
theorem genStepKcBody_eval (P : Params) (tIdx : ℕ) (s : HSt CK MK AD M C) :
    (genStepKcBody (I₀ := I₀) ae G kPRG kAEAD).eval
      (.cons (t := .prod kcTy' slotTy') (encKc s.1.keys, encSlot s.2)
        (.cons (t := .prod .nat .nat) (tIdx, P.j) ρ)) =
      (fun z => (encKc z.2.1.keys, encSlot z.2.2)) <$>
        (genStep (m := OracleComp T) G P (DG G)).run s := by
  rcases s with ⟨h, sl⟩
  cases sl with
  | unknown =>
    simp only [genStepKcBody, genStep, StateT.run_mk, encSlot, Comp.eval,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.eval, Env.get, encKc_fst,
      liftP_withSamp, unifSamplers, fsStateSampleSort,
      hliftP]
    by_cases hlt : h.keys.length < P.j
    · simp only [hlt, decide_true, ↓reduceIte, map_bind, map_pure]
      refine bind_congr fun a => ?_
      simp only [List.length_append, keys_append_getElem?, encKc]
      rfl
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte, DG, liftP_map_eq hliftP,
        bind_map_left, map_bind, map_pure]
      refine bind_congr fun a => ?_
      simp only [Ops.sum, prgOps, Sum.elim, Env.get,
        List.length_append, List.length_singleton, keys_append_getElem?, encKc]
      rfl
  | seed w =>
    simp only [genStepKcBody, genStep, StateT.run_mk, encSlot, Comp.eval, prgGenE, Ops.sum,
      prgOps, Sum.elim, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.eval, Env.get,
      List.length_append, List.length_singleton, keys_append_getElem?,
      encKc, map_pure]
  | mat pos mt =>
    simp only [genStepKcBody, genStep, StateT.run_mk, encSlot, Comp.eval,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.eval, Env.get, encKc_fst,
      liftP_withSamp, unifSamplers, fsStateSampleSort,
      hliftP]
    by_cases hlt : h.keys.length < pos
    · simp only [hlt, decide_true, ↓reduceIte, map_bind, map_pure]
      refine bind_congr fun a => ?_
      simp only [List.length_append,
        keys_append_getElem?, encKc]
      rfl
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.length_append,
        List.length_singleton, keys_append_getElem?, encKc, map_pure]

include hliftP in
theorem genUpTo_kc_iterM (P : Params) (i : ℕ) :
    ∀ (fuel : ℕ) (s : HSt CK MK AD M C), i - s.1.keys.length ≤ fuel →
      iterM (fun a : (ℕ × (ℕ → Option MK)) × (slotTy').denote =>
        if a.1.1 < i then
          (genStepKcBody (I₀ := I₀) ae G kPRG kAEAD).eval
            (.cons (t := .prod kcTy' slotTy') a (.cons (t := .prod .nat .nat) (i, P.j) ρ))
        else pure a)
        fuel (encKc s.1.keys, encSlot s.2) =
      (fun z => (encKc z.2.1.keys, encSlot z.2.2)) <$>
        (genN (m := OracleComp T) G P (DG G) (i - s.1.keys.length)).run s
  | 0, s, hle => by
    have h0 : i - s.1.keys.length = 0 := by omega
    simp [iterM, h0, genN]
  | fuel + 1, s, hle => by
    simp only [iterM, encKc_fst]
    by_cases hlt : s.1.keys.length < i
    · have hsub : i - s.1.keys.length = (i - (s.1.keys.length + 1)) + 1 := by omega
      simp only [hlt, ↓reduceIte, genStepKcBody_eval ae G kPRG kAEAD hliftP ρ P i s,
        hsub, genN, StateT.run_bind, map_bind, bind_map_left]
      refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
      obtain ⟨K, hK⟩ := genStep_support G P (DG G) s z hz
      have hlen : z.2.1.keys.length = s.1.keys.length + 1 := by simp [hK]
      rw [← hlen]
      exact genUpTo_kc_iterM P i fuel z.2 (by omega)
    · simp only [hlt, ↓reduceIte, pure_bind]
      exact genUpTo_kc_iterM P i fuel s (by omega)

include hliftP in
theorem genUpToC_eval (maxSkip : ℕ) (P : Params)
    (iE : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ .nat)
    (sE : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ stTy')
    (s : HSt CK MK AD M C) (hs : sE.eval ρ = encSt s)
    (hfuel : iE.eval ρ - s.1.keys.length ≤ maxSkip + 1) :
    (genUpToC (I₀ := I₀) ae G kPRG kAEAD maxSkip P.j iE sE).eval ρ =
      (fun z => encSt z.2) <$> (genUpTo (m := OracleComp T) G P (DG G) (iE.eval ρ)).run s := by
  dsimp only [genUpToC, callC, genUpToBody, Comp.eval]
  simp only [pure_bind, Expr.v0, Expr.v1, Expr.eval, Env.get, hs,
    encSt_fst, encSt_snd, encHS_nKeys, encHS_keysT, genUpTo, getH, onH,
    StateT.run_bind, StateT.run_mk, StateT.run_get, map_pure]
  have hinit : (s.1.keys.length, fun p => s.1.keys[p]?) = encKc s.1.keys := rfl
  rw [hinit, iterM_step_eq (g := fun a : (ℕ × (ℕ → Option MK)) × (slotTy').denote =>
      if a.1.1 < iE.eval ρ then
        (genStepKcBody (I₀ := I₀) ae G kPRG kAEAD).eval
          (.cons (t := .prod kcTy' slotTy') a
            (.cons (t := .prod .nat .nat) (iE.eval ρ, P.j)
              (.cons (t := .prod .nat stTy') (iE.eval ρ, encSt s) ρ)))
      else pure a)
    (fun a => by simp only [decide_eq_true_eq])]
  rw [genUpTo_kc_iterM ae G kPRG kAEAD hliftP
    (.cons (t := .prod .nat stTy') (iE.eval ρ, encSt s) ρ) P (iE.eval ρ) (maxSkip + 1) s hfuel,
    bind_map_left, map_eq_bind_pure_comp]
  refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
  obtain ⟨ks, _, hst⟩ := genN_support G P (DG G) (iE.eval ρ - s.1.keys.length) s z hz
  have hst' : z.2.1 = { s.1 with keys := z.2.1.keys } := by rw [hst]
  simp only [Expr.v2, Expr.eval, Env.get, Function.comp, encSt]
  exact congrArg (fun hs' => (pure (hs', encSlot z.2.2) : OracleComp T _))
    (by rw [hst']; simp [encHS])

include hliftP in
theorem revealBody_eval (s : HSt CK MK AD M C) :
    (revealBody (I₀ := I₀) ae G kPRG kAEAD).eval (.cons (encSt s) ρ) =
      Prod.map id encSt <$> (reveal (m := OracleComp T) (CK := CK) (MK := MK)).run s := by
  rcases s with ⟨h, sl⟩
  cases sl <;> {
    simp [revealBody, reveal, StateT.run_mk, encSt, encSlot, Comp.eval, Expr.v0, Expr.v2,
      Expr.v3, Expr.eval, Env.get, liftP_withSamp, unifSamplers, fsStateSampleSort, hliftP,
      Prod.map]
    try rfl
  }

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  [SampleableType MK] [SampleableType CK] [MonadLiftT ProbComp (OracleComp T)] in
theorem chainFrom_iterM (c : ℕ) (w : CK) (m : ℕ) :
    ∀ (fuel k : ℕ), k ≤ m → m - k ≤ fuel →
      iterM (fun a : ℕ × CK =>
        (pure (if a.1 < m then (a.1 + 1, ((G (c + a.1)).gen a.2).1) else a) :
          OracleComp T (ℕ × CK))) fuel (k, chainFrom G c w k) =
      pure (m, chainFrom G c w m)
  | 0, k, _, hle => by
    have hk : k = m := by omega
    subst hk; rfl
  | fuel + 1, k, hkm, hle => by
    simp only [iterM]
    by_cases hlt : k < m
    · simp only [hlt, ↓reduceIte, pure_bind]
      exact chainFrom_iterM c w m fuel (k + 1) (by omega) (by omega)
    · simp only [hlt, ↓reduceIte, pure_bind]
      exact chainFrom_iterM c w m fuel k hkm (by omega)

omit [SampleableType MK] [SampleableType CK] [MonadLiftT ProbComp (OracleComp T)] in
theorem chainFromC_eval {I : Iface (fsSig CK MK AD Unit M C) T} (fuel : ℕ)
    (cE : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ .nat)
    (wE : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (bt .ss))
    (mE : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ .nat)
    (hm : mE.eval ρ ≤ fuel) :
    (chainFromC (I := I) ae G kPRG kAEAD fuel cE wE mE).eval ρ =
      pure (chainFrom G (cE.eval ρ) (wE.eval ρ) (mE.eval ρ)) := by
  dsimp only [chainFromC, callC, chainFromBody, Comp.eval]
  simp only [pure_bind, Expr.v0, Expr.eval, Env.get]
  rw [iterM_step_eq (g := fun a : ℕ × CK =>
      pure (if a.1 < mE.eval ρ then (a.1 + 1, ((G (cE.eval ρ + a.1)).gen a.2).1) else a))
    (fun a => by
      simp only [Ops.sum, prgOps, Sum.elim, Expr.v1, Expr.eval, Env.get,
        decide_eq_true_eq]
      rfl)]
  have hiter := chainFrom_iterM (T := T) G (cE.eval ρ) (wE.eval ρ) (mE.eval ρ)
    fuel 0 (Nat.zero_le _) (by omega)
  dsimp only [chainFrom] at hiter
  rw [hiter]
  simp only [pure_bind]

include hliftP in
theorem senderKeyBody_eval (q : ℕ) (s : HSt CK MK AD M C)
    (hsent : s.1.lastSentIdx ≤ q) :
    (senderKeyBody (I₀ := I₀) ae G kPRG kAEAD q).eval (.cons (encSt s) ρ) =
      Prod.map id encSt <$> (senderKey (m := OracleComp T) G).run s := by
  rcases s with ⟨h, sl⟩
  have hsent' : h.lastSentIdx ≤ q := hsent
  simp only [senderKeyBody, senderKey, getH, onH, StateT.run_bind, StateT.run_mk, StateT.run_get,
    map_pure, pure_bind, Comp.eval, hsCorrAt, hsCorrKey, Expr.v0, Expr.v1, Expr.eval, Env.get,
    encSt_fst, encHS_corrAt, encHS_corrKey]
  cases hcorr : h.senderCorruptedAt with
  | none =>
    exact revealBody_eval ae G kPRG kAEAD hliftP ρ (h, sl)
  | some c =>
    dsimp only
    cases hck : h.corrKey with
    | none =>
      exact revealBody_eval ae G kPRG kAEAD hliftP (.cons (t := .nat) c (.cons (encSt (h, sl)) ρ))
        (h, sl)
    | some w =>
      dsimp only
      rw [chainFromC_eval (I := I₀.withSamp (HSamp CK MK AD M C)) ae G kPRG kAEAD
        (.cons (t := bt .ss) w (.cons (t := .nat) c (.cons (encSt (h, sl)) ρ)))
        q _ _ _
        (by
          simp only [Expr.v2, Expr.eval, Env.get, encSt_fst, encHS_lastSent]
          exact Nat.le_trans (Nat.sub_le _ _) hsent')]
      simp [Expr.v2, Expr.v3, Expr.eval, Env.get, Prod.map]

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  [SampleableType MK] [SampleableType CK] [MonadLiftT ProbComp (OracleComp T)] in
theorem prependNewSkipped_iterM (i : ℕ) :
    ∀ (fuel k : ℕ) (acc : ℕ → Bool), i - k ≤ fuel →
      iterM (fun a : ℕ × (ℕ → Bool) =>
        (pure (if a.1 < i then (a.1 + 1, fun j => if j = a.1 then true else a.2 j) else a) :
          OracleComp T (ℕ × (ℕ → Bool)))) fuel (k, acc) =
      pure (max k i, fun j => if k ≤ j ∧ j < i then true else acc j)
  | 0, k, acc, hle => by
    have hik : i ≤ k := by omega
    have hmax : max k i = k := Nat.max_eq_left hik
    have hfn : (fun j => if k ≤ j ∧ j < i then true else acc j) = acc := by
      funext j
      have : ¬(k ≤ j ∧ j < i) := by omega
      simp only [this, ↓reduceIte]
    simp only [iterM, hmax, hfn]
  | fuel + 1, k, acc, hle => by
    simp only [iterM]
    by_cases hlt : k < i
    · simp only [hlt, ↓reduceIte, pure_bind]
      rw [prependNewSkipped_iterM i fuel (k + 1) (fun j => if j = k then true else acc j)
        (by omega)]
      have hmax : max (k + 1) i = max k i := by omega
      have hfn : (fun j => if k + 1 ≤ j ∧ j < i then true else if j = k then true else acc j) =
          (fun j => if k ≤ j ∧ j < i then true else acc j) := by
        funext j
        by_cases h1 : j = k
        · subst h1
          simp [hlt]
        · have hiff : (k + 1 ≤ j ∧ j < i) ↔ (k ≤ j ∧ j < i) := by omega
          simp only [h1, hiff, ↓reduceIte]
      rw [hmax, hfn]
    · simp only [hlt, ↓reduceIte, pure_bind]
      exact prependNewSkipped_iterM i fuel k acc (by omega)

theorem mem_newSkipped_iff (iB i j : ℕ) :
    j ∈ newSkipped iB i ↔ iB + 1 ≤ j ∧ j < i := by
  simp only [newSkipped, List.mem_reverse, List.mem_range'_1]
  omega

omit [SampleableType MK] [SampleableType CK] [MonadLiftT ProbComp (OracleComp T)] in
theorem prependNewSkippedBody_eval {I : Iface (fsSig CK MK AD Unit M C) T} (maxSkip : ℕ)
    (iBE : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ .nat)
    (iE : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ .nat)
    (skE : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.tbl .bool))
    (sk : List ℕ) (hskE : skE.eval ρ = encSkipped sk)
    (hskip : iE.eval ρ - iBE.eval ρ - 1 ≤ maxSkip) :
    (callC (.pair iBE (.pair iE skE))
      (prependNewSkippedBody (I := I) ae G kPRG kAEAD maxSkip)).eval ρ =
      pure (encSkipped (newSkipped (iBE.eval ρ) (iE.eval ρ) ++ sk)) := by
  dsimp only [callC, prependNewSkippedBody, Comp.eval]
  simp only [pure_bind, Expr.v0, Expr.v1, Expr.eval, Env.get, hskE]
  rw [iterM_step_eq (g := fun a : ℕ × (ℕ → Bool) =>
      pure (if a.1 < iE.eval ρ then
        (a.1 + 1, fun j => if j = a.1 then true else a.2 j) else a))
    (fun a => by
      simp only [decide_eq_true_eq])]
  rw [prependNewSkipped_iterM (T := T) (iE.eval ρ) maxSkip (iBE.eval ρ + 1)
    (encSkipped sk) (by omega)]
  simp only [pure_bind]
  congr 1; funext j
  by_cases hj : iBE.eval ρ + 1 ≤ j ∧ j < iE.eval ρ
  · have hm : j ∈ newSkipped (iBE.eval ρ) (iE.eval ρ) := (mem_newSkipped_iff _ _ _).mpr hj
    simp only [hj, and_self, ↓reduceIte, encSkipped, List.mem_append, hm, true_or, decide_true]
  · have hm : j ∉ newSkipped (iBE.eval ρ) (iE.eval ρ) :=
      fun h => hj ((mem_newSkipped_iff _ _ _).mp h)
    simp only [hj, ↓reduceIte, encSkipped, List.mem_append, hm, false_or]

@[expose] def buildDUp (c : ℕ) (sk : ℕ → Bool) (kt : ℕ → Option MK) : ℕ → List (ℕ × MK)
  | 0 => []
  | m + 1 =>
    let acc := buildDUp c sk kt m
    if c < m + 1 then
      if sk (m + 1) = true then
        match kt m with
        | none => acc
        | some K => (m + 1, K) :: acc
      else acc
    else acc

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  [SampleableType MK] [SampleableType CK] [MonadLiftT ProbComp (OracleComp T)] in
theorem corruptReceiverD_iterM (c : ℕ) (sk : ℕ → Bool) (kt : ℕ → Option MK) :
    ∀ (fuel k : ℕ),
      iterM (fun p : ℕ × List (ℕ × MK) =>
        (pure (p.1 + 1,
          if c < p.1 + 1 then
            if sk (p.1 + 1) = true then
              match kt p.1 with
              | none => p.2
              | some K => (p.1 + 1, K) :: p.2
            else p.2
          else p.2) : OracleComp T (ℕ × List (ℕ × MK))))
        fuel (k, buildDUp c sk kt k) =
      pure (k + fuel, buildDUp c sk kt (k + fuel))
  | 0, k => by simp [iterM]
  | fuel + 1, k => by
    simp only [iterM, pure_bind]
    have h := corruptReceiverD_iterM c sk kt fuel (k + 1)
    have hadd : k + 1 + fuel = k + (fuel + 1) := by omega
    simpa [buildDUp, hadd] using h

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  [SampleableType MK] [SampleableType CK] [MonadLiftT ProbComp (OracleComp T)] in
theorem buildDUp_congr (c : ℕ) {sk₁ sk₂ : ℕ → Bool} (kt : ℕ → Option MK) :
    ∀ {m : ℕ}, (∀ j, 1 ≤ j → j ≤ m → sk₁ j = sk₂ j) →
      buildDUp c sk₁ kt m = buildDUp c sk₂ kt m
  | 0, _ => rfl
  | m + 1, h => by
    have ih := buildDUp_congr c kt (m := m) (fun j hj1 hjm => h j hj1 (by omega))
    have hm1 : sk₁ (m + 1) = sk₂ (m + 1) := h (m + 1) (by omega) le_rfl
    simp only [buildDUp, ih, hm1]

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  [SampleableType MK] [SampleableType CK] [MonadLiftT ProbComp (OracleComp T)] in
theorem buildDUp_eq_filterMap (c : ℕ) (kt : ℕ → Option MK) :
    ∀ (m : ℕ) (L : List ℕ),
      L.Pairwise (· > ·) →
      (∀ i ∈ L, 1 ≤ i) →
      (∀ i ∈ L, i ≤ m) →
      buildDUp c (encSkipped L) kt m =
        (L.filter (fun i => decide (c < i))).filterMap (fun i => (kt (i - 1)).map (i, ·))
  | 0, [], _, _, _ => rfl
  | 0, a :: rest, _, hpos, hle => by
    have := hpos a List.mem_cons_self
    have := hle a List.mem_cons_self
    omega
  | m + 1, [], _, _, _ => by
    have h0 : encSkipped [] (m + 1) = false := rfl
    have ih := buildDUp_eq_filterMap c kt m [] List.Pairwise.nil (by simp) (by simp)
    simp [buildDUp, h0, ih]
  | m + 1, a :: rest, hs, hpos, hle => by
    rw [List.pairwise_cons] at hs
    obtain ⟨hgt, hprest⟩ := hs
    have hpos_rest : ∀ i ∈ rest, 1 ≤ i := fun i hi => hpos i (List.mem_cons_of_mem a hi)
    by_cases ha : a = m + 1
    · subst ha
      have hle_rest : ∀ i ∈ rest, i ≤ m := by
        intro i hi
        have := hgt i hi
        omega
      have hcg : buildDUp c (encSkipped ((m + 1) :: rest)) kt m =
          buildDUp c (encSkipped rest) kt m :=
        buildDUp_congr c kt fun j _ hjm => by
          have hjne : j ≠ m + 1 := by omega
          simp [encSkipped, hjne]
      have ih := buildDUp_eq_filterMap c kt m rest hprest hpos_rest hle_rest
      have hsk1 : encSkipped ((m + 1) :: rest) (m + 1) = true := by simp [encSkipped]
      simp only [buildDUp, hcg, ih, hsk1, ↓reduceIte, List.filter_cons]
      by_cases hc : c < m + 1
      · simp only [hc, decide_true, ↓reduceIte, List.filterMap_cons, Nat.add_sub_cancel]
        cases kt m <;> rfl
      · simp [hc]
    · have ha_le : a ≤ m := by
        have := hle a List.mem_cons_self
        omega
      have hle_all : ∀ i ∈ a :: rest, i ≤ m := by
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hmem
        · exact ha_le
        · have := hgt i hmem
          omega
      have hsk0 : encSkipped (a :: rest) (m + 1) = false := by
        simp only [encSkipped, decide_eq_false_iff_not]
        intro hm
        have := hle_all (m + 1) hm
        omega
      have ih := buildDUp_eq_filterMap c kt m (a :: rest)
        (List.pairwise_cons.mpr ⟨hgt, hprest⟩) hpos hle_all
      simp only [buildDUp, hsk0, Bool.false_eq_true, ↓reduceIte, ite_self, ih]

omit [SampleableType MK] [SampleableType CK] [MonadLiftT ProbComp (OracleComp T)] in
theorem corruptReceiverDBody_eval {I : Iface (fsSig CK MK AD Unit M C) T}
    (maxSkip q : ℕ) (h : HState CK MK AD M C)
    (hs : h.skipped.Pairwise (· > ·))
    (hpos : ∀ i ∈ h.skipped, 1 ≤ i)
    (hle : ∀ i ∈ h.skipped, i ≤ (maxSkip + 1) * q) :
    (corruptReceiverDBody (I := I) ae G kPRG kAEAD maxSkip q).eval
      (.cons (t := hsTy') (encHS h) ρ) =
      pure ((h.skipped.filter h.isCompromised).filterMap
        (fun i => (h.keys[i - 1]?).map (i, ·))) := by
  dsimp only [corruptReceiverDBody, Comp.eval]
  simp only [Expr.v0, Expr.eval, Env.get, encHS_corrAt]
  cases hcorr : h.senderCorruptedAt with
  | none =>
    have hflt : h.skipped.filter h.isCompromised = [] := by
      rw [List.filter_eq_nil_iff]
      intro i _
      simp [HState.isCompromised, hcorr]
    simp [hflt]
  | some c =>
    dsimp only
    simp only [Expr.v1, Expr.eval, Env.get,
      encHS_skipped, encHS_keysT, pure_bind]
    rw [iterM_step_eq (g := fun p : ℕ × List (ℕ × MK) =>
        pure (p.1 + 1,
          if c < p.1 + 1 then
            if encSkipped h.skipped (p.1 + 1) = true then
              match h.keys[p.1]? with
              | none => p.2
              | some K => (p.1 + 1, K) :: p.2
            else p.2
          else p.2))
      (fun p => by
        simp only [Expr.v2, Expr.eval, Env.get, decide_eq_true_eq]
        cases h.keys[p.1]? <;> rfl)]
    have hiter := corruptReceiverD_iterM (T := T) c (encSkipped h.skipped)
      (fun p => h.keys[p]?) ((maxSkip + 1) * q) 0
    simp only [Nat.zero_add] at hiter
    change iterM _ ((maxSkip + 1) * q) (0, buildDUp c (encSkipped h.skipped)
        (fun p => h.keys[p]?) 0) >>= _ = _
    rw [hiter]
    simp only [pure_bind]
    have hcomp : h.isCompromised = fun i => decide (c < i) := by
      funext i; simp [HState.isCompromised, hcorr]
    rw [hcomp, buildDUp_eq_filterMap c (fun p => h.keys[p]?) ((maxSkip + 1) * q)
      h.skipped hs hpos hle]

@[expose, reducible] def SpecialDecRel
    {I : Iface (fsSig CK MK AD Unit M C) T}
    (specialDec : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .ct)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I Δ (.opt (bt .msg))))
    (ops : Option (SpecialOps AD M C (OracleComp T))) : Prop :=
  match specialDec, ops with
  | none, none => True
  | some sDec, some o =>
    ∀ {Δ : List HT'} (ρ' : Env Δ)
      (iae : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .ct))),
      (sDec iae).eval ρ' = o.dec (iae.eval ρ').1 (iae.eval ρ').2
  | _, _ => False

@[expose, reducible] def SpecialEncRel
    {I : Iface (fsSig CK MK AD Unit M C) T}
    (specialEnc : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .msg)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I Δ (bt .ct)))
    (ops : Option (SpecialOps AD M C (OracleComp T))) : Prop :=
  match specialEnc, ops with
  | none, none => True
  | some sEnc, some o =>
    ∀ {Δ : List HT'} (ρ' : Env Δ)
      (iam : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .msg))),
      (sEnc iam).eval ρ' = o.enc (iam.eval ρ').1 (iam.eval ρ').2
  | _, _ => False

@[expose, reducible] def SampleIdealRel
    {I : Iface (fsSig CK MK AD Unit M C) T}
    (sampleIdeal : ∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod .nat (bt .ad)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I Δ (bt .ct))
    (ideal : ℕ × AD → ProbComp C) : Prop :=
  ∀ {Δ : List HT'} (ρ' : Env Δ)
    (ia : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod .nat (bt .ad))),
    (sampleIdeal ia).eval ρ' = (liftM (ideal (ia.eval ρ')) : OracleComp T C)

omit [SampleableType MK] [SampleableType CK] [MonadLiftT ProbComp (OracleComp T)] in
theorem decIdxBody_eval {I : Iface (fsSig CK MK AD Unit M C) T} (mSlot : ℕ)
    (specialDec : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .ct)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I Δ (.opt (bt .msg))))
    (ops : Option (SpecialOps AD M C (OracleComp T)))
    (hDec : SpecialDecRel ae G kPRG kAEAD specialDec ops)
    (argE : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ
      (.prod (.prod (.opt (bt .msg)) (.prod .nat (.prod (bt .ad) (bt .ct)))) hsTy'))
    (hint : Option M) (i : ℕ) (a : AD) (e : C) (s : HSt CK MK AD M C)
    (harg : argE.eval ρ = ((hint, (i, (a, e))), encHS s.1)) :
    (multiDecIdx ae 0 mSlot ops hint i a e).run s =
      (·, s) <$> (callC argE (decIdxBody (I := I) ae G kPRG kAEAD mSlot specialDec)).eval ρ := by
  rcases s with ⟨h, sl⟩
  rw [callC_eval, harg]
  cases hint with
  | some msg =>
    simp [multiDecIdx, decIdxBody, Comp.eval, Expr.v0, Expr.eval, Env.get]
  | none =>
    have hi0 : decide (i = 0) = decide (i ≤ 0) := by
      by_cases h0 : i = 0 <;> simp [h0]
    cases specialDec with
    | none =>
      cases ops with
      | none =>
        simp only [multiDecIdx, multiKind, getH, onH, StateT.run_bind, StateT.run_mk,
          StateT.run_get, map_pure, pure_bind, decIdxBody, Comp.eval,
          hsKeysT, Expr.v0, Expr.v1, Expr.eval, Env.get, isCompromisedE_eval,
          encHS_corrAt, isCompromised_eq_isCompAt, hi0, encHS_keysT, Option.isSome_none,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        split_ifs
        · simp
        · cases h.keys[i - 1]?
          · simp
          · simp [Ops.sum, otccaOps]
      | some _ => exact False.elim hDec
    | some sDec =>
      cases ops with
      | none => exact False.elim hDec
      | some o =>
        dsimp only [SpecialDecRel] at hDec
        have him : decide (i < mSlot + 1) = decide (i ≤ mSlot) := by
          by_cases hm : i ≤ mSlot
          · have : i < mSlot + 1 := by omega
            simp [hm, this]
          · have : ¬(i < mSlot + 1) := by omega
            simp [hm, this]
        simp only [multiDecIdx, multiKind, getH, onH, StateT.run_bind, StateT.run_mk,
          StateT.run_get, map_pure, pure_bind, decIdxBody, Comp.eval,
          hsKeysT, Expr.v0, Expr.v1, Expr.eval, Env.get, isCompromisedE_eval,
          encHS_corrAt, isCompromised_eq_isCompAt, hi0, him, encHS_keysT, Option.isSome_some,
          Bool.true_and]
        split_ifs with h1 h2
        · simp
        · rw [hDec]
          simp [Expr.eval, Env.get]
        · cases h.keys[i - 1]?
          · simp
          · simp [Ops.sum, otccaOps]

omit [SampleableType MK] [SampleableType CK] in
theorem encIdxBody_eval {I : Iface (fsSig CK MK AD Unit M C) T} (mSlot : ℕ)
    (ideal : ℕ × AD → ProbComp C)
    (sampleIdeal : ∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod .nat (bt .ad)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I Δ (bt .ct))
    (hIdeal : SampleIdealRel ae G kPRG kAEAD sampleIdeal ideal)
    (specialEnc : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .msg)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I Δ (bt .ct)))
    (ops : Option (SpecialOps AD M C (OracleComp T)))
    (hEnc : SpecialEncRel ae G kPRG kAEAD specialEnc ops)
    (argE : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ
      (.prod (.prod .nat (.prod (bt .ad) (bt .msg))) hsTy'))
    (i : ℕ) (a : AD) (msg : M) (s : HSt CK MK AD M C)
    (harg : argE.eval ρ = ((i, (a, msg)), encHS s.1)) :
    (multiEncIdxWith ideal ae 0 mSlot ops i a msg).run s =
      (·, s) <$> (callC argE
        (encIdxBody (I := I) ae G kPRG kAEAD mSlot sampleIdeal specialEnc)).eval ρ := by
  dsimp only [SampleIdealRel] at hIdeal
  rcases s with ⟨h, sl⟩
  rw [callC_eval, harg]
  have hi0 : decide (i = 0) = decide (i ≤ 0) := by
    by_cases h0 : i = 0 <;> simp [h0]
  cases specialEnc with
  | none =>
    cases ops with
    | none =>
      simp only [multiEncIdxWith, multiKind, getH, onH, sampleH, StateT.run_bind, StateT.run_mk,
        StateT.run_get, map_pure, pure_bind, encIdxBody, Comp.eval,
        hsKeysT, Expr.v0, Expr.v1, Expr.eval, Env.get, isCompromisedE_eval,
        encHS_corrAt, isCompromised_eq_isCompAt, hi0, encHS_keysT, Option.isSome_none,
        Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · rw [hIdeal]
        simp [Expr.eval, Env.get]
      · cases h.keys[i - 1]? with
        | none =>
          dsimp only
          rw [hIdeal]
          simp [Expr.eval, Env.get]
        | some _ =>
          simp [Ops.sum, otccaOps]
    | some _ => exact False.elim hEnc
  | some sEnc =>
    cases ops with
    | none => exact False.elim hEnc
    | some o =>
      dsimp only [SpecialEncRel] at hEnc
      have him : decide (i < mSlot + 1) = decide (i ≤ mSlot) := by
        by_cases hm : i ≤ mSlot
        · have : i < mSlot + 1 := by omega
          simp [hm, this]
        · have : ¬(i < mSlot + 1) := by omega
          simp [hm, this]
      simp only [multiEncIdxWith, multiKind, getH, onH, sampleH, StateT.run_bind, StateT.run_mk,
        StateT.run_get, map_pure, pure_bind, encIdxBody, Comp.eval,
        hsKeysT, Expr.v0, Expr.v1, Expr.eval, Env.get, isCompromisedE_eval,
        encHS_corrAt, isCompromised_eq_isCompAt, hi0, him, encHS_keysT, Option.isSome_some,
        Bool.true_and]
      split_ifs with h1 h2
      · rw [hIdeal]
        simp [Expr.eval, Env.get]
      · rw [hEnc]
        simp [Expr.eval, Env.get]
      · cases h.keys[i - 1]? with
        | none =>
          dsimp only
          rw [hIdeal]
          simp [Expr.eval, Env.get]
        | some _ =>
          simp [Ops.sum, otccaOps]

include hliftP in
theorem receiveBody_eval (maxSkip mSlot : ℕ) (P : Params) (ht : P.t = some 0)
    (specialDec : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .ct)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (.opt (bt .msg))))
    (ops : Option (SpecialOps AD M C (OracleComp T)))
    (hDec : SpecialDecRel ae G kPRG kAEAD specialDec ops)
    (argE : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ
      (.prod (.prod (.opt (bt .msg)) (.prod (bt .ad) (.prod .nat (bt .ct)))) stTy'))
    (hint : Option M) (a : AD) (i : ℕ) (e : C) (s : HSt CK MK AD M C)
    (harg : argE.eval ρ = ((hint, (a, (i, e))), encSt s))
    (hrecv : s.1.receiverIdx ≤ s.1.keys.length) :
    (callC argE (receiveBody (I₀ := I₀) ae G kPRG kAEAD maxSkip P.j mSlot P.la specialDec)).eval
        ρ =
      Prod.map id encSt <$>
        (multiReceiveH ae G maxSkip P mSlot (DG G) ops hint a (i, e)).run s := by
  rcases s with ⟨h, sl⟩
  have hrecv' : h.receiverIdx ≤ h.keys.length := hrecv
  let ρ0 : Env (.prod (.prod (.opt (bt .msg)) (.prod (bt .ad) (.prod .nat (bt .ct)))) stTy' :: Γ) :=
    .cons ((hint, (a, (i, e))), encSt (h, sl)) ρ
  rw [callC_eval, harg]
  change (receiveBody (I₀ := I₀) ae G kPRG kAEAD maxSkip P.j mSlot P.la specialDec).eval ρ0 = _
  dsimp only [receiveBody, multiReceiveH, Comp.eval]
  rw [skippedContainsE_eval_eq ρ0 _ _ h rfl]
  have hiE :
      (Expr.fst (.snd (.snd (.fst (Expr.v0 (O := hybOps CK MK AD M C ae G kPRG kAEAD)))))).eval ρ0 =
        i := rfl
  rw [hiE]
  simp only [ht, Option.getD_some, getH, onH, modifyH, StateT.run_bind, StateT.run_mk,
    StateT.run_get, StateT.run_modify, map_pure, pure_bind]
  by_cases hcont : h.skipped.contains i = true
  · simp only [hcont, ↓reduceIte, StateT.run_bind]
    have hdec := decIdxBody_eval ae G kPRG kAEAD ρ0 mSlot specialDec ops hDec
      (.pair (.pair (.fst (.fst .v0)) (.pair (.fst (.snd (.snd (.fst .v0))))
        (.pair (.fst (.snd (.fst .v0))) (.snd (.snd (.snd (.fst .v0))))))) (.fst (.snd .v0)))
      hint i a e (h, sl) rfl
    rw [hdec, bind_map_left, map_bind]
    refine bind_congr fun optMsg => ?_
    cases optMsg with
    | none =>
      simp [Expr.v0, Expr.v1, Expr.eval, Env.get, Prod.map, ρ0]
    | some msg =>
      simp only [skippedRemoveE, callE_eval, Expr.v0, Expr.v2, Expr.eval, Env.get, encSt, ρ0]
      rw [skippedRemoveBody_eval _ h i]
      simp [StateT.run_mk, encSt, encHS, Prod.map]
  · have hcontF : h.skipped.contains i = false := Bool.eq_false_iff.mpr hcont
    simp only [hcontF, Bool.false_eq_true, ↓reduceIte, cond_true_left,
      isCompromisedE_eval, Expr.v0, Expr.eval, Env.get, encSt_fst,
      encHS_recvIdx, encHS_lastSent, encHS_corrAt, isCompromised_eq_isCompAt, ρ0]
    by_cases hwin : i ≤ h.receiverIdx ∨ maxSkip < i - h.receiverIdx - 1
    · have hwinB : (decide (i < h.receiverIdx + 1) || decide (maxSkip < i - h.receiverIdx - 1)) =
          true := by
        rcases hwin with h1 | h2
        · have : i < h.receiverIdx + 1 := by omega
          simp [this]
        · simp [h2]
      simp only [hwin, hwinB, ↓reduceIte, StateT.run_pure, map_pure, Prod.map, id_eq]
    · have hwinB : (decide (i < h.receiverIdx + 1) || decide (maxSkip < i - h.receiverIdx - 1)) =
          false := by
        have h1 : ¬(i < h.receiverIdx + 1) := by omega
        have h2 : ¬(maxSkip < i - h.receiverIdx - 1) := by omega
        simp [h1, h2]
      simp only [hwin, hwinB, Bool.false_eq_true, ↓reduceIte, ← Bool.and_assoc]
      by_cases hla : ((!P.la && decide (h.lastSentIdx < i)) && !isCompAt h.senderCorruptedAt i) =
          true
      · simp only [hla, ↓reduceIte, StateT.run_pure, map_pure, Prod.map, id_eq]
      · simp only [hla, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
        have hgen := genUpToC_eval ae G kPRG kAEAD hliftP ρ0 maxSkip P
          (.fst (.snd (.snd (.fst .v0)))) (.snd .v0) (h, sl) rfl
          (by
            change i - h.keys.length ≤ maxSkip + 1
            omega)
        dsimp only [Expr.v0, ρ0] at hgen
        rw [hgen, bind_map_left, map_bind]
        refine bind_congr fun z => ?_
        rcases z with ⟨_, h', sl'⟩
        let ρ1 : Env (stTy' :: _ :: Γ) := .cons (encSt (h', sl')) ρ0
        have hdec := decIdxBody_eval ae G kPRG kAEAD ρ1
          mSlot specialDec ops hDec
          (.pair (.pair (.fst (.fst .v1)) (.pair (.fst (.snd (.snd (.fst .v1))))
            (.pair (.fst (.snd (.fst .v1))) (.snd (.snd (.snd (.fst .v1))))))) (.fst .v0))
          hint i a e (h', sl') rfl
        dsimp only [ρ1, ρ0] at hdec
        rw [hdec, bind_map_left, map_bind]
        refine bind_congr fun optMsg => ?_
        cases optMsg with
        | none =>
          simp [Expr.v1, Expr.eval, Env.get, Prod.map]
        | some msg =>
          dsimp only [Comp.eval]
          let ρ2 : Env (bt .msg :: .opt (bt .msg) :: stTy' :: _ :: Γ) :=
            .cons msg (.cons (some msg) ρ1)
          have hprep := prependNewSkippedBody_eval
            (I := I₀.withSamp (HSamp CK MK AD M C)) ae G kPRG kAEAD ρ2 maxSkip
            (hsRecvIdx (.fst (.snd .v3))) (.fst (.snd (.snd (.fst .v3))))
            (hsSkipped (.fst .v2)) h'.skipped
            (by simp [Expr.v2, Expr.eval, Env.get, ρ2, ρ1])
            (by
              change i - h.receiverIdx - 1 ≤ maxSkip
              omega)
          simp only [callC_eval, hsRecvIdx, hsSkipped, Expr.v2, Expr.v3, Expr.eval, Env.get,
            encSt_fst, encHS_recvIdx, encHS_skipped, ρ2, ρ1, ρ0] at hprep
          simp only [Expr.v2, Expr.v3, Expr.eval, Env.get,
            encSt_fst, encHS_recvIdx, encHS_skipped]
          rw [hprep]
          simp [Expr.v1, Expr.v4, Expr.eval, Env.get,
            StateT.run_mk, encSt, encHS, Prod.map]

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem multiReceiveH_trans_eq (maxSkip mSlot : ℕ) (P : Params)
    (ops : Option (SpecialOps AD M C (OracleComp T)))
    (hint : Option M) (a : AD) (c : ℕ × C) (s : HSt CK MK AD M C) :
    ∀ z ∈ support ((multiReceiveH ae G maxSkip P mSlot (DG G) ops hint a c).run s),
      z.2.1.inTransit = s.1.inTransit ∧
      z.2.1.challengesInTransit = s.1.challengesInTransit := by
  rcases c with ⟨i, e⟩
  rcases s with ⟨h, sl⟩
  intro z hz
  simp only [multiReceiveH, getH, onH, modifyH, StateT.run_bind, StateT.run_mk,
    StateT.run_get, StateT.run_modify, map_pure, pure_bind] at hz
  split_ifs at hz with h1 h2 h3
  · simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have hy2 := multiDecIdx_frame ae P mSlot ops _ _ _ _ _ y hy
    rcases y with ⟨_ | msg, s'⟩ <;> simp only at hy2 <;> subst hy2 <;>
      simp at hz <;> subst hz <;> exact ⟨rfl, rfl⟩
  · simp at hz; subst hz; exact ⟨rfl, rfl⟩
  · simp at hz; subst hz; exact ⟨rfl, rfl⟩
  · simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨g, hg, y, hy, hz⟩ := hz
    obtain ⟨ks, -, hg1⟩ := genUpTo_support G P (DG G) i (h, sl) g hg
    have hy2 := multiDecIdx_frame ae P mSlot ops _ _ _ _ _ y hy
    rcases y with ⟨_ | msg, s'⟩ <;> simp only at hy2 <;> subst hy2 <;>
      simp at hz <;> subst hz <;> simp [hg1]

/-! ## Handler evaluation -/

include hliftP in
theorem corruptSenderBody_eval (q : ℕ) (P : Params)
    (s : HSt CK MK AD M C)
    (hsent : s.1.lastSentIdx ≤ q) :
    Prod.map (Option.map rssDec) id <$>
      (corruptSenderBody (I₀ := I₀) ae G kPRG kAEAD q P.la).eval
        (.cons (encSt s) ρ) =
      Prod.map id encSt <$>
        (corruptSenderH (m := OracleComp T) (AD := AD) (M := M) (C := C) G P ()).run s := by
  rcases s with ⟨h, sl⟩
  have hsent' : h.lastSentIdx ≤ q := hsent
  let ρ0 : Env (stTy' :: Γ) := .cons (encSt (h, sl)) ρ
  change Prod.map (Option.map rssDec) id <$>
    (corruptSenderBody (I₀ := I₀) ae G kPRG kAEAD q P.la).eval ρ0 = _
  dsimp only [corruptSenderBody, corruptSenderH, Comp.eval]
  simp only [getH, onH, modifyH, StateT.run_bind, StateT.run_mk, StateT.run_get,
    StateT.run_modify, map_pure, pure_bind, Expr.v0, Expr.eval, Env.get,
    encSt_fst, encHS_ended, ρ0]
  by_cases hend : h.ended = true
  · simp [hend, Prod.map]
  · have hendF : h.ended = false := Bool.eq_false_iff.mpr hend
    simp only [hendF, Bool.false_eq_true, ↓reduceIte]
    cases hla : P.la
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      rw [senderKeyBody_eval ae G kPRG kAEAD hliftP ρ q (h, sl) hsent',
        bind_map_left, map_bind, map_bind]
      refine bind_congr fun z => ?_
      rcases z with ⟨w, h', sl'⟩
      simp only [Expr.v1, Expr.eval, Env.get, encSt, encHS, Prod.map,
        id_eq, map_pure]
      cases h.senderCorruptedAt <;> cases h.corrKey <;> rfl
    · simp [encSt, encHS, encKc, Prod.map]

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] [SampleableType MK]
  [SampleableType CK] [MonadLiftT ProbComp (OracleComp T)] in
@[simp] theorem decide_pos_length_eq_not_isEmpty {α : Type} (xs : List α) :
    decide (0 < xs.length) = !xs.isEmpty := by
  cases xs <;> rfl

include hliftP in
theorem corruptReceiverResumeBody_eval (maxSkip q : ℕ) (P : Params)
    (s : HSt CK MK AD M C)
    (hbadF : ((s.1.ended || !s.1.challengesInTransit.isEmpty) ||
      s.1.inTransit.any (fun r => !s.1.isCompromised r.idx)) = false)
    (hsent : s.1.lastSentIdx ≤ q)
    (hrecv : s.1.receiverIdx ≤ (maxSkip + 1) * q)
    (hs : s.1.skipped.Pairwise (· > ·))
    (hpos : ∀ i ∈ s.1.skipped, 1 ≤ i)
    (hle : ∀ i ∈ s.1.skipped, i ≤ (maxSkip + 1) * q) :
    Prod.map
      ((ratchetCodec (CK := CK) (MK := MK) (AD := AD) (Pub := Unit) (M := M) (C := C)).rdec
        (Sum.inl (Sum.inl (Sum.inr ())))) id <$>
      (corruptReceiverResumeBody (I₀ := I₀) ae G kPRG kAEAD maxSkip q P.la).eval
        (.cons (encSt s) ρ) =
      Prod.map id encSt <$>
        (corruptReceiverH (m := OracleComp T) (AD := AD) (M := M) (C := C) (MK := MK) G P ()).run
          s := by
  rcases s with ⟨h, sl⟩
  have hbadF' : ((h.ended || !h.challengesInTransit.isEmpty) ||
      h.inTransit.any (fun r => !h.isCompromised r.idx)) = false := hbadF
  have hsent' : h.lastSentIdx ≤ q := hsent
  have hrecv' : h.receiverIdx ≤ (maxSkip + 1) * q := hrecv
  have hs' : h.skipped.Pairwise (· > ·) := hs
  have hpos' : ∀ i ∈ h.skipped, 1 ≤ i := hpos
  have hle' : ∀ i ∈ h.skipped, i ≤ (maxSkip + 1) * q := hle
  let ρ0 : Env (stTy' :: Γ) := .cons (encSt (h, sl)) ρ
  change Prod.map _ id <$>
    (corruptReceiverResumeBody (I₀ := I₀) ae G kPRG kAEAD maxSkip q P.la).eval ρ0 = _
  dsimp only [corruptReceiverResumeBody, corruptReceiverH, Comp.eval]
  simp only [getH, onH, modifyH, StateT.run_bind, StateT.run_mk, StateT.run_get,
    StateT.run_modify, map_pure, pure_bind, hbadF', Bool.false_eq_true, ↓reduceIte, ρ0]
  cases hla : P.la
  · simp only [Expr.eval, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    rw [senderKeyBody_eval ae G kPRG kAEAD hliftP ρ q (h, sl) hsent',
      bind_map_left, map_bind, map_bind]
    refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
    have hz1 := senderKey_fst G (h, sl) z hz
    rcases z with ⟨wA, h', sl'⟩
    simp only at hz1; subst h'
    dsimp only [Prod.map, id_eq]
    cases hcorr : h.senderCorruptedAt with
    | none =>
      simp only [hcorr, Expr.v0, Expr.v1, Expr.eval, Env.get, encSt_fst,
        encHS_corrAt, pure_bind]
      rw [corruptReceiverDBody_eval (I := I₀.withSamp (HSamp CK MK AD M C))
        ae G kPRG kAEAD _ maxSkip q h hs' hpos' hle']
      simp [ratchetCodec, hcorr, Expr.v2, Expr.eval, Env.get,
        encSt, encHS, encKc, rssDec, rrsDec, Prod.map]
    | some c =>
      cases hck : h.corrKey with
      | none =>
        simp only [hcorr, hck, Expr.v0, Expr.v1, Expr.eval, Env.get, encSt_fst,
          encHS_corrAt, encHS_corrKey, pure_bind]
        rw [corruptReceiverDBody_eval (I := I₀.withSamp (HSamp CK MK AD M C))
          ae G kPRG kAEAD _ maxSkip q h hs' hpos' hle']
        simp [ratchetCodec, hcorr, hck, Expr.v2, Expr.eval, Env.get,
          encSt, encHS, encKc, rssDec, rrsDec, Prod.map]
      | some w =>
        let ρ1 : Env (bt .ss :: .nat :: .prod (bt .ss) stTy' :: stTy' :: Γ) :=
          .cons w (.cons c (.cons (wA, encSt (h, sl')) (.cons (encSt (h, sl)) ρ)))
        have hc1 : (encSt (h, sl')).1.1.1.2.1 = some c := hcorr
        have hc2 : (encSt (h, sl')).1.2.2.2.1 = some w := hck
        simp only [Expr.v0, Expr.v1, Expr.eval, Env.get]
        rw [hc1]; dsimp only
        rw [hc2]; dsimp only
        have hcf := chainFromC_eval (I := I₀.withSamp (HSamp CK MK AD M C)) ae G kPRG kAEAD ρ1
          ((maxSkip + 1) * q) (.var (.succ .zero)) (.var .zero)
          (.sub (hsRecvIdx (.fst (.snd .v2))) (.var (.succ .zero)))
          (by
            dsimp only [hsRecvIdx, Expr.v2, Expr.eval, Env.get, encSt, encHS, ρ1]
            exact Nat.le_trans (Nat.sub_le _ _) hrecv')
        dsimp only [ρ1] at hcf
        rw [hcf]
        simp only [Expr.eval, Env.get, encSt_fst, pure_bind]
        rw [corruptReceiverDBody_eval (I := I₀.withSamp (HSamp CK MK AD M C))
          ae G kPRG kAEAD _ maxSkip q h hs' hpos' hle']
        simp [ratchetCodec, hcorr, hck, Expr.v2, Expr.eval, Env.get,
          encSt, encHS, encKc, rssDec, rrsDec, Prod.map]
  · simp [ratchetCodec,
      Expr.v0, Expr.eval, Env.get, encSt, encHS, encKc, Prod.map]

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] [SampleableType MK] in
theorem corruptReceiverH_ended_of_good (P : Params) (s : HSt CK MK AD M C)
    (hbadF : ((s.1.ended || !s.1.challengesInTransit.isEmpty) ||
      s.1.inTransit.any (fun r => !s.1.isCompromised r.idx)) = false) :
    ∀ z ∈ support
      ((corruptReceiverH (m := OracleComp T) (AD := AD) (M := M) (C := C) (MK := MK) G P ()).run
        s),
      z.2.1.ended = true := by
  rcases s with ⟨h, sl⟩
  have hbadF' : ((h.ended || !h.challengesInTransit.isEmpty) ||
      h.inTransit.any (fun r => !h.isCompromised r.idx)) = false := hbadF
  intro z hz
  simp only [corruptReceiverH, getH, onH, StateT.run_bind, StateT.run_mk, StateT.run_get,
    map_pure, pure_bind, hbadF', Bool.false_eq_true, ↓reduceIte] at hz
  split_ifs at hz
  · simp [modifyH, onH] at hz; subst hz; rfl
  · simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨w, _, hz⟩ := hz
    simp [modifyH, onH] at hz; subst hz; rfl

include hliftP in
theorem transmitBody_eval (maxSkip mSlot : ℕ) (P : Params) (ht : P.t = some 0)
    (ideal : ℕ × AD → ProbComp C)
    (sampleIdeal : ∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod .nat (bt .ad)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (bt .ct))
    (hIdeal : SampleIdealRel ae G kPRG kAEAD sampleIdeal ideal)
    (specialEnc : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .msg)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (bt .ct)))
    (ops : Option (SpecialOps AD M C (OracleComp T)))
    (hEnc : SpecialEncRel ae G kPRG kAEAD specialEnc ops)
    (a : AD) (m : M) (s : HSt CK MK AD M C)
    (hks : s.1.lastSentIdx ≤ s.1.keys.length) :
    (transmitBody (I₀ := I₀) ae G kPRG kAEAD maxSkip P.j mSlot sampleIdeal specialEnc).eval
        (.cons ((a, m), encSt s) ρ) =
      Prod.map id encSt <$>
        (multiTransmitHWith ideal ae G P mSlot (DG G) ops (a, m)).run s := by
  rcases s with ⟨h, sl⟩
  have hks' : h.lastSentIdx ≤ h.keys.length := hks
  let ρ0 : Env (.prod (.prod (bt .ad) (bt .msg)) stTy' :: Γ) :=
    .cons ((a, m), encSt (h, sl)) ρ
  change (transmitBody (I₀ := I₀) ae G kPRG kAEAD maxSkip P.j mSlot sampleIdeal specialEnc).eval
    ρ0 = _
  dsimp only [transmitBody, multiTransmitHWith, Comp.eval]
  have hend_eq :
      (hsEnded (.fst (.snd (Expr.v0 (O := hybOps CK MK AD M C ae G kPRG kAEAD))))).eval ρ0 =
      h.ended := rfl
  rw [hend_eq]
  simp only [ht, Option.getD_some, getH, onH, modifyH, StateT.run_bind, StateT.run_mk,
    StateT.run_get, StateT.run_modify, map_pure, pure_bind]
  by_cases hend : h.ended = true
  · simp [hend, Expr.v0, Expr.eval, Env.get, Prod.map, ρ0]
  · have hendF : h.ended = false := Bool.eq_false_iff.mpr hend
    simp only [hendF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hgen := genUpToC_eval ae G kPRG kAEAD hliftP ρ0 maxSkip P
      (.add (hsLastSent (.fst (.snd .v0))) (.nat 1)) (.snd .v0) (h, sl) rfl
      (by
        change (h.lastSentIdx + 1) - h.keys.length ≤ maxSkip + 1
        omega)
    change (genUpToC ae G kPRG kAEAD maxSkip P.j
        (.add (hsLastSent (.fst (.snd .v0))) (.nat 1)) (.snd .v0)).eval ρ0 =
      (fun z => encSt z.2) <$> (genUpTo G P (DG G) (h.lastSentIdx + 1)).run (h, sl) at hgen
    rw [hgen, bind_map_left, map_bind]
    refine bind_congr fun z => ?_
    rcases z with ⟨_, h', sl'⟩
    let ρ1 : Env (stTy' :: _ :: Γ) := .cons (encSt (h', sl')) ρ0
    have henc := encIdxBody_eval ae G kPRG kAEAD ρ1 mSlot ideal sampleIdeal hIdeal
      specialEnc ops hEnc
      (.pair (.pair (.add (hsLastSent (.fst (.snd .v1))) (.nat 1)) (.fst .v1)) (.fst .v0))
      (h.lastSentIdx + 1) a m (h', sl') rfl
    dsimp only [ρ1, ρ0] at henc
    rw [henc, bind_map_left, map_bind]
    refine bind_congr fun e => ?_
    simp only [Expr.v0, Expr.v1, Expr.v2, Expr.eval, Env.get, encSt, encHS, ρ0]
    rfl

include hliftP in
theorem challengeBody_eval (maxSkip mSlot : ℕ) (P : Params) (ht : P.t = some 0)
    (ideal : ℕ × AD → ProbComp C)
    (sampleIdeal : ∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod .nat (bt .ad)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (bt .ct))
    (hIdeal : SampleIdealRel ae G kPRG kAEAD sampleIdeal ideal)
    (specialEnc : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .msg)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (bt .ct)))
    (ops : Option (SpecialOps AD M C (OracleComp T)))
    (hEnc : SpecialEncRel ae G kPRG kAEAD specialEnc ops)
    (a : AD) (m₀ m₁ : M) (s : HSt CK MK AD M C)
    (hks : s.1.lastSentIdx ≤ s.1.keys.length) :
    (challengeBody (I₀ := I₀) ae G kPRG kAEAD maxSkip P.j mSlot sampleIdeal specialEnc).eval
        (.cons ((a, (m₀, m₁)), encSt s) ρ) =
      Prod.map id encSt <$>
        (multiChallengeHWith ideal ae G P mSlot (DG G) ops (a, (m₀, m₁))).run s := by
  rcases s with ⟨h, sl⟩
  have hks' : h.lastSentIdx ≤ h.keys.length := hks
  let ρ0 : Env (.prod (.prod (bt .ad) (.prod (bt .msg) (bt .msg))) stTy' :: Γ) :=
    .cons ((a, (m₀, m₁)), encSt (h, sl)) ρ
  change (challengeBody (I₀ := I₀) ae G kPRG kAEAD maxSkip P.j mSlot sampleIdeal specialEnc).eval
    ρ0 = _
  dsimp only [challengeBody, multiChallengeHWith, Comp.eval]
  have hcond :
      (orE (hsEnded (.fst (.snd (Expr.v0 (O := hybOps CK MK AD M C ae G kPRG kAEAD)))))
        (isSomeE (hsCorrAt (.fst (.snd .v0))))).eval ρ0 =
        (h.ended || h.senderCorruptedAt.isSome) := by
    simp only [Expr.v0, Expr.eval, Env.get, encSt_fst, encHS_ended, encHS_corrAt,
      cond_true_left, ρ0]
    cases h.senderCorruptedAt <;> rfl
  rw [hcond]
  simp only [ht, Option.getD_some, getH, onH, modifyH, StateT.run_bind, StateT.run_mk,
    StateT.run_get, StateT.run_modify, map_pure, pure_bind]
  by_cases hbad : (h.ended || h.senderCorruptedAt.isSome) = true
  · simp [hbad, Expr.v0, Expr.eval, Env.get, Prod.map, ρ0]
  · have hbadF : (h.ended || h.senderCorruptedAt.isSome) = false := Bool.eq_false_iff.mpr hbad
    simp only [hbadF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hgen := genUpToC_eval ae G kPRG kAEAD hliftP ρ0 maxSkip P
      (.add (hsLastSent (.fst (.snd .v0))) (.nat 1)) (.snd .v0) (h, sl) rfl
      (by
        change (h.lastSentIdx + 1) - h.keys.length ≤ maxSkip + 1
        omega)
    change (genUpToC ae G kPRG kAEAD maxSkip P.j
        (.add (hsLastSent (.fst (.snd .v0))) (.nat 1)) (.snd .v0)).eval ρ0 =
      (fun z => encSt z.2) <$> (genUpTo G P (DG G) (h.lastSentIdx + 1)).run (h, sl) at hgen
    rw [hgen, bind_map_left, map_bind]
    refine bind_congr fun z => ?_
    rcases z with ⟨_, h', sl'⟩
    let ρ1 : Env (stTy' :: _ :: Γ) := .cons (encSt (h', sl')) ρ0
    have henc := encIdxBody_eval ae G kPRG kAEAD ρ1 mSlot ideal sampleIdeal hIdeal
      specialEnc ops hEnc
      (.pair (.pair (.add (hsLastSent (.fst (.snd .v1))) (.nat 1))
        (.pair (.fst (.fst .v1))
          (.ite (hsB (.fst (.snd .v1))) (.snd (.snd (.fst .v1))) (.fst (.snd (.fst .v1))))))
        (.fst .v0))
      (h.lastSentIdx + 1) a (if h.b then m₁ else m₀) (h', sl') rfl
    dsimp only [ρ1, ρ0] at henc
    rw [henc, bind_map_left, map_bind]
    refine bind_congr fun e => ?_
    simp only [Expr.v0, Expr.v1, Expr.v2, Expr.eval, Env.get, encSt, encHS, ρ0]
    rfl

include hliftP in
theorem deliverBody_eval (maxSkip q mSlot : ℕ) (P : Params) (ht : P.t = some 0)
    (specialDec : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .ct)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (.opt (bt .msg))))
    (ops : Option (SpecialOps AD M C (OracleComp T)))
    (hDec : SpecialDecRel ae G kPRG kAEAD specialDec ops)
    (a : AD) (i : ℕ) (e : C) (s : HSt CK MK AD M C)
    (hrecv : s.1.receiverIdx ≤ s.1.keys.length)
    (htr : s.1.inTransit.length ≤ q)
    (hch : s.1.challengesInTransit.length ≤ q) :
    Prod.map (Option.map rrDecM) id <$>
      (deliverBody (I₀ := I₀) ae G kPRG kAEAD maxSkip q P.j mSlot P.la specialDec).eval
        (.cons ((a, (i, e)), encSt s) ρ) =
      Prod.map id encSt <$>
        (multiDeliverH ae G maxSkip P mSlot (DG G) ops (a, (i, e))).run s := by
  rcases s with ⟨h, sl⟩
  have hrecv' : h.receiverIdx ≤ h.keys.length := hrecv
  have htr' : h.inTransit.length ≤ q := htr
  have hch' : h.challengesInTransit.length ≤ q := hch
  let ρ0 : Env (.prod (.prod (bt .ad) (.prod .nat (bt .ct))) stTy' :: Γ) :=
    .cons ((a, (i, e)), encSt (h, sl)) ρ
  change Prod.map (Option.map rrDecM) id <$>
    (deliverBody (I₀ := I₀) ae G kPRG kAEAD maxSkip q P.j mSlot P.la specialDec).eval ρ0 = _
  dsimp only [deliverBody, multiDeliverH, Comp.eval]
  have hend_eq :
      (hsEnded (.fst (.snd (Expr.v0 (O := hybOps CK MK AD M C ae G kPRG kAEAD))))).eval ρ0 =
      h.ended := rfl
  rw [hend_eq]
  simp only [getH, onH, modifyH, StateT.run_bind, StateT.run_mk, StateT.run_get,
    StateT.run_modify, map_pure, pure_bind]
  by_cases hend : h.ended = true
  · simp [hend, Expr.v0, Expr.eval, Env.get, Prod.map, ρ0]
  · have hendF : h.ended = false := Bool.eq_false_iff.mpr hend
    simp only [hendF, Bool.false_eq_true, ↓reduceIte]
    have hft :
        (findInTransitE ae G kPRG kAEAD q (.fst (.snd .v0)) (.fst .v0)).eval ρ0 =
          (h.inTransit.find? (fun r => r.ad == a && r.ct == (i, e))).map encRec :=
      findInTransitE_eval_eq ae G kPRG kAEAD ρ0 q
        (.fst (.snd .v0)) (.fst .v0) h rfl htr'
    rw [hft]
    cases hfind : h.inTransit.find? (fun r => r.ad == a && r.ct == (i, e)) with
    | none =>
      simp [Expr.v0, Expr.eval, Env.get, Prod.map, ρ0]
    | some r =>
      dsimp only [Option.map, StateT.run_bind]
      let ρ1 : Env (recTy' :: _ :: Γ) := .cons (encRec r) ρ0
      have hrec := receiveBody_eval ae G kPRG kAEAD hliftP ρ1 maxSkip mSlot P ht
        specialDec ops hDec
        (.pair (.pair (.some (recMsg .v0)) (.fst .v1)) (.snd .v1))
        (some r.msg) a i e (h, sl) rfl hrecv'
      rw [callC_eval] at hrec
      dsimp only [ρ1] at hrec
      rw [hrec, bind_map_left, map_bind, map_bind]
      refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
      obtain ⟨htr_z, hch_z⟩ := multiReceiveH_trans_eq ae G maxSkip mSlot P ops
        (some r.msg) a (i, e) (h, sl) z hz
      rcases z with ⟨optRes, h', sl'⟩
      simp only at htr_z hch_z
      have hwin_eq : decide (r.idx < h.receiverIdx + maxSkip + 2) =
          decide (r.idx ≤ h.receiverIdx + maxSkip + 1) := by
        by_cases hw : r.idx ≤ h.receiverIdx + maxSkip + 1
        · have : r.idx < h.receiverIdx + maxSkip + 2 := by omega
          simp [hw, this]
        · have : ¬(r.idx < h.receiverIdx + maxSkip + 2) := by omega
          simp [hw, this]
      cases optRes with
      | none =>
        simp [recIdx, Expr.v0, Expr.v1, Expr.v2, Expr.eval, Env.get, encSt, encHS, encKc, encRec,
          isCompromised_eq_isCompAt, hwin_eq, rrDecM, Prod.map, ρ0]
      | some im =>
        rcases im with ⟨i', m'⟩
        have htr_h' : h'.inTransit.length ≤ q := htr_z ▸ htr'
        have hch_h' : h'.challengesInTransit.length ≤ q := hch_z ▸ hch'
        have hch0_take : List.take q h.challengesInTransit = h.challengesInTransit :=
          List.take_of_length_le hch'
        have htr_take : List.take q (List.map encRec h'.inTransit) = List.map encRec h'.inTransit :=
          List.take_of_length_le (by simpa using htr_h')
        have hch_take : List.take q h'.challengesInTransit = h'.challengesInTransit :=
          List.take_of_length_le hch_h'
        have hne_i : (!decide (i' = r.idx)) = (i' != r.idx) := by
          rw [bne, beq_eq_decide]
        have hne_m : (!(m' == r.msg)) = (m' != r.msg) := rfl
        simp [removeFromTransitBody, challsContainsBody, eqME, Ops.sum, otccaOps, mkHS, hsB,
          hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin, hsLf, hsInTransit, hsChalls, hsNKeys,
          hsKeysT, hsCorrKey, hsSkipped, recIdx, recMsg, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
          Expr.eval, Env.get, encSt, encHS, encKc, encRec, isCompromised_eq_isCompAt, hwin_eq, hne_i,
          hne_m, hch0_take, htr_take, hch_take, foldr_filter_recIdx', foldr_filter_nat',
          HState.removeFromTransit, rrDecM, Prod.map, ρ0]

include hliftP in
theorem injectBody_eval (maxSkip q mSlot : ℕ) (P : Params) (ht : P.t = some 0)
    (specialDec : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .ct)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (.opt (bt .msg))))
    (ops : Option (SpecialOps AD M C (OracleComp T)))
    (hDec : SpecialDecRel ae G kPRG kAEAD specialDec ops)
    (a : AD) (i : ℕ) (e : C) (s : HSt CK MK AD M C)
    (hrecv : s.1.receiverIdx ≤ s.1.keys.length)
    (htr : s.1.inTransit.length ≤ q)
    (hch : s.1.challengesInTransit.length ≤ q) :
    Prod.map (Option.map rrDecM) id <$>
      (injectBody (I₀ := I₀) ae G kPRG kAEAD maxSkip q P.j mSlot P.la specialDec).eval
        (.cons ((a, (i, e)), encSt s) ρ) =
      Prod.map id encSt <$>
        (multiInjectH ae G maxSkip P mSlot (DG G) ops (a, (i, e))).run s := by
  rcases s with ⟨h, sl⟩
  have hrecv' : h.receiverIdx ≤ h.keys.length := hrecv
  have htr' : h.inTransit.length ≤ q := htr
  have hch' : h.challengesInTransit.length ≤ q := hch
  let ρ0 : Env (.prod (.prod (bt .ad) (.prod .nat (bt .ct))) stTy' :: Γ) :=
    .cons ((a, (i, e)), encSt (h, sl)) ρ
  change Prod.map (Option.map rrDecM) id <$>
    (injectBody (I₀ := I₀) ae G kPRG kAEAD maxSkip q P.j mSlot P.la specialDec).eval ρ0 = _
  dsimp only [injectBody, multiInjectH, Comp.eval]
  have hcond :
      (orE (hsEnded (.fst (.snd (Expr.v0 (O := hybOps CK MK AD M C ae G kPRG kAEAD)))))
        (anyInTransitE ae G kPRG kAEAD q (.fst (.snd .v0)) (.fst .v0))).eval ρ0 =
        (h.ended || h.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) := by
    have hat := anyInTransitE_eval_eq ae G kPRG kAEAD ρ0 q
      (.fst (.snd .v0)) (.fst .v0) h rfl htr'
    dsimp only [orE, Expr.eval]
    rw [hat]
    change (if h.ended = true then true
      else h.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = _
    cases h.ended <;> rfl
  rw [hcond]
  simp only [getH, onH, modifyH, StateT.run_bind, StateT.run_mk, StateT.run_get,
    StateT.run_modify, map_pure, pure_bind]
  by_cases hbad : (h.ended || h.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = true
  · simp [hbad, Expr.v0, Expr.eval, Env.get, Prod.map, ρ0]
  · have hbadF : (h.ended || h.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false :=
      Bool.eq_false_iff.mpr hbad
    simp only [hbadF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hrec := receiveBody_eval ae G kPRG kAEAD hliftP ρ0 maxSkip mSlot P ht
      specialDec ops hDec
      (.pair (.pair .none (.fst .v0)) (.snd .v0))
      none a i e (h, sl) rfl hrecv'
    rw [callC_eval] at hrec
    rw [hrec, bind_map_left, map_bind, map_bind]
    refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
    obtain ⟨htr_z, hch_z⟩ := multiReceiveH_trans_eq ae G maxSkip mSlot P ops
      none a (i, e) (h, sl) z hz
    rcases z with ⟨optRes, h', sl'⟩
    simp only at htr_z hch_z
    cases optRes with
    | none =>
      simp [Expr.v0, Expr.eval, Env.get, rrDecM, Prod.map]
    | some im =>
      rcases im with ⟨i', m'⟩
      have htr_h' : h'.inTransit.length ≤ q := htr_z ▸ htr'
      have hch_h' : h'.challengesInTransit.length ≤ q := hch_z ▸ hch'
      have htr_take : List.take q (List.map encRec h'.inTransit) = List.map encRec h'.inTransit :=
        List.take_of_length_le (by simpa using htr_h')
      have hch_take : List.take q h'.challengesInTransit = h'.challengesInTransit :=
        List.take_of_length_le hch_h'
      simp [removeFromTransitBody, recIdx, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded,
        hsWin, hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped,
        Expr.v0, Expr.v1, Expr.v2, Expr.eval, Env.get, encSt, encHS, encKc,
        isCompromised_eq_isCompAt, htr_take, hch_take,
        foldr_filter_recIdx', foldr_filter_nat', HState.removeFromTransit, rrDecM,
        Prod.map, ρ0]

end Subroutines

/-! ## Two-stage simulation -/

theorem bind_pure_option_map {ι : Type} {T : OracleSpec ι} {α β γ : Type}
    (oa : OracleComp T (Option α × β)) (f : α → γ) :
    (oa >>= fun x => pure (Option.map f x.1, x.2)) =
      Prod.map (Option.map f) id <$> oa := by
  rw [map_eq_bind_pure_comp]; rfl

theorem bind_map_fst {ι : Type} {T : OracleSpec ι} {α β γ δ : Type}
    (oa : OracleComp T (α × β)) (g : α → γ) (f : γ → β → OracleComp T δ) :
    (oa >>= fun x => f (g x.1) x.2) = ((Prod.map g id <$> oa) >>= fun y => f y.1 y.2) := by
  rw [bind_map_left]; rfl

section TwoStageSim

variable {CK MK AD M C : Type} [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  [SampleableType MK] [SampleableType CK]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (kPRG kAEAD : ℕ)
  {ι : Type} {T : OracleSpec.{0, 0} ι} [MonadLiftT ProbComp (OracleComp T)]
  {I₀ : Iface (fsSig CK MK AD Unit M C) T}
  (hliftP : ∀ {α : Type} (p : ProbComp α), I₀.liftP p = (liftM p : OracleComp T α))

local notation "stTy'" => stTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)

omit [SampleableType MK] [SampleableType CK] [MonadLiftT ProbComp (OracleComp T)] in
theorem hybFinishC_eval {I : Iface (fsSig CK MK AD Unit M C) T}
    (la b' : Bool) (y : Unit) (s : HSt CK MK AD M C) :
    (hybFinishC (I := I) ae G kPRG kAEAD la).eval
      (.cons (encSt s) (.cons b' (.cons y .nil))) = pure (hOut la (b', s)) := by
  rcases s with ⟨h, sl⟩
  simp only [hybFinishC, hOut, Comp.eval, hsB, hsWin, hsLf, orE, beqBoolE,
    Expr.v0, Expr.v1, Expr.eval, Env.get, encSt_fst, encHS_b, encHS_win, encHS_lf]
  cases la <;> cases h.b <;> cases b' <;> cases h.win <;> cases h.lf <;> rfl

theorem multiImplWith_inl_run (maxSkip mSlot : ℕ) (P : Params)
    (ideal : ℕ × AD → ProbComp C)
    (ops : Option (SpecialOps AD M C (OracleComp T)))
    (u : ℕ) (s : HSt CK MK AD M C) :
    ((multiImplWith (m := OracleComp T) ideal ae G maxSkip P mSlot (DG G) ops)
      (Sum.inl u)).run s =
      (·, s) <$> (liftM (query (spec := unifSpec) u : ProbComp (Fin (u + 1))) :
        OracleComp T (Fin (u + 1))) := by
  simp [multiImplWith, QueryImpl.add_apply_inl, StateT.run_monadLift]

theorem multiImplWith_ended (maxSkip mSlot : ℕ) (P : Params)
    (ideal : ℕ × AD → ProbComp C)
    (ops : Option (SpecialOps AD M C (OracleComp T)))
    (t : (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)).Domain)
    (s : HSt CK MK AD M C) (hend : s.1.ended = true) :
    ((multiImplWith (m := OracleComp T) ideal ae G maxSkip P mSlot (DG G) ops)
      (Sum.inr t)).run s =
      pure ((ratchetCodec (CK := CK) (MK := MK) (AD := AD) (Pub := Unit) (M := M) (C := C)).rdec
        t (Sum.inl none), s) := by
  rcases s with ⟨h, sl⟩
  have hend' : h.ended = true := hend
  rcases t with (((((⟨a, msg⟩ | ⟨a, m₀, m₁⟩) | ⟨⟩) | ⟨⟩) | ⟨a, i, e⟩) | ⟨a, i, e⟩)
  · change (multiTransmitHWith ideal ae G P mSlot (DG G) ops (a, msg)).run (h, sl) =
      pure (none, h, sl)
    simp [multiTransmitHWith, getH, onH, hend']
  · change (multiChallengeHWith ideal ae G P mSlot (DG G) ops (a, m₀, m₁)).run (h, sl) =
      pure (none, h, sl)
    simp [multiChallengeHWith, getH, onH, hend']
  · change (corruptSenderH G P ()).run (h, sl) = pure (none, h, sl)
    simp [corruptSenderH, getH, onH, hend']
  · change (corruptReceiverH G P ()).run (h, sl) = pure (none, h, sl)
    simp [corruptReceiverH, getH, onH, hend']
  · change (multiDeliverH ae G maxSkip P mSlot (DG G) ops (a, i, e)).run (h, sl) =
      pure (none, h, sl)
    simp [multiDeliverH, getH, onH, hend']
  · change (multiInjectH ae G maxSkip P mSlot (DG G) ops (a, i, e)).run (h, sl) =
      pure (none, h, sl)
    simp [multiInjectH, getH, onH, hend']

include hliftP in
theorem runFuel_handlePost_eq_simulateQ (maxSkip mSlot : ℕ) (P : Params)
    (ideal : ℕ × AD → ProbComp C)
    (ops : Option (SpecialOps AD M C (OracleComp T)))
    {α : Type} (dflt : α)
    (oa : OracleComp (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK)
      AD M (ℕ × C)) α) :
    ∀ {m fuel₂ : ℕ} {s : HSt CK MK AD M C},
      oa.IsQueryBoundP (fun x => x.isRight = true) m →
      m ≤ fuel₂ →
      s.1.ended = true →
      runFuel (C := ratchetCodec)
        (hybHandlePostC (I := I₀.withSamp (HSamp CK MK AD M C)) ae G kPRG kAEAD)
        dflt oa fuel₂ (encSt s) =
      Prod.map id encSt <$>
        (simulateQ (multiImplWith (m := OracleComp T) ideal ae G maxSkip P mSlot (DG G) ops)
          oa).run s := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro m fuel₂ s _ _ _
    simp [runFuel, Prod.map]
  | query_bind t mx ih =>
    intro m fuel₂ s hb hm hend
    rw [isQueryBoundP_query_bind_iff] at hb
    rcases t with u | t
    · have hfwd : (I₀.withSamp (HSamp CK MK AD M C)).fwdU u =
          (liftM (query (spec := unifSpec) u : ProbComp (Fin (u + 1))) :
            OracleComp T (Fin (u + 1))) := by
        simpa [Iface.withSamp, Iface.liftP, simulateQ_query] using
          hliftP (query (spec := unifSpec) u)
      simp only [runFuel, construct_query_bind, hfwd, simulateQ_query_bind,
        OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind, map_bind]
      change _ = (((multiImplWith (m := OracleComp T) ideal ae G maxSkip P mSlot (DG G) ops)
        (Sum.inl u)).run s >>= _)
      rw [multiImplWith_inl_run ae G maxSkip mSlot P ideal ops u s, bind_map_left]
      exact bind_congr fun v => ih v (by simpa using hb.2 v) hm hend
    · have hm_pos : 0 < m := hb.1.resolve_left (by simp)
      cases fuel₂ with
      | zero => omega
      | succ f₂ =>
        simp only [runFuel, construct_query_bind, hybHandlePostC, Comp.eval,
          Expr.v0, Expr.eval, simulateQ_query_bind,
          OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind, map_bind]
        change _ = (((multiImplWith (m := OracleComp T) ideal ae G maxSkip P mSlot (DG G) ops)
          (Sum.inr t)).run s >>= _)
        rw [multiImplWith_ended ae G maxSkip mSlot P ideal ops t s hend, pure_bind]
        exact ih _ (by simpa using hb.2 _) (by omega) hend

include hliftP in
set_option maxHeartbeats 400000 in
/-- Simulates `multiImplWith` via Stage 1 (`run1`) followed by Stage 2 (`eval2`) on bounded-query computations. -/
theorem run1_eval2_eq_simulateQ
    {rIn : Ty (fsSig CK MK AD Unit M C)}
    (initC : Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
      (I₀.withSamp (HSamp CK MK AD M C)) [rIn] (.prod .unit stTy'))
    (maxSkip q mSlot fuel₂ : ℕ) (P : Params) (ht : P.t = some 0)
    (ideal : ℕ × AD → ProbComp C)
    (sampleIdeal : ∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod .nat (bt .ad)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (bt .ct))
    (hIdeal : SampleIdealRel ae G kPRG kAEAD sampleIdeal ideal)
    (specialEnc : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .msg)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (bt .ct)))
    (specialDec : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .ct)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (.opt (bt .msg))))
    (ops : Option (SpecialOps AD M C (OracleComp T)))
    (hEnc : SpecialEncRel ae G kPRG kAEAD specialEnc ops)
    (hDec : SpecialDecRel ae G kPRG kAEAD specialDec ops)
    (oa : OracleComp (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK)
      AD M (ℕ × C)) Bool) :
    let R : TwoStageCostedReduction (hybOps CK MK AD M C ae G kPRG kAEAD)
        (I₀.withSamp (HSamp CK MK AD M C))
        (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
        ratchetCodec rIn .unit .bool .unit .unit .bool :=
      { σ := stTy'
        π := .unit
        init := initC
        handlePre := hybHandlePreC ae G kPRG kAEAD maxSkip q P.j mSlot P.la
          sampleIdeal specialEnc specialDec
        chDone := hybChDoneC ae G kPRG kAEAD
        resume := hybResumeC ae G kPRG kAEAD maxSkip q P.la
        handlePost := hybHandlePostC ae G kPRG kAEAD
        finish := hybFinishC ae G kPRG kAEAD P.la }
    ∀ {m n fuel₁ : ℕ} {s : HSt CK MK AD M C},
      oa.IsQueryBoundP (fun x => x.isRight = true) m →
      HInv maxSkip n s.1 →
      n + m ≤ q →
      m ≤ fuel₁ →
      m ≤ fuel₂ + 1 →
      (do
        let mid ← R.run1 false oa fuel₁ (encSt s)
        R.eval2 mid () fuel₂ false) =
      (do
        let z ← (simulateQ (multiImplWith (m := OracleComp T) ideal ae G maxSkip P mSlot (DG G) ops)
          oa).run s
        pure (hOut P.la z)) := by
  intro R
  induction oa using OracleComp.inductionOn with
  | pure b' =>
    intro m n fuel₁ s _ _ _ _ _
    simp only [TwoStageCostedReduction.run1, construct_pure, pure_bind,
      TwoStageCostedReduction.eval2, simulateQ_pure, StateT.run_pure]
    exact hybFinishC_eval ae G kPRG kAEAD P.la b' () s
  | query_bind t mx ih =>
    intro m n fuel₁ s hb hI hq hm1 hm2
    rw [isQueryBoundP_query_bind_iff] at hb
    rcases t with u | t
    · have hfwd : (I₀.withSamp (HSamp CK MK AD M C)).fwdU u =
          (liftM (query (spec := unifSpec) u : ProbComp (Fin (u + 1))) :
            OracleComp T (Fin (u + 1))) := by
        simpa [Iface.withSamp, Iface.liftP, simulateQ_query] using
          hliftP (query (spec := unifSpec) u)
      simp only [TwoStageCostedReduction.run1, construct_query_bind, R, hfwd, bind_assoc,
        simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
      change _ = (((multiImplWith (m := OracleComp T) ideal ae G maxSkip P mSlot (DG G) ops)
        (Sum.inl u)).run s >>= _)
      rw [multiImplWith_inl_run ae G maxSkip mSlot P ideal ops u s, bind_map_left]
      exact bind_congr fun v => ih v (by simpa using hb.2 v) hI hq hm1 hm2
    · have hm_pos : 0 < m := hb.1.resolve_left (by simp)
      cases fuel₁ with
      | zero => omega
      | succ f₁ =>
        have hn : n ≤ q := by omega
        have hIq : HInv maxSkip q s.1 := hI.mono hn
        have hsent : s.1.lastSentIdx ≤ q := hIq.sent_le
        have hrecv : s.1.receiverIdx ≤ (maxSkip + 1) * q := hIq.recv_le
        have htr : s.1.inTransit.length ≤ q := hIq.transit_len
        have hch : s.1.challengesInTransit.length ≤ q := hIq.chal_len
        have hks : s.1.lastSentIdx ≤ s.1.keys.length := hIq.keys_sent
        have hkr : s.1.receiverIdx ≤ s.1.keys.length := hIq.keys_recv
        have hpres := multiImplWith_inv ideal ae G P mSlot (DG G) ops (Sum.inr t) s hI
        simp only [Sum.isRight, ↓reduceIte] at hpres
        simp only [TwoStageCostedReduction.run1, construct_query_bind, bind_assoc,
          simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
        rw [show R.handlePre.eval (.cons (encSt s) (.cons (ratchetCodec.qenc t) .nil)) =
          (hybHandlePreC ae G kPRG kAEAD maxSkip q P.j mSlot P.la
            sampleIdeal specialEnc specialDec).eval
            (.cons (encSt s) (.cons (ratchetCodec.qenc t) .nil)) from rfl]
        rcases t with (((((⟨a, msg⟩ | ⟨a, m₀, m₁⟩) | ⟨⟩) | ⟨⟩) | ⟨a, i, e⟩) | ⟨a, i, e⟩)
        ·
          change _ = ((multiTransmitHWith ideal ae G P mSlot (DG G) ops (a, msg)).run s >>= _)
          simp only [hybHandlePreC, ratchetCodec, Comp.eval,
            Expr.v0, Expr.v1, Expr.eval, Env.get, bind_assoc, pure_bind]
          rw [transmitBody_eval ae G kPRG kAEAD hliftP _ maxSkip mSlot P ht
            ideal sampleIdeal hIdeal specialEnc ops hEnc a msg s hks, bind_map_left]
          refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
          exact ih z.1 (by simpa using hb.2 z.1) (hpres z hz) (by omega) (by omega) (by omega)
        ·
          change _ = ((multiChallengeHWith ideal ae G P mSlot (DG G) ops (a, m₀, m₁)).run s >>= _)
          simp only [hybHandlePreC, ratchetCodec, Comp.eval,
            Expr.v0, Expr.v1, Expr.v2, Expr.eval, Env.get, bind_assoc, pure_bind]
          rw [challengeBody_eval ae G kPRG kAEAD hliftP _ maxSkip mSlot P ht
            ideal sampleIdeal hIdeal specialEnc ops hEnc a m₀ m₁ s hks, bind_map_left]
          refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
          exact ih z.1 (by simpa using hb.2 z.1) (hpres z hz) (by omega) (by omega) (by omega)
        ·
          change _ = ((corruptSenderH G P ()).run s >>= _)
          simp only [hybHandlePreC, ratchetCodec, Comp.eval,
            Expr.v0, Expr.v1, Expr.v3, Expr.eval, Env.get, bind_assoc, pure_bind]
          change ((corruptSenderBody ae G kPRG kAEAD q P.la).eval _ >>= fun x =>
            R.run1 false (mx (Option.map rssDec x.1)) f₁ x.2 >>= fun mid =>
            R.eval2 mid () fuel₂ false) = _
          rw [bind_map_fst _ (Option.map rssDec)
              (fun v s' => R.run1 false (mx v) f₁ s' >>= fun mid => R.eval2 mid () fuel₂ false),
            corruptSenderBody_eval ae G kPRG kAEAD hliftP _ q P s hsent, bind_map_left]
          refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
          exact ih z.1 (by simpa using hb.2 z.1) (hpres z hz) (by omega) (by omega) (by omega)
        ·
          change _ = ((corruptReceiverH G P ()).run s >>= _)
          simp only [hybHandlePreC, ratchetCodec, Comp.eval, orE, cond_true_left,
            hsEnded, hsChalls, Expr.v0, Expr.v1, Expr.v4, Expr.eval, Env.get,
            encSt_fst, encHS_ended, encHS_challs, decide_pos_length_eq_not_isEmpty,
            ← Bool.or_assoc, anyUncompInTransitE_eval, anyUncompInTransitBody_eval _ q s.1 htr]
          by_cases hbad :
              ((s.1.ended || !s.1.challengesInTransit.isEmpty) ||
                s.1.inTransit.any (fun r => !s.1.isCompromised r.idx)) = true
          · have hcr_bad :
                (corruptReceiverH (m := OracleComp T) (AD := AD) (M := M) (C := C) (MK := MK)
                  G P ()).run s = pure (none, s) := by
              rcases s with ⟨h, sl⟩
              have hbad' : ((h.ended || !h.challengesInTransit.isEmpty) ||
                  h.inTransit.any (fun r => !h.isCompromised r.idx)) = true := hbad
              simp only [corruptReceiverH, getH, onH, StateT.run_bind, StateT.run_mk,
                StateT.run_get, StateT.run_pure, map_pure, pure_bind, hbad', ↓reduceIte]
            simp only [hbad, ↓reduceIte, pure_bind, hcr_bad]
            exact ih none (by simpa using hb.2 none) (hI.mono (Nat.le_succ n))
              (by omega) (by omega) (by omega)
          · have hbadF :
                ((s.1.ended || !s.1.challengesInTransit.isEmpty) ||
                  s.1.inTransit.any (fun r => !s.1.isCompromised r.idx)) = false :=
              Bool.eq_false_iff.mpr hbad
            have hres_eq : R.resume = hybResumeC ae G kPRG kAEAD maxSkip q P.la := rfl
            simp only [hbadF, Bool.false_eq_true, ↓reduceIte, pure_bind,
              TwoStageCostedReduction.eval2, hres_eq, hybResumeC]
            try rw [bind_assoc]
            let env2 : Env (S := HSig CK MK AD M C) [.unit, .unit] :=
              .cons (t := .unit) () (.cons (t := .unit) () .nil)
            let kPost := fun ans s' =>
              runFuel (C := ratchetCodec)
                (hybHandlePostC (I := I₀.withSamp (HSamp CK MK AD M C)) ae G kPRG kAEAD)
                false (mx ans) fuel₂ s' >>=
              fun bs => (hybFinishC (I := I₀.withSamp (HSamp CK MK AD M C)) ae G kPRG kAEAD P.la).eval
                (.cons bs.2 (.cons (t := .bool) bs.1 (.cons (t := .unit) () .nil)))
            refine (bind_map_fst
              ((corruptReceiverResumeBody (I₀ := I₀) ae G kPRG kAEAD maxSkip q P.la).eval
                (.cons (encSt s) env2))
              ((ratchetCodec (CK := CK) (MK := MK) (AD := AD) (Pub := Unit) (M := M) (C := C)).rdec
                (Sum.inl (Sum.inl (Sum.inr ()))))
              kPost).trans ?_
            have hres_eval := corruptReceiverResumeBody_eval ae G kPRG kAEAD hliftP env2
              maxSkip q P s hbadF hsent hrecv hIq.skipped_sorted hIq.skipped_pos
              (fun i hi => (hIq.skipped_le i hi).trans hIq.recv_le)
            refine (congrArg (· >>= fun y => kPost y.1 y.2) hres_eval).trans ?_
            rw [bind_map_left]
            dsimp only [kPost]
            refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
            have hz_end : z.2.1.ended = true := corruptReceiverH_ended_of_good G P s hbadF z hz
            rcases z with ⟨ans, s'⟩
            dsimp only [Prod.map, id_eq] at hz_end ⊢
            rw [runFuel_handlePost_eq_simulateQ ae G kPRG kAEAD hliftP maxSkip mSlot P ideal ops
              false (mx ans) (by simpa using hb.2 ans) (by omega) hz_end, bind_map_left]
            refine bind_congr fun ⟨b'', s''⟩ => ?_
            exact hybFinishC_eval ae G kPRG kAEAD P.la b'' () s''
        ·
          change _ = ((multiDeliverH ae G maxSkip P mSlot (DG G) ops (a, i, e)).run s >>= _)
          simp only [hybHandlePreC, ratchetCodec, Comp.eval,
            Expr.v0, Expr.v1, Expr.v5, Expr.eval, Env.get, bind_assoc, pure_bind]
          change ((deliverBody ae G kPRG kAEAD maxSkip q P.j mSlot P.la specialDec).eval _ >>=
            fun x => R.run1 false (mx (Option.map rrDecM x.1)) f₁ x.2 >>= fun mid =>
            R.eval2 mid () fuel₂ false) = _
          rw [bind_map_fst _ (Option.map rrDecM)
              (fun v s' => R.run1 false (mx v) f₁ s' >>= fun mid => R.eval2 mid () fuel₂ false),
            deliverBody_eval ae G kPRG kAEAD hliftP _ maxSkip q mSlot P ht
              specialDec ops hDec a i e s hkr htr hch, bind_map_left]
          refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
          exact ih z.1 (by simpa using hb.2 z.1) (hpres z hz) (by omega) (by omega) (by omega)
        ·
          change _ = ((multiInjectH ae G maxSkip P mSlot (DG G) ops (a, i, e)).run s >>= _)
          simp only [hybHandlePreC, ratchetCodec, Comp.eval,
            Expr.v0, Expr.v1, Expr.v5, Expr.eval, Env.get, bind_assoc, pure_bind]
          change ((injectBody ae G kPRG kAEAD maxSkip q P.j mSlot P.la specialDec).eval _ >>=
            fun x => R.run1 false (mx (Option.map rrDecM x.1)) f₁ x.2 >>= fun mid =>
            R.eval2 mid () fuel₂ false) = _
          rw [bind_map_fst _ (Option.map rrDecM)
              (fun v s' => R.run1 false (mx v) f₁ s' >>= fun mid => R.eval2 mid () fuel₂ false),
            injectBody_eval ae G kPRG kAEAD hliftP _ maxSkip q mSlot P ht
              specialDec ops hDec a i e s hkr htr hch, bind_map_left]
          refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
          exact ih z.1 (by simpa using hb.2 z.1) (hpres z hz) (by omega) (by omega) (by omega)

end TwoStageSim

/-! ## Top-level evaluation agreement -/

section TopLevel

theorem bind_congr' {m : Type → Type} [Bind m] {α β : Type} (x : m α) {f g : α → m β}
    (h : ∀ a, f a = g a) : (x >>= f) = (x >>= g) :=
  congrArg (x >>= ·) (funext h)

theorem multiDecIdx_zero_none {CK MK AD M C : Type} {m : Type → Type} [Monad m]
    (ae : AEADScheme MK (ℕ × AD) M C) (P : Params) (ht : P.t = some 0) :
    multiDecIdx ae (P.t.getD 0) 0 (none : Option (SpecialOps AD M C m)) =
      decIdx (CK := CK) ae P none := by
  funext hint i a e
  apply StateT.ext
  intro ⟨h, sl⟩
  simp [multiDecIdx, decIdx, multiKind, kind, getH, onH, ht]; rfl

theorem multiEncIdxWith_zero_none {CK MK AD M C : Type} {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m]
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (P : Params) (ht : P.t = some 0) :
    multiEncIdxWith ideal ae (P.t.getD 0) 0 (none : Option (SpecialOps AD M C m)) =
      encIdxWith (CK := CK) ideal ae P none := by
  funext i a msg
  apply StateT.ext
  intro ⟨h, sl⟩
  simp [multiEncIdxWith, encIdxWith, multiKind, kind, getH, onH, ht]

theorem multiReceiveH_zero_none {CK MK AD M C : Type} {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m] [SampleableType MK] [SampleableType CK]
    (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip : ℕ) (P : Params) (D : ℕ → ProbComp (CK × MK)) (ht : P.t = some 0) :
    multiReceiveH ae G maxSkip P 0 D (none : Option (SpecialOps AD M C m)) =
      receiveH ae G maxSkip P D none := by
  funext hint a ⟨i, e⟩
  unfold multiReceiveH receiveH
  rw [multiDecIdx_zero_none ae P ht]
  refine bind_congr' _ fun st => ?_
  split
  · refine bind_congr' _ fun r => ?_
    cases r <;> rfl
  · split
    · rfl
    · split
      · rfl
      · refine bind_congr' _ fun _ => bind_congr' _ fun r => ?_
        cases r <;> rfl

theorem multiTransmitHWith_zero_none {CK MK AD M C : Type} {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m] [SampleableType MK] [SampleableType CK]
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ht : P.t = some 0) :
    multiTransmitHWith ideal ae G P 0 D (none : Option (SpecialOps AD M C m)) =
      transmitHWith ideal ae G P D none := by
  funext q
  unfold multiTransmitHWith transmitHWith
  rw [multiEncIdxWith_zero_none ideal ae P ht]

theorem multiChallengeHWith_zero_none {CK MK AD M C : Type} {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m] [SampleableType MK] [SampleableType CK]
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ht : P.t = some 0) :
    multiChallengeHWith ideal ae G P 0 D (none : Option (SpecialOps AD M C m)) =
      challengeHWith ideal ae G P D none := by
  funext q
  unfold multiChallengeHWith challengeHWith
  rw [multiEncIdxWith_zero_none ideal ae P ht]

theorem multiDeliverH_zero_none {CK MK AD M C : Type} {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m] [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip : ℕ) (P : Params) (D : ℕ → ProbComp (CK × MK)) (ht : P.t = some 0) :
    multiDeliverH ae G maxSkip P 0 D (none : Option (SpecialOps AD M C m)) =
      deliverH ae G maxSkip P D none := by
  funext q
  unfold multiDeliverH deliverH
  rw [multiReceiveH_zero_none ae G maxSkip P D ht]
  refine bind_congr' _ fun st => ?_
  split
  · rfl
  · cases st.inTransit.find? (fun r => r.ad == q.1 && r.ct == q.2) with
    | none => rfl
    | some r =>
      dsimp only
      refine bind_congr' _ fun res => ?_
      cases res <;> rfl

theorem multiInjectH_zero_none {CK MK AD M C : Type} {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m] [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip : ℕ) (P : Params) (D : ℕ → ProbComp (CK × MK)) (ht : P.t = some 0) :
    multiInjectH ae G maxSkip P 0 D (none : Option (SpecialOps AD M C m)) =
      injectH ae G maxSkip P D none := by
  funext q
  unfold multiInjectH injectH
  rw [multiReceiveH_zero_none ae G maxSkip P D ht]
  refine bind_congr' _ fun st => ?_
  split
  · rfl
  · refine bind_congr' _ fun res => ?_
    cases res <;> rfl

theorem multiImplWith_zero_none {CK MK AD M C : Type} {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m] [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) (P : Params)
    (D : ℕ → ProbComp (CK × MK)) (ht : P.t = some 0) :
    multiImplWith ideal ae G maxSkip P 0 D (none : Option (SpecialOps AD M C m)) =
      implWith ideal ae G maxSkip P D none := by
  unfold multiImplWith implWith multiOraclesWith oraclesWith
  rw [multiTransmitHWith_zero_none ideal ae G P D ht,
    multiChallengeHWith_zero_none ideal ae G P D ht,
    multiDeliverH_zero_none ae G maxSkip P D ht,
    multiInjectH_zero_none ae G maxSkip P D ht]

theorem prgIface_liftP {S : Sig} {α : Type} (p : ProbComp α) :
    (prgIface S).liftP p = (liftM p : ProbComp α) := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t mx ih =>
    simp only [Iface.liftP, simulateQ_query_bind, prgIface] at ih ⊢
    exact bind_congr ih

theorem otccaIface_liftP {S : Sig} (adT msgT ctT : Ty S)
    (ideal : adT.denote → ProbComp ctT.denote) (kIdeal : ℕ)
    {α : Type} (p : ProbComp α) :
    (otccaIface adT msgT ctT ideal kIdeal).liftP p =
      (liftM p :
        OracleComp (unifSpec + AEADScheme.otccaSpec adT.denote msgT.denote ctT.denote) α) := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t mx ih =>
    simp only [Iface.liftP, simulateQ_query_bind, otccaIface, monadLift_bind] at ih ⊢
    exact bind_congr ih

theorem isQueryBoundP_isRight_of_isGameQuery {κ : Type} {G : OracleSpec κ} {α : Type}
    {oa : OracleComp (unifSpec + G) α} {q : ℕ}
    (h : oa.IsQueryBoundP (isGameQuery (G := G)) q) :
    oa.IsQueryBoundP (fun t => t.isRight = true) q := by
  have heq : (fun t : ℕ ⊕ κ => t.isRight = true) = isGameQuery (G := G) := by
    funext t; cases t <;> simp [isGameQuery]
  simpa [heq] using h

theorem isQueryBoundP_isRight_of_makesAtMost {SS RS AD Msg C : Type}
    {A : CryptoGames.FSAEAD.Adversary SS RS AD Msg C} {q : ℕ}
    (hA : CryptoGames.FSAEAD.MakesAtMostQueries A q) :
    A.IsQueryBoundP (fun t => t.isRight = true) q :=
  Computational.Proofs.GameHop.StateSim.isQueryBoundP_congr_pred (fun t => by cases t <;> rfl) hA

theorem isQueryBoundP_isGameQuery_of_makesAtMost {SS RS AD Msg C : Type}
    {A : CryptoGames.FSAEAD.Adversary SS RS AD Msg C} {q : ℕ}
    (hA : CryptoGames.FSAEAD.MakesAtMostQueries A q) :
    A.IsQueryBoundP (isGameQuery (G := CryptoGames.FSAEAD.spec SS RS AD Msg C)) q :=
  Computational.Proofs.GameHop.StateSim.isQueryBoundP_congr_pred
    (fun t => by cases t <;> simp [isGameQuery]) hA

theorem eval1_bind_eval2_ret_unit
    {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aOut out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn .unit aOut .unit .unit out)
    (hch : R.chDone = .ret .unit)
    (A : Unit → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote)
    (fuel₁ fuel₂ : ℕ) (dflt : aOut.denote) :
    (do
      let (_, m) ← R.eval1 A x fuel₁ dflt
      R.eval2 m () fuel₂ dflt) =
    (do
      let (a, s) ← R.init.eval (.cons x .nil)
      let m ← R.run1 dflt (A a) fuel₁ s
      R.eval2 m () fuel₂ dflt) := by
  simp only [TwoStageCostedReduction.eval1, hch, Comp.eval, bind_assoc]
  refine bind_congr fun as => bind_congr fun m => ?_
  cases m <;> simp


end TopLevel

end Soundness

end CryptoGames.FSAEAD.Thm5.Costed
