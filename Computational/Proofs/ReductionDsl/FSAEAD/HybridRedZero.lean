/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FSAEAD.HybridRedBase -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SimRel
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.ReductionDsl.Tables
import Computational.Proofs.GameHop.StateSim

public section

set_option autoImplicit false

namespace CryptoGames.FSAEAD.Thm5.Costed

open ReductionDsl CryptoGames.FSAEAD.Costed CryptoGames.PRG.Costed CryptoGames.OTCCA.Costed
open OracleComp OracleSpec

variable {CK MK AD M C : Type}

local notation "HSig" => fsSig CK MK AD Unit M C
local notation "HT" => Ty HSig

local notation "HSamp" =>
  unifSamplers (S := HSig) fsStateSampleSort (fun _ => 1)

local notation "hybOps" ae:arg G:arg kPRG:arg kAEAD:arg =>
  Ops.sum
    (prgOps (S := HSig) (Ty.prod Ty.nat (bt FSort.ss)) (Ty.prod (bt FSort.ss) (bt FSort.rs))
      (fun pw => PRGScheme.gen (G (Prod.fst pw)) (Prod.snd pw)) kPRG)
    (otccaOps (S := HSig) (bt FSort.rs) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.ad)
      (bt FSort.msg) (bt FSort.ct) ae kAEAD Ty.unit (fun _ => ()))

local notation "prgRedZeroIface" ideal:arg kIdeal:arg =>
  Iface.withSamp
    (Iface.withSamp (prgIface HSig)
      (idealSamplers (S := HSig) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.ct) ideal kIdeal))
    HSamp

local notation "multiRedIface" ideal:arg kIdeal:arg =>
  Iface.withSamp
    (otccaIface (S := HSig) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.msg) (bt FSort.ct)
      ideal kIdeal)
    HSamp

local notation "recTy'" => recTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "kcTy'" => kcTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "slotTy'" => slotTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "hsTy'" => hsTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "stTy'" => stTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)


section TopLevel

variable [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  [SampleableType MK] [SampleableType CK]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (kPRG kAEAD : ℕ)
  (ideal : ℕ × AD → ProbComp C) (kIdeal : ℕ)

open CryptoVerification.LibsignalSession (evalTwoStage1)
open Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out
  (advBit cumulativeChainPrgReductionOut multiSlotOtccaReductionOut)


/-- On any `q`-query ratchet adversary, `prgRedZeroProg` evaluates to `cumulativeChainPrgReduction`. -/
theorem prgRedZeroProg_eval (q maxSkip j : ℕ)
    (A : RatchetAdversary CK MK AD M C)
    (hA : A.IsQueryBoundP
      (isGameQuery (G := spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)))
      q)
    (mt : CK × MK) :
    evalTwoStage1 (prgRedZeroProg ae G kPRG kAEAD ideal kIdeal q maxSkip j)
        q false (fun _ => A) mt =
      cumulativeChainPrgReduction ideal ae G maxSkip j A mt := by
  dsimp only [evalTwoStage1]
  have hliftP : ∀ {α : Type} (p : ProbComp α),
      (Iface.withSamp (prgIface HSig)
        (idealSamplers (S := HSig) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.ct)
          ideal kIdeal)).liftP p = (liftM p : ProbComp α) := fun p => by
    rw [liftP_withSamp, prgIface_liftP]
  have hIdeal : SampleIdealRel (T := unifSpec) (I := prgRedZeroIface ideal kIdeal)
      ae G kPRG kAEAD
      (fun ia =>
        Comp.sample (O := hybOps ae G kPRG kAEAD)
          (I := prgRedZeroIface ideal kIdeal)
          (Sum.inl (Sum.inr ()) : (Empty ⊕ Unit) ⊕ UniformSamplerTag Bool) ia)
      ideal := by
    intro Δ ρ' ia
    dsimp only [Comp.eval, liftP_withSamp, samp_withSamp_inl, samp_withSamp_inr, idealSamplers]
    exact prgIface_liftP (S := HSig) _
  let R : TwoStageCostedReduction (hybOps ae G kPRG kAEAD)
      (prgRedZeroIface ideal kIdeal)
      (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      ratchetCodec (.prod (bt .ss) (bt .rs)) .unit .bool .unit .unit .bool :=
    { σ := stTy
      π := .unit
      init := (prgRedZeroProg ae G kPRG kAEAD ideal kIdeal q maxSkip j).init
      handlePre := hybHandlePreC ae G kPRG kAEAD maxSkip q
        (hp (j / 2) 0 (isLookaheadHop j)).j 0 (hp (j / 2) 0 (isLookaheadHop j)).la
        (fun ia =>
          Comp.sample (O := hybOps ae G kPRG kAEAD)
            (I := prgRedZeroIface ideal kIdeal)
            (Sum.inl (Sum.inr ()) : (Empty ⊕ Unit) ⊕ UniformSamplerTag Bool) ia)
        none none
      chDone := hybChDoneC ae G kPRG kAEAD
      resume := hybResumeC ae G kPRG kAEAD maxSkip q (hp (j / 2) 0 (isLookaheadHop j)).la
      handlePost := hybHandlePostC ae G kPRG kAEAD
      finish := hybFinishC ae G kPRG kAEAD (hp (j / 2) 0 (isLookaheadHop j)).la }
  have hsim := fun (b : Bool) =>
    run1_eval2_eq_simulateQ ae G kPRG kAEAD hliftP
      (prgRedZeroProg ae G kPRG kAEAD ideal kIdeal q maxSkip j).init
      maxSkip q 0 q (hp (j / 2) 0 (isLookaheadHop j)) rfl
      ideal _ hIdeal none none none trivial trivial A
      (m := q) (n := 0) (fuel₁ := q) (s := hInit b (.mat (j / 2) mt))
      (isQueryBoundP_isRight_of_isGameQuery hA) (HInv.init b) (by omega) (by omega) (by omega)
  have hinitC :
      R.init.eval (.cons (t := .prod (bt .ss) (bt .rs)) mt .nil) =
      (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        pure ((), encSt (hInit b (.mat (j / 2) mt)))) := by
    simp only [R, prgRedZeroProg, Comp.eval, Expr.v0, Expr.v1, Expr.eval, Env.get,
      liftP_withSamp, prgIface_liftP]
    dsimp only [Iface.withSamp, Samplers.sum, unifSamplers, Sum.elim]
    refine bind_congr fun b => ?_
    have hsk : (fun _ : ℕ => false) = encSkipped [] := by funext x; rfl
    simp [Env.get, encSt, encSlot, encHS, encKc, hInit, hsk]
  rw [eval1_bind_eval2_ret_unit (prgRedZeroProg ae G kPRG kAEAD ideal kIdeal q maxSkip j) rfl]
  change (do
    let (a, s) ← R.init.eval (.cons (t := .prod (bt .ss) (bt .rs)) mt .nil)
    let m ← R.run1 false A q s
    R.eval2 m () q false) = _
  rw [hinitC]
  simp only [cumulativeChainPrgReduction, hRunWith, bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  rw [← multiImplWith_zero_none ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j)) (DG G) rfl]
  exact hsim b

/-- On any `q`-query ratchet adversary, `multiRedProg` evaluates to `multiSlotOtccaReduction`. -/
theorem multiRedProg_eval (q maxSkip N : ℕ) (la : Bool)
    (A : RatchetAdversary CK MK AD M C)
    (hA : A.IsQueryBoundP
      (isGameQuery (G := spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)))
      q) :
    evalTwoStage1 (multiRedProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la)
        q false (fun _ => A) () =
      multiSlotOtccaReduction ideal ae G maxSkip N la A := by
  dsimp only [evalTwoStage1]
  have hliftP : ∀ {α : Type} (p : ProbComp α),
      (otccaIface (S := HSig) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.msg)
        (bt FSort.ct) ideal kIdeal).liftP p =
        (liftM p : OracleComp (unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C) α) :=
    fun p => otccaIface_liftP _ _ _ ideal kIdeal p
  have hIdeal : SampleIdealRel
      (T := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C)
      (I := multiRedIface ideal kIdeal)
      ae G kPRG kAEAD
      (fun ia =>
        Comp.sample (O := hybOps ae G kPRG kAEAD)
          (I := multiRedIface ideal kIdeal)
          (Sum.inl () : Unit ⊕ UniformSamplerTag Bool) ia)
      ideal := by
    intro Δ ρ' ia
    dsimp only [Comp.eval, liftP_withSamp, samp_withSamp_inl, otccaIface, idealSamplers]
    exact otccaIface_liftP _ _ _ ideal kIdeal _
  have hEnc : SpecialEncRel
      (T := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C)
      (I := multiRedIface ideal kIdeal)
      ae G kPRG kAEAD
      (some (otSpecialEncC ae G kPRG kAEAD ideal kIdeal))
      (some (otOpsWith ideal)) := by
    intro Δ ρ' iam
    dsimp only [otSpecialEncC, otOpsWith, callC, Comp.eval, Expr.v0, Expr.v1, Expr.eval, Env.get]
    change ((id <$> (query (spec := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C)
        (Sum.inr (Sum.inl (iam.eval ρ'))) :
          OracleComp (unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C) (Option C))) >>= _) = _
    rw [id_map]
    refine bind_congr fun r => ?_
    cases r with
    | none => exact otccaIface_liftP _ _ _ ideal kIdeal _
    | some c => rfl
  have hDec : SpecialDecRel
      (T := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C)
      (I := multiRedIface ideal kIdeal)
      ae G kPRG kAEAD
      (some (otSpecialDecC ae G kPRG kAEAD ideal kIdeal))
      (some (otOpsWith ideal)) := by
    intro Δ ρ' iae
    change id <$> (query (spec := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C)
        (Sum.inr (Sum.inr (iae.eval ρ'))) :
          OracleComp (unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C) (Option M)) =
      (query (spec := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C)
        (Sum.inr (Sum.inr (iae.eval ρ'))) :
          OracleComp (unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C) (Option M))
    exact id_map _
  let R : TwoStageCostedReduction (hybOps ae G kPRG kAEAD)
      (multiRedIface ideal kIdeal)
      (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      ratchetCodec .unit .unit .bool .unit .unit .bool :=
    { σ := stTy
      π := .unit
      init := (multiRedProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la).init
      handlePre := hybHandlePreC ae G kPRG kAEAD maxSkip q
        (hp N 0 la).j N (hp N 0 la).la
        (fun ia =>
          Comp.sample (O := hybOps ae G kPRG kAEAD)
            (I := multiRedIface ideal kIdeal)
            (Sum.inl () : Unit ⊕ UniformSamplerTag Bool) ia)
        (some (otSpecialEncC ae G kPRG kAEAD ideal kIdeal))
        (some (otSpecialDecC ae G kPRG kAEAD ideal kIdeal))
      chDone := hybChDoneC ae G kPRG kAEAD
      resume := hybResumeC ae G kPRG kAEAD maxSkip q (hp N 0 la).la
      handlePost := hybHandlePostC ae G kPRG kAEAD
      finish := hybFinishC ae G kPRG kAEAD (hp N 0 la).la }
  have hsim := fun (b : Bool) =>
    run1_eval2_eq_simulateQ ae G kPRG kAEAD hliftP
      (multiRedProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la).init
      maxSkip q N q (hp N 0 la) rfl
      ideal _ hIdeal
      (some (otSpecialEncC ae G kPRG kAEAD ideal kIdeal))
      (some (otSpecialDecC ae G kPRG kAEAD ideal kIdeal))
      (some (otOpsWith ideal)) hEnc hDec A
      (m := q) (n := 0) (fuel₁ := q) (s := hInit b .unknown)
      (isQueryBoundP_isRight_of_isGameQuery hA) (HInv.init b) (by omega) (by omega) (by omega)
  have hinitC :
      R.init.eval (.cons (t := .unit) () .nil) =
      (do
        let b ← (liftM ($ᵗ Bool) :
          OracleComp (unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C) Bool)
        pure ((), encSt (hInit b .unknown))) := by
    simp only [R, multiRedProg, Comp.eval, Expr.v0, Expr.eval,
      liftP_withSamp]
    dsimp only [Iface.withSamp, Samplers.sum, unifSamplers, Sum.elim]
    rw [otccaIface_liftP]
    refine bind_congr fun b => ?_
    have hsk : (fun _ : ℕ => false) = encSkipped [] := by funext x; rfl
    simp [Env.get, encSt, encSlot, encHS, encKc, hInit, hsk]
  rw [eval1_bind_eval2_ret_unit (multiRedProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la) rfl]
  change (do
    let (a, s) ← R.init.eval (.cons (t := .unit) () .nil)
    let m ← R.run1 false A q s
    R.eval2 m () q false) = _
  rw [hinitC]
  simp only [multiSlotOtccaReduction, multiRunWith, bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  exact hsim b

theorem multiRedProg_queries (q maxSkip N : ℕ) (la : Bool)
    (A : RatchetAdversary CK MK AD M C)
    (_hA : A.IsQueryBoundP
      (isGameQuery (G := spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)))
      q) :
    (evalTwoStage1 (multiRedProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la)
      q false (fun _ => A) ()).IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec (ℕ × AD) M C)) q := by
  simpa [evalTwoStage1] using isQueryBoundP_bind
    (multiRedProg_eval1_queries ae G kPRG kAEAD ideal kIdeal q maxSkip N la A)
    (fun pm _ => multiRedProg_eval2_queries ae G kPRG kAEAD ideal kIdeal q maxSkip N la pm.2)


end TopLevel

end CryptoGames.FSAEAD.Thm5.Costed
