/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeyGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhStep
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq

/-!
# Forgetful Simulation Seam for Shadow-Indexed `KeyInd` Gap-DH

Defines RO-entry well-formedness predicates, zero-query RO-vs-RO `entryMatchesC` exactness,
sentinel forget maps, state invariants (`GdhSimInv`, `Sig1KeyActiveSimInv`,
`Gdh1KeyActiveSimInv`), and the `KeyIndStepSim` combiner for the `KeyInd` Gap-DH and one-key
active shadow-indexed reductions. Credit: the persistent AVL RO table and session shadow-index
split was suggested by Charles Sutton.
-/

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase

set_option autoImplicit false

public section

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Var Expr Comp Env Iface pqAtomicSig pqAtomicOps pqKeyIndCodec drKeyT findML)
open _root_.SignalPqxdh (Bytes Setup QueryBudget KeyIndQuery F_X25519)
open _root_.SignalPqxdh.Security.FgGapDh (GdhSimSpec)
open _root_.SignalPqxdh.Security.FgGapDh1Key (liftGdhToSign)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqGapDhIface pqSigAndDdhIface B)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  PT Ext v letV bindV caseOptV caseSumV
  keyIndStateTy fgPosTy fgPatchEntryTy paramsTy simTy emptyStE smMk emptySimE
  fePos1 fePos2 fePos3 fePos4 feSs
  ddhQ ddhEqC ddhEqOptC entryMatchesC eqB orE
  eqB_eval orE_eval letV_eval
  Ext.refl_wk' Ext.step_wk' Env.get_zero' Env.get_succ'
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (
  liftGdhComp liftGdhComp_eval liftGdhToSign_pure liftGdhToSign_bind mem_support_liftGdhToSign
)
open Computational.Proofs.ReductionDsl.StepSim (bumpPred)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  TagLift AtomicIface embedTy embedBase embedVal projVal projVal_embedVal embedEnv
  mapComp mapComp_eval tlGapDhKeyInd tlSigDdhKeyInd
)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  sig1KeyActiveStTy gdh1KeyActiveStateTy
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  dfltDrKeyE
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine (
  TaggedEntry roEntriesOf ShadowRelB192 RoCacheRelB192
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase (
  keyIndSimPred keyIndSimBounds keyIndSimPred_one_iff_kind fixSent BaseOnlineLenInv
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (
  KeyIndKFuels keyIndKFuelsOfBudget
  fgShadowAtomicTy dfltFgRoValE emptyFgShadowE simShadowAtomicTy gdhShadowState2AtomicTy
  GdhAtomicLift gdhLift2Key gdhLift1Key liftGdhAtomic
)

/-- Atomic value type of a Gap-DH consistency table entry (`fgPatchEntryTy`). -/
abbrev FgEntryA : Type := (embedTy fgPatchEntryTy).denote

/-- Atomic value type of a 96-byte derived root/chain key (`drKeyT`). -/
abbrev DrKeyA : Type := (drKeyT (ℓ := 0) (Pt := Empty)).denote

@[expose] def fgEntryDk (e : FgEntryA) : DrKeyA :=
  e.2.2.2.2.2

@[expose] def fgEntryPos1 (e : FgEntryA) : (embedTy fgPosTy).denote :=
  e.1

@[expose] def fgEntryPos2 (e : FgEntryA) : (embedTy fgPosTy).denote :=
  e.2.1

@[expose] def fgEntryPos3 (e : FgEntryA) : (embedTy fgPosTy).denote :=
  e.2.2.1

@[expose] def fgEntryPos4 (e : FgEntryA) : Option (embedTy fgPosTy).denote :=
  e.2.2.2.1

@[expose] def fgEntrySs (e : FgEntryA) : Bytes :=
  e.2.2.2.2.1

/-- Well-formedness of an `.ro sec`-tagged `FgEntryA` entry whose `.inl` secret positions match the
    32-byte slices of a `160`- or `192`-byte `F_X25519`-prefixed input `sec`. -/
@[expose] def RoFgEntryWf (sec : Bytes) (e : FgEntryA) : Prop :=
  sec.take 32 = F_X25519 ∧
  ((sec.length = 160 ∧
      (∃ c1 c2 c3 : Bool,
        e.1 = .inl ((sec.drop 32).take 32, c1) ∧
        e.2.1 = .inl ((sec.drop 64).take 32, c2) ∧
        e.2.2.1 = .inl ((sec.drop 96).take 32, c3)) ∧
      e.2.2.2.1 = none ∧
      e.2.2.2.2.1 = (sec.drop 128).take 32) ∨
   (sec.length = 192 ∧
      (∃ c1 c2 c3 c4 : Bool,
        e.1 = .inl ((sec.drop 32).take 32, c1) ∧
        e.2.1 = .inl ((sec.drop 64).take 32, c2) ∧
        e.2.2.1 = .inl ((sec.drop 96).take 32, c3) ∧
        e.2.2.2.1 = some (.inl ((sec.drop 128).take 32, c4))) ∧
      e.2.2.2.2.1 = (sec.drop 160).take 32))

/-- Well-formedness of the pre-AVL secret-position pack `(p1, p2, p3, p4?, ss)` parsed from a
    `160`- or `192`-byte `F_X25519`-prefixed RO input `sec`. -/
@[expose] def RoQueryPackWf (sec : Bytes)
    (p1 p2 p3 : fgPosTy.denote) (p4? : (Ty.opt fgPosTy).denote) (ss : Bytes) : Prop :=
  sec.take 32 = F_X25519 ∧
  ((sec.length = 160 ∧
      (∃ c1 c2 c3 : Bool,
        p1 = .inl ((sec.drop 32).take 32, c1) ∧
        p2 = .inl ((sec.drop 64).take 32, c2) ∧
        p3 = .inl ((sec.drop 96).take 32, c3)) ∧
      p4? = none ∧
      ss = (sec.drop 128).take 32) ∨
   (sec.length = 192 ∧
      (∃ c1 c2 c3 c4 : Bool,
        p1 = .inl ((sec.drop 32).take 32, c1) ∧
        p2 = .inl ((sec.drop 64).take 32, c2) ∧
        p3 = .inl ((sec.drop 96).take 32, c3) ∧
        p4? = some (.inl ((sec.drop 128).take 32, c4))) ∧
      ss = (sec.drop 160).take 32))

private theorem eq_of_take_eq_drop_eq {α : Type} {x y : List α} (n : ℕ)
    (ht : x.take n = y.take n) (hd : x.drop n = y.drop n) : x = y := by
  rw [← List.take_append_drop n x, ← List.take_append_drop n y, ht, hd]

private theorem eq_of_slices_160 {a b : Bytes}
    (ha : a.length = 160) (hb : b.length = 160)
    (h0 : a.take 32 = b.take 32)
    (h1 : (a.drop 32).take 32 = (b.drop 32).take 32)
    (h2 : (a.drop 64).take 32 = (b.drop 64).take 32)
    (h3 : (a.drop 96).take 32 = (b.drop 96).take 32)
    (h4 : (a.drop 128).take 32 = (b.drop 128).take 32) : a = b := by
  refine eq_of_take_eq_drop_eq 32 h0 ?_
  refine eq_of_take_eq_drop_eq 32 h1 ?_
  simp only [List.drop_drop, Nat.reduceAdd]
  refine eq_of_take_eq_drop_eq 32 h2 ?_
  simp only [List.drop_drop, Nat.reduceAdd]
  refine eq_of_take_eq_drop_eq 32 h3 ?_
  simp only [List.drop_drop, Nat.reduceAdd]
  have ha128 : (a.drop 128).length ≤ 32 := by simp [List.length_drop, ha]
  have hb128 : (b.drop 128).length ≤ 32 := by simp [List.length_drop, hb]
  rwa [List.take_of_length_le ha128, List.take_of_length_le hb128] at h4

private theorem eq_of_slices_192 {a b : Bytes}
    (ha : a.length = 192) (hb : b.length = 192)
    (h0 : a.take 32 = b.take 32)
    (h1 : (a.drop 32).take 32 = (b.drop 32).take 32)
    (h2 : (a.drop 64).take 32 = (b.drop 64).take 32)
    (h3 : (a.drop 96).take 32 = (b.drop 96).take 32)
    (h4 : (a.drop 128).take 32 = (b.drop 128).take 32)
    (h5 : (a.drop 160).take 32 = (b.drop 160).take 32) : a = b := by
  refine eq_of_take_eq_drop_eq 32 h0 ?_
  refine eq_of_take_eq_drop_eq 32 h1 ?_
  simp only [List.drop_drop, Nat.reduceAdd]
  refine eq_of_take_eq_drop_eq 32 h2 ?_
  simp only [List.drop_drop, Nat.reduceAdd]
  refine eq_of_take_eq_drop_eq 32 h3 ?_
  simp only [List.drop_drop, Nat.reduceAdd]
  refine eq_of_take_eq_drop_eq 32 h4 ?_
  simp only [List.drop_drop, Nat.reduceAdd]
  have ha160 : (a.drop 160).length ≤ 32 := by simp [List.length_drop, ha]
  have hb160 : (b.drop 160).length ≤ 32 := by simp [List.length_drop, hb]
  rwa [List.take_of_length_le ha160, List.take_of_length_le hb160] at h5

/-- On two `.inl` secret positions, `ddhEqC` issues zero oracle queries and evaluates purely to
    `z1 == z2`. -/
theorem ddhEqC_inl_eval {Γ : List PT}
    (p1 p2 : Expr pqxdhOps Γ fgPosTy) (env : Env Γ)
    (z1 z2 : Bytes) (c1 c2 : Bool)
    (h1 : p1.eval env = .inl (z1, c1))
    (h2 : p2.eval env = .inl (z2, c2)) :
    (ddhEqC p1 p2).eval env = pure (z1 == z2) := by
  unfold ddhEqC
  simp [letV_eval, caseSumV, Comp.eval, Expr.eval, eqB_eval, v, h1, h2]

private theorem embedVal_fgPos_inl_iff (p : fgPosTy.denote) (z : Bytes) (c : Bool) :
    embedVal fgPosTy p = .inl (z, c) ↔ p = .inl (z, c) := by
  rcases p with ⟨z', c'⟩ | ⟨a, b, w1, w2⟩ <;> simp [embedVal, embedBase]

private theorem embedVal_opt_fgPos_none_iff (p? : (Ty.opt fgPosTy).denote) :
    embedVal (.opt fgPosTy) p? = none ↔ p? = none := by
  cases p? <;> simp [embedVal]

private theorem embedVal_opt_fgPos_some_inl_iff (p? : (Ty.opt fgPosTy).denote) (z : Bytes) (c : Bool) :
    embedVal (.opt fgPosTy) p? = some (.inl (z, c)) ↔ p? = some (.inl (z, c)) := by
  rcases p? with _ | (⟨z', c'⟩ | ⟨a, b, w1, w2⟩) <;> simp [embedVal, embedBase]

/-- Under `RoQueryPackWf sec` and `RoFgEntryWf sec'`, `entryMatchesC` evaluates to `pure (sec' == sec)`
    with zero oracle queries. -/
theorem entryMatchesC_ro_eval_eq_beq {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ssVar : Var Γ₅ (B 32))
    (eVar : Var Δ fgPatchEntryTy) (env : Env Δ)
    (sec sec' : Bytes)
    (hQ : RoQueryPackWf sec
      (env.get (Ext.wk pos1)) (env.get (Ext.wk pos2)) (env.get (Ext.wk pos3))
      (env.get (Ext.wk pos4?)) (env.get (Ext.wk ssVar)))
    (hE : RoFgEntryWf sec' (embedVal fgPatchEntryTy (env.get eVar))) :
    (entryMatchesC pos1 pos2 pos3 pos4? ssVar eVar).eval env = pure (sec' == sec) := by
  rcases he : env.get eVar with ⟨ep1, ep2, ep3, ep4?, ess, edk⟩
  have hE' : RoFgEntryWf sec' (embedVal fgPatchEntryTy (ep1, ep2, ep3, ep4?, ess, edk)) := by
    simpa [he] using hE
  dsimp only [RoFgEntryWf, embedVal, embedBase] at hE'
  rcases hQ with ⟨hPreQ, hLenQ⟩
  rcases hE' with ⟨hPreE, hLenE⟩
  unfold entryMatchesC
  have hCond : (Expr.not (eqB (v ssVar) (feSs (v eVar)))).eval env =
      !(env.get (Ext.wk ssVar) == ess) := by
    simp [Expr.eval, eqB_eval, v, feSs, Ext.refl_wk', he]
  rw [Comp.eval, hCond]
  rcases hLenQ with ⟨h160Q, ⟨qc1, qc2, qc3, hp1, hp2, hp3⟩, hp4, hss⟩ |
                    ⟨h192Q, ⟨qc1, qc2, qc3, qc4, hp1, hp2, hp3, hp4⟩, hss⟩ <;>
  rcases hLenE with ⟨h160E, ⟨ec1, ec2, ec3, hep1, hep2, hep3⟩, hep4, hess⟩ |
                    ⟨h192E, ⟨ec1, ec2, ec3, ec4, hep1, hep2, hep3, hep4⟩, hess⟩
  ·
    rw [embedVal_fgPos_inl_iff] at hep1 hep2 hep3
    rw [embedVal_opt_fgPos_none_iff] at hep4
    rw [hss, hess]
    by_cases hssEq : (sec.drop 128).take 32 = (sec'.drop 128).take 32
    · have hFalse : (!((sec.drop 128).take 32 == (sec'.drop 128).take 32)) = false := by
        simp [hssEq]
      rw [hFalse]
      simp only [Bool.false_eq_true, ↓reduceIte, bindV, Comp.eval]
      rw [ddhEqC_inl_eval _ _ _ ((sec.drop 32).take 32) ((sec'.drop 32).take 32) qc1 ec1
        (by simp [v, Expr.eval, hp1])
        (by simp [fePos1, v, Expr.eval, Ext.refl_wk', he, hep1])]
      simp only [pure_bind]
      rw [ddhEqC_inl_eval _ _ _ ((sec.drop 64).take 32) ((sec'.drop 64).take 32) qc2 ec2
        (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ', hp2])
        (by simp [fePos2, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', he, hep2])]
      simp only [pure_bind]
      rw [ddhEqC_inl_eval _ _ _ ((sec.drop 96).take 32) ((sec'.drop 96).take 32) qc3 ec3
        (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ', hp3])
        (by simp [fePos3, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', he, hep3])]
      simp only [pure_bind]
      have hOpt : ∀ b1 b2 b3 : Bool,
          (ddhEqOptC (v pos4?) (fePos4 (v eVar))).eval
            (Env.cons (t := .bool) b3 (Env.cons (t := .bool) b2 (Env.cons (t := .bool) b1 env))) = pure true := by
        intro b1 b2 b3
        unfold ddhEqOptC
        simp [letV_eval, caseOptV, Comp.eval, Expr.eval, fePos4, v,
          Ext.step_wk', Ext.refl_wk', Env.get_succ', hp4, he, hep4]
      rw [hOpt]
      simp only [pure_bind, Expr.eval, v, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ', Bool.and_true]
      congr 1
      by_cases hAll :
          ((sec.drop 32).take 32 == (sec'.drop 32).take 32) &&
          ((sec.drop 64).take 32 == (sec'.drop 64).take 32) &&
          ((sec.drop 96).take 32 == (sec'.drop 96).take 32)
      · simp only [Bool.and_eq_true, beq_iff_eq] at hAll
        have hSecEq : sec' = sec := eq_of_slices_160 h160E h160Q
          (hPreE.trans hPreQ.symm) hAll.1.1.symm hAll.1.2.symm hAll.2.symm hssEq.symm
        simp [hSecEq, hAll.1.1, hAll.1.2, hAll.2]
      · have hNe : sec' ≠ sec := by
          intro hEq
          subst hEq
          simp at hAll
        rcases hF :
          (((sec.drop 32).take 32 == (sec'.drop 32).take 32) &&
           ((sec.drop 64).take 32 == (sec'.drop 64).take 32) &&
           ((sec.drop 96).take 32 == (sec'.drop 96).take 32))
        · symm; simpa [beq_eq_false_iff_ne] using hNe
        · exact False.elim (hAll hF)
    · have hBeqF : ((sec.drop 128).take 32 == (sec'.drop 128).take 32) = false :=
        beq_eq_false_iff_ne.mpr hssEq
      have hSecNe : (sec' == sec) = false :=
        beq_eq_false_iff_ne.mpr (fun hEq => hssEq (by rw [hEq]))
      rw [hBeqF, hSecNe]
      rfl
  ·
    rw [embedVal_fgPos_inl_iff] at hep1 hep2 hep3
    rw [embedVal_opt_fgPos_some_inl_iff] at hep4
    have hSecNe : (sec' == sec) = false :=
      beq_eq_false_iff_ne.mpr (fun hEq => by have := congrArg List.length hEq; omega)
    rw [hSecNe]
    split
    · rfl
    · simp only [bindV, Comp.eval]
      rw [ddhEqC_inl_eval _ _ _ ((sec.drop 32).take 32) ((sec'.drop 32).take 32) qc1 ec1
        (by simp [v, Expr.eval, hp1])
        (by simp [fePos1, v, Expr.eval, Ext.refl_wk', he, hep1])]
      simp only [pure_bind]
      rw [ddhEqC_inl_eval _ _ _ ((sec.drop 64).take 32) ((sec'.drop 64).take 32) qc2 ec2
        (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ', hp2])
        (by simp [fePos2, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', he, hep2])]
      simp only [pure_bind]
      rw [ddhEqC_inl_eval _ _ _ ((sec.drop 96).take 32) ((sec'.drop 96).take 32) qc3 ec3
        (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ', hp3])
        (by simp [fePos3, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', he, hep3])]
      simp only [pure_bind]
      have hOpt : ∀ b1 b2 b3 : Bool,
          (ddhEqOptC (v pos4?) (fePos4 (v eVar))).eval
            (Env.cons (t := .bool) b3 (Env.cons (t := .bool) b2 (Env.cons (t := .bool) b1 env))) = pure false := by
        intro b1 b2 b3
        unfold ddhEqOptC
        simp [letV_eval, caseOptV, Comp.eval, Expr.eval, fePos4, v,
          Ext.step_wk', Ext.refl_wk', Env.get_succ', hp4, he, hep4]
      rw [hOpt]
      simp [Expr.eval, v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']
  ·
    rw [embedVal_fgPos_inl_iff] at hep1 hep2 hep3
    rw [embedVal_opt_fgPos_none_iff] at hep4
    have hSecNe : (sec' == sec) = false :=
      beq_eq_false_iff_ne.mpr (fun hEq => by have := congrArg List.length hEq; omega)
    rw [hSecNe]
    split
    · rfl
    · simp only [bindV, Comp.eval]
      rw [ddhEqC_inl_eval _ _ _ ((sec.drop 32).take 32) ((sec'.drop 32).take 32) qc1 ec1
        (by simp [v, Expr.eval, hp1])
        (by simp [fePos1, v, Expr.eval, Ext.refl_wk', he, hep1])]
      simp only [pure_bind]
      rw [ddhEqC_inl_eval _ _ _ ((sec.drop 64).take 32) ((sec'.drop 64).take 32) qc2 ec2
        (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ', hp2])
        (by simp [fePos2, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', he, hep2])]
      simp only [pure_bind]
      rw [ddhEqC_inl_eval _ _ _ ((sec.drop 96).take 32) ((sec'.drop 96).take 32) qc3 ec3
        (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ', hp3])
        (by simp [fePos3, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', he, hep3])]
      simp only [pure_bind]
      have hOpt : ∀ b1 b2 b3 : Bool,
          (ddhEqOptC (v pos4?) (fePos4 (v eVar))).eval
            (Env.cons (t := .bool) b3 (Env.cons (t := .bool) b2 (Env.cons (t := .bool) b1 env))) = pure false := by
        intro b1 b2 b3
        unfold ddhEqOptC
        simp [letV_eval, caseOptV, Comp.eval, Expr.eval, fePos4, v,
          Ext.step_wk', Ext.refl_wk', Env.get_succ', hp4, he, hep4]
      rw [hOpt]
      simp [Expr.eval, v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']
  ·
    rw [embedVal_fgPos_inl_iff] at hep1 hep2 hep3
    rw [embedVal_opt_fgPos_some_inl_iff] at hep4
    rw [hss, hess]
    by_cases hssEq : (sec.drop 160).take 32 = (sec'.drop 160).take 32
    · have hFalse : (!((sec.drop 160).take 32 == (sec'.drop 160).take 32)) = false := by
        simp [hssEq]
      rw [hFalse]
      simp only [Bool.false_eq_true, ↓reduceIte, bindV, Comp.eval]
      rw [ddhEqC_inl_eval _ _ _ ((sec.drop 32).take 32) ((sec'.drop 32).take 32) qc1 ec1
        (by simp [v, Expr.eval, hp1])
        (by simp [fePos1, v, Expr.eval, Ext.refl_wk', he, hep1])]
      simp only [pure_bind]
      rw [ddhEqC_inl_eval _ _ _ ((sec.drop 64).take 32) ((sec'.drop 64).take 32) qc2 ec2
        (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ', hp2])
        (by simp [fePos2, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', he, hep2])]
      simp only [pure_bind]
      rw [ddhEqC_inl_eval _ _ _ ((sec.drop 96).take 32) ((sec'.drop 96).take 32) qc3 ec3
        (by simp [v, Expr.eval, Ext.step_wk', Env.get_succ', hp3])
        (by simp [fePos3, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', he, hep3])]
      simp only [pure_bind]
      have hOpt : ∀ b1 b2 b3 : Bool,
          (ddhEqOptC (v pos4?) (fePos4 (v eVar))).eval
            (Env.cons (t := .bool) b3 (Env.cons (t := .bool) b2 (Env.cons (t := .bool) b1 env))) =
          pure ((sec.drop 128).take 32 == (sec'.drop 128).take 32) := by
        intro b1 b2 b3
        unfold ddhEqOptC
        simp only [letV_eval, caseOptV, Comp.eval, Expr.eval, fePos4, v,
          Ext.step_wk', Ext.refl_wk', Env.get_succ', hp4, he, hep4]
        exact ddhEqC_inl_eval _ _ _ ((sec.drop 128).take 32) ((sec'.drop 128).take 32) qc4 ec4
          (by simp [Expr.eval, Env.get_zero', Env.get_succ'])
          (by simp [Expr.eval, Env.get_zero'])
      rw [hOpt]
      simp only [pure_bind, Expr.eval, v, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ']
      congr 1
      by_cases hAll :
          (((sec.drop 32).take 32 == (sec'.drop 32).take 32) &&
           ((sec.drop 64).take 32 == (sec'.drop 64).take 32) &&
           ((sec.drop 96).take 32 == (sec'.drop 96).take 32)) &&
          ((sec.drop 128).take 32 == (sec'.drop 128).take 32)
      · simp only [Bool.and_eq_true, beq_iff_eq] at hAll
        have hSecEq : sec' = sec := eq_of_slices_192 h192E h192Q
          (hPreE.trans hPreQ.symm)
          hAll.1.1.1.symm hAll.1.1.2.symm hAll.1.2.symm hAll.2.symm hssEq.symm
        simp [hSecEq, hAll.1.1.1, hAll.1.1.2, hAll.1.2, hAll.2]
      · have hNe : sec' ≠ sec := by
          intro hEq
          subst hEq
          simp at hAll
        rcases hF :
          ((((sec.drop 32).take 32 == (sec'.drop 32).take 32) &&
            ((sec.drop 64).take 32 == (sec'.drop 64).take 32) &&
            ((sec.drop 96).take 32 == (sec'.drop 96).take 32)) &&
           ((sec.drop 128).take 32 == (sec'.drop 128).take 32))
        · symm; simpa [beq_eq_false_iff_ne] using hNe
        · exact False.elim (hAll hF)
    · have hBeqF : ((sec.drop 160).take 32 == (sec'.drop 160).take 32) = false :=
        beq_eq_false_iff_ne.mpr hssEq
      have hSecNe : (sec' == sec) = false :=
        beq_eq_false_iff_ne.mpr (fun hEq => hssEq (by rw [hEq]))
      rw [hBeqF, hSecNe]
      rfl

/-- Semantic lift contract for `gl : GdhAtomicLift A` against a monad morphism `evalGdh`. -/
structure GdhAtomicLiftValid {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A)
    (evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α) : Prop where
  eval_liftI : ∀ {Γ : List PT} {τ : PT} (c : Comp pqxdhOps pqGapDhIface Γ τ) (ρ : Env Γ),
    (gl.liftI c).eval ρ = evalGdh (c.eval ρ)
  unsupported_eq : ∀ {Γ : List PT} {τ : PT} (c : Comp pqxdhOps pqGapDhIface Γ τ),
    (gl.liftI c).queries gl.tl.unsupportedW (fun _ => 0) =
      c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0)
  evalGdh_pure : ∀ {α : Type} (x : α), evalGdh (pure x) = pure x
  evalGdh_bind : ∀ {α β : Type} (m : OracleComp GdhSimSpec α)
    (k : α → OracleComp GdhSimSpec β),
    evalGdh (m >>= k) = evalGdh m >>= fun a => evalGdh (k a)
  mem_support_evalGdh : ∀ {α : Type} {m : OracleComp GdhSimSpec α} {x : α},
    x ∈ support (evalGdh m) → x ∈ support m

theorem liftGdhComp_unsupported_keyInd {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ τ) :
    (liftGdhComp c).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) =
      c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) := by
  induction c with
  | ret _ => rfl
  | bind _ _ ih1 ih2 => simp [liftGdhComp, Comp.queries, ih1, ih2]
  | ite _ _ _ ih1 ih2 => simp [liftGdhComp, Comp.queries, ih1, ih2]
  | caseOpt _ _ _ ih1 ih2 => simp [liftGdhComp, Comp.queries, ih1, ih2]
  | caseSum _ _ _ ih1 ih2 => simp [liftGdhComp, Comp.queries, ih1, ih2]
  | sample _ _ => rfl
  | query g _ => rcases g with t | ⟨⟩ <;> rfl
  | iter _ _ _ ih => simp [liftGdhComp, Comp.queries, ih]
  | findM _ _ _ ih => simp [liftGdhComp, Comp.queries, ih]
  | anyM _ _ _ ih => simp [liftGdhComp, Comp.queries, ih]
  | mapM _ _ _ ih => simp [liftGdhComp, Comp.queries, ih]
  | consumeFirstM _ _ _ _ ih => simp [liftGdhComp, Comp.queries, ih]
  | foldM _ _ _ _ ih => simp [liftGdhComp, Comp.queries, ih]

theorem gdhLift2Key_valid : GdhAtomicLiftValid gdhLift2Key (fun {_} m => m) where
  eval_liftI _ _ := rfl
  unsupported_eq _ := rfl
  evalGdh_pure _ := rfl
  evalGdh_bind _ _ := rfl
  mem_support_evalGdh h := h

theorem gdhLift1Key_valid : GdhAtomicLiftValid gdhLift1Key (fun {_} m => liftGdhToSign m) where
  eval_liftI c ρ := liftGdhComp_eval c ρ
  unsupported_eq c := liftGdhComp_unsupported_keyInd c
  evalGdh_pure x := liftGdhToSign_pure x
  evalGdh_bind m k := liftGdhToSign_bind m k
  mem_support_evalGdh h := mem_support_liftGdhToSign h

theorem GdhAtomicLiftValid.liftGdhAtomic_eval
    {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A}
    {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh)
    {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ τ)
    (hOk : c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0)
    (ρ : Env Γ) :
    (liftGdhAtomic gl c).eval (embedEnv ρ) = embedVal τ <$> evalGdh (c.eval ρ) := by
  unfold liftGdhAtomic
  rw [mapComp_eval gl.tl (gl.liftI c) (by rw [hgl.unsupported_eq]; exact hOk) ρ, hgl.eval_liftI]

theorem GdhAtomicLiftValid.evalGdh_map
    {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A}
    {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh)
    {α β : Type} (f : α → β) (m : OracleComp GdhSimSpec α) :
    evalGdh (f <$> m) = f <$> evalGdh m := by
  rw [map_eq_bind_pure_comp, hgl.evalGdh_bind, map_eq_bind_pure_comp]
  congr 1; funext a; exact hgl.evalGdh_pure (f a)

theorem GdhAtomicLiftValid.evalGdh_findML
    {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A}
    {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh)
    {α : Type} (p : α → OracleComp GdhSimSpec Bool) (L : List α) :
    evalGdh (findML p L) = findML (fun x => evalGdh (p x)) L := by
  induction L with
  | nil => exact hgl.evalGdh_pure none
  | cons x xs ih =>
    simp only [findML, hgl.evalGdh_bind]
    congr 1; funext b; cases b
    · exact ih
    · exact hgl.evalGdh_pure (some x)

theorem ddhEqC_unsupported_zero {Γ : List PT} (p1 p2 : Expr pqxdhOps Γ fgPosTy) :
    (ddhEqC p1 p2).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [ddhEqC, ddhQ, letV, caseSumV, Comp.queries, tlGapDhKeyInd]

theorem ddhEqOptC_unsupported_zero {Γ : List PT} (p1? p2? : Expr pqxdhOps Γ (.opt fgPosTy)) :
    (ddhEqOptC p1? p2?).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [ddhEqOptC, ddhEqC_unsupported_zero, letV, caseOptV, Comp.queries]

theorem entryMatchesC_unsupported_zero {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ssVar : Var Γ₅ (B 32))
    (eVar : Var Δ fgPatchEntryTy) :
    (entryMatchesC pos1 pos2 pos3 pos4? ssVar eVar).queries
      tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [entryMatchesC, ddhEqC_unsupported_zero, ddhEqOptC_unsupported_zero, bindV, Comp.queries]

theorem GdhAtomicLiftValid.liftGdhAtomic_entryMatchesC_ro_eval_eq_beq
    {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A}
    {evalGdh : ∀ {α : Type}, OracleComp GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ssVar : Var Γ₅ (B 32))
    (eVar : Var Δ fgPatchEntryTy) (env : Env Δ)
    (sec sec' : Bytes)
    (hQ : RoQueryPackWf sec
      (env.get (Ext.wk pos1)) (env.get (Ext.wk pos2)) (env.get (Ext.wk pos3))
      (env.get (Ext.wk pos4?)) (env.get (Ext.wk ssVar)))
    (hE : RoFgEntryWf sec' (embedVal fgPatchEntryTy (env.get eVar))) :
    (liftGdhAtomic gl (entryMatchesC pos1 pos2 pos3 pos4? ssVar eVar)).eval (embedEnv env) =
      pure (sec' == sec) := by
  rw [hgl.liftGdhAtomic_eval _ (entryMatchesC_unsupported_zero _ _ _ _ _ _) env,
      entryMatchesC_ro_eval_eq_beq pos1 pos2 pos3 pos4? ssVar eVar env sec sec' hQ hE,
      hgl.evalGdh_pure]
  rfl

/-- Maps `keyIndSentinel S b` back to `b.q_total + 1` on the four ordinal slots of `paramsTy`,
    leaving all other fields unchanged. -/
@[expose] def fixParamsSent (S : Setup) (b : QueryBudget)
    (pa : (embedTy paramsTy).denote) : (embedTy paramsTy).denote :=
  let (u, (vPk, (up, (prinFlag, (prinIdx, (dhFlag, (ephIdx, (spkIdx, (opkMode, (opkIdx, mode)))))))))) := pa
  (u, (vPk, (up, (prinFlag, (fixSent S b prinIdx,
    (dhFlag, (fixSent S b ephIdx, (fixSent S b spkIdx, (opkMode, (fixSent S b opkIdx, mode))))))))))

@[expose] def fixSig1KeyActiveSent (S : Setup) (b : QueryBudget)
    (st : (embedTy sig1KeyActiveStTy).denote) : (embedTy sig1KeyActiveStTy).denote :=
  let (tp?, (sm, (ord, rest))) := st
  (tp?, (sm, (fixSent S b ord, rest)))

/-- Forget map for `sigKeyInd1KeyKindAtomicProg`, dropping `fgShadowAtomicTy` and normalizing the
    target ordinal sentinel. -/
@[expose] def forgetSig1KeyActiveK (S : Setup) (b : QueryBudget)
    (stK : (Ty.prod (embedTy sig1KeyActiveStTy) fgShadowAtomicTy).denote) :
    (embedTy sig1KeyActiveStTy).denote :=
  fixSig1KeyActiveSent S b stK.1

@[expose] def fixGdh1KeyActiveSent (S : Setup) (b : QueryBudget)
    (st : (embedTy gdh1KeyActiveStateTy).denote) : (embedTy gdh1KeyActiveStateTy).denote :=
  let (((pa, sm), sigB), rest) := st
  (((fixParamsSent S b pa, sm), sigB), rest)

/-- Forget map for `fgKeyInd1KeyGapDhKindAtomicProg`, dropping `fgShadowAtomicTy` and normalizing
    `paramsTy` sentinels. -/
@[expose] def forgetGdh1KeyActiveK (S : Setup) (b : QueryBudget)
    (stK : (Ty.prod (embedTy gdh1KeyActiveStateTy) fgShadowAtomicTy).denote) :
    (embedTy gdh1KeyActiveStateTy).denote :=
  fixGdh1KeyActiveSent S b stK.1

/-- Shared simulation invariant bounding online and offline state lengths by `c` and relating
    `smFgL` and `smRaw` to their shadow AVL and session indices via `ShadowRelB192` and
    `RoCacheRelB192`. -/
structure GdhSimInv (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (sK : simShadowAtomicTy.denote) : Prop where
  online_len : BaseOnlineLenInv c (projVal keyIndStateTy sK.1.1)
  fg_sess_le : sK.2.1.length ≤ c 0
  fg_shadow  :
    ∃ tagged : List (TaggedEntry Bytes FgEntryA),
      ShadowRelB192 (drKeyT (ℓ := 0) (Pt := Empty)) b.q_total (keyIndKFuelsOfBudget S b).kAvl
        fgEntryDk sK.1.2.1 tagged sK.2.2.2.1 sK.2.1 sK.2.2.1 ∧
      (∀ te ∈ tagged, ∀ sec, te.tag = .ro sec → RoFgEntryWf sec te.entry) ∧
      (roEntriesOf fgEntryDk tagged).length ≤ c 1
  raw_len    : sK.1.2.2.1.length ≤ c 1
  raw_shadow :
    RoCacheRelB192 (drKeyT (ℓ := 0) (Pt := Empty)) b.q_total (keyIndKFuelsOfBudget S b).kAvl
      sK.1.2.2.1 sK.2.2.2.2
  log_len    : sK.1.2.2.2.1.length ≤ c 1
  pows_len   : sK.1.2.2.2.2.length ≤ c 0

theorem GdhSimInv_emptySim (S : Setup) (b : QueryBudget) (secb : Bool) :
    GdhSimInv S b 0
      (embedVal simTy ((emptySimE (.bool secb) : Expr pqxdhOps [] simTy).eval .nil),
       (emptyFgShadowE (Γ := [])).eval .nil) := by
  refine
    { online_len := ?_
      fg_sess_le := Nat.zero_le _
      fg_shadow := ⟨[], ?_, ?_, Nat.zero_le _⟩
      raw_len := Nat.zero_le _
      raw_shadow :=
        RoCacheRelB192.empty (drKeyT (ℓ := 0) (Pt := Empty))
          b.q_total (keyIndKFuelsOfBudget S b).kAvl dfltDrKeyE .nil
      log_len := Nat.zero_le _
      pows_len := Nat.zero_le _ }
  · have hProj :
        projVal keyIndStateTy
          (embedVal simTy ((emptySimE (.bool secb) : Expr pqxdhOps [] simTy).eval .nil)).1 =
          ((emptyStE (.bool secb) : Expr pqxdhOps [] keyIndStateTy).eval .nil) :=
      congrArg Prod.fst
        (projVal_embedVal simTy ((emptySimE (.bool secb) : Expr pqxdhOps [] simTy).eval .nil))
    rw [hProj]
    exact BaseOnlineLenInv.empty secb
  · exact ShadowRelB192.empty (drKeyT (ℓ := 0) (Pt := Empty))
      b.q_total (keyIndKFuelsOfBudget S b).kAvl fgEntryDk dfltFgRoValE .nil
  · intro te hMem; cases hMem

@[expose] def Gdh2SimInv (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (st : gdhShadowState2AtomicTy.denote) : Prop :=
  GdhSimInv S b c (st.1.2, st.2)

@[expose] def Sig1KeyActiveSimInv (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ)
    (stK : (Ty.prod (embedTy sig1KeyActiveStTy) fgShadowAtomicTy).denote) : Prop :=
  GdhSimInv S b c (stK.1.2.1, stK.2)

/-- Simulation invariant for `fgKeyInd1KeyGapDhKindAtomicProg`, pairing `GdhSimInv` with the
    `sendOpkCnt ≤ c 0` bound. -/
structure Gdh1KeyActiveSimInv (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ)
    (stK : (Ty.prod (embedTy gdh1KeyActiveStateTy) fgShadowAtomicTy).denote) : Prop where
  sim_inv       : GdhSimInv S b c (stK.1.1.1.2, stK.2)
  sendOpkCnt_le : stK.1.2.2 ≤ c 0

theorem GdhSimInv.fgSess_length_le_kOn {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {sK : simShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c sK)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j) :
    sK.2.1.length ≤ (keyIndKFuelsOfBudget S b).kOn := by
  have h0 := hB 0
  dsimp only [keyIndSimBounds, keyIndKFuelsOfBudget] at h0 ⊢
  exact Nat.le_trans hInv.fg_sess_le h0

theorem GdhSimInv.fgL_length_le_kFg {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {sK : simShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c sK)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j) :
    sK.1.2.1.length ≤ (keyIndKFuelsOfBudget S b).kFg := by
  obtain ⟨tagged, hRel, _, hRoLe⟩ := hInv.fg_shadow
  have hLen := hRel.length_eq_ro_add_sess
  have hSess := hInv.fg_sess_le
  have hSum := hInv.online_len.counts_eq
  have h0 := hB 0; have h1 := hB 1; have h2 := hB 2
  dsimp only [keyIndSimBounds, keyIndKFuelsOfBudget] at h0 h1 h2 ⊢
  omega

theorem GdhSimInv.fgL_length_le_q_total {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {sK : simShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c sK)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j) :
    sK.1.2.1.length ≤ b.q_total := by
  have h := hInv.fgL_length_le_kFg hB
  dsimp only [keyIndKFuelsOfBudget] at h
  omega

theorem GdhSimInv.ctr_add_one_le_q_total {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {sK : simShadowAtomicTy.denote} {t : KeyIndQuery S}
    (hInv : GdhSimInv S b c sK)
    (hRoom : ∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j) :
    sK.2.2.1 + 1 ≤ b.q_total := by
  obtain ⟨tagged, hRel, _, hRoLe⟩ := hInv.fg_shadow
  have hCtr : sK.2.2.1 = (roEntriesOf fgEntryDk tagged).length + sK.2.1.length :=
    hRel.1.ctr_eq_ro_add_sess
  have hSess := hInv.fg_sess_le
  have hSum := hInv.online_len.counts_eq
  have h2 : c 2 + 1 ≤ keyIndSimBounds b 2 := hRoom 2 trivial
  dsimp only [keyIndSimBounds] at h2
  have hLe : (roEntriesOf fgEntryDk tagged).length + sK.2.1.length + 1 ≤ b.q_total :=
    Nat.le_trans (Nat.add_le_add_right (hSum ▸ Nat.add_comm (c 0) (c 1) ▸ Nat.add_le_add hRoLe hSess) 1) h2
  exact hCtr ▸ hLe

theorem GdhSimInv.smRaw_length_le_kOff {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {sK : simShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c sK)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j) :
    sK.1.2.2.1.length ≤ (keyIndKFuelsOfBudget S b).kOff := by
  have h1 := hB 1
  dsimp only [keyIndSimBounds, keyIndKFuelsOfBudget] at h1 ⊢
  exact Nat.le_trans hInv.raw_len h1

theorem GdhSimInv.smRaw_length_le_q_total {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {sK : simShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c sK)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j) :
    sK.1.2.2.1.length ≤ b.q_total := by
  have h := hInv.smRaw_length_le_kOff hB
  dsimp only [keyIndKFuelsOfBudget] at h
  omega

theorem GdhSimInv.smRaw_add_one_le_q_total {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {sK : simShadowAtomicTy.denote} {sec : Bytes}
    (hInv : GdhSimInv S b c sK)
    (hRoom : ∀ j, keyIndSimPred S j (.roQuery sec) → c j + 1 ≤ keyIndSimBounds b j) :
    sK.1.2.2.1.length + 1 ≤ b.q_total := by
  have h1 : c 1 + 1 ≤ keyIndSimBounds b 1 := hRoom 1 ((keyIndSimPred_one_iff_kind _).mpr rfl)
  dsimp only [keyIndSimBounds] at h1
  have hRaw := hInv.raw_len
  omega

theorem GdhSimInv.smRaw_add_one_le_kAvl {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {sK : simShadowAtomicTy.denote} {sec : Bytes}
    (hInv : GdhSimInv S b c sK)
    (hRoom : ∀ j, keyIndSimPred S j (.roQuery sec) → c j + 1 ≤ keyIndSimBounds b j) :
    sK.1.2.2.1.length + 1 ≤ (keyIndKFuelsOfBudget S b).kAvl := by
  have h1 : c 1 + 1 ≤ keyIndSimBounds b 1 := hRoom 1 ((keyIndSimPred_one_iff_kind _).mpr rfl)
  dsimp only [keyIndSimBounds, keyIndKFuelsOfBudget] at h1 ⊢
  have hRaw := hInv.raw_len
  omega

theorem GdhSimInv.smLog_length_le_kOff {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {sK : simShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c sK)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j) :
    sK.1.2.2.2.1.length ≤ (keyIndKFuelsOfBudget S b).kOff := by
  have h1 := hB 1
  dsimp only [keyIndSimBounds, keyIndKFuelsOfBudget] at h1 ⊢
  exact Nat.le_trans hInv.log_len h1

theorem GdhSimInv.smPows_length_le_kOn {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {sK : simShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c sK)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j) :
    sK.1.2.2.2.2.length ≤ (keyIndKFuelsOfBudget S b).kOn := by
  have h0 := hB 0
  dsimp only [keyIndSimBounds, keyIndKFuelsOfBudget] at h0 ⊢
  exact Nat.le_trans hInv.pows_len h0

/-- Per-query step simulation obligation for a one-stage `KeyInd` reduction handler at query `t`,
    matching `StepSim.ForgetSim.hHandle`. -/
@[expose] def KeyIndStepSim
    {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {σ' σ : Ty pqAtomicSig}
    (S : Setup) (b : QueryBudget)
    (forget : σ'.denote → σ.denote)
    (Inv : (Fin 3 → ℕ) → σ'.denote → Prop)
    (handleK : Comp pqAtomicOps I [σ', (pqKeyIndCodec S).Q] (.prod (pqKeyIndCodec S).R σ'))
    (handleOld : Comp pqAtomicOps I [σ, (pqKeyIndCodec S).Q] (.prod (pqKeyIndCodec S).R σ))
    (t : KeyIndQuery S) : Prop :=
  ∀ (c : Fin 3 → ℕ) (s' : σ'.denote),
    (∀ j, c j ≤ keyIndSimBounds b j) →
    (∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j) →
    Inv c s' →
    Prod.map id forget <$> handleK.eval (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      handleOld.eval (.cons (forget s') (.cons ((pqKeyIndCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support (handleK.eval (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil))),
      Inv (bumpPred (keyIndSimPred S) c t) p.2

/-- Combines the 14 per-constructor `KeyIndStepSim` obligations into `StepSim.ForgetSim.hHandle`. -/
theorem hHandle_of_keyIndStepSim
    {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {σ' σ : Ty pqAtomicSig}
    (S : Setup) (b : QueryBudget)
    (forget : σ'.denote → σ.denote)
    (Inv : (Fin 3 → ℕ) → σ'.denote → Prop)
    (handleK : Comp pqAtomicOps I [σ', (pqKeyIndCodec S).Q] (.prod (pqKeyIndCodec S).R σ'))
    (handleOld : Comp pqAtomicOps I [σ, (pqKeyIndCodec S).Q] (.prod (pqKeyIndCodec S).R σ))
    (hInitPrin : ∀ u, KeyIndStepSim S b forget Inv handleK handleOld (.initPrin u))
    (hCorruptIK : ∀ u, KeyIndStepSim S b forget Inv handleK handleOld (.corruptIK u))
    (hGenSPK : ∀ u j, KeyIndStepSim S b forget Inv handleK handleOld (.genSPK u j))
    (hGenOPK : ∀ u j o, KeyIndStepSim S b forget Inv handleK handleOld (.genOPK u j o))
    (hInitOPK : ∀ u i bu, KeyIndStepSim S b forget Inv handleK handleOld (.initiateOPK u i bu))
    (hInitNoOPK : ∀ u i bu, KeyIndStepSim S b forget Inv handleK handleOld (.initiateNoOPK u i bu))
    (hAccOPK : ∀ k j o hdr, KeyIndStepSim S b forget Inv handleK handleOld (.acceptOPK k j o hdr))
    (hAccNoOPK : ∀ k j l hdr, KeyIndStepSim S b forget Inv handleK handleOld (.acceptNoOPK k j l hdr))
    (hTest : ∀ sid, KeyIndStepSim S b forget Inv handleK handleOld (.testSession sid))
    (hRo : ∀ sec, KeyIndStepSim S b forget Inv handleK handleOld (.roQuery sec))
    (hRevDh : KeyIndStepSim S b forget Inv handleK handleOld .revealDhSecrets)
    (hRevSess : ∀ sid, KeyIndStepSim S b forget Inv handleK handleOld (.revealSessionKey sid))
    (hRegKey : ∀ sk, KeyIndStepSim S b forget Inv handleK handleOld (.registerKey sk))
    (hRevSpk : ∀ u j, KeyIndStepSim S b forget Inv handleK handleOld (.revealSpkSk u j)) :
    ∀ (c : Fin 3 → ℕ) (s' : σ'.denote) (t : KeyIndQuery S),
      (∀ j, c j ≤ keyIndSimBounds b j) →
      (∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j) →
      Inv c s' →
      Prod.map id forget <$> handleK.eval (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
        handleOld.eval (.cons (forget s') (.cons ((pqKeyIndCodec S).qenc t) .nil)) ∧
      ∀ p ∈ support (handleK.eval (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil))),
        Inv (bumpPred (keyIndSimPred S) c t) p.2 := by
  intro c s' t
  cases t with
  | initPrin u => exact hInitPrin u c s'
  | corruptIK u => exact hCorruptIK u c s'
  | genSPK u j => exact hGenSPK u j c s'
  | genOPK u j o => exact hGenOPK u j o c s'
  | initiateOPK u i bu => exact hInitOPK u i bu c s'
  | initiateNoOPK u i bu => exact hInitNoOPK u i bu c s'
  | acceptOPK k j o hdr => exact hAccOPK k j o hdr c s'
  | acceptNoOPK k j l hdr => exact hAccNoOPK k j l hdr c s'
  | testSession sid => exact hTest sid c s'
  | roQuery sec => exact hRo sec c s'
  | revealDhSecrets => exact hRevDh c s'
  | revealSessionKey sid => exact hRevSess sid c s'
  | registerKey sk => exact hRegKey sk c s'
  | revealSpkSk u j => exact hRevSpk u j c s'

end

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase
