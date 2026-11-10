/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
public import Computational.Proofs.ReductionDsl.Soundness
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRG.CostedTables
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRF.CostedTables
import Computational.Proofs.ReductionDsl.Notation
import Computational.Proofs.ReductionDsl.Size
public import LibsignalBinary.Proofs.CryptoGames.Ratchet.RootKdfProofDefs

/-!
# Costed Root-KDF Step Reduction

Expresses `rootStepRed` as a 1-query `CostedReduction` (`rootStepRedProg`) over the shared PRF and
PRG operator tables, and proves operator size honesty, evaluation equivalence with `rootStepRed`,
total cost, and the 1-query bound.
-/

@[expose] public section

namespace CryptoGames.Ratchet.Costed

open ReductionDsl OracleComp OracleSpec CryptoGames CryptoGames.Ratchet
  CryptoGames.PRF.Costed CryptoGames.PRG.Costed
  CryptoVerification.LibsignalSession.Costed HMAC MACScheme
open scoped Computational.Proofs.ReductionDsl.Notation

variable (F : ShaState → List (BitVec 8) → ShaState) {Pt : Type} (I : Pt) (k : ℕ)

@[simp] private theorem env_get_cons_zero {S : Sig} {Γ : List (Ty S)} {t : Ty S}
    (x : t.denote) (ρ : Env Γ) : (Env.cons x ρ).get Var.zero = x := rfl

@[simp] private theorem env_get_cons_succ {S : Sig} {Γ : List (Ty S)} {t u : Ty S}
    (x : u.denote) (ρ : Env Γ) (v : Var Γ t) : (Env.cons x ρ).get (Var.succ v) = ρ.get v := rfl

/-- Costed 1-query PRF reduction for `rootStepPRG`: queries the PRF at `I`, expands the output via
`(expandPRG F).gen` at declared cost `k`, and runs the PRG distinguisher on the resulting pair. -/
def rootStepRedProg :
    CostedReduction
      (Ops.sum
        (prfConstantInputOps (S := prfSig Pt (BitVec 256)) (.base .inp) (fun _ : Unit => I))
        (prgOps (S := prfSig Pt (BitVec 256)) (.base .tag)
          (.prod (.base .tag) (.base .tag)) (expandPRG F).gen k))
      (prfIface (S := prfSig Pt (BitVec 256)) (.base .inp) (.base .tag))
      prgSpec (prgCodec (prfSig Pt (BitVec 256)))
      .unit (.prod (.base .tag) (.base .tag)) .bool .bool where
  σ := .unit
  init :=
    let O := Ops.sum
      (prfConstantInputOps (S := prfSig Pt (BitVec 256)) (.base .inp) (fun _ : Unit => I))
      (prgOps (S := prfSig Pt (BitVec 256)) (.base .tag)
        (.prod (.base .tag) (.base .tag)) (expandPRG F).gen k)
    rdsl do
      rk ← query () (Expr.op (O := O) (raw (.inl ())) ())
      return (Expr.op (O := O) (raw (.inr ())) rk, ())
  handle := rdsl do return ((), ())
  finish := rdsl [_, b] do return b

theorem rootStepOps_sizeHonest (hk : 1 ≤ k) :
    OpsSizeHonest
      (Ops.sum
        (prfConstantInputOps (S := prfSig Pt (BitVec 256)) (.base .inp) (fun _ : Unit => I))
        (prgOps (S := prfSig Pt (BitVec 256)) (.base .tag)
          (.prod (.base .tag) (.base .tag)) (expandPRG F).gen k)) := by
  refine OpsSizeHonest.sum (prfOps_sizeHonest (fun _ : Unit => I)) ?_
  intro _ x B _
  simp only [Ty.Fits]
  exact ⟨by omega, by omega⟩

theorem rootStepRedProg_eval (B : PRGScheme.PRGAdversary (RootKey × ChainKey)) :
    (rootStepRedProg F I k).eval (liftPRGAdv B) () = rootStepRed F I B := by
  have hU : ∀ n, (prfIface (S := prfSig Pt (BitVec 256)) (.base .inp) (.base .tag)).fwdU n =
      query (spec := unifSpec + MACScheme.prfSpec Pt (BitVec 256)) (.inl n) :=
    fun _ => rfl
  simp only [CostedReduction.eval, liftPRGAdv, simulateQ_liftPRGAdv_run hU (rootStepRedProg F I k)]
  simp [rootStepRedProg, rootStepRed, prfIface, Ops.sum, prfConstantInputOps, prgOps,
    Comp.eval, Expr.eval, Expr.v0, Expr.v1, evalQuery, bind_map_left]

theorem rootStepRedProg_totalCost (q : ℕ) :
    (rootStepRedProg F I k).totalCost q = q * 5 + k + 10 := by
  simp [CostedReduction.totalCost, rootStepRedProg, prgCodec, prfIface, Ops.sum, prfConstantInputOps, prgOps,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1]
  omega

theorem rootStepRedProg_queries (B : PRGScheme.PRGAdversary (RootKey × ChainKey)) :
    ((rootStepRedProg F I k).eval (liftPRGAdv B) ()).IsQueryBoundP
      (isGameQuery (G := MACScheme.prfSpec Pt (BitVec 256))) 1 := by
  have := CostedReduction.queryBound_eval (rootStepRedProg F I k)
    (isGameQuery (G := MACScheme.prfSpec Pt (BitVec 256))) (fun _ => 1) (fun s => nomatch s)
    (fun _ _ _ => le_rfl) (fun n => by simp [prfIface, isGameQuery])
    (liftPRGAdv B) 0 (isQueryBoundP_liftPRGAdv B 0) ()
  refine this.mono (le_of_eq ?_)
  simp [CostedReduction.totalQueries, rootStepRedProg, Comp.queries]

end CryptoGames.Ratchet.Costed
