/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith
import VCVio.OracleComp.QueryTracking.SubSpec
public import Computational.Proofs.CryptoGames.FSAEAD.HybridWithProofDefs
import Computational.Proofs.GameHop.StateSim

/-!
# Query Bounds for the OT-CCA Reduction

**Checked by Lean.**

Defines the state-uniform query-bound predicate `QB` on the OT-CCA reduction monad `RM` and proves
that coin sampling, key generation, key reveal, and corruption operations make zero non-coin
OT-CCA queries.
-/

@[expose] public section

open OracleComp OracleSpec

set_option linter.unusedSectionVars false

namespace CryptoGames.FSAEAD.Thm5

section Generic

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

theorem isQueryBoundP_false (oa : OracleComp spec α) (n : ℕ) :
    IsQueryBoundP oa (fun _ => False) n := by
  induction oa using OracleComp.inductionOn with
  | pure x => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl not_false, fun u => by simp [ih u]⟩

end Generic

variable {CK MK AD M C : Type}

/-- State monad of the hybrid game over the OT-CCA reduction oracles. -/
abbrev RM (CK MK AD M C : Type) := StateT (HSt CK MK AD M C) (OracleComp (RSpec AD M C))

section QB

/-- `x` makes at most `n` `Q`-queries from every hybrid state. -/
def QB (Q : (RSpec AD M C).Domain → Prop) [DecidablePred Q] {α : Type} (x : RM CK MK AD M C α)
    (n : ℕ) : Prop :=
  ∀ s : HSt CK MK AD M C, IsQueryBoundP (StateT.run x s) Q n

variable {Q : (RSpec AD M C).Domain → Prop} [DecidablePred Q]

theorem qb_pure {α : Type} (a : α) (n : ℕ) : QB Q (pure a : RM CK MK AD M C α) n := fun s => by
  simp

theorem qb_bind {α β : Type} {x : RM CK MK AD M C α} {f : α → RM CK MK AD M C β} {n m : ℕ} (hx : QB Q x n)
    (hf : ∀ a, QB Q (f a) m) : QB Q (x >>= f) (n + m) := fun s => by
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (hx s) fun p _ => hf p.1 p.2

theorem qb_bind0 {α β : Type} {x : RM CK MK AD M C α} {f : α → RM CK MK AD M C β} {m : ℕ} (hx : QB Q x 0)
    (hf : ∀ a, QB Q (f a) m) : QB Q (x >>= f) m := by
  simpa using qb_bind hx hf

theorem qb_mono {α : Type} {x : RM CK MK AD M C α} {n m : ℕ} (h : QB Q x n) (hnm : n ≤ m) : QB Q x m :=
  fun s => (h s).mono hnm

variable (hQu : ∀ u, ¬ Q (.inl u))
include hQu

theorem isQueryBoundP_liftProb {α : Type} (p : ProbComp α) :
    IsQueryBoundP (liftM p : OracleComp (RSpec AD M C) α) Q 0 :=
  IsQueryBoundP.liftComp_subSpec (p := fun _ => False)
    (fun t => ⟨False.elim, fun h => hQu t h⟩)
    (Computational.Proofs.GameHop.StateSim.isQueryBoundP_false p 0)

theorem isQueryBoundP_liftProb_pure {α β : Type} (p : ProbComp α) (f : α → β) :
    IsQueryBoundP ((liftM p : OracleComp (RSpec AD M C) α) >>= fun a => pure (f a)) Q 0 := by
  simpa using isQueryBoundP_bind (isQueryBoundP_liftProb hQu p)
    (fun a _ => isQueryBoundP_pure Q (f a) 0)

omit hQu in
theorem qb_bind_r {α β : Type} {x : RM CK MK AD M C α} {f : α → RM CK MK AD M C β} {n : ℕ}
    (hx : QB Q x n) (hf : ∀ a, QB Q (f a) 0) : QB Q (x >>= f) n := by
  simpa using qb_bind hx hf

omit hQu in
theorem qb_liftOM {α : Type} (x : OracleComp (RSpec AD M C) α) {n : ℕ} (h : IsQueryBoundP x Q n) :
    QB Q (liftM x : RM CK MK AD M C α) n := fun s => by
  show IsQueryBoundP (x >>= fun a => pure (a, s)) Q n
  simpa using isQueryBoundP_bind h (fun a _ => isQueryBoundP_pure Q (a, s) 0)

theorem qb_sampleH {α : Type} (p : ProbComp α) : QB Q (sampleH p : RM CK MK AD M C α) 0 :=
  qb_liftOM _ (isQueryBoundP_liftProb hQu p)

omit hQu in
theorem qb_getH : QB Q (getH : RM CK MK AD M C (HState CK MK AD M C)) 0 := fun s => by
  simp [getH, onH]

omit hQu in
theorem qb_modifyH (f : HState CK MK AD M C → HState CK MK AD M C) :
    QB Q (modifyH f : RM CK MK AD M C Unit) 0 := fun s => by
  simp [modifyH, onH]

end QB

section Ops

variable [SampleableType MK] [SampleableType CK]
  {Q : (RSpec AD M C).Domain → Prop} [DecidablePred Q] (hQu : ∀ u, ¬ Q (.inl u))
  (G : ℕ → PRGScheme CK (CK × MK)) (P : Params) (D : ℕ → ProbComp (CK × MK))
include hQu

theorem qb_genStep : QB Q (genStep G P D : RM CK MK AD M C Unit) 0 := by
  rintro ⟨h, sl⟩
  cases sl with
  | seed w => exact isQueryBoundP_pure _ _ _
  | mat pos mt =>
    simp only [genStep, StateT.run_mk]
    split_ifs <;> first | exact isQueryBoundP_liftProb_pure hQu _ _ | exact isQueryBoundP_pure _ _ _
  | unknown =>
    simp only [genStep, StateT.run_mk]
    split_ifs <;> exact isQueryBoundP_liftProb_pure hQu _ _

theorem qb_genN (n : ℕ) : QB Q (genN G P D n : RM CK MK AD M C Unit) 0 := by
  induction n with
  | zero => exact qb_pure _ _
  | succ n ih => exact qb_bind0 (qb_genStep hQu G P D) fun _ => ih

theorem qb_genUpTo (i : ℕ) : QB Q (genUpTo G P D i : RM CK MK AD M C Unit) 0 :=
  qb_bind0 qb_getH fun _ => qb_genN hQu G P D _

theorem qb_reveal : QB Q (reveal : RM CK MK AD M C CK) 0 := by
  rintro ⟨h, sl⟩
  cases sl with
  | seed w => exact isQueryBoundP_pure _ _ _
  | _ => simp only [reveal, StateT.run_mk]; exact isQueryBoundP_liftProb_pure hQu _ _

theorem qb_senderKey : QB Q (senderKey G : RM CK MK AD M C CK) 0 := by
  refine qb_bind0 qb_getH fun st => ?_
  split
  · exact qb_pure _ _
  · exact qb_reveal hQu

theorem qb_corruptSenderH (u : Unit) :
    QB Q (corruptSenderH (AD := AD) (M := M) (C := C) (MK := MK) G P u :
      RM CK MK AD M C _) 0 := by
  unfold corruptSenderH
  refine qb_bind0 qb_getH fun st => ?_
  split_ifs
  · exact qb_pure _ _
  · exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
  · exact qb_bind0 (qb_senderKey hQu G) fun _ => qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _

theorem qb_corruptReceiverH (u : Unit) :
    QB Q (corruptReceiverH (AD := AD) (M := M) (C := C) (MK := MK) G P u :
      RM CK MK AD M C _) 0 := by
  unfold corruptReceiverH
  refine qb_bind0 qb_getH fun st => ?_
  split_ifs
  · exact qb_pure _ _
  · exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
  · refine qb_bind0 (qb_senderKey hQu G) fun _ => ?_
    exact qb_bind0 qb_getH fun _ => qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _

end Ops

end CryptoGames.FSAEAD.Thm5
