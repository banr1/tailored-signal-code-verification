/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import Computational.Proofs.CryptoGames.SM.ReductionsQueries
public import Computational.Proofs.CryptoGames.FSAEAD.AeadRedBound
public import Computational.Proofs.CryptoGames.FSAEAD.PubProofDefs
import Computational.Proofs.GameHop.StateSim

/-!
# Query and AD-class preservation for `FSAEAD.pubRed`

**Checked by Lean.**

Proves decryption-query bounds (`pubRed_makesAtMostDecQueries`) and single-AD-class preservation
(`pubRed_adClassConst`) for `FSAEAD.pubRed`, along with single-query `IsQueryBoundP` helpers.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

set_option linter.unusedSectionVars false

namespace CryptoGames.LibsignalSM.Proofs.IndexRestrictions

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA
  AEADScheme MACScheme WireAEAD FSAEAD FSAEAD.Thm5

section Generic

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {σ α β : Type}

theorem stateT_lift_run {m : Type → Type} [Monad m] (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

theorem query_eq_liftM (t : spec.Domain) :
    (query (spec := spec) t : OracleComp spec (spec.Range t)) = liftM (spec.query t) := rfl

theorem isQueryBoundP_query_bind_pure_one {Q : spec.Domain → Prop} [DecidablePred Q]
    (t : spec.Domain) (f : spec.Range t → α) :
    IsQueryBoundP ((query (spec := spec) t : OracleComp spec _) >>= fun r => pure (f r)) Q 1 := by
  rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩

theorem isQueryBoundP_query_bind_pure_zero {Q : spec.Domain → Prop} [DecidablePred Q]
    (t : spec.Domain) (ht : ¬ Q t) (f : spec.Range t → α) :
    IsQueryBoundP ((query (spec := spec) t : OracleComp spec _) >>= fun r => pure (f r)) Q 0 := by
  rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl ht, fun _ => by simp⟩

end Generic

section PubRed

variable {SS RS AD Pub M C : Type}

theorem pubRed_makesAtMostDecQueries (pubOf : C → Option Pub)
    (A : FSAEAD.Adversary SS RS AD (Pub × M) C) {qd : ℕ}
    (hqd : FSAEAD.MakesAtMostDecQueries A qd) :
    FSAEAD.MakesAtMostDecQueries (FSAEAD.pubRed pubOf A) qd := by
  unfold FSAEAD.MakesAtMostDecQueries FSAEAD.pubRed
  rw [StateT.run'_eq]; refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  simpa only [Nat.mul_one] using
    Computational.Proofs.GameHop.StateSim.isQueryBoundP_simulateQ_stateT_inv
      (FSAEAD.pubRedImpl pubOf) (fun _ _ => True) 1
      (fun t _ _ hp _ => ⟨by
        rcases t with n | (((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩)
        · cases hp
        · cases hp
        · cases hp
        · cases hp
        · cases hp
        · unfold FSAEAD.pubRedImpl FSAEAD.deliverQuery; dsimp only
          cases pubOf c with
          | none => simp
          | some _ =>
            simp only [stateT_lift_run, bind_assoc]
            exact isQueryBoundP_query_bind_pure_one _ _
        · unfold FSAEAD.pubRedImpl FSAEAD.injectQuery; dsimp only
          cases pubOf c with
          | none => simp [StateT.run_get]
          | some _ =>
            simp only [stateT_lift_run, bind_assoc]
            exact isQueryBoundP_query_bind_pure_one _ _,
        fun _ _ => trivial⟩)
      (fun t _ _ hnp _ => ⟨by
        rcases t with n | (((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩)
        · exact isQueryBoundP_query_bind_pure_zero _ (by simp [FSAEAD.isDecQuery]) _
        · exact isQueryBoundP_query_bind_pure_zero _ (by simp [FSAEAD.isDecQuery]) _
        · exact isQueryBoundP_query_bind_pure_zero _ (by simp [FSAEAD.isDecQuery]) _
        · exact isQueryBoundP_query_bind_pure_zero _ (by simp [FSAEAD.isDecQuery]) _
        · unfold FSAEAD.pubRedImpl FSAEAD.corruptReceiverQuery
          simp only [StateT.run_bind, stateT_lift_run, bind_assoc]
          rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
          refine ⟨Or.inl (by simp [FSAEAD.isDecQuery]), fun r => by cases r <;> simp⟩
        · exact absurd rfl hnp
        · exact absurd rfl hnp, fun _ _ => trivial⟩)
      A qd hqd false trivial

theorem pubRed_adClassConst {κ : Type} [DecidableEq κ] (cls : AD → κ)
    (pubOf : C → Option Pub) (A : FSAEAD.Adversary SS RS AD (Pub × M) C)
    (hcls : FSAEAD.AllQueriesInOneADClass cls A) :
    FSAEAD.AllQueriesInOneADClass (fun ap : AD × Pub => cls ap.1) (FSAEAD.pubRed pubOf A) := by
  rcases hcls with ⟨k₀, hk₀⟩; refine ⟨k₀, ?_⟩
  unfold FSAEAD.pubRed; rw [StateT.run'_eq]; refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  simpa using
    Computational.Proofs.GameHop.StateSim.isQueryBoundP_simulateQ_stateT_inv
      (FSAEAD.pubRedImpl pubOf) (fun n _ => n = 0) 0
      (fun _ _ _ _ hm => nomatch hm)
      (fun t _ _ hnp hn => ⟨by
        rcases t with n | (((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩)
        · exact isQueryBoundP_query_bind_pure_zero _ (by simp [FSAEAD.queryADOutsideClass]) _
        · exact isQueryBoundP_query_bind_pure_zero _ (by simpa [FSAEAD.queryADOutsideClass] using hnp) _
        · exact isQueryBoundP_query_bind_pure_zero _ (by simpa [FSAEAD.queryADOutsideClass] using hnp) _
        · exact isQueryBoundP_query_bind_pure_zero _ (by simp [FSAEAD.queryADOutsideClass]) _
        · unfold FSAEAD.pubRedImpl FSAEAD.corruptReceiverQuery
          simp only [StateT.run_bind, stateT_lift_run, bind_assoc]
          rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
          refine ⟨Or.inl (by simp [FSAEAD.queryADOutsideClass]), fun r => by cases r <;> simp⟩
        · unfold FSAEAD.pubRedImpl FSAEAD.deliverQuery; dsimp only
          cases pubOf c with
          | none => simp
          | some p =>
            simp only [stateT_lift_run, bind_assoc]
            exact isQueryBoundP_query_bind_pure_zero _ (by simpa [FSAEAD.queryADOutsideClass] using hnp) _
        · unfold FSAEAD.pubRedImpl FSAEAD.injectQuery; dsimp only
          cases pubOf c with
          | none => simp [StateT.run_get]
          | some p =>
            simp only [stateT_lift_run, bind_assoc]
            exact isQueryBoundP_query_bind_pure_zero _ (by simpa [FSAEAD.queryADOutsideClass] using hnp) _,
        fun _ _ => hn⟩)
      A 0 hk₀ false rfl

end PubRed

section IdxBound

variable {CK MK AD M C : Type}

local notation "St" => HSt CK MK AD M C
local notation "HS" => HState CK MK AD M C
local notation "RMo" => RM CK MK AD M C

end IdxBound

section Main

variable {Pt : Type}

end Main

end CryptoGames.LibsignalSM.Proofs.IndexRestrictions
