/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacHA
public import Computational.Proofs.SignalPqxdh.Security.AeadMacInputInj
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M1
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacHA2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5C1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5M1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key MAC-Input Discipline for the `Auth` INT-CTXT Reduction

Proves `MacInputDisciplined'` for `aeadMuIntReductionAuth1Key` over the single-identity-key `Auth`
oracle `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

section PW

variable (P : Primitives)

end PW

section MuOK

variable (P : Primitives)

end MuOK

section Reduction

variable (P : Primitives)

theorem pw_stepAuthOtherPrim1Key (S : Setup) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hInv : PrinInv P hst) :
    PW P (stepAuthOtherPrim1Key true S q hst) (fun p => PrinInv P p.2) := by
  unfold stepAuthOtherPrim1Key
  dsimp only
  cases q
  all_goals
    repeat' (first
      | ((with_reducible refine pw_pure P _ _ ?_); exact hInv)
      | (with_reducible refine pw_pure P _ _ ?_)
      | with_reducible refine pw_ite P _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      | (with_reducible refine pw_primQ_bind P _ _ _ ?_)
      | with_reducible refine pw_bind_any P _ _ _ (fun _ => ?_)
      | split)
  all_goals
    intro e he
    simp only [List.mem_cons, List.mem_map] at he
    first
      | (rcases he with rfl | he
         · exact ⟨_, rfl⟩
         · exact hInv e he)
      | (obtain ⟨e0, he0, rfl⟩ := he
         obtain ⟨sk, hsk⟩ := hInv e0 he0
         exact ⟨sk, by split_ifs <;> exact hsk⟩)

theorem muOK_stepAuthMuPrim1Key (hP : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32)
    (S : Setup) (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hInv : PrinInv P hst) :
    MuOK P (stepAuthMuPrim1Key S q hst) (fun p => PrinInv P p.2) := by
  unfold stepAuthMuPrim1Key
  split
  · exact muOK_ite P _ _ _ _ (fun _ => muOK_pure P _ _ hInv)
      (fun _ => muOK_runAuthSendMuPrim P hP hLaw S _ _ _ _ _ hst hInv)
  · exact muOK_ite P _ _ _ _ (fun _ => muOK_pure P _ _ hInv)
      (fun _ => muOK_runAuthSendMuPrim P hP hLaw S _ _ _ _ _ hst hInv)
  · exact muOK_recv P S _ hst hInv _ (pw_prepareAuthRecvOPKPrim P S _ _ _ _ hst hInv) hP
  · exact muOK_recv P S _ hst hInv _ (pw_prepareAuthRecvNoOPKPrim P S _ _ _ _ hst hInv) hP
  · exact muOK_embedPrimMu P _ _ (pw_stepAuthOtherPrim1Key P S _ hst hInv)

theorem muOK_runWithMuStep1Key (hP : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32)
    (S : Setup) {α : Type} (oa : OracleComp (unifSpec + authSpec S) α) :
    ∀ hst : AuthHybridStateFixed S, PrinInv P hst →
      MuOK P (runWithMuStep (stepAuthMuPrim1Key S) oa hst) (fun _ => True) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro hst _; exact muOK_pure P _ _ trivial
  | query_bind t k ih =>
    intro hst hInv
    rcases t with n | gq
    · rw [runWithMuStep_query_inl]
      refine muOK_bind_any P _ _ _ ⟨?_, fun _ _ => trivial⟩ (fun u => ih u hst hInv)
      simp [primDetImpl, badAdQuery]
    · rw [runWithMuStep_query_inr]
      exact muOK_bind P _ _ _ _ (muOK_stepAuthMuPrim1Key P hP hLaw S gq hst hInv)
        (fun p hp => ih p.1 p.2 hp)

end Reduction

/-- The one-key `Auth` multi-key INT-CTXT reduction satisfies `MacInputDisciplined'`. -/
theorem aeadMuIntReductionAuth_disciplined1Key (S : Setup) (P : Primitives)
    (hP : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    MacInputDisciplined' P goodFirstMsgAD (aeadMuIntReductionAuth1Key S b A) := by
  unfold MacInputDisciplined' aeadMuIntReductionAuth1Key aeadMuIntReductionAuthRun1Key unifMu
  dsimp only
  have hInv : ∀ secb : Bool, PrinInv P (AuthHybridStateFixed.empty S secb) := by
    intro secb e he
    simp [AuthHybridStateFixed.empty, AuthHybridState.empty, AuthState.empty] at he
  have hstep : ∀ secb : Bool, MuOK P
      (runWithMuStep (stepAuthMuPrim1Key S) A.1.run (AuthHybridStateFixed.empty S secb) >>=
        fun _ => (pure () : OracleComp AeadMuIntSimSpec Unit)) (fun _ => True) :=
    fun secb => muOK_bind_any P _ _ (fun _ => True)
      (muOK_runWithMuStep1Key P hP hLaw S _ _ (hInv secb)) (fun _ => muOK_pure P _ _ trivial)
  exact (muOK_bind_any P _ _ (fun _ => True)
    (muOK_embedPrimMu P _ (fun _ => True) (fun _ _ => trivial)) hstep).1

end SignalPqxdh.Security
