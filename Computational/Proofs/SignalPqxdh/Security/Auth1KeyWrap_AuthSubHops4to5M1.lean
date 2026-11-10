/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthAead
public import Computational.Proofs.SignalPqxdh.Security.SigHopA
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C2
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5C1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-key multi-user AEAD integrity query bounds

One-key (`pqxdhAuthImpl1KeyG`) counterparts of the `MuBounded` and query-budget lemmas in
`AuthSubHops4to5M1` for `aeadMuIntReductionAuth1Key`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh

theorem muBounded_stepAuthMuPrim1Key (S : Setup) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    MuBounded (stepAuthMuPrim1Key S q hst)
      (if isAuthSendQuery (.inr q) then 1 else 0)
      (if isAuthRecvQuery (.inr q) then 1 else 0)
      (perQueryAuthPrimBudget S) := by
  unfold stepAuthMuPrim1Key
  cases q with
  | sendOPK u i bundle m0 m1 =>
    simp only [isAuthSendQuery, isAuthRecvQuery, ↓reduceIte]
    split <;>
      [exact muBounded_pure'; exact muBounded_runAuthSendMuPrim S (.sendOPK u i) u bundle m0 m1 hst]
  | sendNoOPK u i bundle m0 m1 =>
    simp only [isAuthSendQuery, isAuthRecvQuery, ↓reduceIte]
    split <;>
      [exact muBounded_pure';
       exact muBounded_runAuthSendMuPrim S (.sendNoOPK u i) u bundle m0 m1 hst]
  | recvOPK k j o msg =>
    simp only [isAuthSendQuery, isAuthRecvQuery, ↓reduceIte]
    unfold perQueryAuthPrimBudget
    refine muBounded_bind_le 0 1 (S.N_dh * 2 + S.N_sess_tot * 10 + 8)
      (muBounded_embedPrimMu _ 0 0 (S.N_dh * 4 + 8)
        (primBounded_prepareAuthRecvOPKPrim S k j o msg hst.toAuthHybridState))
      (fun prep? => ?_)
    cases prep? with
    | none => exact muBounded_pure'
    | some prep =>
      exact muBounded_bind_le 0 0 0
        (muBounded_evalAuthRecvScheduleMuPrim S prep.hstDec
          hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg)
        (fun _ => muBounded_pure')
  | recvNoOPK k j l msg =>
    simp only [isAuthSendQuery, isAuthRecvQuery, ↓reduceIte]
    unfold perQueryAuthPrimBudget
    refine muBounded_bind_le 0 1 (S.N_dh * 2 + S.N_sess_tot * 10 + 8)
      (muBounded_embedPrimMu _ 0 0 (S.N_dh * 4 + 8)
        (primBounded_prepareAuthRecvNoOPKPrim S k j l msg hst.toAuthHybridState))
      (fun prep? => ?_)
    cases prep? with
    | none => exact muBounded_pure'
    | some prep =>
      exact muBounded_bind_le 0 0 0
        (muBounded_evalAuthRecvScheduleMuPrim S prep.hstDec
          hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg)
        (fun _ => muBounded_pure')
  | initPrin u | corruptIK u | genSPK u j | genOPK u j o | registerKey sk | roQuery secrets
  | roRootQuery rk dh | revealDhSecrets =>
    simp only [isAuthSendQuery, isAuthRecvQuery, ↓reduceIte]
    unfold perQueryAuthPrimBudget
    exact muBounded_embedPrimMu _ 0 0 (S.N_dh * 14 + S.N_sess_tot * 10 + 18)
      ((primBounded_stepAuthOtherPrim1Key true S _ hst).mono (by omega))

theorem muBounded_aeadMuIntReductionAuthRun1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    MuBounded (aeadMuIntReductionAuthRun1Key S A.1)
      S.N_send_tot S.N_recv_tot (b.q_total * perQueryAuthPrimBudget S + S.N_dh * 5) := by
  unfold aeadMuIntReductionAuthRun1Key
  refine muBounded_bind_le S.N_send_tot S.N_recv_tot
    (b.q_total * perQueryAuthPrimBudget S + S.N_dh * 5)
    (muBounded_unifMu ($ᵗ Bool) 0 0 0) (fun secb => ?_)
  have hStep : MuBounded
      (runWithMuStep (stepAuthMuPrim1Key S) A.1.run (AuthHybridStateFixed.empty S secb))
      S.N_send_tot S.N_recv_tot (b.q_total * perQueryAuthPrimBudget S) :=
    ⟨isQueryBoundP_runWithMuStep_counted isMuEncQuery (fun _ h => by cases h)
      isAuthSendQuery (fun _ h => by cases h) (stepAuthMuPrim1Key S)
      (fun gq st => (muBounded_stepAuthMuPrim1Key S gq st).1)
      A.1.run S.N_send_tot (QueryBounded.auth_send A.2) (AuthHybridStateFixed.empty S secb),
     isQueryBoundP_runWithMuStep_counted isMuForgeQuery (fun _ h => by cases h)
      isAuthRecvQuery (fun _ h => by cases h) (stepAuthMuPrim1Key S)
      (fun gq st => (muBounded_stepAuthMuPrim1Key S gq st).2.1)
      A.1.run S.N_recv_tot (QueryBounded.auth_recv A.2) (AuthHybridStateFixed.empty S secb),
     isQueryBoundP_runWithMuStep_prim
      (stepAuthMuPrim1Key S) (perQueryAuthPrimBudget S)
      (fun gq st => (muBounded_stepAuthMuPrim1Key S gq st).2.2)
      A.1.run b.q_total (QueryBounded.auth_total A.2) (AuthHybridStateFixed.empty S secb)⟩
  exact muBounded_bind_le 0 0 (S.N_dh * 5) hStep (fun _ => muBounded_pure')

theorem aeadMuIntReductionAuth_bounded1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (aeadMuIntReductionAuth1Key S b A).Bounded :=
  muBounded_aeadMuIntReductionAuthRun1Key S b A

theorem aeadMuIntReductionAuth_queries1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (aeadMuIntReductionAuth1Key S b A).q_dec ≤ S.N_recv_tot := le_rfl

theorem aeadMuIntReductionAuth_enc_queries1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (aeadMuIntReductionAuth1Key S b A).q_enc ≤ S.N_send_tot := le_rfl

theorem aeadMuIntReductionAuth_prim_queries1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (aeadMuIntReductionAuth1Key S b A).q_prim ≤ primQueryBudget S b := by
  unfold aeadMuIntReductionAuth1Key perQueryAuthPrimBudget primQueryBudget
  dsimp only
  nlinarith

end SignalPqxdh.Security
