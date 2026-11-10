/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.CollisionsA
public import Computational.Proofs.GameHop.Advantage
public import Computational.Proofs.GameHop.Fel
public import Computational.Proofs.GameHop.StateSim
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Computational.Proofs.SignalPqxdh.Security.CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-key collision invariant and potential bound

One-key (`pqxdhAuthImpl1KeyG`) counterparts of `runAuthSim` and
`pqxdhAuthImpl_valid_and_potential_le` from `CollisionsB`.
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal MeasureTheory BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

/-- Shared simulation core for `Auth` (`useRo = true, checkAuth = true`) and `HndlFirstMsg`
    (`useRo = false, checkAuth = false`). -/
noncomputable def runAuthSim1Key (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthState S) := do
  let secb ← $ᵗ Bool
  let initSt := AuthState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
    pqxdhAuthImpl1KeyG useRo checkAuth S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalSt)

theorem pqxdhAuthImpl_valid_and_potential_le1Key (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b1 b2 : Nat)
    (q : AuthQuery S) (st : AuthState S) (hV : ValidSpkBundlesKem S st.spkBundles) :
    (∀ x ∈ support ((pqxdhAuthImpl1KeyG useRo checkAuth S P q).run st),
        ValidSpkBundlesKem S x.2.spkBundles) ∧
    probExpect ((pqxdhAuthImpl1KeyG useRo checkAuth S P q).run st)
      (fun x => kemPairPotential S x.2.spkBundles b1 b2) ≤
      kemPairPotential S st.spkBundles b1 b2 := by
  suffices h_eq_or_gen :
      PreservesAt AuthState.spkBundles st (pqxdhAuthImpl1KeyG useRo checkAuth S P q) ∨
      (∃ u j, q = .genSPK u j) by
    rcases h_eq_or_gen with heq | ⟨u, j, rfl⟩
    · refine ⟨fun x hx => (heq x hx) ▸ hV, ?_⟩
      exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [heq x hx])
    · unfold pqxdhAuthImpl1KeyG
      dsimp only
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases hFresh : st.spkBundles.any (fun (k, _) => k == (u.val, j.val))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases st.principals.find? (fun (idx, _) => idx == u.val) with
        | none =>
          simp [StateT.run_pure, probExpect_pure, hV]
        | some uPair =>
          rcases uPair with ⟨_, uEntry⟩
          dsimp only
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind]
          refine ⟨?_, ?_⟩
          · intro x hx
            simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
            exact validSpkBundlesKem_cons S u j _ st.spkBundles hV hFresh
          · simp only [probExpect_bind, probExpect_pure]
            apply probExpect_const_le_of_support; intro spkSk _
            apply probExpect_const_le_of_support; intro rSpk _
            exact probExpect_kemPairPotential_cons_le S P hP u j st.spkBundles hV hFresh
              (fun pair rPq => {
                spkSk := spkSk
                spkPk := P.x25519Base spkSk
                spkSig := P.sigSign uEntry.secIKAsign (encodeEC (P.x25519Base spkSk)) rSpk
                pqspkSk := pair.2
                pqspkPk := pair.1
                pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pair.1) rPq
              })
              (fun _ _ => rfl) b1 b2
      · simp [StateT.run_pure, probExpect_pure, hV]
  have hSend : ∀ sid u bundle m0 m1,
      PreservesAt AuthState.spkBundles st (runAuthSend useRo S P sid u bundle m0 m1) := by
    intro sid u bundle m0 m1
    unfold runAuthSend; dsimp only
    repeat (first
      | with_reducible apply PreservesAt.pure
      | with_reducible apply PreservesAt.get_bind
      | (with_reducible apply PreservesAt.liftM_bind; intro _)
      | (with_reducible apply PreservesAt.set_bind; rfl)
      | (split; try dsimp only))
  cases q with
  | genSPK u j => right; exact ⟨u, j, rfl⟩
  | sendOPK u i bundle m0 m1 =>
    left; unfold pqxdhAuthImpl1KeyG; dsimp only
    split
    · exact PreservesAt.pure _ _ _
    · exact hSend _ _ _ _ _
  | sendNoOPK u i bundle m0 m1 =>
    left; unfold pqxdhAuthImpl1KeyG; dsimp only
    split
    · exact PreservesAt.pure _ _ _
    · exact hSend _ _ _ _ _
  | _ =>
    left; unfold pqxdhAuthImpl1KeyG
    dsimp only
    repeat (first
      | with_reducible apply PreservesAt.pure
      | with_reducible apply PreservesAt.get_bind
      | (with_reducible apply PreservesAt.liftM_bind; intro _)
      | (with_reducible apply PreservesAt.set_bind; rfl)
      | (split; try dsimp only))

end SignalPqxdh.Security
