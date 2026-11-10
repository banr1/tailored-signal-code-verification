/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyDefs
import Computational.Proofs.SignalPqxdh.Delta.KeyInd.Stop

/-!
# One-Key PQXDH δ Key Indistinguishability: Stop Disjunction and Store Invariance

**Checked by Lean.** Proves `KI1KeyStopStmt` (DEV-CLI16, DEV-PQ21) from `kiStop` and shows that
single-scalar `.initPrin` in `pqxdhKeyIndImpl1KeyRo` preserves `ValidKeyStores`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.RoKem
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

theorem validKeyStores_initPrin1Key (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (st : KeyIndState S) (hKS : ValidKeyStores S P st) :
    ∀ y ∈ support ((pqxdhKeyIndImpl1KeyRo S P (.initPrin u)).run st),
      ValidKeyStores S P y.2 := by
  rcases hKS with ⟨hVP, hVS, hVO, hPrins, hSpks, hOpks, hAdv⟩
  intro y hy
  unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal at hy
  dsimp only at hy
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
  revert hy
  cases hFresh : st.principals.any (fun (idx, _) => idx == u.val) with
  | true =>
    intro hy
    simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hVP, hVS, hVO, hPrins, hSpks, hOpks, hAdv⟩
  | false =>
    intro hy
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨secIKA0, hSec, rfl⟩
    have hLen : secIKA0.length = 32 := length_of_mem_support_sampleScalar32 hSec
    refine ⟨(validPrincipals_cons S u _ st.principals hVP hFresh).1, hVS, hVO, ?_, ?_, hOpks, hAdv⟩
    · intro kv hkv
      rcases List.mem_cons.mp hkv with rfl | hMem
      · exact ⟨hLen, rfl⟩
      · exact hPrins kv hMem
    · intro kv hkv
      rcases hSpks kv hkv with ⟨h1, h2, ⟨uEntry, huMem⟩, h4⟩
      exact ⟨h1, h2, ⟨uEntry, List.mem_cons_of_mem _ huMem⟩, h4⟩

theorem ki1KeyStop (S : Setup) : KI1KeyStopStmt S :=
  kiStop S

end Proofs.SignalPqxdh.Security.PqxdhDelta
