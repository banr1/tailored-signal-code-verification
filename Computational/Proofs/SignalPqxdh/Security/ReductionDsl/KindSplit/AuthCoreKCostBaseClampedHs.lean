/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyShCr

/-!
# Clamped `AuthHs` Base Wrapper Bounds

Cost, `.random64` (`sampR64W`), and primitive query bounds for the clamped `AuthHs` base wrappers
`initPrin1KeyKB`, `corruptKB`, `genOpkKB`, and `registerKB`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBaseClampedHs

open _root_.ReductionDsl (Ty Var Comp)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (sampR64W r64W)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK (
  AuthKindFuels
  initPrin1KeyFuelB initPrin1KeyKB corruptKB genOpkKB registerKB
)

section ClampedHsWrapperBounds

open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (
  Ext RS
  initPrinB_costUB corruptB_costUB genOpkB_costUB registerB_costUB
  initPrinB_queries corruptB_queries genOpkB_queries registerB_queries
  initPrin1KeyB_cost_le initPrin1KeyB_queries_le
)

variable {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]

theorem initPrin1KeyKB_cost_le (F : AuthKindFuels) (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) :
    (initPrin1KeyKB F (Δ := Δ) st u).cost ≤ 419 + 5 * F.K_on :=
  (initPrin1KeyB_cost_le F.K_on st u).trans ((Comp.cost_le_costUB _).trans (le_of_eq (initPrinB_costUB F.K_on st u)))

theorem initPrin1KeyKB_r64_le (F : AuthKindFuels) (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) :
    (initPrin1KeyKB F (Δ := Δ) st u).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  change (initPrin1KeyKB F (Δ := Δ) st u).queries (fun _ => 0) r64W = 0
  simp [initPrin1KeyKB, initPrin1KeyFuelB, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV,
    _root_.ReductionDsl.Comp.iteC, _root_.ReductionDsl.Comp.sampleBytes32,
    _root_.ReductionDsl.Comp.queryPrim, r64W, Comp.queries]

theorem initPrin1KeyKB_queries_prim_le (F : AuthKindFuels)
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) :
    (initPrin1KeyKB F (Δ := Δ) st u).queries (fun _ => 1) (fun _ => 0) ≤ 2 :=
  (initPrin1KeyB_queries_le F.K_on st u _ _).trans (le_of_eq (initPrinB_queries F.K_on st u))

theorem corruptKB_cost_le (F : AuthKindFuels) (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) :
    (corruptKB F (Δ := Δ) st u).cost ≤ 212 + 38 * F.K_on :=
  (Comp.cost_le_costUB _).trans (le_of_eq (corruptB_costUB F.K_on st u))

theorem corruptKB_r64_le (F : AuthKindFuels) (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) :
    (corruptKB F (Δ := Δ) st u).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  simp [corruptKB, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.corruptB,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV, _root_.ReductionDsl.Comp.caseOptC, Comp.queries]

theorem corruptKB_queries_prim_le (F : AuthKindFuels) (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) :
    (corruptKB F (Δ := Δ) st u).queries (fun _ => 1) (fun _ => 0) = 0 :=
  corruptB_queries F.K_on st u

theorem genOpkKB_cost_le (F : AuthKindFuels)
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) :
    (genOpkKB F (Δ := Δ) st x).cost ≤ 314 + 25 * F.K_on :=
  (Comp.cost_le_costUB _).trans (le_of_eq (genOpkB_costUB F.K_on st x))

theorem genOpkKB_r64_le (F : AuthKindFuels)
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) :
    (genOpkKB F (Δ := Δ) st x).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  change (genOpkKB F (Δ := Δ) st x).queries (fun _ => 0) r64W = 0
  simp [genOpkKB, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genOpkB,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV, _root_.ReductionDsl.Comp.iteC,
    _root_.ReductionDsl.Comp.sampleBytes32, _root_.ReductionDsl.Comp.queryPrim,
    r64W, Comp.queries]

theorem genOpkKB_queries_prim_le (F : AuthKindFuels)
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) :
    (genOpkKB F (Δ := Δ) st x).queries (fun _ => 1) (fun _ => 0) ≤ 1 :=
  le_of_eq (genOpkB_queries F.K_on st x)

theorem registerKB_cost_le
    (st : Var Γ₁ authStateTy) (sk : Var Γ₂ (_root_.SignalPqxdh.LegacyCosted.B 32)) :
    (registerKB (Δ := Δ) st sk).cost ≤ 350 :=
  (Comp.cost_le_costUB _).trans (le_of_eq (registerB_costUB st sk))

theorem registerKB_r64_le
    (st : Var Γ₁ authStateTy) (sk : Var Γ₂ (_root_.SignalPqxdh.LegacyCosted.B 32)) :
    (registerKB (Δ := Δ) st sk).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  simp [registerKB, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.registerB,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV, _root_.ReductionDsl.Comp.iteC,
    _root_.ReductionDsl.Comp.queryPrim, Comp.queries]

theorem registerKB_queries_prim_le
    (st : Var Γ₁ authStateTy) (sk : Var Γ₂ (_root_.SignalPqxdh.LegacyCosted.B 32)) :
    (registerKB (Δ := Δ) st sk).queries (fun _ => 1) (fun _ => 0) ≤ 2 :=
  le_of_eq (registerB_queries st sk)

end ClampedHsWrapperBounds

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBaseClampedHs
