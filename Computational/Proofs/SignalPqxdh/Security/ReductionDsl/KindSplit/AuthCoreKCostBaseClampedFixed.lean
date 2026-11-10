/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfBase

/-!
# Clamped `AuthPrf` Fixed-State Wrapper Bounds

Step-cost, `.random64`-coin, and primitive-query bounds for the clamped `AuthPrf` fixed-state
wrappers `initPrin1KeyFixedKB`, `corruptFixedKB`, `genSpkFixedKB`, `genOpkFixedKB`, and
`registerFixedKB`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBaseClampedFixed

open _root_.ReductionDsl (Ty Var Expr Comp)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (sampR64W r64W)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK (
  AuthKindFuels
  initPrin1KeyFixedKB corruptFixedKB genSpkFixedKB genOpkFixedKB registerFixedKB
)

section ClampedFixedWrapperBounds

open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface PTag PSamp B)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf (
  Ext PT authHybridStateFixedTy RSF
  v bindV letV caseOptV samplePrim queryPrim
  initPrinFixedB corruptFixedB genSpkFixedB genOpkFixedB registerFixedB
  initPrin1KeyFixedB initPrin1KeyFixedB_cost_le initPrin1KeyFixedB_queries_le
  initPrinFixedB_cost_le corruptFixedB_cost_le genSpkFixedB_cost_le
  genOpkFixedB_cost_le registerFixedB_cost_le
  primW primWS
  initPrinFixedB_queries corruptFixedB_queries genSpkFixedB_queries
  genOpkFixedB_queries registerFixedB_queries
)

@[local simp] private theorem samplePrim_r64_eq {Γ : List PT} (s : PSamp) :
    (samplePrim (Γ := Γ) s).queries (fun _ => 0) (sampR64W rfl) = r64W s := rfl

@[local simp] private theorem queryPrim_r64_eq {Γ : List PT} (g : PTag)
    (e : Expr pqxdhOps Γ g.dom) :
    (queryPrim g e).queries (fun _ => 0) (sampR64W rfl) = 0 := rfl

local macro "prove_r64" : tactic => `(tactic| {
  simp only [initPrin1KeyFixedKB, corruptFixedKB, genSpkFixedKB, genOpkFixedKB, registerFixedKB,
    initPrin1KeyFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, registerFixedB,
    bindV, letV, caseOptV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    Comp.iteC, Comp.caseOptC,
    samplePrim_r64_eq, queryPrim_r64_eq, r64W, Comp.queries,
    Nat.max_self, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  try omega })

section FixedTwoVar

variable {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]

theorem initPrin1KeyFixedKB_cost_le (F : AuthKindFuels)
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) :
    (initPrin1KeyFixedKB F (Δ := Δ) fhst u).cost ≤ 500 + F.K_on * 20 :=
  Nat.le_trans (initPrin1KeyFixedB_cost_le F.K_on fhst u) (initPrinFixedB_cost_le F.K_on fhst u)

theorem initPrin1KeyFixedKB_r64_le (F : AuthKindFuels)
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) :
    (initPrin1KeyFixedKB F (Δ := Δ) fhst u).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  prove_r64

theorem initPrin1KeyFixedKB_queries_prim_le (F : AuthKindFuels)
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) :
    (initPrin1KeyFixedKB F (Δ := Δ) fhst u).queries (fun _ => 1) (fun _ => 0) ≤ 2 :=
  Nat.le_trans (initPrin1KeyFixedB_queries_le F.K_on fhst u primW primWS)
    (Nat.le_of_eq (initPrinFixedB_queries F.K_on fhst u))

theorem corruptFixedKB_cost_le (F : AuthKindFuels)
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) :
    (corruptFixedKB F (Δ := Δ) fhst u).cost ≤ 500 + F.K_on * 50 :=
  corruptFixedB_cost_le F.K_on fhst u

theorem corruptFixedKB_r64_le (F : AuthKindFuels)
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) :
    (corruptFixedKB F (Δ := Δ) fhst u).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  prove_r64

theorem corruptFixedKB_queries_prim_le (F : AuthKindFuels)
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) :
    (corruptFixedKB F (Δ := Δ) fhst u).queries (fun _ => 1) (fun _ => 0) = 0 :=
  corruptFixedB_queries F.K_on fhst u

theorem genSpkFixedKB_cost_le (F : AuthKindFuels)
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat .nat)) :
    (genSpkFixedKB F (Δ := Δ) fhst x).cost ≤ 9500 + F.K_on * 30 :=
  genSpkFixedB_cost_le F.K_on fhst x

theorem genSpkFixedKB_r64_le (F : AuthKindFuels)
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat .nat)) :
    (genSpkFixedKB F (Δ := Δ) fhst x).queries (fun _ => 0) (sampR64W rfl) ≤ 3 := by
  prove_r64

theorem genSpkFixedKB_queries_prim_le (F : AuthKindFuels)
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat .nat)) :
    (genSpkFixedKB F (Δ := Δ) fhst x).queries (fun _ => 1) (fun _ => 0) ≤ 4 :=
  Nat.le_of_eq (genSpkFixedB_queries F.K_on fhst x)

theorem genOpkFixedKB_cost_le (F : AuthKindFuels)
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) :
    (genOpkFixedKB F (Δ := Δ) fhst x).cost ≤ 500 + F.K_on * 30 :=
  genOpkFixedB_cost_le F.K_on fhst x

theorem genOpkFixedKB_r64_le (F : AuthKindFuels)
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) :
    (genOpkFixedKB F (Δ := Δ) fhst x).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  prove_r64

theorem genOpkFixedKB_queries_prim_le (F : AuthKindFuels)
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) :
    (genOpkFixedKB F (Δ := Δ) fhst x).queries (fun _ => 1) (fun _ => 0) ≤ 1 :=
  Nat.le_of_eq (genOpkFixedB_queries F.K_on fhst x)

theorem registerFixedKB_cost_le
    (fhst : Var Γ₁ authHybridStateFixedTy) (sk : Var Γ₂ (B 32)) :
    (registerFixedKB (Δ := Δ) fhst sk).cost ≤ 500 :=
  registerFixedB_cost_le fhst sk

theorem registerFixedKB_r64_le
    (fhst : Var Γ₁ authHybridStateFixedTy) (sk : Var Γ₂ (B 32)) :
    (registerFixedKB (Δ := Δ) fhst sk).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  prove_r64

theorem registerFixedKB_queries_prim_le
    (fhst : Var Γ₁ authHybridStateFixedTy) (sk : Var Γ₂ (B 32)) :
    (registerFixedKB (Δ := Δ) fhst sk).queries (fun _ => 1) (fun _ => 0) ≤ 2 :=
  Nat.le_of_eq (registerFixedB_queries fhst sk)

end FixedTwoVar

end ClampedFixedWrapperBounds

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBaseClampedFixed
