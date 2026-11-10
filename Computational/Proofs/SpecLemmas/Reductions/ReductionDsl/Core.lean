/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core

@[expose] public section

set_option autoImplicit false

/-!
# Additional `ReductionDsl` variable helper

**Checked by Lean.** De Bruijn variable shorthand `Expr.v7` for `ReductionDsl` programs.
-/

namespace ReductionDsl

variable {S : Sig}

variable {O : Ops S}

def Expr.v7 {Γ t a b c d e f g} : Expr O (a :: b :: c :: d :: e :: f :: g :: t :: Γ) t :=
  .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))

variable {ι : Type} {T : OracleSpec ι} {I : Iface S T}

variable {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}

variable {rIn aIn aOut out : Ty S}

variable {ch rIn2 : Ty S}

end ReductionDsl
