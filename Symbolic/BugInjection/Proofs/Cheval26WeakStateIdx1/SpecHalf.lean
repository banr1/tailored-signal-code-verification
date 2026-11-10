/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecAssembly
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCloseFinal
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoCloseFinal

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open Symbolic.BugInjection Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1
open Symbolic.BugInjection.Proofs.Common443

theorem specLeaves : SpecAssembly.SpecLeaves :=
  ⟨WsIdx1Split40MemoCloseFinal.split40MemoCensusOwn,
   WsIdx1Split81MemoCloseFinal.split81MemoCensusOwn⟩

theorem specObls : SpecTop.SpecObls :=
  SpecAssembly.specObls_of specLeaves

theorem not_collisionAt_wsIdx1 {r : Records} {S : Sem}
    (hfits : compFitsPinned setup SpecTop.compI0 r)
    (hnb : ∀ g ms τ₁, ExplainsMoves SpecTop.compI0 r S who ok g ms τ₁ → CompSetupSecrecy.NoBrk r ms) :
    ¬ CollisionAt SpecTop.compI0 r S who ok trace :=
  SpecTop.not_collisionAt_of specObls hfits hnb

end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1
