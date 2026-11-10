/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnSt
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnWire
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnB

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFn
open Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs
theorem split40RestFnPreOwn : Split40RestFnPreOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; obtain ⟨hwL₁, hwU₁, hwL₂, hwU₂⟩ := WsIdx1Split40MemoRestFnWire.split40_wire_bounds hp hinv
  exact WsIdx1Split40MemoRestFnSt.fnOK40_preMemo40_of_pins hfits hp hinv hown
    (by omega) (by omega) (by omega) (by omega)
theorem split40RestFnOwn : WsIdx1Split40MemoPreRest.Split40RestFnOwn := split40RestFnOwn_of_halves split40RestFnPreOwn WsIdx1Split40MemoRestFnB.split40RestFnNewOwn WsIdx1Split40MemoRestFnTbl.split40TblNodup
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFn
