/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnTbl
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnWire
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnSt
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnB

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFn
open Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs
theorem split81RestFnPreOwn : Split81RestFnPreOwn := WsIdx1Split81MemoRestFnSt.split81RestFnPreOwn
theorem split81RestFnOwn : Split81RestFnOwn := split81RestFnOwn_of_halves split81RestFnPreOwn WsIdx1Split81MemoRestFnB.split81RestFnNewOwn WsIdx1Split81MemoRestFnTbl.split81TblNodup
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFn
