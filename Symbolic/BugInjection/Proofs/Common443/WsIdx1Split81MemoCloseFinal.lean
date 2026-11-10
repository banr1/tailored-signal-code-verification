/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoClose
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81Enum
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoPreUntag
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFn
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoPreKdf

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoCloseFinal
open Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs
open Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRest (Split81DrawPinsOwn)
theorem split81RestFnOwn : Split81RestFnOwn := WsIdx1Split81MemoRestFn.split81RestFnOwn
theorem split81MemoCensusOwn_of_preKdf (hS : Split81PrefixEnum → Split81PreSalt32Own)
    (hKK : Split81PrefixEnum → Split81ExtKKOwn)
    (hKIR : Split81PrefixEnum → Split81DrawPinsOwn → Split81PreKIROwn) :
    WsIdx1CensusOwn.Split81MemoCensusOwn :=
  let hEnum := WsIdx1Prefix81Enum.split81PrefixEnum
  WsIdx1Split81MemoClose.split81MemoCensusOwn_of_leaves hEnum (WsIdx1Split81MemoPreUntag.split81PreNXOKOwn_of_enum hEnum) (hS hEnum) (hKK hEnum) (hKIR hEnum WsIdx1Split81MemoClose.split81DrawPinsOwn) split81RestFnOwn
theorem split81MemoCensusOwn : WsIdx1CensusOwn.Split81MemoCensusOwn := split81MemoCensusOwn_of_preKdf WsIdx1Split81MemoPreKdf.split81PreSalt32Own_of_enum WsIdx1Split81MemoPreKdf.split81ExtKKOwn_of_enum WsIdx1Split81MemoPreKdf.split81PreKIROwn_of_enum
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoCloseFinal
