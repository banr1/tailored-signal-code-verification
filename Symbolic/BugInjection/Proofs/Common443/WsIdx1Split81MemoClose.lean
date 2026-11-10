/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPinRun
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNonInjOffZ
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRest
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoClose
open Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusOwn Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPrefix Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKdf Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPinRun Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNonInjOffZ Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRest Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape (QRest)
export WsIdx1Split81MemoQRest (split81DrawPinsOwn)
theorem split81ExtPairsOwn_qZ40_of_nx_offZ (hNX : Split81PreNXOKOwn) (hOffZ : Split81NonInjOffZOwn) : Split81ExtPairsOwn QZ40 := split81ExtPairsOwn_qZ40_of (split81ExtBaseUntaggedOwn_of_preNXOK hNX) hOffZ split81ZTagInj
theorem split81ExtPairsOwn_qZ40_of_enum (hEnum : Split81PrefixEnum) (hNX : Split81PreNXOKOwn) : Split81ExtPairsOwn QZ40 := split81ExtPairsOwn_qZ40_of_nx_offZ hNX (split81NonInjOffZOwn_of_enum hEnum)
theorem split81ExtPairsOwn_qRest40_of_enum_leaves (hEnum : Split81PrefixEnum) (hNX : Split81PreNXOKOwn) (hS : Split81PreSalt32Own) (hKK : Split81ExtKKOwn) (hKIR : Split81PreKIROwn) (hFn : Split81RestFnOwn) : Split81ExtPairsOwn QRest40 := split81ExtPairsOwn_qRest40_of_leaves' hEnum hNX hS hKK hKIR (split81NonInjCensusOwn_of_enum hEnum) hFn
theorem split81MemoCensusOwn_of_leaves (hEnum : Split81PrefixEnum) (hNX : Split81PreNXOKOwn) (hS : Split81PreSalt32Own) (hKK : Split81ExtKKOwn) (hKIR : Split81PreKIROwn) (hFn : Split81RestFnOwn) : WsIdx1CensusOwn.Split81MemoCensusOwn := split81MemoCensusOwn_of_ext_parts (split81ExtPairsOwn_qZ40_of_enum hEnum hNX) (split81ExtPairsOwn_qRest40_of_enum_leaves hEnum hNX hS hKK hKIR hFn)
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoClose
