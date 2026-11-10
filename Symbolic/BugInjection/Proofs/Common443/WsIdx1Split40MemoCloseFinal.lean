/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoClose
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKK
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreNX
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSub
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFn

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCloseFinal
open Symbolic.BugInjection.Proofs.Common443
theorem split40MemoCensusOwn_of_pending (hF : WsIdx1Split40MemoPreRest.Split40RestFnOwn) : WsIdx1CensusOwn.Split40MemoCensusOwn := WsIdx1Split40MemoClose.split40MemoCensusOwn_of_enum WsIdx1Prefix40Enum.split40PrefixEnum WsIdx1Split40MemoNewSub.split40NewSubOwn WsIdx1Split40MemoNewCensus.split40NewCensusOwn WsIdx1Split40MemoNewCensus.split40DrawPinsOwn WsIdx1Split40MemoPreKK.split40PreKKOwn WsIdx1Split40MemoPreNX.split40PreNXOKOwn hF
theorem split40MemoCensusOwn : WsIdx1CensusOwn.Split40MemoCensusOwn := split40MemoCensusOwn_of_pending WsIdx1Split40MemoRestFn.split40RestFnOwn
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCloseFinal
