/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.ArmChainHeap
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.DecInterfacePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.DefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Tag-6 (`sender_chain`) Heap Framing Lemmas

Re-exports the layout-independent `SepProp` framing identities from `ArmChainHeap` alongside
`DecInterfacePlaced` and `DefsPlaced` for `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

abbrev overDecChainFramePlaced := overDecChainFrame
abbrev overDecChain_heap_pre_placed := @overDecChain_heap_pre
abbrev overDecChain_heap_post_placed := @overDecChain_heap_post
abbrev overDecChain_mem96_placed := @overDecChain_mem96
abbrev overDecChain_bridge_placed := @overDecChain_bridge

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
